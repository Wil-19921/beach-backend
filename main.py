from __future__ import annotations

from fastapi import FastAPI, HTTPException, Query, Request, Header
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import StreamingResponse, PlainTextResponse, JSONResponse
from pydantic import BaseModel, Field
from typing import Literal, Optional, List
from datetime import datetime, date, timedelta, time as dtime
from io import BytesIO
import os
import hmac
import hashlib
import base64

import psycopg
from psycopg.rows import dict_row

import qrcode

# =========================
# Config
# =========================

DATABASE_URL = os.environ.get("DATABASE_URL")

ENV = (os.environ.get("ENV") or "development").strip().lower()
CORS_ORIGINS = os.environ.get("CORS_ORIGINS", "")

ADMIN_EMAIL = os.environ.get("ADMIN_EMAIL", "admin@beach.com").strip().lower()
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "123456")

Status = Literal["awaiting_payment", "paid_with_deposit", "completed", "canceled"]
PayMethod = Literal["pix", "debit", "credit", "cash", "card"]

PRECO_PRIMEIRO_DIA_KIT = 50.0
PRECO_DEMAIS_DIAS_KIT = 25.0
PRECO_CADEIRA_EXTRA_DIA = 10.0
CAUCAO_POR_KIT = 200.0

TOTAL_KITS = 50
RESERVATION_EXPIRATION_MINUTES = 30

CANCEL_DEADLINE_DAYS_BEFORE_INICIO = 2
CANCEL_FEE_DEPOSIT_RATE = 0.30

PICKUP_SECRET = os.environ.get("PICKUP_SECRET", "troque-essa-chave-em-producao")

KIT_NOME = "Kit Praia"
KIT_ITENS = ["2 cadeiras", "1 guarda-sol", "1 mesa de centro"]
KIT_DESCRICAO = "Inclui 2 cadeiras, 1 guarda-sol e 1 mesa de centro."

CODE_PREFIX = "BCH"
CODE_TOKEN_LEN = 10


def _require_admin_credentials_configured():
    if ENV == "production":
        if not ADMIN_EMAIL or not ADMIN_PASSWORD:
            raise RuntimeError(
                "ADMIN_EMAIL e ADMIN_PASSWORD devem estar definidos em produção."
            )


def _parse_origins(s: str) -> list[str]:
    return [o.strip() for o in (s or "").split(",") if o.strip()]


def require_admin_credentials(
    x_admin_email: str | None = Header(default=None),
    x_admin_password: str | None = Header(default=None),
):
    if not x_admin_email or not x_admin_password:
        raise HTTPException(status_code=401, detail="Admin não autenticado.")

    email = x_admin_email.strip().lower()
    password = x_admin_password

    if email != ADMIN_EMAIL or password != ADMIN_PASSWORD:
        raise HTTPException(status_code=401, detail="Email ou senha de admin inválidos.")


# =========================
# DB helpers (Postgres)
# =========================

def _require_db_url():
    if not DATABASE_URL:
        raise RuntimeError(
            "DATABASE_URL não definido. No Render, crie um Postgres e configure DATABASE_URL no serviço."
        )


def get_conn() -> psycopg.Connection:
    _require_db_url()
    return psycopg.connect(DATABASE_URL, row_factory=dict_row, autocommit=True)


def normalize_phone(phone: str) -> str:
    raw = "".join(ch for ch in (phone or "") if ch.isdigit())

    if not raw:
        raise HTTPException(status_code=400, detail="Telefone inválido.")

    if raw.startswith("55") and len(raw) >= 12:
        raw = raw[2:]

    if len(raw) < 10 or len(raw) > 11:
        raise HTTPException(status_code=400, detail="Telefone inválido. Use DDD + número.")

    return raw


def _normalize_phone_lenient(phone: str) -> str:
    raw = "".join(ch for ch in (phone or "") if ch.isdigit())
    if raw.startswith("55") and len(raw) >= 12:
        raw = raw[2:]
    return raw


def deduplicate_customers(conn: psycopg.Connection) -> None:
    rows = conn.execute(
        "SELECT id, name, phone, created_at FROM customers ORDER BY id ASC;"
    ).fetchall()

    if not rows:
        return

    grouped: dict[str, list[dict]] = {}
    for row in rows:
        phone_norm = _normalize_phone_lenient(row.get("phone") or "")
        if not phone_norm:
            continue
        grouped.setdefault(phone_norm, []).append(dict(row))

    for normalized_phone, items in grouped.items():
        keeper = items[0]
        keeper_id = int(keeper["id"])

        conn.execute(
            "UPDATE customers SET phone = %s WHERE id = %s;",
            (normalized_phone, keeper_id),
        )

        for dup in items[1:]:
            dup_id = int(dup["id"])

            conn.execute(
                """
                UPDATE reservations
                SET customer_id = %s
                WHERE customer_id = %s;
                """,
                (keeper_id, dup_id),
            )

            dup_name = (dup.get("name") or "").strip()
            keeper_name = (keeper.get("name") or "").strip()

            if not keeper_name and dup_name:
                conn.execute(
                    "UPDATE customers SET name = %s WHERE id = %s;",
                    (dup_name, keeper_id),
                )
                keeper["name"] = dup_name

            conn.execute("DELETE FROM customers WHERE id = %s;", (dup_id,))

    conn.execute(
        "UPDATE customers SET phone = regexp_replace(phone, '\\D', '', 'g') WHERE phone IS NOT NULL;"
    )
    conn.execute(
        """
        UPDATE customers
        SET phone = substring(phone from 3)
        WHERE phone ~ '^55[0-9]{10,11}$';
        """
    )


def init_db() -> None:
    with get_conn() as conn:
        conn.execute("""
        CREATE TABLE IF NOT EXISTS kits (
            id INTEGER PRIMARY KEY
        );
        """)

        conn.execute("""
        CREATE TABLE IF NOT EXISTS customers (
            id SERIAL PRIMARY KEY,
            name TEXT NOT NULL,
            phone TEXT NOT NULL,
            created_at TIMESTAMPTZ NOT NULL
        );
        """)

        conn.execute("""
        CREATE TABLE IF NOT EXISTS reservations (
            id SERIAL PRIMARY KEY,
            kit_id INTEGER NOT NULL REFERENCES kits(id),

            inicio DATE NOT NULL,
            fim DATE NOT NULL,

            dias INTEGER NOT NULL,
            cadeiras_extras INTEGER NOT NULL,

            aluguel_kit DOUBLE PRECISION NOT NULL,
            valor_cadeiras_extras DOUBLE PRECISION NOT NULL,
            total DOUBLE PRECISION NOT NULL,
            caucao DOUBLE PRECISION NOT NULL,

            status TEXT NOT NULL,
            created_at TIMESTAMPTZ NOT NULL,

            paid_at TIMESTAMPTZ,
            pay_method TEXT,

            checked_out_at TIMESTAMPTZ,
            checked_in_at TIMESTAMPTZ,

            canceled_at TIMESTAMPTZ,
            cancel_reason TEXT,
            cancel_fee DOUBLE PRECISION,
            cancel_fee_type TEXT,

            customer_id INTEGER REFERENCES customers(id),
            source TEXT
        );
        """)

        conn.execute("""
        ALTER TABLE reservations
        ADD COLUMN IF NOT EXISTS customer_id INTEGER REFERENCES customers(id);
        """)

        conn.execute("""
        ALTER TABLE reservations
        ADD COLUMN IF NOT EXISTS source TEXT;
        """)

        conn.execute("""
        CREATE INDEX IF NOT EXISTS idx_resv_kit_status_dates
        ON reservations (kit_id, status, inicio, fim);
        """)

        conn.execute("""
        CREATE INDEX IF NOT EXISTS idx_resv_customer_id
        ON reservations (customer_id);
        """)

        deduplicate_customers(conn)

        conn.execute("""
        CREATE UNIQUE INDEX IF NOT EXISTS ux_customers_phone
        ON customers (phone);
        """)

        cur = conn.execute("SELECT COUNT(*) AS c FROM kits;")
        c = int(cur.fetchone()["c"])

        if c < TOTAL_KITS:
            conn.execute("DELETE FROM kits;")

        with conn.cursor() as cur2:
            cur2.executemany(
                "INSERT INTO kits(id) VALUES (%s) ON CONFLICT (id) DO NOTHING;",
                [(i,) for i in range(1, TOTAL_KITS + 1)],
            )


# =========================
# Helpers
# =========================

def parse_date(s: str) -> date:
    try:
        return date.fromisoformat(s)
    except Exception:
        raise HTTPException(status_code=400, detail="Data inválida. Use YYYY-MM-DD.")


def calc_dias(inicio: date, fim: date) -> int:
    delta = (fim - inicio).days
    if delta < 0:
        raise HTTPException(status_code=400, detail="fim não pode ser anterior ao início.")
    return delta + 1


def calc_preco(dias: int, cadeiras_extras: int) -> tuple[float, float, float]:
    if dias <= 0:
        return 0.0, 0.0, 0.0

    if dias == 1:
        aluguel_kit = PRECO_PRIMEIRO_DIA_KIT
    else:
        aluguel_kit = PRECO_PRIMEIRO_DIA_KIT + (dias - 1) * PRECO_DEMAIS_DIAS_KIT

    valor_cadeiras = float(cadeiras_extras) * PRECO_CADEIRA_EXTRA_DIA * dias
    total = aluguel_kit + valor_cadeiras
    return aluguel_kit, valor_cadeiras, total


def expire_awaiting_payments(conn: psycopg.Connection) -> int:
    now = datetime.utcnow()
    threshold = now - timedelta(minutes=RESERVATION_EXPIRATION_MINUTES)

    rows = conn.execute(
        """
        SELECT id
        FROM reservations
        WHERE status = 'awaiting_payment'
          AND created_at <= %s
        """,
        (threshold,),
    ).fetchall()

    if not rows:
        return 0

    ids = [int(r["id"]) for r in rows]
    conn.execute(
        """
        UPDATE reservations
        SET status = 'canceled',
            canceled_at = %s,
            cancel_reason = COALESCE(cancel_reason, 'expired')
        WHERE id = ANY(%s)
        """,
        (now, ids),
    )
    return len(ids)


def kit_disponivel(conn: psycopg.Connection, kit_id: int, inicio: date, fim: date) -> bool:
    r = conn.execute(
        """
        SELECT 1
        FROM reservations
        WHERE kit_id = %s
          AND status <> 'canceled'
          AND NOT (fim < %s OR inicio > %s)
        LIMIT 1
        """,
        (kit_id, inicio, fim),
    ).fetchone()
    return r is None


def cancel_deadline_dt(inicio_str: str) -> datetime:
    inicio = parse_date(inicio_str)
    deadline_date = inicio - timedelta(days=CANCEL_DEADLINE_DAYS_BEFORE_INICIO)
    return datetime.combine(deadline_date, dtime(23, 59, 59))


def get_or_create_customer(conn: psycopg.Connection, name: str, phone: str) -> int:
    name = (name or "").strip()
    phone = normalize_phone(phone)

    if not name:
        raise HTTPException(status_code=400, detail="Nome do cliente é obrigatório.")

    existing = conn.execute(
        "SELECT id, name, phone, created_at FROM customers WHERE phone = %s LIMIT 1;",
        (phone,),
    ).fetchone()

    if existing:
        customer_id = int(existing["id"])
        old_name = (existing.get("name") or "").strip()

        if name and old_name != name:
            conn.execute(
                "UPDATE customers SET name = %s WHERE id = %s;",
                (name, customer_id),
            )

        return customer_id

    created_at = datetime.utcnow()
    row = conn.execute(
        """
        INSERT INTO customers(name, phone, created_at)
        VALUES (%s, %s, %s)
        RETURNING id;
        """,
        (name, phone, created_at),
    ).fetchone()

    return int(row["id"])


# =========================
# Signing / codes
# =========================

def _b64u(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).decode().rstrip("=")


def sign_pickup_token(reservation_id: int, created_at: str) -> str:
    msg = f"{reservation_id}|{created_at}".encode()
    sig = hmac.new(PICKUP_SECRET.encode(), msg, hashlib.sha256).digest()
    return _b64u(sig)


def verify_pickup_token_prefix(reservation_id: int, created_at: str, token_prefix: str) -> bool:
    expected = sign_pickup_token(reservation_id, created_at)
    return hmac.compare_digest(expected[:len(token_prefix)], token_prefix)


def build_code_text(reservation_id: int, kit_id: int, created_at: str) -> str:
    token_prefix = sign_pickup_token(reservation_id, created_at)[:CODE_TOKEN_LEN]
    return f"{CODE_PREFIX}-{reservation_id}-{kit_id}-{token_prefix}"


def parse_code_text(code: str) -> tuple[int, int, str]:
    raw = (code or "").strip()

    parts = raw.split("-", 3)

    if len(parts) != 4 or parts[0] != CODE_PREFIX:
        raise HTTPException(
            status_code=400,
            detail="Código inválido. Formato: BCH-<rid>-<kit>-<token>."
        )

    try:
        rid = int(parts[1])
        kit = int(parts[2])
    except Exception:
        raise HTTPException(status_code=400, detail="Código inválido: IDs não numéricos.")

    token = parts[3].strip()
    if not token:
        raise HTTPException(status_code=400, detail="Código inválido: token vazio.")

    return rid, kit, token


# =========================
# Schemas
# =========================

class KitOut(BaseModel):
    id: int


class AvailabilityOut(BaseModel):
    inicio: str
    fim: str
    available_kits: List[int]


class ReservationCreate(BaseModel):
    customer_id: int
    inicio: str = Field(..., description="YYYY-MM-DD")
    fim: str = Field(..., description="YYYY-MM-DD")
    kit_id: int
    cadeiras_extras: int = 0


class ReservationOut(BaseModel):
    id: int
    kit_id: int
    inicio: str
    fim: str
    dias: int
    cadeiras_extras: int
    aluguel_kit: float
    valor_cadeiras_extras: float
    total: float
    caucao: float
    status: Status
    created_at: str
    paid_at: Optional[str] = None
    pay_method: Optional[PayMethod] = None
    checked_out_at: Optional[str] = None
    checked_in_at: Optional[str] = None
    canceled_at: Optional[str] = None
    cancel_reason: Optional[str] = None
    cancel_fee: Optional[float] = None
    cancel_fee_type: Optional[str] = None
    customer_id: Optional[int] = None
    source: Optional[str] = None


class PaymentCreate(BaseModel):
    reservation_id: int
    method: PayMethod


class PaymentOut(BaseModel):
    reservation_id: int
    method: PayMethod
    deposit_amount: float
    paid_at: str
    new_status: Status


class ProductOut(BaseModel):
    name: str
    description: str
    items: List[str]
    pricing: dict


class QuoteOut(BaseModel):
    inicio: str
    fim: str
    dias: int
    cadeiras_extras: int
    aluguel_kit: float
    valor_cadeiras_extras: float
    total: float
    caucao: float


class BulkReservationCreate(BaseModel):
    inicio: str = Field(..., description="YYYY-MM-DD")
    fim: str = Field(..., description="YYYY-MM-DD")
    quantity: int = Field(..., ge=1, le=TOTAL_KITS)
    cadeiras_extras: int = Field(0, ge=0, description="por kit")
    customer_name: str = Field(..., min_length=2)
    customer_phone: str = Field(..., min_length=8)


class BulkReservationOut(BaseModel):
    reservations: List[ReservationOut]


class CancelIn(BaseModel):
    reason: Optional[str] = Field(None, description="Motivo do cancelamento (opcional)")


class CancelOut(BaseModel):
    ok: bool
    reservation: ReservationOut
    fee_retained_from_deposit: float
    deposit_refund_expected: float
    rent_refund_expected: float
    cancel_deadline_utc: str


class AdminScanCodeIn(BaseModel):
    code: str


class AdminCancelIn(BaseModel):
    reason: Optional[str] = None


class AdminCancelOut(BaseModel):
    ok: bool
    reservation: ReservationOut
    fee_retained_from_deposit: float
    deposit_refund_expected: float
    rent_refund_expected: float


class CustomerCreate(BaseModel):
    name: str
    phone: str


class CustomerOut(BaseModel):
    id: int
    name: str
    phone: str
    created_at: str


class CustomerLoginIn(BaseModel):
    name: str
    phone: str


class CustomerLoginOut(BaseModel):
    customer: CustomerOut
    is_new: bool


class AdminWalkInReservationCreate(BaseModel):
    customer_id: int
    inicio: str
    fim: str
    quantity: int = Field(..., ge=1, le=TOTAL_KITS)
    cadeiras_extras: int = Field(0, ge=0)
    pay_method: PayMethod = Field(..., description="cash | card | pix | debit | credit")


class AdminLoginIn(BaseModel):
    email: str
    password: str


class AdminLoginOut(BaseModel):
    ok: bool
    email: str
    message: str


# =========================
# App
# =========================

app = FastAPI(title="Beach Backend", version="0.8.0")


@app.get("/")
def root():
    return {"ok": True, "service": "beach-backend"}


origins = ["*"] if ENV != "production" else _parse_origins(CORS_ORIGINS)

app.add_middleware(
    CORSMiddleware,
    allow_origins=origins,
    allow_credentials=False,
    allow_methods=["*"],
    allow_headers=["*"],
)


@app.middleware("http")
async def security_middleware(request: Request, call_next):
    path = request.url.path

    if request.method == "OPTIONS":
        return await call_next(request)

    if ENV == "production" and path in ("/docs", "/redoc", "/openapi.json"):
        return JSONResponse(status_code=404, content={"detail": "Not found"})

    return await call_next(request)


@app.on_event("startup")
def on_startup():
    _require_admin_credentials_configured()
    init_db()


@app.get("/health")
def health():
    return {"ok": True, "env": ENV}


@app.get("/product", response_model=ProductOut)
def product():
    return {
        "name": KIT_NOME,
        "description": KIT_DESCRICAO,
        "items": KIT_ITENS,
        "pricing": {
            "primeiro_dia_kit": PRECO_PRIMEIRO_DIA_KIT,
            "demais_dias_kit": PRECO_DEMAIS_DIAS_KIT,
            "cadeira_extra_dia": PRECO_CADEIRA_EXTRA_DIA,
            "caucao_por_kit": CAUCAO_POR_KIT,
        },
    }


@app.get("/quote", response_model=QuoteOut)
def quote(
    inicio: str = Query(..., description="YYYY-MM-DD"),
    fim: str = Query(..., description="YYYY-MM-DD"),
    cadeiras_extras: int = Query(0, ge=0, description="por kit"),
):
    dias = calc_dias(parse_date(inicio), parse_date(fim))
    aluguel_kit, valor_cadeiras, total = calc_preco(dias, cadeiras_extras)
    return {
        "inicio": inicio,
        "fim": fim,
        "dias": dias,
        "cadeiras_extras": cadeiras_extras,
        "aluguel_kit": aluguel_kit,
        "valor_cadeiras_extras": valor_cadeiras,
        "total": total,
        "caucao": CAUCAO_POR_KIT,
    }


@app.get("/kits", response_model=List[KitOut])
def list_kits():
    with get_conn() as conn:
        rows = conn.execute("SELECT id FROM kits ORDER BY id;").fetchall()
        return [{"id": r["id"]} for r in rows]


@app.get("/availability", response_model=AvailabilityOut)
def availability(
    inicio: str = Query(..., description="YYYY-MM-DD"),
    fim: str = Query(..., description="YYYY-MM-DD"),
):
    di = parse_date(inicio)
    df = parse_date(fim)
    _ = calc_dias(di, df)

    with get_conn() as conn:
        expire_awaiting_payments(conn)
        available: List[int] = []
        for kit_id in range(1, TOTAL_KITS + 1):
            if kit_disponivel(conn, kit_id, di, df):
                available.append(kit_id)
        return {"inicio": inicio, "fim": fim, "available_kits": available}


# =========================
# Cliente público
# =========================

@app.post("/customer/login", response_model=CustomerLoginOut)
def customer_login(payload: CustomerLoginIn):
    name = (payload.name or "").strip()
    phone = normalize_phone(payload.phone)

    if not name:
        raise HTTPException(status_code=400, detail="Nome obrigatório.")

    with get_conn() as conn:
        existing = conn.execute(
            "SELECT * FROM customers WHERE phone = %s LIMIT 1;",
            (phone,),
        ).fetchone()

        if existing:
            customer_id = int(existing["id"])
            old_name = (existing.get("name") or "").strip()

            if old_name != name:
                conn.execute(
                    "UPDATE customers SET name = %s WHERE id = %s;",
                    (name, customer_id),
                )
                existing = conn.execute(
                    "SELECT * FROM customers WHERE id = %s;",
                    (customer_id,),
                ).fetchone()

            out = dict(existing)
            out["created_at"] = _iso(out["created_at"])
            return {
                "customer": out,
                "is_new": False,
            }

        created_at = datetime.utcnow()
        created = conn.execute(
            """
            INSERT INTO customers(name, phone, created_at)
            VALUES (%s, %s, %s)
            RETURNING *;
            """,
            (name, phone, created_at),
        ).fetchone()

        out = dict(created)
        out["created_at"] = _iso(out["created_at"])

        return {
            "customer": out,
            "is_new": True,
        }


@app.get("/customer/by-phone/{phone}", response_model=CustomerOut)
def get_customer_by_phone(phone: str):
    normalized = normalize_phone(phone)

    with get_conn() as conn:
        row = conn.execute(
            "SELECT * FROM customers WHERE phone = %s LIMIT 1;",
            (normalized,),
        ).fetchone()

        if not row:
            raise HTTPException(status_code=404, detail="Cliente não encontrado.")

        out = dict(row)
        out["created_at"] = _iso(out["created_at"])
        return out


@app.get("/customer/{customer_id}/reservations", response_model=List[ReservationOut])
def customer_reservations(customer_id: int):
    with get_conn() as conn:
        expire_awaiting_payments(conn)

        cust = conn.execute(
            "SELECT id FROM customers WHERE id = %s;",
            (customer_id,),
        ).fetchone()

        if not cust:
            raise HTTPException(status_code=404, detail="Cliente não encontrado.")

        rows = conn.execute(
            """
            SELECT *
            FROM reservations
            WHERE customer_id = %s
            ORDER BY created_at DESC, id DESC;
            """,
            (customer_id,),
        ).fetchall()

        return [_row_to_out(r) for r in rows]


# =========================
# Reservas públicas
# =========================

@app.post("/reservations", response_model=ReservationOut)
def create_reservation(payload: ReservationCreate):
    di = parse_date(payload.inicio)
    df = parse_date(payload.fim)
    dias = calc_dias(di, df)

    if payload.kit_id < 1 or payload.kit_id > TOTAL_KITS:
        raise HTTPException(status_code=400, detail="kit_id inválido.")

    aluguel_kit, valor_cadeiras, total = calc_preco(dias, payload.cadeiras_extras)
    created_at = datetime.utcnow()

    with get_conn() as conn:
        expire_awaiting_payments(conn)

        cust = conn.execute(
            "SELECT id FROM customers WHERE id = %s;",
            (payload.customer_id,),
        ).fetchone()
        if not cust:
            raise HTTPException(status_code=404, detail="Cliente não encontrado.")

        if not kit_disponivel(conn, payload.kit_id, di, df):
            raise HTTPException(status_code=409, detail="Kit indisponível neste período.")

        cur = conn.execute(
            """
            INSERT INTO reservations
            (kit_id, inicio, fim, dias, cadeiras_extras, aluguel_kit, valor_cadeiras_extras, total, caucao,
             status, created_at, customer_id, source)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, 'awaiting_payment', %s, %s, 'app')
            RETURNING id
            """,
            (
                payload.kit_id,
                di,
                df,
                dias,
                payload.cadeiras_extras,
                aluguel_kit,
                valor_cadeiras,
                total,
                CAUCAO_POR_KIT,
                created_at,
                payload.customer_id,
            )
        ).fetchone()

        rid = int(cur["id"])
        row = conn.execute("SELECT * FROM reservations WHERE id = %s;", (rid,)).fetchone()
        return _row_to_out(row)


@app.post("/reservations/bulk", response_model=BulkReservationOut)
def create_reservations_bulk(payload: BulkReservationCreate):
    di = parse_date(payload.inicio)
    df = parse_date(payload.fim)
    dias = calc_dias(di, df)

    with get_conn() as conn:
        expire_awaiting_payments(conn)

        customer_id = get_or_create_customer(
            conn,
            payload.customer_name,
            payload.customer_phone,
        )

        available: List[int] = []
        for kit_id in range(1, TOTAL_KITS + 1):
            if kit_disponivel(conn, kit_id, di, df):
                available.append(kit_id)

        if len(available) < payload.quantity:
            raise HTTPException(status_code=409, detail=f"Quantidade indisponível. Disponíveis: {len(available)}")

        aluguel_kit, valor_cadeiras, total = calc_preco(dias, payload.cadeiras_extras)
        created_at = datetime.utcnow()

        created: List[dict] = []
        for kit_id in available[:payload.quantity]:
            rid = conn.execute(
                """
                INSERT INTO reservations
                (kit_id, inicio, fim, dias, cadeiras_extras, aluguel_kit, valor_cadeiras_extras, total, caucao,
                 status, created_at, customer_id, source)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, 'awaiting_payment', %s, %s, 'app')
                RETURNING id
                """,
                (
                    kit_id,
                    di,
                    df,
                    dias,
                    payload.cadeiras_extras,
                    aluguel_kit,
                    valor_cadeiras,
                    total,
                    CAUCAO_POR_KIT,
                    created_at,
                    customer_id,
                )
            ).fetchone()["id"]

            row = conn.execute("SELECT * FROM reservations WHERE id = %s;", (rid,)).fetchone()
            created.append(_row_to_out(row))

        return {"reservations": created}


@app.get("/reservations", response_model=List[ReservationOut])
def list_reservations():
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        rows = conn.execute("SELECT * FROM reservations ORDER BY id DESC;").fetchall()
        return [_row_to_out(r) for r in rows]


@app.get("/reservations/{reservation_id}", response_model=ReservationOut)
def get_reservation(reservation_id: int):
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        row = conn.execute("SELECT * FROM reservations WHERE id = %s;", (reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        return _row_to_out(row)


@app.post("/reservations/{reservation_id}/cancel", response_model=CancelOut)
def cancel_reservation(reservation_id: int, payload: CancelIn):
    now = datetime.utcnow()

    with get_conn() as conn:
        expire_awaiting_payments(conn)

        row = conn.execute("SELECT * FROM reservations WHERE id = %s;", (reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")

        rowd = _row_to_out(row)

        if row["status"] == "canceled":
            fee = float(row.get("cancel_fee") or 0.0)
            caucao = float(row.get("caucao") or 0.0)
            return {
                "ok": True,
                "reservation": rowd,
                "fee_retained_from_deposit": fee,
                "deposit_refund_expected": round(max(0.0, caucao - fee), 2),
                "rent_refund_expected": float(row.get("total") or 0.0),
                "cancel_deadline_utc": cancel_deadline_dt(str(rowd["inicio"])).isoformat(),
            }

        if row["status"] == "completed":
            raise HTTPException(status_code=400, detail="Reserva já concluída não pode ser cancelada.")

        deadline = cancel_deadline_dt(str(rowd["inicio"]))
        if now > deadline:
            raise HTTPException(
                status_code=400,
                detail=f"Prazo de cancelamento expirou. Deadline (UTC): {deadline.isoformat()}."
            )

        caucao = float(row.get("caucao") or 0.0)
        fee = round(caucao * CANCEL_FEE_DEPOSIT_RATE, 2)
        reason = (payload.reason or "user_cancel").strip()

        conn.execute(
            """
            UPDATE reservations
            SET status='canceled',
                canceled_at=%s,
                cancel_reason=%s,
                cancel_fee=%s,
                cancel_fee_type='deposit_pct'
            WHERE id=%s
            """,
            (now, reason, fee, reservation_id)
        )

        updated = conn.execute("SELECT * FROM reservations WHERE id = %s;", (reservation_id,)).fetchone()
        upd = _row_to_out(updated)

        return {
            "ok": True,
            "reservation": upd,
            "fee_retained_from_deposit": fee,
            "deposit_refund_expected": round(max(0.0, caucao - fee), 2),
            "rent_refund_expected": round(float(row.get("total") or 0.0), 2),
            "cancel_deadline_utc": deadline.isoformat(),
        }


@app.post("/payments", response_model=PaymentOut)
def pay(payload: PaymentCreate):
    paid_at = datetime.utcnow()

    with get_conn() as conn:
        expire_awaiting_payments(conn)

        row = conn.execute("SELECT * FROM reservations WHERE id = %s;", (payload.reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        if row["status"] == "canceled":
            raise HTTPException(status_code=400, detail="Reserva expirada/cancelada não pode ser paga.")
        if row["status"] == "paid_with_deposit":
            current_paid_at = row.get("paid_at") or paid_at
            return {
                "reservation_id": payload.reservation_id,
                "method": (row.get("pay_method") or payload.method),
                "deposit_amount": float(row.get("caucao") or CAUCAO_POR_KIT),
                "paid_at": current_paid_at.isoformat() if isinstance(current_paid_at, datetime) else str(current_paid_at),
                "new_status": "paid_with_deposit",
            }

        conn.execute(
            "UPDATE reservations SET status='paid_with_deposit', paid_at=%s, pay_method=%s WHERE id=%s;",
            (paid_at, payload.method, payload.reservation_id)
        )

        return {
            "reservation_id": payload.reservation_id,
            "method": payload.method,
            "deposit_amount": CAUCAO_POR_KIT,
            "paid_at": paid_at.isoformat(),
            "new_status": "paid_with_deposit",
        }


# =========================
# Código (texto) + QR
# =========================

@app.get("/reservations/{reservation_id}/code")
def reservation_code(reservation_id: int):
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        row = conn.execute("SELECT * FROM reservations WHERE id = %s;", (reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        if row["status"] != "paid_with_deposit":
            raise HTTPException(status_code=400, detail="Código disponível apenas para reservas pagas.")

        created_at = row["created_at"]
        created_at_str = created_at.isoformat() if isinstance(created_at, datetime) else str(created_at)

        code = build_code_text(reservation_id, int(row["kit_id"]), created_at_str)
        return PlainTextResponse(code)


@app.get("/reservations/{reservation_id}/pickup_qr")
def pickup_qr(reservation_id: int):
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        row = conn.execute("SELECT * FROM reservations WHERE id = %s;", (reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        if row["status"] != "paid_with_deposit":
            raise HTTPException(status_code=400, detail="QR disponível apenas para reservas pagas.")

        created_at = row["created_at"]
        created_at_str = created_at.isoformat() if isinstance(created_at, datetime) else str(created_at)

        code_text = build_code_text(reservation_id, int(row["kit_id"]), created_at_str)
        img = qrcode.make(code_text)
        buf = BytesIO()
        img.save(buf, format="PNG")
        buf.seek(0)
        return StreamingResponse(buf, media_type="image/png")


# =========================
# Admin login
# =========================

@app.post("/admin/login", response_model=AdminLoginOut)
def admin_login(payload: AdminLoginIn):
    email = (payload.email or "").strip().lower()
    password = payload.password or ""

    if email != ADMIN_EMAIL or password != ADMIN_PASSWORD:
        raise HTTPException(status_code=401, detail="Email ou senha inválidos.")

    return {
        "ok": True,
        "email": email,
        "message": "Login realizado com sucesso.",
    }


# =========================
# Admin routes
# =========================

@app.get("/admin/reservations", response_model=List[ReservationOut])
def admin_reservations_by_date(
    date_str: str = Query(..., alias="date", description="YYYY-MM-DD"),
    x_admin_email: str | None = Header(default=None),
    x_admin_password: str | None = Header(default=None),
):
    require_admin_credentials(x_admin_email, x_admin_password)

    d = parse_date(date_str)
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        rows = conn.execute(
            """
            SELECT * FROM reservations
            WHERE status <> 'canceled'
              AND inicio <= %s
              AND fim >= %s
            ORDER BY inicio ASC, id DESC
            """,
            (d, d),
        ).fetchall()
        return [_row_to_out(r) for r in rows]


@app.post("/admin/scan_code")
def admin_scan_code(
    payload: AdminScanCodeIn,
    x_admin_email: str | None = Header(default=None),
    x_admin_password: str | None = Header(default=None),
):
    require_admin_credentials(x_admin_email, x_admin_password)

    rid, kit_id, token_prefix = parse_code_text(payload.code)
    now = datetime.utcnow()

    with get_conn() as conn:
        expire_awaiting_payments(conn)

        row = conn.execute("SELECT * FROM reservations WHERE id = %s;", (rid,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")

        if int(row["kit_id"]) != int(kit_id):
            raise HTTPException(status_code=400, detail="Código não bate com o kit da reserva.")

        if row["status"] == "canceled":
            raise HTTPException(status_code=400, detail="Reserva cancelada.")

        if row["status"] not in ("paid_with_deposit", "completed"):
            raise HTTPException(status_code=400, detail="Reserva não está paga.")

        created_at = row["created_at"]
        created_at_str = created_at.isoformat() if isinstance(created_at, datetime) else str(created_at)

        if not verify_pickup_token_prefix(rid, created_at_str, token_prefix):
            raise HTTPException(status_code=401, detail="Código inválido (token).")

        if row["status"] == "completed" or (row.get("checked_in_at") or None):
            updated = conn.execute("SELECT * FROM reservations WHERE id = %s;", (rid,)).fetchone()
            return {
                "ok": True,
                "action": "none",
                "message": "Já devolvido.",
                "reservation": _row_to_out(updated)
            }

        if not (row.get("checked_out_at") or None):
            conn.execute("UPDATE reservations SET checked_out_at=%s WHERE id=%s;", (now, rid))
            updated = conn.execute("SELECT * FROM reservations WHERE id = %s;", (rid,)).fetchone()
            return {
                "ok": True,
                "action": "checkout",
                "message": "Retirada confirmada ✅",
                "reservation": _row_to_out(updated)
            }

        conn.execute("UPDATE reservations SET checked_in_at=%s, status='completed' WHERE id=%s;", (now, rid))
        updated = conn.execute("SELECT * FROM reservations WHERE id = %s;", (rid,)).fetchone()
        return {
            "ok": True,
            "action": "checkin",
            "message": "Devolução confirmada ✅",
            "reservation": _row_to_out(updated)
        }


@app.post("/admin/reservations/{reservation_id}/checkout")
def admin_checkout(
    reservation_id: int,
    x_admin_email: str | None = Header(default=None),
    x_admin_password: str | None = Header(default=None),
):
    require_admin_credentials(x_admin_email, x_admin_password)

    now = datetime.utcnow()
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        row = conn.execute("SELECT * FROM reservations WHERE id = %s;", (reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        if row["status"] == "canceled":
            raise HTTPException(status_code=400, detail="Reserva cancelada não pode dar checkout.")
        if row["status"] != "paid_with_deposit":
            raise HTTPException(status_code=400, detail="Somente reservas pagas podem dar checkout.")

        conn.execute("UPDATE reservations SET checked_out_at=%s WHERE id=%s;", (now, reservation_id))
        updated = conn.execute("SELECT * FROM reservations WHERE id = %s;", (reservation_id,)).fetchone()
        return {"ok": True, "reservation": _row_to_out(updated)}


@app.post("/admin/reservations/{reservation_id}/checkin")
def admin_checkin(
    reservation_id: int,
    x_admin_email: str | None = Header(default=None),
    x_admin_password: str | None = Header(default=None),
):
    require_admin_credentials(x_admin_email, x_admin_password)

    now = datetime.utcnow()
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        row = conn.execute("SELECT * FROM reservations WHERE id = %s;", (reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        if row["status"] == "canceled":
            raise HTTPException(status_code=400, detail="Reserva cancelada não pode dar check-in.")

        conn.execute("UPDATE reservations SET checked_in_at=%s, status='completed' WHERE id=%s;", (now, reservation_id))
        updated = conn.execute("SELECT * FROM reservations WHERE id = %s;", (reservation_id,)).fetchone()
        return {"ok": True, "reservation": _row_to_out(updated)}


@app.post("/admin/reservations/{reservation_id}/cancel", response_model=AdminCancelOut)
def admin_cancel_reservation(
    reservation_id: int,
    payload: AdminCancelIn,
    x_admin_email: str | None = Header(default=None),
    x_admin_password: str | None = Header(default=None),
):
    require_admin_credentials(x_admin_email, x_admin_password)

    now = datetime.utcnow()
    with get_conn() as conn:
        expire_awaiting_payments(conn)

        row = conn.execute("SELECT * FROM reservations WHERE id = %s;", (reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        if row["status"] == "completed":
            raise HTTPException(status_code=400, detail="Reserva concluída não pode ser cancelada.")

        if row["status"] == "canceled":
            fee = float(row.get("cancel_fee") or 0.0)
            caucao = float(row.get("caucao") or 0.0)
            return {
                "ok": True,
                "reservation": _row_to_out(row),
                "fee_retained_from_deposit": fee,
                "deposit_refund_expected": round(max(0.0, caucao - fee), 2),
                "rent_refund_expected": float(row.get("total") or 0.0),
            }

        caucao = float(row.get("caucao") or 0.0)
        fee = round(caucao * CANCEL_FEE_DEPOSIT_RATE, 2)
        reason = (payload.reason or "admin_cancel_manual").strip()

        conn.execute(
            """
            UPDATE reservations
            SET status='canceled',
                canceled_at=%s,
                cancel_reason=%s,
                cancel_fee=%s,
                cancel_fee_type='deposit_pct'
            WHERE id=%s
            """,
            (now, reason, fee, reservation_id)
        )

        updated = conn.execute("SELECT * FROM reservations WHERE id = %s;", (reservation_id,)).fetchone()
        deposit_refund_expected = max(0.0, caucao - fee)
        rent_refund_expected = float(row.get("total") or 0.0)

        return {
            "ok": True,
            "reservation": _row_to_out(updated),
            "fee_retained_from_deposit": fee,
            "deposit_refund_expected": round(deposit_refund_expected, 2),
            "rent_refund_expected": round(rent_refund_expected, 2),
        }


@app.get("/admin/stats")
def admin_stats(
    x_admin_email: str | None = Header(default=None),
    x_admin_password: str | None = Header(default=None),
):
    require_admin_credentials(x_admin_email, x_admin_password)

    with get_conn() as conn:
        expire_awaiting_payments(conn)
        rows = conn.execute("""
            SELECT status, COUNT(*) as c
            FROM reservations
            GROUP BY status
        """).fetchall()

        by_status = {r["status"]: int(r["c"]) for r in rows} if rows else {}
        total = sum(by_status.values()) if by_status else 0
        awaiting = by_status.get("awaiting_payment", 0)
        paid = by_status.get("paid_with_deposit", 0)
        completed = by_status.get("completed", 0)
        canceled = by_status.get("canceled", 0)
        not_completed = total - completed
        open_active = awaiting + paid

        return {
            "total": total,
            "by_status": {
                "awaiting_payment": awaiting,
                "paid_with_deposit": paid,
                "completed": completed,
                "canceled": canceled,
            },
            "not_completed": not_completed,
            "open_active": open_active,
        }


# =========================
# Admin: Clientes
# =========================

@app.post("/admin/customers", response_model=CustomerOut)
def admin_create_customer(
    payload: CustomerCreate,
    x_admin_email: str | None = Header(default=None),
    x_admin_password: str | None = Header(default=None),
):
    require_admin_credentials(x_admin_email, x_admin_password)

    with get_conn() as conn:
        customer_id = get_or_create_customer(conn, payload.name, payload.phone)
        row = conn.execute("SELECT * FROM customers WHERE id = %s;", (customer_id,)).fetchone()
        out = dict(row)
        out["created_at"] = _iso(out["created_at"])
        return out


@app.get("/admin/customers", response_model=List[CustomerOut])
def admin_search_customers(
    q: str = Query("", description="busca por nome/telefone"),
    x_admin_email: str | None = Header(default=None),
    x_admin_password: str | None = Header(default=None),
):
    require_admin_credentials(x_admin_email, x_admin_password)

    q = (q or "").strip()

    with get_conn() as conn:
        if not q:
            rows = conn.execute("SELECT * FROM customers ORDER BY id DESC LIMIT 50;").fetchall()
        else:
            like = f"%{q}%"
            rows = conn.execute(
                "SELECT * FROM customers WHERE name ILIKE %s OR phone ILIKE %s ORDER BY id DESC LIMIT 50;",
                (like, like),
            ).fetchall()

        out = []
        for r in rows:
            rr = dict(r)
            rr["created_at"] = _iso(rr["created_at"])
            out.append(rr)
        return out


# =========================
# Admin: Venda presencial
# =========================

@app.post("/admin/walkin/reservations")
def admin_create_walkin_reservations(
    payload: AdminWalkInReservationCreate,
    x_admin_email: str | None = Header(default=None),
    x_admin_password: str | None = Header(default=None),
):
    require_admin_credentials(x_admin_email, x_admin_password)

    di = parse_date(payload.inicio)
    df = parse_date(payload.fim)
    dias = calc_dias(di, df)
    created_at = datetime.utcnow()

    with get_conn() as conn:
        expire_awaiting_payments(conn)

        cust = conn.execute("SELECT * FROM customers WHERE id = %s;", (payload.customer_id,)).fetchone()
        if not cust:
            raise HTTPException(status_code=404, detail="Cliente não encontrado.")

        available: List[int] = []
        for kit_id in range(1, TOTAL_KITS + 1):
            if kit_disponivel(conn, kit_id, di, df):
                available.append(kit_id)

        if len(available) < payload.quantity:
            raise HTTPException(status_code=409, detail=f"Quantidade indisponível. Disponíveis: {len(available)}")

        aluguel_kit, valor_cadeiras, total = calc_preco(dias, payload.cadeiras_extras)

        created: List[dict] = []
        for kit_id in available[:payload.quantity]:
            rid = conn.execute(
                """
                INSERT INTO reservations
                (kit_id, inicio, fim, dias, cadeiras_extras, aluguel_kit, valor_cadeiras_extras, total, caucao,
                 status, created_at, paid_at, pay_method, customer_id, source)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s,
                        'paid_with_deposit', %s, %s, %s, %s, 'store')
                RETURNING id
                """,
                (
                    kit_id,
                    di,
                    df,
                    dias,
                    payload.cadeiras_extras,
                    aluguel_kit,
                    valor_cadeiras,
                    total,
                    CAUCAO_POR_KIT,
                    created_at,
                    created_at,
                    payload.pay_method,
                    payload.customer_id,
                ),
            ).fetchone()["id"]

            row = conn.execute("SELECT * FROM reservations WHERE id = %s;", (rid,)).fetchone()
            created.append(_row_to_out(row))

        return {"ok": True, "reservations": created}


# =========================
# Helpers: row -> response dict
# =========================

def _iso(v):
    if v is None:
        return None
    if isinstance(v, datetime):
        return v.isoformat()
    if isinstance(v, date):
        return v.isoformat()
    return str(v)


def _row_to_out(row: dict) -> dict:
    d = dict(row)
    d["inicio"] = _iso(d.get("inicio"))
    d["fim"] = _iso(d.get("fim"))
    d["created_at"] = _iso(d.get("created_at"))
    d["paid_at"] = _iso(d.get("paid_at"))
    d["checked_out_at"] = _iso(d.get("checked_out_at"))
    d["checked_in_at"] = _iso(d.get("checked_in_at"))
    d["canceled_at"] = _iso(d.get("canceled_at"))
    return d
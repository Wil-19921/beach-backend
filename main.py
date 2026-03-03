from __future__ import annotations

from fastapi import FastAPI, HTTPException, Query
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import StreamingResponse, PlainTextResponse
from pydantic import BaseModel, Field
from typing import Literal, Optional, List
from datetime import datetime, date, timedelta, time
from io import BytesIO
import sqlite3
import os
import hmac
import hashlib
import base64

# QR (pip install qrcode[pil])
import qrcode

# =========================
# Config
# =========================

DB_PATH = os.environ.get("DB_PATH") or os.path.join(os.path.dirname(__file__), "beach.db")
Status = Literal["awaiting_payment", "paid_with_deposit", "completed", "canceled"]
PayMethod = Literal["pix", "debit", "credit", "cash", "card"]

PRECO_PRIMEIRO_DIA_KIT = 50.0
PRECO_DEMAIS_DIAS_KIT = 25.0
PRECO_CADEIRA_EXTRA_DIA = 10.0
CAUCAO_POR_KIT = 200.0

TOTAL_KITS = 50

# Expiração de reserva (minutos)
RESERVATION_EXPIRATION_MINUTES = 30

# Cancelamento (cliente pediu):
# - Retém 30% do calção
# - Pra reserva com inicio = D, o cliente pode cancelar até (D - 2) às 23:59 (24h antes da retirada, que é D - 1)
CANCEL_DEADLINE_DAYS_BEFORE_INICIO = 2
CANCEL_FEE_DEPOSIT_RATE = 0.30

# Segredo do QR (troque em produção / use variável de ambiente)
PICKUP_SECRET = os.environ.get("PICKUP_SECRET", "troque-essa-chave-em-producao")

# Kit (descrição exibida no app)
KIT_NOME = "Kit Praia"
KIT_ITENS = ["2 cadeiras", "1 guarda-sol", "1 mesa de centro"]
KIT_DESCRICAO = "Inclui 2 cadeiras, 1 guarda-sol e 1 mesa de centro."

# ✅ Código textual único (o mesmo que vai no QR)
CODE_PREFIX = "BCH"
CODE_TOKEN_LEN = 10  # token curto no texto (prefixo do HMAC)

# =========================
# DB helpers
# =========================
def get_conn() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    return conn

def ensure_column(conn: sqlite3.Connection, table: str, column: str, coltype: str) -> None:
    cols = [r["name"] for r in conn.execute(f"PRAGMA table_info({table})").fetchall()]
    if column not in cols:
        conn.execute(f"ALTER TABLE {table} ADD COLUMN {column} {coltype}")

def init_db() -> None:
    with get_conn() as conn:
        conn.execute("""
        CREATE TABLE IF NOT EXISTS kits (
            id INTEGER PRIMARY KEY
        )
        """)

        conn.execute("""
        CREATE TABLE IF NOT EXISTS reservations (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            kit_id INTEGER NOT NULL,
            inicio TEXT NOT NULL,
            fim TEXT NOT NULL,
            dias INTEGER NOT NULL,
            cadeiras_extras INTEGER NOT NULL,
            aluguel_kit REAL NOT NULL,
            valor_cadeiras_extras REAL NOT NULL,
            total REAL NOT NULL,
            caucao REAL NOT NULL,
            status TEXT NOT NULL,
            created_at TEXT NOT NULL,
            paid_at TEXT,
            pay_method TEXT,
            FOREIGN KEY (kit_id) REFERENCES kits(id)
        )
        """)

        # Clientes
        conn.execute("""
        CREATE TABLE IF NOT EXISTS customers (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            phone TEXT NOT NULL,
            created_at TEXT NOT NULL
        )
        """)

        # colunas extras (compatibilidade + regras)
        ensure_column(conn, "reservations", "checked_out_at", "TEXT")
        ensure_column(conn, "reservations", "checked_in_at", "TEXT")
        ensure_column(conn, "reservations", "canceled_at", "TEXT")
        ensure_column(conn, "reservations", "cancel_reason", "TEXT")
        ensure_column(conn, "reservations", "cancel_fee", "REAL")
        ensure_column(conn, "reservations", "cancel_fee_type", "TEXT")

        # venda presencial / cliente
        ensure_column(conn, "reservations", "customer_id", "INTEGER")
        ensure_column(conn, "reservations", "source", "TEXT")  # app | store

        cur = conn.execute("SELECT COUNT(*) as c FROM kits")
        c = cur.fetchone()["c"]
        if c < TOTAL_KITS:
            conn.execute("DELETE FROM kits")
            conn.executemany(
                "INSERT INTO kits(id) VALUES (?)",
                [(i,) for i in range(1, TOTAL_KITS + 1)]
            )

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

def overlaps(a_start: str, a_end: str, b_start: str, b_end: str) -> bool:
    return not (a_end < b_start or b_end < a_start)

def expire_awaiting_payments(conn: sqlite3.Connection) -> int:
    now = datetime.utcnow()
    threshold = now - timedelta(minutes=RESERVATION_EXPIRATION_MINUTES)

    rows = conn.execute(
        """
        SELECT id, created_at
        FROM reservations
        WHERE status = 'awaiting_payment'
        """
    ).fetchall()

    to_cancel: List[int] = []
    for r in rows:
        try:
            created = datetime.fromisoformat(r["created_at"])
        except Exception:
            continue
        if created <= threshold:
            to_cancel.append(int(r["id"]))

    if to_cancel:
        canceled_at = now.isoformat()
        conn.executemany(
            """
            UPDATE reservations
            SET status = 'canceled',
                canceled_at = ?,
                cancel_reason = COALESCE(cancel_reason, 'expired')
            WHERE id = ?
            """,
            [(canceled_at, rid) for rid in to_cancel]
        )
    return len(to_cancel)

def kit_disponivel(conn: sqlite3.Connection, kit_id: int, inicio: str, fim: str) -> bool:
    rows = conn.execute(
        """
        SELECT inicio, fim, status FROM reservations
        WHERE kit_id = ?
          AND status != 'canceled'
        """,
        (kit_id,)
    ).fetchall()

    for r in rows:
        if overlaps(r["inicio"], r["fim"], inicio, fim):
            return False
    return True

def cancel_deadline_dt(inicio_str: str) -> datetime:
    inicio = parse_date(inicio_str)
    deadline_date = inicio - timedelta(days=CANCEL_DEADLINE_DAYS_BEFORE_INICIO)
    return datetime.combine(deadline_date, time(23, 59, 59))

# =========================
# Signing / codes
# =========================
def _b64u(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).decode().rstrip("=")

def sign_pickup_token(reservation_id: int, created_at: str) -> str:
    msg = f"{reservation_id}|{created_at}".encode()
    sig = hmac.new(PICKUP_SECRET.encode(), msg, hashlib.sha256).digest()
    return _b64u(sig)

def verify_pickup_token(reservation_id: int, created_at: str, token: str) -> bool:
    expected = sign_pickup_token(reservation_id, created_at)
    return hmac.compare_digest(expected, token)

def verify_pickup_token_prefix(reservation_id: int, created_at: str, token_prefix: str) -> bool:
    expected = sign_pickup_token(reservation_id, created_at)
    return hmac.compare_digest(expected[:len(token_prefix)], token_prefix)

def build_code_text(reservation_id: int, kit_id: int, created_at: str) -> str:
    token_prefix = sign_pickup_token(reservation_id, created_at)[:CODE_TOKEN_LEN]
    return f"{CODE_PREFIX}-{reservation_id}-{kit_id}-{token_prefix}"

def parse_code_text(code: str) -> tuple[int, int, str]:
    raw = (code or "").strip()
    parts = raw.split("-")
    if len(parts) != 4 or parts[0] != CODE_PREFIX:
        raise HTTPException(status_code=400, detail="Código inválido. Formato: BCH-<rid>-<kit>-<token>.")
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

class BulkReservationOut(BaseModel):
    reservations: List[ReservationOut]

class PickupScanIn(BaseModel):
    reservation_id: int
    token: str

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

class AdminWalkInReservationCreate(BaseModel):
    customer_id: int
    inicio: str
    fim: str
    quantity: int = Field(..., ge=1, le=TOTAL_KITS)
    cadeiras_extras: int = Field(0, ge=0)
    pay_method: PayMethod = Field(..., description="cash | card | pix | debit | credit")

# =========================
# App
# =========================
app = FastAPI(title="Beach Backend", version="0.5.1")

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=False,
    allow_methods=["*"],
    allow_headers=["*"],
)

@app.on_event("startup")
def on_startup():
    init_db()

@app.get("/health")
def health():
    return {"ok": True}

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
        rows = conn.execute("SELECT id FROM kits ORDER BY id").fetchall()
        return [{"id": r["id"]} for r in rows]

@app.get("/availability", response_model=AvailabilityOut)
def availability(
    inicio: str = Query(..., description="YYYY-MM-DD"),
    fim: str = Query(..., description="YYYY-MM-DD"),
):
    _ = calc_dias(parse_date(inicio), parse_date(fim))
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        available = []
        for kit_id in range(1, TOTAL_KITS + 1):
            if kit_disponivel(conn, kit_id, inicio, fim):
                available.append(kit_id)
        return {"inicio": inicio, "fim": fim, "available_kits": available}

@app.post("/reservations", response_model=ReservationOut)
def create_reservation(payload: ReservationCreate):
    di = parse_date(payload.inicio)
    df = parse_date(payload.fim)
    dias = calc_dias(di, df)

    if payload.kit_id < 1 or payload.kit_id > TOTAL_KITS:
        raise HTTPException(status_code=400, detail="kit_id inválido.")

    aluguel_kit, valor_cadeiras, total = calc_preco(dias, payload.cadeiras_extras)
    created_at = datetime.utcnow().isoformat()

    with get_conn() as conn:
        expire_awaiting_payments(conn)

        if not kit_disponivel(conn, payload.kit_id, payload.inicio, payload.fim):
            raise HTTPException(status_code=409, detail="Kit indisponível neste período.")

        cur = conn.execute(
            """
            INSERT INTO reservations
            (kit_id, inicio, fim, dias, cadeiras_extras, aluguel_kit, valor_cadeiras_extras, total, caucao,
             status, created_at, source)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 'awaiting_payment', ?, 'app')
            """,
            (
                payload.kit_id,
                payload.inicio,
                payload.fim,
                dias,
                payload.cadeiras_extras,
                aluguel_kit,
                valor_cadeiras,
                total,
                CAUCAO_POR_KIT,
                created_at,
            )
        )
        row = conn.execute("SELECT * FROM reservations WHERE id = ?", (cur.lastrowid,)).fetchone()
        return dict(row)

@app.post("/reservations/bulk", response_model=BulkReservationOut)
def create_reservations_bulk(payload: BulkReservationCreate):
    dias = calc_dias(parse_date(payload.inicio), parse_date(payload.fim))
    with get_conn() as conn:
        expire_awaiting_payments(conn)

        available = []
        for kit_id in range(1, TOTAL_KITS + 1):
            if kit_disponivel(conn, kit_id, payload.inicio, payload.fim):
                available.append(kit_id)

        if len(available) < payload.quantity:
            raise HTTPException(status_code=409, detail=f"Quantidade indisponível. Disponíveis: {len(available)}")

        aluguel_kit, valor_cadeiras, total = calc_preco(dias, payload.cadeiras_extras)
        created_at = datetime.utcnow().isoformat()

        created: List[dict] = []
        for kit_id in available[:payload.quantity]:
            cur = conn.execute(
                """
                INSERT INTO reservations
                (kit_id, inicio, fim, dias, cadeiras_extras, aluguel_kit, valor_cadeiras_extras, total, caucao,
                 status, created_at, source)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 'awaiting_payment', ?, 'app')
                """,
                (
                    kit_id,
                    payload.inicio,
                    payload.fim,
                    dias,
                    payload.cadeiras_extras,
                    aluguel_kit,
                    valor_cadeiras,
                    total,
                    CAUCAO_POR_KIT,
                    created_at,
                )
            )
            row = conn.execute("SELECT * FROM reservations WHERE id = ?", (cur.lastrowid,)).fetchone()
            created.append(dict(row))

        return {"reservations": created}

@app.get("/reservations", response_model=List[ReservationOut])
def list_reservations():
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        rows = conn.execute("SELECT * FROM reservations ORDER BY id DESC").fetchall()
        return [dict(r) for r in rows]

@app.get("/reservations/{reservation_id}", response_model=ReservationOut)
def get_reservation(reservation_id: int):
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        row = conn.execute("SELECT * FROM reservations WHERE id = ?", (reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        return dict(row)

@app.post("/reservations/{reservation_id}/cancel", response_model=CancelOut)
def cancel_reservation(reservation_id: int, payload: CancelIn):
    now = datetime.utcnow()
    with get_conn() as conn:
        expire_awaiting_payments(conn)

        row = conn.execute("SELECT * FROM reservations WHERE id = ?", (reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")

        if row["status"] == "canceled":
            existing = dict(row)
            fee = float(existing.get("cancel_fee") or 0.0)
            caucao = float(existing.get("caucao") or 0.0)
            return {
                "ok": True,
                "reservation": existing,
                "fee_retained_from_deposit": fee,
                "deposit_refund_expected": round(max(0.0, caucao - fee), 2),
                "rent_refund_expected": float(existing.get("total") or 0.0),
                "cancel_deadline_utc": cancel_deadline_dt(existing["inicio"]).isoformat(),
            }

        if row["status"] == "completed":
            raise HTTPException(status_code=400, detail="Reserva já concluída não pode ser cancelada.")

        deadline = cancel_deadline_dt(row["inicio"])
        if now > deadline:
            raise HTTPException(
                status_code=400,
                detail=f"Prazo de cancelamento expirou. Deadline (UTC): {deadline.isoformat()}."
            )

        caucao = float(row["caucao"] or 0.0)
        fee = round(caucao * CANCEL_FEE_DEPOSIT_RATE, 2)

        canceled_at = now.isoformat()
        reason = (payload.reason or "user_cancel").strip()

        conn.execute(
            """
            UPDATE reservations
            SET status='canceled',
                canceled_at=?,
                cancel_reason=?,
                cancel_fee=?,
                cancel_fee_type='deposit_pct'
            WHERE id=?
            """,
            (canceled_at, reason, fee, reservation_id)
        )

        updated = conn.execute("SELECT * FROM reservations WHERE id = ?", (reservation_id,)).fetchone()
        updated_dict = dict(updated)

        return {
            "ok": True,
            "reservation": updated_dict,
            "fee_retained_from_deposit": fee,
            "deposit_refund_expected": round(max(0.0, caucao - fee), 2),
            "rent_refund_expected": round(float(row["total"] or 0.0), 2),
            "cancel_deadline_utc": deadline.isoformat(),
        }

@app.post("/payments", response_model=PaymentOut)
def pay(payload: PaymentCreate):
    paid_at = datetime.utcnow().isoformat()
    with get_conn() as conn:
        expire_awaiting_payments(conn)

        row = conn.execute("SELECT * FROM reservations WHERE id = ?", (payload.reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        if row["status"] == "canceled":
            raise HTTPException(status_code=400, detail="Reserva expirada/cancelada não pode ser paga.")
        if row["status"] == "paid_with_deposit":
            return {
                "reservation_id": payload.reservation_id,
                "method": (row["pay_method"] or payload.method),
                "deposit_amount": row["caucao"],
                "paid_at": (row["paid_at"] or paid_at),
                "new_status": "paid_with_deposit",
            }

        conn.execute(
            "UPDATE reservations SET status='paid_with_deposit', paid_at=?, pay_method=? WHERE id=?",
            (paid_at, payload.method, payload.reservation_id)
        )

        return {
            "reservation_id": payload.reservation_id,
            "method": payload.method,
            "deposit_amount": CAUCAO_POR_KIT,
            "paid_at": paid_at,
            "new_status": "paid_with_deposit",
        }

# =========================
# ✅ Código (texto) + QR
# =========================
@app.get("/reservations/{reservation_id}/code")
def reservation_code(reservation_id: int):
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        row = conn.execute("SELECT * FROM reservations WHERE id = ?", (reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        if row["status"] != "paid_with_deposit":
            raise HTTPException(status_code=400, detail="Código disponível apenas para reservas pagas.")
        code = build_code_text(reservation_id, int(row["kit_id"]), row["created_at"])
        return PlainTextResponse(code)

@app.get("/reservations/{reservation_id}/pickup_qr")
def pickup_qr(reservation_id: int):
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        row = conn.execute("SELECT * FROM reservations WHERE id = ?", (reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        if row["status"] != "paid_with_deposit":
            raise HTTPException(status_code=400, detail="QR disponível apenas para reservas pagas.")
        code_text = build_code_text(reservation_id, int(row["kit_id"]), row["created_at"])
        img = qrcode.make(code_text)
        buf = BytesIO()
        img.save(buf, format="PNG")
        buf.seek(0)
        return StreamingResponse(buf, media_type="image/png")

# =========================
# Scan antigo (compat)
# =========================
@app.post("/admin/pickup/scan")
def admin_scan_pickup(payload: PickupScanIn):
    now = datetime.utcnow().isoformat()
    with get_conn() as conn:
        expire_awaiting_payments(conn)

        row = conn.execute("SELECT * FROM reservations WHERE id = ?", (payload.reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        if row["status"] != "paid_with_deposit":
            raise HTTPException(status_code=400, detail="Reserva não está paga para retirada.")

        if not verify_pickup_token(payload.reservation_id, row["created_at"], payload.token):
            raise HTTPException(status_code=401, detail="QR inválido.")

        if row["checked_out_at"]:
            updated = conn.execute("SELECT * FROM reservations WHERE id = ?", (payload.reservation_id,)).fetchone()
            return {"ok": True, "already_checked_out": True, "reservation": dict(updated)}

        conn.execute("UPDATE reservations SET checked_out_at=? WHERE id=?", (now, payload.reservation_id))
        updated = conn.execute("SELECT * FROM reservations WHERE id = ?", (payload.reservation_id,)).fetchone()
        return {"ok": True, "reservation": dict(updated)}

# =========================
# Admin routes (loja)
# =========================
@app.get("/admin/reservations", response_model=List[ReservationOut])
def admin_reservations_by_date(date_str: str = Query(..., alias="date", description="YYYY-MM-DD")):
    _ = parse_date(date_str)
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        rows = conn.execute(
            """
            SELECT * FROM reservations
            WHERE status != 'canceled'
              AND inicio <= ?
              AND fim >= ?
            ORDER BY inicio ASC, id DESC
            """,
            (date_str, date_str),
        ).fetchall()
        return [dict(r) for r in rows]

@app.post("/admin/scan_code")
def admin_scan_code(payload: AdminScanCodeIn):
    rid, kit_id, token_prefix = parse_code_text(payload.code)
    now = datetime.utcnow().isoformat()

    with get_conn() as conn:
        expire_awaiting_payments(conn)
        row = conn.execute("SELECT * FROM reservations WHERE id = ?", (rid,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        if int(row["kit_id"]) != int(kit_id):
            raise HTTPException(status_code=400, detail="Código não bate com o kit da reserva.")
        if row["status"] == "canceled":
            raise HTTPException(status_code=400, detail="Reserva cancelada.")
        if row["status"] not in ("paid_with_deposit", "completed"):
            raise HTTPException(status_code=400, detail="Reserva não está paga.")

        if not verify_pickup_token_prefix(rid, row["created_at"], token_prefix):
            raise HTTPException(status_code=401, detail="Código inválido (token).")

        if row["status"] == "completed" or (row["checked_in_at"] or ""):
            updated = conn.execute("SELECT * FROM reservations WHERE id = ?", (rid,)).fetchone()
            return {"ok": True, "action": "none", "message": "Já devolvido.", "reservation": dict(updated)}

        if not (row["checked_out_at"] or ""):
            conn.execute("UPDATE reservations SET checked_out_at=? WHERE id=?", (now, rid))
            updated = conn.execute("SELECT * FROM reservations WHERE id = ?", (rid,)).fetchone()
            return {"ok": True, "action": "checkout", "message": "Retirada confirmada ✅", "reservation": dict(updated)}

        conn.execute("UPDATE reservations SET checked_in_at=?, status='completed' WHERE id=?", (now, rid))
        updated = conn.execute("SELECT * FROM reservations WHERE id = ?", (rid,)).fetchone()
        return {"ok": True, "action": "checkin", "message": "Devolução confirmada ✅", "reservation": dict(updated)}

@app.post("/admin/reservations/{reservation_id}/checkout")
def admin_checkout(reservation_id: int):
    now = datetime.utcnow().isoformat()
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        row = conn.execute("SELECT * FROM reservations WHERE id = ?", (reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        if row["status"] == "canceled":
            raise HTTPException(status_code=400, detail="Reserva cancelada não pode dar checkout.")
        if row["status"] != "paid_with_deposit":
            raise HTTPException(status_code=400, detail="Somente reservas pagas podem dar checkout.")

        conn.execute("UPDATE reservations SET checked_out_at=? WHERE id=?", (now, reservation_id))
        updated = conn.execute("SELECT * FROM reservations WHERE id = ?", (reservation_id,)).fetchone()
        return {"ok": True, "reservation": dict(updated)}

@app.post("/admin/reservations/{reservation_id}/checkin")
def admin_checkin(reservation_id: int):
    now = datetime.utcnow().isoformat()
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        row = conn.execute("SELECT * FROM reservations WHERE id = ?", (reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        if row["status"] == "canceled":
            raise HTTPException(status_code=400, detail="Reserva cancelada não pode dar check-in.")

        conn.execute("UPDATE reservations SET checked_in_at=?, status='completed' WHERE id=?", (now, reservation_id))
        updated = conn.execute("SELECT * FROM reservations WHERE id = ?", (reservation_id,)).fetchone()
        return {"ok": True, "reservation": dict(updated)}

@app.post("/admin/reservations/{reservation_id}/cancel", response_model=AdminCancelOut)
def admin_cancel_reservation(reservation_id: int, payload: AdminCancelIn):
    now = datetime.utcnow()
    with get_conn() as conn:
        expire_awaiting_payments(conn)

        row = conn.execute("SELECT * FROM reservations WHERE id = ?", (reservation_id,)).fetchone()
        if not row:
            raise HTTPException(status_code=404, detail="Reserva não encontrada.")
        if row["status"] == "completed":
            raise HTTPException(status_code=400, detail="Reserva concluída não pode ser cancelada.")

        if row["status"] == "canceled":
            existing = dict(row)
            fee = float(existing.get("cancel_fee") or 0.0)
            caucao = float(existing.get("caucao") or 0.0)
            return {
                "ok": True,
                "reservation": existing,
                "fee_retained_from_deposit": fee,
                "deposit_refund_expected": round(max(0.0, caucao - fee), 2),
                "rent_refund_expected": float(existing.get("total") or 0.0),
            }

        caucao = float(row["caucao"] or 0.0)
        fee = round(caucao * CANCEL_FEE_DEPOSIT_RATE, 2)
        canceled_at = now.isoformat()
        reason = (payload.reason or "admin_cancel_manual").strip()

        conn.execute(
            """
            UPDATE reservations
            SET status='canceled',
                canceled_at=?,
                cancel_reason=?,
                cancel_fee=?,
                cancel_fee_type='deposit_pct'
            WHERE id=?
            """,
            (canceled_at, reason, fee, reservation_id)
        )

        updated = conn.execute("SELECT * FROM reservations WHERE id = ?", (reservation_id,)).fetchone()
        updated_dict = dict(updated)

        deposit_refund_expected = max(0.0, caucao - fee)
        rent_refund_expected = float(row["total"] or 0.0)

        return {
            "ok": True,
            "reservation": updated_dict,
            "fee_retained_from_deposit": fee,
            "deposit_refund_expected": round(deposit_refund_expected, 2),
            "rent_refund_expected": round(rent_refund_expected, 2),
        }

@app.get("/admin/stats")
def admin_stats():
    with get_conn() as conn:
        expire_awaiting_payments(conn)
        rows = conn.execute("""
            SELECT status, COUNT(*) as c
            FROM reservations
            GROUP BY status
        """).fetchall()
        by_status = {r["status"]: r["c"] for r in rows}
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
def admin_create_customer(payload: CustomerCreate):
    now = datetime.utcnow().isoformat()
    name = payload.name.strip()
    phone = payload.phone.strip()
    if not name:
        raise HTTPException(status_code=400, detail="Nome obrigatório.")
    if not phone:
        raise HTTPException(status_code=400, detail="Telefone obrigatório.")

    with get_conn() as conn:
        cur = conn.execute(
            "INSERT INTO customers(name, phone, created_at) VALUES (?, ?, ?)",
            (name, phone, now),
        )
        row = conn.execute("SELECT * FROM customers WHERE id = ?", (cur.lastrowid,)).fetchone()
        return dict(row)

@app.get("/admin/customers", response_model=List[CustomerOut])
def admin_search_customers(q: str = Query("", description="busca por nome/telefone")):
    q = (q or "").strip()
    with get_conn() as conn:
        if not q:
            rows = conn.execute("SELECT * FROM customers ORDER BY id DESC LIMIT 50").fetchall()
        else:
            like = f"%{q}%"
            rows = conn.execute(
                "SELECT * FROM customers WHERE name LIKE ? OR phone LIKE ? ORDER BY id DESC LIMIT 50",
                (like, like),
            ).fetchall()
        return [dict(r) for r in rows]

# =========================
# Admin: Venda presencial
# =========================
@app.post("/admin/walkin/reservations")
def admin_create_walkin_reservations(payload: AdminWalkInReservationCreate):
    dias = calc_dias(parse_date(payload.inicio), parse_date(payload.fim))
    created_at = datetime.utcnow().isoformat()

    with get_conn() as conn:
        expire_awaiting_payments(conn)

        cust = conn.execute("SELECT * FROM customers WHERE id = ?", (payload.customer_id,)).fetchone()
        if not cust:
            raise HTTPException(status_code=404, detail="Cliente não encontrado.")

        available = []
        for kit_id in range(1, TOTAL_KITS + 1):
            if kit_disponivel(conn, kit_id, payload.inicio, payload.fim):
                available.append(kit_id)

        if len(available) < payload.quantity:
            raise HTTPException(status_code=409, detail=f"Quantidade indisponível. Disponíveis: {len(available)}")

        aluguel_kit, valor_cadeiras, total = calc_preco(dias, payload.cadeiras_extras)

        created: List[dict] = []
        for kit_id in available[:payload.quantity]:
            cur = conn.execute(
                """
                INSERT INTO reservations
                (kit_id, inicio, fim, dias, cadeiras_extras, aluguel_kit, valor_cadeiras_extras, total, caucao,
                 status, created_at, paid_at, pay_method, customer_id, source)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 'paid_with_deposit', ?, ?, ?, ?, 'store')
                """,
                (
                    kit_id,
                    payload.inicio,
                    payload.fim,
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
            )
            row = conn.execute("SELECT * FROM reservations WHERE id = ?", (cur.lastrowid,)).fetchone()
            created.append(dict(row))

        return {"ok": True, "reservations": created}
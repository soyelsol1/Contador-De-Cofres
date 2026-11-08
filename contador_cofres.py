import os
import re
import sys
import zlib
import base64
from operator import mul
import csv
import json
import math
import time
import uuid
import wave
import hashlib
import subprocess
import array
import ctypes
import shutil
import calendar
import threading
import http.client
import urllib.parse
from collections import Counter
from ctypes import wintypes
from datetime import date, datetime, timedelta, timezone
from functools import lru_cache
import tkinter as tk
import tkinter.font as tkfont
from tkinter import messagebox, filedialog

import mss
from PIL import Image, ImageChops, ImageDraw, ImageFilter

MSS = getattr(mss, "MSS", None) or mss.mss

try:
    import winsound
except ImportError:
    winsound = None

try:
    ctypes.windll.shcore.SetProcessDpiAwareness(2)
except Exception:
    pass

try:
    _u = ctypes.windll.user32
    _u.GetParent.argtypes = [wintypes.HWND]
    _u.GetParent.restype = wintypes.HWND
    _u.GetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int]
    _u.GetWindowLongW.restype = ctypes.c_long
    _u.SetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_long]
    _u.SetWindowLongW.restype = ctypes.c_long
    _u.GetAsyncKeyState.argtypes = [ctypes.c_int]
    _u.GetAsyncKeyState.restype = ctypes.c_short
except Exception:
    pass

if getattr(sys, "frozen", False):
    CARPETA = os.path.dirname(sys.executable)
else:
    CARPETA = os.path.dirname(os.path.abspath(__file__))


# ---------------------------------------------------------------- dónde se guardan tus datos
def _elegir_carpeta_datos():
    """Los datos van a %APPDATA%\\ContadorDeCofres: un sitio fijo de tu usuario de Windows.
    Así NO se pierden si mueves el programa, lo abres desde un .zip, desde Descargas, etc."""
    base = os.environ.get("APPDATA") or os.environ.get("LOCALAPPDATA")
    candidatos = ([os.path.join(base, "ContadorDeCofres")] if base else []) + [CARPETA]
    for c in candidatos:
        try:
            os.makedirs(c, exist_ok=True)
            prueba = os.path.join(c, ".prueba_escritura")
            with open(prueba, "w") as f:
                f.write("ok")
            os.remove(prueba)
            return c
        except OSError:
            continue
    return CARPETA


DATOS = _elegir_carpeta_datos()


def _migrar_datos_antiguos():
    """Si venías de la versión que guardaba junto al programa, copia tus datos al sitio nuevo."""
    if os.path.normcase(os.path.abspath(DATOS)) == os.path.normcase(os.path.abspath(CARPETA)):
        return
    try:
        for nombre in ("contador_cofres.json", "historial_cofres.json"):
            nuevo = os.path.join(DATOS, nombre)
            viejo = os.path.join(CARPETA, nombre)
            if os.path.exists(nuevo) or os.path.exists(nuevo + ".bak"):
                continue
            for suf in ("", ".bak"):
                if os.path.isfile(viejo + suf):
                    shutil.copy2(viejo + suf, nuevo + suf)
        viejos = os.path.join(CARPETA, "sonidos")
        nuevos = os.path.join(DATOS, "sonidos")
        if os.path.isdir(viejos):
            os.makedirs(nuevos, exist_ok=True)
            for f in os.listdir(viejos):
                if f.lower().startswith("mi_sonido.") and not os.path.exists(os.path.join(nuevos, f)):
                    shutil.copy2(os.path.join(viejos, f), os.path.join(nuevos, f))
    except OSError:
        pass


_migrar_datos_antiguos()

# ---------------------------------------------------------------- actualización automática
VERSION = "1.2.1"
REPO_RAW = "https://raw.githubusercontent.com/soyelsol1/Contador-De-Cofres/main"
CARPETA_CODIGO = os.path.join(DATOS, "codigo")
ARCHIVO_CODIGO = os.path.join(CARPETA_CODIGO, "contador_cofres.py")
CARPETA_COPIAS = os.path.join(DATOS, "copias")


def version_tupla(v):
    t = tuple(int(x) for x in re.findall(r"\d+", str(v))[:4])
    return t or (0,)


def version_de_codigo(texto):
    m = re.search(r'^VERSION\s*=\s*"([^"]+)"', texto, re.M)
    return m.group(1) if m else ""


def _get_raw(nombre, timeout=10):
    p = urllib.parse.urlsplit(REPO_RAW)
    c = http.client.HTTPSConnection(p.netloc, timeout=timeout)
    try:
        c.request("GET", "%s/%s?t=%d" % (p.path, nombre, int(time.time())),
                  headers={"User-Agent": "ContadorDeCofres", "Cache-Control": "no-cache"})
        r = c.getresponse()
        datos = r.read()
        if r.status != 200:
            raise ValueError("GitHub respondió %d" % r.status)
        return datos
    finally:
        c.close()


def buscar_actualizacion():
    # None = estás al día; dict = hay una versión nueva
    d = json.loads(_get_raw("version.json").decode("utf-8-sig"))
    if isinstance(d, dict) and version_tupla(d.get("version")) > version_tupla(VERSION):
        return d
    return None


def descargar_actualizacion(info):
    nombre = os.path.basename(str(info.get("archivo") or "contador_cofres.py"))
    datos = _get_raw(nombre, 40).replace(b"\r\n", b"\n")
    if len(datos) < 20000:
        raise ValueError("la descarga está incompleta")
    sha = str(info.get("sha256") or "").lower()
    if sha and hashlib.sha256(datos).hexdigest() != sha:
        raise ValueError("el archivo no coincide con su firma (reintenta en unos minutos)")
    texto = datos.decode("utf-8")
    if version_de_codigo(texto) != str(info.get("version")):
        raise ValueError("la versión del archivo no coincide con version.json")
    compile(texto, nombre, "exec")
    os.makedirs(CARPETA_CODIGO, exist_ok=True)
    tmp = ARCHIVO_CODIGO + ".tmp"
    with open(tmp, "wb") as f:
        f.write(datos)
    os.replace(tmp, ARCHIVO_CODIGO)


def _lanzar_codigo_nuevo():
    # Si hay una versión descargada más nueva que este archivo, se ejecuta esa.
    if globals().get("_ES_ACTUALIZADA"):
        return False
    try:
        if not os.path.isfile(ARCHIVO_CODIGO):
            return False
        with open(ARCHIVO_CODIGO, "rb") as f:
            texto = f.read().decode("utf-8")
        if version_tupla(version_de_codigo(texto)) <= version_tupla(VERSION):
            return False
        codigo = compile(texto, ARCHIVO_CODIGO, "exec")
    except Exception:
        return False
    g = {"__name__": "__main__", "__file__": ARCHIVO_CODIGO, "_ES_ACTUALIZADA": True}
    try:
        exec(codigo, g)
    except Exception:
        try:
            os.remove(ARCHIVO_CODIGO)      # si la nueva falla al arrancar, se descarta
        except OSError:
            pass
        return False
    return True


def reiniciar_programa():
    env = dict(os.environ)
    env["CONTADOR_REINICIO"] = "1"
    env["PYINSTALLER_RESET_ENVIRONMENT"] = "1"
    env.pop("_MEIPASS2", None)
    if getattr(sys, "frozen", False):
        cmd = [sys.executable]
    else:
        cmd = [sys.executable, os.path.abspath(sys.argv[0])]
    subprocess.Popen(cmd, env=env, close_fds=True, creationflags=0x00000008 | 0x00000200)


def copia_diaria():
    # Una copia de tus datos al día (se guardan las últimas 14).
    try:
        os.makedirs(CARPETA_COPIAS, exist_ok=True)
        hoy = date.today().isoformat()
        for ruta in (os.path.join(DATOS, "contador_cofres.json"), os.path.join(DATOS, "historial_cofres.json")):
            base = os.path.basename(ruta)
            destino = os.path.join(CARPETA_COPIAS, "%s_%s" % (hoy, base))
            if os.path.isfile(ruta) and not os.path.exists(destino):
                shutil.copy2(ruta, destino)
            viejas = sorted(f for f in os.listdir(CARPETA_COPIAS) if f.endswith("_" + base))
            for f in viejas[:-14]:
                os.remove(os.path.join(CARPETA_COPIAS, f))
    except Exception:
        pass


ARCHIVO = os.path.join(DATOS, "contador_cofres.json")
ARCHIVO_HIST = os.path.join(DATOS, "historial_cofres.json")
CARPETA_SONIDOS = os.path.join(DATOS, "sonidos")
CARPETA_DETECCIONES = os.path.join(DATOS, "detecciones")

# Zona de la pantalla donde salen los avisos "+N PE / COFRE ..." (fracciones de la ventana del juego).
# Es una franja alta para ver TODOS los avisos a la vez (si cogés dos cofres seguidos, se apilan).
FX0, FY0, FW, FH = 0.60, 0.14, 0.19, 0.34
# El análisis se hace siempre con el texto al mismo tamaño: 84 px de ancho para el 13 % de la pantalla.
ANCHO_ANALISIS_BASE = 1456.0

INTERVALO_MS = 80
FRAMES_PARA_CONTAR = 2      # fotogramas seguidos viendo un aviso nuevo para darlo por bueno (~0,15 s)
FRAMES_PARA_REARMAR = 4     # fotogramas seguidos sin ese aviso para dar por terminado el anterior
MAX_DETECCIONES_GUARDADAS = 25

# Detección del lobby (medido sobre tu captura): (x, y, ancho, alto) en fracciones de la ventana
LOBBY_BOTON = (0.060, 0.815, 0.150, 0.060)      # botón amarillo grande "JUGAR"
LOBBY_PASTILLA = (0.112, 0.048, 0.053, 0.034)   # pastilla gris clara "JUGAR" del menú de arriba
LOBBY_CADA = 5          # se mira el lobby cada 5 vueltas (~0,4 s)
LOBBY_CONFIRMAR = 3     # veces seguidas que hay que verlo para darlo por bueno (~1,2 s)
LOBBY_REARMAR = 4       # veces seguidas sin verlo para poder detectar otro lobby
LOBBY_GRACIA_ARRANQUE = 12.0   # si al abrir el programa ya estás en el lobby, no se cierra la partida

# Colores
BG = "#0e0b1a"
CARD = "#1b1730"
PANEL = "#241f3d"
ORO = "#ffc83d"
ORO_OSC = "#a8791c"
TEXTO = "#ece8f8"
APAGADO = "#8a84a6"
VERDE = "#3ddc84"
ROJO = "#ff6b7a"
MORADO = "#8f63ff"
CIAN = "#6fd3ff"
CONTORNO = "#140e24"
TRANSPARENTE = "#010101"
COLOR_PARTIDA = "#c4b0ff"
AZUL = "#3b6fb0"

TAMANOS = {"Pequeño": 34, "Mediano": 54, "Grande": 80}

MAX_NUMERO = 9999999
BARRA_META_W = 300

# ---------------------------------------------------------------- teclas
# Acciones con atajo de teclado. Se puede asignar CUALQUIER tecla (o Ctrl/Alt/Mayús + tecla).
TECLAS_DEF = {"sumar": "F9", "restar": "F7", "nueva": "F8",
              "overlay": "Ninguna", "meta": "Ninguna", "mover": "Ninguna", "stats": "Ninguna"}
ETIQUETAS_TECLA = (
    ("sumar", "Sumar +1 cofre"),
    ("restar", "Restar −1 cofre"),
    ("nueva", "Fin de partida / nueva partida"),
    ("overlay", "Mostrar / ocultar el número en pantalla"),
    ("meta", "Mostrar / ocultar la meta en pantalla"),
    ("mover", "Activar / desactivar «Mover»"),
    ("stats", "Abrir / cerrar estadísticas"),
)
MODS = (("Ctrl+", 0x11), ("Alt+", 0x12), ("Mayús+", 0x10))


def _construir_teclas():
    n = {}
    for i in range(1, 25):
        n["F%d" % i] = 0x6F + i
    for ch in "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789":
        n[ch] = ord(ch)
    for i in range(10):
        n["Num %d" % i] = 0x60 + i
    n.update({"Num *": 0x6A, "Num +": 0x6B, "Num -": 0x6D, "Num .": 0x6E, "Num /": 0x6F,
              "Espacio": 0x20, "Enter": 0x0D, "Tab": 0x09, "Insert": 0x2D, "Supr": 0x2E,
              "Inicio": 0x24, "Fin": 0x23, "RePág": 0x21, "AvPág": 0x22,
              "Flecha ↑": 0x26, "Flecha ↓": 0x28, "Flecha ←": 0x25, "Flecha →": 0x27,
              "Pausa": 0x13, "ImprPant": 0x2C, "Bloq Mayús": 0x14, "Bloq Num": 0x90,
              "Bloq Despl": 0x91,
              "Ratón: rueda (clic)": 0x04, "Ratón: lateral 1": 0x05, "Ratón: lateral 2": 0x06})
    return n


TECLA_VK = _construir_teclas()
VK_TECLA = {v: k for k, v in TECLA_VK.items()}
# Teclas que no se pueden usar como tecla principal (modificadores, Windows, Esc y Retroceso)
VK_EXCLUIDAS = {0x1B, 0x08, 0x10, 0x11, 0x12, 0x5B, 0x5C, 0x5D, 0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5}
RANGO_CAPTURA = [vk for vk in range(8, 255) if vk not in VK_EXCLUIDAS or vk in (0x1B, 0x08)] + [0x04, 0x05, 0x06]


def nombre_vk(vk):
    return VK_TECLA.get(vk, "Tecla %d" % vk)


def vk_de_nombre(nombre):
    if nombre in TECLA_VK:
        return TECLA_VK[nombre]
    m = re.fullmatch(r"Tecla (\d{1,3})", nombre or "")
    if m and 8 <= int(m.group(1)) <= 254:
        return int(m.group(1))
    return None


def parsear_combo(texto):
    """'Ctrl+F9' -> (frozenset({0x11}), 0x78). 'Ninguna' o algo raro -> None."""
    resto = (texto or "").strip()
    if not resto or resto == "Ninguna":
        return None
    mods = set()
    cambio = True
    while cambio:
        cambio = False
        for pref, vk in MODS:
            if resto.startswith(pref) and vk not in mods:
                mods.add(vk)
                resto = resto[len(pref):]
                cambio = True
    vk = vk_de_nombre(resto)
    if vk is None or vk in VK_EXCLUIDAS:
        return None
    return frozenset(mods), vk


# ---------------------------------------------------------------- utilidades
def entero(v, mx=MAX_NUMERO):
    try:
        n = int(v)
    except (TypeError, ValueError):
        return 0
    return max(0, min(mx, n))


def parsear_numero(t):
    t = (t or "").strip()
    if not (t.isascii() and t.isdigit()):
        return None
    n = int(t)
    return n if n <= MAX_NUMERO else None


def limpiar_sala(t):
    return re.sub(r"[^a-zA-Z0-9_-]", "", (t or "").strip())[:40].lower()


def limpiar_url(u):
    u = (u or "").strip().rstrip("/")
    if u.endswith(".json"):
        u = u[:-5].rstrip("/")
    if u and not u.startswith(("http://", "https://")):
        u = "https://" + u
    return u


def nombre_por_defecto():
    n = (os.environ.get("USERNAME") or "").strip()
    return (n or "Jugador")[:20]


def f1(x):
    return ("%.1f" % x).replace(".", ",")


def duracion(seg):
    seg = int(round(seg))
    if seg < 60:
        return "%d s" % seg
    return "%d min %02d s" % (seg // 60, seg % 60)


def hms(seg):
    seg = int(max(0, seg))
    h, r = divmod(seg, 3600)
    m, s = divmod(r, 60)
    return ("%d:%02d:%02d" % (h, m, s)) if h else ("%02d:%02d" % (m, s))


def es_hito(n):
    """Hitos que se celebran: cada 100 y cada 250 cofres (100, 200, 250, 300 ... 500 ...)."""
    return n > 0 and (n % 100 == 0 or n % 250 == 0)


def instancia_unica():
    """Evita abrir dos copias a la vez (se pisarían los datos al guardar)."""
    try:
        k = ctypes.windll.kernel32
        h = k.CreateMutexW(None, False, "ContadorDeCofres_UnicaInstancia")
        if k.GetLastError() == 183:      # ERROR_ALREADY_EXISTS
            return False
        globals()["_MUTEX"] = h
    except Exception:
        pass
    return True


# ---------------------------------------------------------------- guardado seguro
def leer_json(ruta):
    """Lee un JSON; si el archivo principal está roto o no existe, prueba con la copia .bak.
    Si el principal estaba roto, guarda una copia aparte (.corrupto) antes de que nada lo pise."""
    for r in (ruta, ruta + ".bak"):
        try:
            with open(r, "r", encoding="utf-8") as f:
                d = json.load(f)
            if isinstance(d, dict):
                return d
        except FileNotFoundError:
            continue
        except (OSError, ValueError):
            if r == ruta:
                try:
                    shutil.copy2(ruta, ruta + ".corrupto")
                except OSError:
                    pass
            continue
    return {}


def guardar_json(ruta, datos, **kw):
    """Escribe de forma atómica (archivo temporal + reemplazo) y deja una copia de seguridad.
    Devuelve True si se guardó de verdad, False si no se pudo."""
    try:
        txt = json.dumps(datos, **kw)
    except (TypeError, ValueError):
        return False
    tmp = ruta + ".tmp"
    for _ in range(3):
        try:
            with open(tmp, "w", encoding="utf-8") as f:
                f.write(txt)
                f.flush()
                try:
                    os.fsync(f.fileno())
                except OSError:
                    pass
            try:
                if os.path.exists(ruta) and os.path.getsize(ruta) > 2:
                    shutil.copy2(ruta, ruta + ".bak")
            except OSError:
                pass
            os.replace(tmp, ruta)
            return True
        except OSError:
            time.sleep(0.03)
    return False


# ---------------------------------------------------------------- hora de España
@lru_cache(maxsize=16)
def _limites_dst(anio):
    """Horario de verano de la UE: del último domingo de marzo al último de octubre, 01:00 UTC."""
    def ultimo_domingo(mes):
        d = date(anio, mes, 31)
        while d.weekday() != 6:
            d -= timedelta(days=1)
        return calendar.timegm((anio, mes, d.day, 1, 0, 0))
    return ultimo_domingo(3), ultimo_domingo(10)


def a_madrid(ts):
    """Marca de tiempo (UTC) -> fecha y hora de España peninsular (sin zona)."""
    dt = datetime.fromtimestamp(ts, timezone.utc)
    ini, fin = _limites_dst(dt.year)
    horas = 2 if ini <= ts < fin else 1
    return (dt + timedelta(hours=horas)).replace(tzinfo=None)


def fecha_madrid(ts):
    return a_madrid(ts).date()


# ---------------------------------------------------------------- sonidos
SR = 22050


def _tono(f1_, dur, f2=None, vol=0.5, forma="seno", decay=4.0):
    n = max(1, int(SR * dur))
    f2 = f1_ if f2 is None else f2
    out = []
    fase = 0.0
    ataque = SR * 0.004
    for i in range(n):
        t = i / float(n)
        fase += 2 * math.pi * (f1_ + (f2 - f1_) * t) / SR
        if forma == "cuadrada":
            s = 0.6 if math.sin(fase) >= 0 else -0.6
        elif forma == "sierra":
            s = 2 * ((fase / (2 * math.pi)) % 1.0) - 1
        else:
            s = math.sin(fase)
        env = math.exp(-decay * t) * min(1.0, i / ataque)
        out.append(s * vol * env)
    return out


def _mezcla(*pistas):
    """pistas = (inicio en segundos, muestras)"""
    total = max(int(SR * ini) + len(m) for ini, m in pistas)
    buf = [0.0] * total
    for ini, m in pistas:
        o = int(SR * ini)
        for i, v in enumerate(m):
            buf[o + i] += v
    return buf


def _guardar_wav(ruta, muestras):
    pico = max((abs(v) for v in muestras), default=1.0) or 1.0
    k = 0.85 / pico if pico > 0.85 else 1.0
    datos = array.array("h", (int(max(-1.0, min(1.0, v * k)) * 32767) for v in muestras))
    with wave.open(ruta, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(SR)
        w.writeframes(datos.tobytes())


def _s_moneda():
    return _mezcla((0, _tono(988, 0.09, vol=0.35, forma="cuadrada", decay=1.5)),
                   (0.09, _tono(1319, 0.40, vol=0.35, forma="cuadrada", decay=5)))


def _s_campana():
    return _mezcla((0, _tono(880, 0.9, vol=0.5, decay=4)),
                   (0, _tono(1760, 0.9, vol=0.25, decay=5)),
                   (0, _tono(2640, 0.6, vol=0.12, decay=6)))


def _s_cofre():
    return _mezcla((0, _tono(250, 0.28, f2=700, vol=0.25, forma="sierra", decay=1.5)),
                   (0.25, _tono(784, 0.5, vol=0.3, decay=4)),
                   (0.25, _tono(988, 0.5, vol=0.3, decay=4)),
                   (0.25, _tono(1175, 0.5, vol=0.3, decay=4)))


def _s_pop():
    return _tono(700, 0.14, f2=140, vol=0.7, decay=5)


def _s_nivel():
    notas = (523, 659, 784, 1047)
    pistas = [(i * 0.09, _tono(f, 0.12, vol=0.4, decay=3)) for i, f in enumerate(notas)]
    pistas.append((0.36, _tono(1319, 0.4, vol=0.45, decay=4)))
    return _mezcla(*pistas)


def _s_laser():
    return _tono(1800, 0.28, f2=250, vol=0.35, forma="sierra", decay=3)


def _s_ding():
    return _mezcla((0, _tono(1568, 0.6, vol=0.55, decay=6)),
                   (0, _tono(3136, 0.4, vol=0.15, decay=8)))


def _s_tesoro():
    notas = (659, 784, 988, 1175, 1319, 1568)
    pistas = [(i * 0.06, _tono(f, 0.15, vol=0.3, decay=4)) for i, f in enumerate(notas)]
    for f in (1047, 1319, 1568):
        pistas.append((0.38, _tono(f, 0.55, vol=0.25, decay=4)))
    return _mezcla(*pistas)


GENERADORES = {"Moneda": _s_moneda, "Campana": _s_campana, "Cofre": _s_cofre, "Pop": _s_pop,
               "Nivel": _s_nivel, "Laser": _s_laser, "Ding": _s_ding, "Tesoro": _s_tesoro}
OPCIONES_SONIDO = ["Ninguno"] + list(GENERADORES) + ["Windows", "Mi sonido"]


def ruta_sonido(nombre):
    return os.path.join(CARPETA_SONIDOS, nombre + ".wav")


def asegurar_sonidos():
    """Crea los sonidos predeterminados la primera vez que se abre el programa."""
    try:
        os.makedirs(CARPETA_SONIDOS, exist_ok=True)
        for nombre, gen in GENERADORES.items():
            ruta = ruta_sonido(nombre)
            if not os.path.isfile(ruta) or os.path.getsize(ruta) < 100:
                _guardar_wav(ruta, gen())
    except Exception:
        pass


def reproducir_archivo(ruta):
    """WAV con winsound; MP3/WMA/M4A con MCI de Windows."""
    if not ruta or not os.path.isfile(ruta):
        return False
    try:
        if ruta.lower().endswith(".wav") and winsound:
            winsound.PlaySound(ruta, winsound.SND_FILENAME | winsound.SND_ASYNC)
            return True
        mci = ctypes.windll.winmm.mciSendStringW
        mci("close sonido_cofre", None, 0, None)
        if mci('open "%s" alias sonido_cofre' % ruta, None, 0, None) == 0:
            mci("play sonido_cofre", None, 0, None)
            return True
    except Exception:
        pass
    return False


def sonar(notas):
    """Melodía corta en segundo plano (frecuencia Hz, duración ms)."""
    if not winsound:
        return

    def run():
        for f, d in notas:
            try:
                winsound.Beep(f, d)
            except Exception:
                return

    threading.Thread(target=run, daemon=True).start()


# ---------------------------------------------------------------- historial
def media_entre_cofres(eventos):
    gaps = []
    prev = None
    for ts, _ in eventos:
        if prev is not None and 0 <= ts - prev <= 1800:
            gaps.append(ts - prev)
        prev = ts
    return gaps


class Historial:
    """Cada partida es una lista de cofres [hora, 1=automático / 0=manual].
    Solo se guarda lo que cuenta el programa; lo que escribes a mano en el total no entra."""

    def __init__(self, ruta):
        self.ruta = ruta
        self.partidas = []
        self.actual = []
        self.version = 0
        self.error = False
        self.sucio = False
        self.cargar()

    @staticmethod
    def _limpiar(lista):
        out = []
        if isinstance(lista, list):
            for e in lista:
                if isinstance(e, (list, tuple)) and len(e) == 2 and isinstance(e[0], (int, float)):
                    out.append([int(e[0]), 1 if e[1] else 0])
        return out

    def cargar(self):
        d = leer_json(self.ruta)
        if not d:
            return
        for p in d.get("partidas", []) if isinstance(d.get("partidas"), list) else []:
            ev = self._limpiar(p.get("c") if isinstance(p, dict) else None)
            if ev:
                self.partidas.append(ev)
        act = d.get("actual")
        self.actual = self._limpiar(act.get("c") if isinstance(act, dict) else None)

    def guardar(self):
        datos = {"version": 1, "partidas": [{"c": p} for p in self.partidas],
                 "actual": {"c": self.actual}}
        ok = guardar_json(self.ruta, datos, separators=(",", ":"))
        self.error = not ok
        if ok:
            self.sucio = False
        return ok

    def sumar(self, ts, auto):
        self.actual.append([int(ts), 1 if auto else 0])
        self.version += 1
        self.sucio = True            # se guarda en un momento (ver App.ciclo_amigo), no a mitad de la cuenta

    def quitar(self):
        if self.actual:
            self.actual.pop()
            self.version += 1
            self.sucio = True
            return True
        return False

    def cerrar(self):
        """Termina la partida en curso. Si no tiene cofres no se guarda."""
        if self.actual:
            self.partidas.append(self.actual)
            self.actual = []
            self.version += 1
            self.guardar()
            return True
        return False

    def borrar_todo(self):
        """Vacía el historial (partidas y cofres por día). No toca tus contadores."""
        self.partidas = []
        self.actual = []
        self.version += 1
        self.guardar()

    def todas(self):
        return [p for p in self.partidas if p] + ([self.actual] if self.actual else [])

    def exportar(self, ruta_partidas, ruta_dias):
        juegos = self.todas()
        with open(ruta_partidas, "w", encoding="utf-8-sig", newline="") as f:
            w = csv.writer(f, delimiter=";")
            w.writerow(["Partida", "Fecha", "Primer cofre", "Último cofre", "Cofres", "Automáticos",
                        "Manuales", "Segundos medios entre cofres", "En curso"])
            for i, ev in enumerate(juegos, 1):
                a, b = a_madrid(ev[0][0]), a_madrid(ev[-1][0])
                autos = sum(1 for _, x in ev if x)
                gaps = media_entre_cofres(ev)
                med = ("%.1f" % (sum(gaps) / len(gaps))).replace(".", ",") if gaps else ""
                w.writerow([i, a.strftime("%d/%m/%Y"), a.strftime("%H:%M:%S"), b.strftime("%H:%M:%S"),
                            len(ev), autos, len(ev) - autos, med,
                            "sí" if (ev is self.actual) else "no"])
        por_dia = Counter()
        for ev in juegos:
            for ts, _ in ev:
                por_dia[fecha_madrid(ts)] += 1
        with open(ruta_dias, "w", encoding="utf-8-sig", newline="") as f:
            w = csv.writer(f, delimiter=";")
            w.writerow(["Fecha", "Cofres"])
            for d in sorted(por_dia):
                w.writerow([d.strftime("%d/%m/%Y"), por_dia[d]])


def calcular_stats(partidas, actual, ahora):
    juegos = [p for p in partidas if p] + ([actual] if actual else [])
    hoy = fecha_madrid(ahora)
    por_dia = Counter()
    por_hora = Counter()
    autos = manuales = partidas_hoy = 0
    dur_tot = cof_dur = 0
    gaps = []
    for ev in juegos:
        hubo_hoy = False
        for ts, a in ev:
            d = fecha_madrid(ts)
            por_dia[d] += 1
            por_hora[a_madrid(ts).hour] += 1
            if d == hoy:
                hubo_hoy = True
            if a:
                autos += 1
            else:
                manuales += 1
        if hubo_hoy:
            partidas_hoy += 1
        gaps.extend(media_entre_cofres(ev))
        if len(ev) >= 2:
            dur_tot += ev[-1][0] - ev[0][0]
            cof_dur += len(ev)

    total_ev = sum(por_dia.values())
    cofres_hoy = por_dia.get(hoy, 0)

    mejor_racha = run = 0
    prev = None
    for d in sorted(por_dia):
        run = run + 1 if (prev is not None and (d - prev).days == 1) else 1
        mejor_racha = max(mejor_racha, run)
        prev = d
    racha = 0
    d = hoy if hoy in por_dia else hoy - timedelta(days=1)
    while d in por_dia:
        racha += 1
        d -= timedelta(days=1)

    wd = hoy.weekday()
    lunes = hoy - timedelta(days=wd)
    lunes_ant = lunes - timedelta(days=7)
    esta = sum(por_dia.get(lunes + timedelta(days=k), 0) for k in range(wd + 1))
    ant = sum(por_dia.get(lunes_ant + timedelta(days=k), 0) for k in range(wd + 1))
    pct = ((esta - ant) * 100.0 / ant) if ant > 0 else None

    dias14 = []
    for i in range(14):
        d = hoy - timedelta(days=13 - i)
        dias14.append((d, por_dia.get(d, 0)))
    ultimas = [(len(ev), a_madrid(ev[0][0])) for ev in juegos[-20:]]

    return {
        "hoy_fecha": hoy,
        "hoy": cofres_hoy,
        "partidas_hoy": partidas_hoy,
        "media_hoy": (cofres_hoy / partidas_hoy) if partidas_hoy else None,
        "partidas": len(juegos),
        "mejor_partida": max((len(ev) for ev in juegos), default=0),
        "mejor_dia": max(por_dia.values(), default=0),
        "racha": racha,
        "mejor_racha": mejor_racha,
        "media_total": (total_ev / len(juegos)) if juegos else None,
        "semana": esta,
        "semana_ant": ant,
        "semana_pct": pct,
        "gap": (sum(gaps) / len(gaps)) if gaps else None,
        "cph": (cof_dur * 3600.0 / dur_tot) if dur_tot > 0 else None,
        "mejor_hora": (max(por_hora, key=por_hora.get) if por_hora else None),
        "mejor_hora_n": (max(por_hora.values()) if por_hora else 0),
        "autos": autos,
        "manuales": manuales,
        "dias14": dias14,
        "ultimas": ultimas,
    }


# ---------------------------------------------------------------- detección
def _lut(f):
    return [255 if f(v) else 0 for v in range(256)]


_L_B170 = _lut(lambda v: v >= 170)
_L_BG85 = _lut(lambda v: v >= 85)
_L_R70_200 = _lut(lambda v: 70 <= v <= 200)
_L_BR30 = _lut(lambda v: v >= 30)
_L_B215 = _lut(lambda v: v > 215)
_L_R165_250 = _lut(lambda v: 165 < v < 250)
_L_G130_225 = _lut(lambda v: 130 < v < 225)
_L_BG35 = _lut(lambda v: v > 35)
_L_RG10 = _lut(lambda v: v > 10)
_L_CONTRASTE = [max(0, min(255, int((v - 60) * 255 / 150))) for v in range(256)]
_L_BIN = [255 if v else 0 for v in range(256)]

# Plantilla de la palabra «COFRE» tal y como se ve en el aviso (medida sobre una captura real).
# Todos los avisos de cofre empiezan por esa palabra, con la misma tipografía; el resto de avisos
# de experiencia (la que da la partida por el tiempo, etc.) llevan otra palabra.
PLANTILLA_COFRE_TAM = (43, 16)
PLANTILLA_COFRE_B64 = (
    "eNrNUlFLmmEUPl1syLwIQzZiIdKI7WJjhCOUocToQxQpRIpIJBHpYwQyiHCEEXWVCCFKF5OhDLsK"
    "YhGLiMZohCHhkG8Xg+/CGHYxkBCGEnYRT+d9I/oLnYtz3nPe5zw853CI7oW593UtztG4VtVyT4g+"
    "FPL5Ys6++LOqfQ0QTYl0UyKXISxOz5oiVulhQxYi0mOBjmUUSDuwGe3g1KyhObkNKM+B8+NydgaI"
    "RYG/ljPoxeK6gB6ibaDfaDC5Sl52I8Aw1+fQMdAWGoPAzI3Qx8AWUbKwdIQrA3mYahbo4Y8Cat3m"
    "Gva502/u6+LKBDAvWh6dQ+99ytShz0A2v+bSUJs6YD2qlGpiSAIYJePHWBLYGfLuAW8PxVcpIIf7"
    "n6R1oF6vCLY04KAw8B3I2R1tnA6e4dfejwSXvtRxYrOWUH5jtwnoCjBNJ+yAbwOcrLwGll/aXvCu"
    "XDnAbW2zXMU7wFAepFMDUq/YlXitQz4g+C7iTwGWOWDWIqX+UwXtJ/HMOh3RS47lMec8K/IUMxut"
    "P9YAi1AkVA/LdfV7hvt9IX8kOP3eG1LdzrDPFjzajS+Ojyiqq1cgHpjMt0fQrUwE03placwfmFzQ"
    "LgqjaqXZ6mSiq6G7Q7kGwscsgA==")
UMBRAL_COFRE = 0.76
_PLANTILLAS = {}


def _plantilla_cofre(escala):
    clave = round(escala, 2)
    p = _PLANTILLAS.get(clave)
    if p is None:
        base = Image.frombytes("L", PLANTILLA_COFRE_TAM, zlib.decompress(base64.b64decode(PLANTILLA_COFRE_B64)))
        if clave != 1.0:
            base = base.resize((max(8, int(round(PLANTILLA_COFRE_TAM[0] * clave))),
                                max(4, int(round(PLANTILLA_COFRE_TAM[1] * clave)))), Image.BILINEAR)
        d = list(base.tobytes())
        n = len(d)
        sb = sum(d)
        mb = sb / float(n)
        vb = sum(map(mul, d, d)) / float(n) - mb * mb
        p = (base.size, d, n, mb, vb)
        _PLANTILLAS[clave] = p
    return p


def _ncc_en(F, x, y, plant):
    (tw, th), d, n, mb, vb = plant
    a = list(F.crop((x, y, x + tw, y + th)).tobytes())
    sa = sum(a)
    if sa == 0:
        return 0.0
    ma = sa / float(n)
    va = sum(map(mul, a, a)) / float(n) - ma * ma
    if va <= 1e-6:
        return 0.0
    return (sum(map(mul, a, d)) / float(n) - ma * mb) / (math.sqrt(va) * math.sqrt(vb))


def puntuacion_cofre(F, x0, y0, x1=None):
    """Parecido (de 0 a 1) con la palabra «COFRE», buscándola en CUALQUIER punto de la línea 2
    (entre x0 y x1): puede ir al principio («COFRE DE ESPÍRITU») o después de otras palabras.
    Se prueban pequeños desplazamientos y tamaños, porque el aviso se anima."""
    p1 = _plantilla_cofre(1.0)
    if p1[4] <= 1e-6:
        return 0.0
    tw = p1[0][0]
    fin = max(x0, (x1 if x1 is not None else x0) - tw + 8)
    mejor, mx, my = 0.0, x0, y0
    for x in range(x0, fin + 1, 3):
        for dy in (0, -1, 1, -2, 2, -3, 3):
            s = _ncc_en(F, x, y0 + dy, p1)
            if s > mejor:
                mejor, mx, my = s, x, y0 + dy
        if mejor >= 0.9:
            return mejor
    if mejor < 0.5:
        return mejor                   # ni se le parece: no merece la pena afinar
    for escala in (1.0, 0.92, 1.08):
        p = _plantilla_cofre(escala)
        for dx in range(-2, 3):
            for dy in range(-2, 3):
                s = _ncc_en(F, mx + dx, my + dy, p)
                if s > mejor:
                    mejor = s
    return mejor


_CACHE_COFRE = {}


def mascara_aviso(img):
    r, g, b = img.convert("RGB").split()
    mul_ = ImageChops.multiply
    bg = ImageChops.subtract(b, g)
    borde = mul_(mul_(b.point(_L_B170), bg.point(_L_BG85)),
                 mul_(r.point(_L_R70_200), ImageChops.subtract(b, r).point(_L_BR30)))
    relleno = mul_(mul_(mul_(b.point(_L_B215), r.point(_L_R165_250)), mul_(g.point(_L_G130_225), bg.point(_L_BG35))),
                   ImageChops.subtract(r, g).point(_L_RG10))
    cerca = borde.filter(ImageFilter.MaxFilter(5))
    return ImageChops.lighter(borde, mul_(relleno, cerca))


def _tramos(flags, hueco=0):
    out = []
    ini = fin = None
    vacios = 0
    for i, f in enumerate(flags):
        if f:
            if ini is None:
                ini = i
            fin = i
            vacios = 0
        elif ini is not None:
            vacios += 1
            if vacios > hueco:
                out.append((ini, fin))
                ini = None
    if ini is not None:
        out.append((ini, fin))
    return out


def _buscar_avisos_dos(img, depurar=False):
    m = mascara_aviso(img)
    w, h = m.size
    datos = m.tobytes()
    filas = [datos[y * w:(y + 1) * w].count(255) for y in range(h)]
    bandas = []
    for y0, y1 in _tramos([n >= 3 for n in filas], 2):
        banda = m.crop((0, y0, w, y1 + 1)).transpose(Image.TRANSPOSE)
        bh = y1 - y0 + 1
        bd = banda.tobytes()
        cuenta = [bd[x * bh:(x + 1) * bh].count(255) for x in range(w)]
        cols = [c > 0 for c in cuenta]
        xs = [x for x, c in enumerate(cols) if c]
        if not xs:
            continue
        bandas.append({"y0": y0, "y1": y1, "n": sum(cuenta), "cmin": xs[0], "cmax": xs[-1],
                       "tramos": len(_tramos(cols, 1)), "h": bh})
    F = None
    avisos = []
    i = 0
    while i < len(bandas) - 1:
        A, B = bandas[i], bandas[i + 1]
        hueco = B["y0"] - A["y1"] - 1
        info = {"y": A["y0"], "l1": A["n"], "l2": B["n"], "hA": A["h"], "hB": B["h"],
                "wA": A["cmax"] - A["cmin"] + 1, "wB": B["cmax"] - B["cmin"] + 1, "hueco": hueco,
                "tA": A["tramos"], "tB": B["tramos"], "dx": B["cmin"] - A["cmin"], "cofre": 0.0}
        info["ok"] = (0 <= hueco <= 10
                      and 8 <= info["hA"] <= 34 and 6 <= info["hB"] <= 28
                      and 0.45 <= info["hB"] / float(info["hA"]) <= 1.4
                      and A["n"] >= 40 and B["n"] >= 80
                      and 30 <= info["wA"] <= 220 and 30 <= info["wB"] <= 330
                      and A["tramos"] >= 3
                      and 0.05 <= A["n"] / float(info["wA"] * A["h"]) <= 0.7
                      and 0.15 <= B["n"] / float(info["wB"] * B["h"]) <= 0.9
                      and -20 <= info["dx"] <= 60)
        if info["ok"]:
            if F is None:
                gris = img.convert("L").point(_L_CONTRASTE)
                F = ImageChops.multiply(gris, m.filter(ImageFilter.MaxFilter(7)).point(_L_BIN))
            clave = (B["y0"], B["cmin"], B["cmax"], B["n"] // 15)
            ahora = time.time()
            c = _CACHE_COFRE.get(clave)
            if c is not None and ahora - c[0] < 1.0:
                info["cofre"] = c[1]        # el mismo aviso de hace un instante: no se repite el cálculo
            else:
                info["cofre"] = puntuacion_cofre(F, B["cmin"] - 2, B["y0"], B["cmax"])
                if len(_CACHE_COFRE) > 40:
                    _CACHE_COFRE.clear()
                _CACHE_COFRE[clave] = (ahora, info["cofre"])
            avisos.append(info)
            i += 2
        else:
            if depurar:
                avisos.append(info)
            i += 1
    return avisos


# --- avisos de TRES líneas: «+750 PE» / «NIVEL DE ESPÍRITU» / «COFRE» -------------------------
_L_B150 = _lut(lambda v: v >= 150)
_L_BG22 = _lut(lambda v: v >= 22)
_L_BR3 = _lut(lambda v: v >= 3)


def _mascara_laxa(img):
    """Máscara más permisiva (vídeo comprimido, capturas con menos color)."""
    r, g, b = img.convert("RGB").split()
    mul_ = ImageChops.multiply
    return mul_(mul_(b.point(_L_B150), ImageChops.subtract(b, g).point(_L_BG22)),
                ImageChops.subtract(b, r).point(_L_BR3))


def _bandas_mascara(m):
    w, h = m.size
    datos = m.tobytes()
    filas = [datos[y * w:(y + 1) * w].count(255) for y in range(h)]
    out = []
    for y0, y1 in _tramos([n >= 3 for n in filas], 2):
        bh = y1 - y0 + 1
        bd = m.crop((0, y0, w, y1 + 1)).transpose(Image.TRANSPOSE).tobytes()
        cuenta = [bd[x * bh:(x + 1) * bh].count(255) for x in range(w)]
        xs = [x for x, c in enumerate(cuenta) if c]
        if xs:
            out.append({"y0": y0, "y1": y1, "n": sum(cuenta), "cmin": xs[0], "cmax": xs[-1],
                        "tramos": len(_tramos([c > 0 for c in cuenta], 1)), "h": bh})
    return out


def _region(datos, w, h, x0, x1, y0, y1):
    """(píxeles encendidos, ancho que ocupan) dentro de un rectángulo de la máscara."""
    x0 = max(0, x0)
    x1 = min(w - 1, x1)
    n = 0
    lo = hi = None
    for y in range(max(0, y0), min(h - 1, y1) + 1):
        fila = datos[y * w + x0:y * w + x1 + 1]
        c = fila.count(255)
        if c:
            n += c
            a = fila.find(255) + x0
            b = fila.rfind(255) + x0
            lo = a if lo is None else min(lo, a)
            hi = b if hi is None else max(hi, b)
    return n, ((hi - lo + 1) if lo is not None else 0)


def _buscar_tres_lineas(img):
    """Aviso de cofre de TRES líneas: «+750 PE» / «NIVEL DE ESPÍRITU» / «COFRE».
    Se busca la palabra corta de abajo (COFRE) con una línea ancha justo encima y la línea del
    «+N PE» más arriba."""
    m = _mascara_laxa(img)
    w, h = m.size
    datos = m.tobytes()
    F = None
    out = []
    for C in _bandas_mascara(m):
        wc = C["cmax"] - C["cmin"] + 1
        if not (26 <= wc <= 60 and 7 <= C["h"] <= 18 and C["n"] >= 0.25 * wc * C["h"]):
            continue
        xa, xb = C["cmin"] - 14, C["cmin"] + 140
        nB, spanB = _region(datos, w, h, xa, xb, C["y0"] - 17, C["y0"] - 1)
        if nB < 160 or spanB < 70:
            continue
        nA, _ = _region(datos, w, h, xa, xb, C["y0"] - 42, C["y0"] - 28)
        if nA < 60:
            continue
        if F is None:
            gris = img.convert("L").point(_L_CONTRASTE)
            F = ImageChops.multiply(gris, m.filter(ImageFilter.MaxFilter(7)).point(_L_BIN))
        s = puntuacion_cofre(F, C["cmin"] - 2, C["y0"], C["cmax"])
        if s < 0.30:
            continue
        out.append({"y": max(0, C["y0"] - 40), "yc": C["y0"], "l1": nA, "l2": nB, "cofre": max(s, UMBRAL_COFRE),
                    "tres": True, "ok": True})
    return out


def buscar_avisos(img, depurar=False):
    avisos = _buscar_avisos_dos(img, depurar)
    try:
        tres = _buscar_tres_lineas(img)
    except Exception:
        tres = []
    if tres:
        # las parejas de líneas que forman parte de un aviso de tres líneas ya no cuentan aparte
        avisos = [a for a in avisos if not any(t["yc"] - 60 <= a["y"] <= t["yc"] for t in tres)]
        avisos.extend(tres)
    return avisos


def hay_aviso_clasico(img):
    """El detector de siempre: el aviso morado de dos líneas, '+600 PE' arriba y la palabra corta
    'COFRE' debajo. Se mantiene tal cual funcionaba, como red de seguridad del detector nuevo."""
    px = img.convert("RGB").load()
    l1 = 0
    l2 = 0
    cmin = None
    cmax = None
    cols1 = [False] * 84
    for y in range(10, 29):
        for x in range(84):
            r, g, b = px[x, y]
            if b > 215 and 165 < r < 250 and 130 < g < 225 and (b - g) > 35 and (r - g) > 10:
                if y < 21:
                    l1 += 1
                    cols1[x] = True
                else:
                    l2 += 1
                    if cmin is None or x < cmin:
                        cmin = x
                    if cmax is None or x > cmax:
                        cmax = x
    ancho = (cmax - cmin + 1) if cmin is not None else 0
    # «+600 PE» son varias letras/cifras separadas; una mancha de color (pelo, ropa, fondo) no
    ok = l1 >= 35 and l2 >= 20 and 10 <= ancho <= 24 and len(_tramos(cols1, 0)) >= 3
    return ok, l1, l2, ancho


def _amarillo(r, g, b):
    return r > 215 and g > 215 and b < 90


def _pastilla(r, g, b):
    return min(r, g, b) > 185 and (max(r, g, b) - min(r, g, b)) < 35


def fraccion_color(img, pred):
    im = img.convert("RGB").resize((32, 12))
    px = im.load()
    n = 0
    for y in range(12):
        for x in range(32):
            r, g, b = px[x, y]
            if pred(r, g, b):
                n += 1
    return n / 384.0


def hay_lobby(img_boton, img_pastilla):
    """Lobby = el botón amarillo grande de JUGAR (abajo a la izquierda) Y la pastilla gris
    de «JUGAR» seleccionada en el menú de arriba. Hacen falta las dos a la vez."""
    fa = fraccion_color(img_boton, _amarillo)
    fp = fraccion_color(img_pastilla, _pastilla)
    return (fa >= 0.65 and fp >= 0.50), fa, fp


def buscar_ventana_fortnite():
    user32 = ctypes.windll.user32
    encontrada = []
    EnumProc = ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)

    def cb(hwnd, lparam):
        if user32.IsWindowVisible(hwnd):
            n = user32.GetWindowTextLengthW(hwnd)
            if n:
                buf = ctypes.create_unicode_buffer(n + 1)
                user32.GetWindowTextW(hwnd, buf, n + 1)
                if buf.value.strip() == "Fortnite":
                    encontrada.append(hwnd)
        return True

    user32.EnumWindows(EnumProc(cb), 0)
    return encontrada[0] if encontrada else None


def rect_cliente(hwnd):
    user32 = ctypes.windll.user32
    rc = wintypes.RECT()
    if not user32.GetClientRect(hwnd, ctypes.byref(rc)):
        return None
    pt = wintypes.POINT(0, 0)
    user32.ClientToScreen(hwnd, ctypes.byref(pt))
    return (pt.x, pt.y, rc.right, rc.bottom)


# ---------------------------------------------------------------- dibujo
def dibujar_cofre(c, ox=0.0, oy=0.0, k=1.0):
    """Dibuja un cofre (46x38 px a escala 1) en el canvas c."""
    def X(v):
        return ox + v * k

    def Y(v):
        return oy + v * k

    lw = max(1, int(round(2 * k)))
    c.create_rectangle(X(4), Y(18), X(42), Y(35), fill="#8a4b1f", outline="#2e1606", width=lw)
    c.create_arc(X(4), Y(4), X(42), Y(32), start=0, extent=180, fill="#b3652b", outline="#2e1606",
                 width=lw, style="pieslice")
    c.create_rectangle(X(4), Y(17), X(42), Y(22), fill=ORO, outline="#2e1606")
    c.create_rectangle(X(10), Y(8), X(14), Y(35), fill=ORO, outline="#2e1606")
    c.create_rectangle(X(32), Y(8), X(36), Y(35), fill=ORO, outline="#2e1606")
    c.create_rectangle(X(19), Y(15), X(27), Y(26), fill="#ffe27a", outline="#2e1606", width=lw)
    c.create_oval(X(21), Y(18), X(25), Y(22), fill="#2e1606", outline="")


def texto_contorno(c, x, y, txt, fuente, color, tam):
    """Texto con borde oscuro para que se lea sobre cualquier fondo del juego."""
    o = 1 if tam < 24 else max(2, tam // 18)
    for dx, dy in ((-o, 0), (o, 0), (0, -o), (0, o), (-o, -o), (o, o), (-o, o), (o, -o)):
        c.create_text(x + dx, y + dy, text=txt, font=fuente, fill=CONTORNO, anchor="w")
    c.create_text(x, y, text=txt, font=fuente, fill=color, anchor="w")


# ---------------------------------------------------------------- conexión online
class ErrorHTTP(Exception):
    def __init__(self, codigo):
        super().__init__("HTTP %d" % codigo)
        self.codigo = codigo


class Sincronizador(threading.Thread):
    """Habla con una base de datos Firebase (solo internet, sin instalar nada) en segundo plano.

    Estructura en la base de datos:
      salas/<sala>/j/<id>      → los números de cada jugador
      salas/<sala>/meta        → {lider: id, expulsados: {id: true}}

    Usa UNA conexión que se mantiene abierta y solo enseña un error si fallan varias
    consultas seguidas, no por un fallo suelto."""

    PERIODO = 0.6              # segundos entre consultas
    LATIDO = 5.0               # cada cuánto se avisa de que sigues conectado
    ONLINE_MS = 20000          # si su último latido es más viejo que esto, se le ve desconectado
    LIDER_AUSENTE_MS = 90000   # líder desconectado más de esto → otro miembro asume el mando
    FALLOS_PARA_ERROR = 3

    def __init__(self):
        super().__init__(daemon=True)
        self.lock = threading.Lock()
        self.evento = threading.Event()
        self.url = ""
        self.sala = ""
        self.pid = ""
        self.activo = False
        self.mios = {"nombre": "", "total": 0, "partida": 0}
        self.version = 0
        self.enviada = -1
        self.ultimo_envio = 0.0
        self.amigos = []
        self.ocultos = []        # entradas antiguas repetidas (fantasmas) que no se enseñan
        self.lider = ""
        self.expulsados = set()
        self.expulsado = False
        self.nivel = "off"       # off / trabajando / ok / error
        self.texto = ""
        self.fallos = 0
        self.cola = []
        self.fin = False
        self._conn = None
        self._conn_clave = None
        self._recrear = False
        self._promo_hasta = 0.0

    # --- llamadas desde la ventana ---
    def configurar(self, url, sala, pid, activo):
        activo = bool(activo and url and sala and pid)
        with self.lock:
            if (url, sala, pid, activo) != (self.url, self.sala, self.pid, self.activo):
                self.url, self.sala, self.pid, self.activo = url, sala, pid, activo
                self.amigos = []
                self.ocultos = []
                self.lider = ""
                self.expulsados = set()
                self.expulsado = False
                self.cola = []
                self.enviada = -1
                self.fallos = 0
                self.version += 1
                self.nivel = "trabajando" if activo else "off"
                self.texto = ""
                self._recrear = True
        self.evento.set()

    def publicar(self, nombre, total, partida):
        nuevo = {"nombre": nombre, "total": total, "partida": partida}
        with self.lock:
            if nuevo == self.mios:
                return
            self.mios = nuevo
            self.version += 1
        self.evento.set()

    def estado(self):
        with self.lock:
            return {"nivel": self.nivel, "texto": self.texto, "activo": self.activo,
                    "amigos": [dict(a) for a in self.amigos], "lider": self.lider,
                    "soy_lider": bool(self.activo and self.lider and self.lider == self.pid),
                    "expulsado": self.expulsado, "n_exp": len(self.expulsados)}

    def parar(self):
        self.fin = True
        self.evento.set()

    # --- gestión de la sala (solo el líder) ---
    def _encolar(self, metodo, ruta, cuerpo=None):
        with self.lock:
            if not self.activo:
                return False
            if len(self.cola) < 200:
                self.cola.append((metodo, ruta, cuerpo))
        self.evento.set()
        return True

    def expulsar(self, pid_amigo):
        with self.lock:
            sala = self.sala
            self.amigos = [a for a in self.amigos if a["pid"] != pid_amigo]
            self.expulsados.add(pid_amigo)
        self._encolar("PUT", "/salas/%s/meta/expulsados/%s" % (sala, pid_amigo), True)
        self._encolar("DELETE", "/salas/%s/j/%s" % (sala, pid_amigo))

    def hacer_lider(self, pid_amigo):
        with self.lock:
            sala = self.sala
            self.lider = pid_amigo
        self._encolar("PUT", "/salas/%s/meta/lider" % sala, pid_amigo)

    def perdonar_expulsados(self):
        with self.lock:
            sala = self.sala
            self.expulsados = set()
        self._encolar("DELETE", "/salas/%s/meta/expulsados" % sala)

    def limpiar_desconectados(self):
        """Borra de la sala a los que están desconectados y a las entradas antiguas repetidas."""
        with self.lock:
            sala = self.sala
            fuera = [a["pid"] for a in self.amigos if not a["online"]] + list(self.ocultos)
            self.amigos = [a for a in self.amigos if a["online"]]
            self.ocultos = []
        for p in fuera:
            self._encolar("DELETE", "/salas/%s/j/%s" % (sala, p))
        return len(fuera)

    @staticmethod
    def borrar_entrada(url, sala, pid):
        """Quita tu entrada de una sala (para «salir de la sala» o al cambiar de sala). Usa su
        propia conexión y va en segundo plano; si falla no pasa nada: la entrada se ve
        «desconectada» y el líder puede limpiarla."""
        def tarea():
            try:
                p = urllib.parse.urlsplit(url)
                clase = http.client.HTTPSConnection if p.scheme == "https" else http.client.HTTPConnection
                c = clase(p.netloc, timeout=8)
                c.request("DELETE", "%s/salas/%s/j/%s.json" % (p.path.rstrip("/"), sala, pid))
                c.getresponse().read()
                c.close()
            except Exception:
                pass

        threading.Thread(target=tarea, daemon=True).start()

    # --- hilo ---
    def run(self):
        while not self.fin:
            with self.lock:
                activo = self.activo
                url, sala, pid = self.url, self.sala, self.pid
                mios = dict(self.mios)
                version = self.version
                enviar = version != self.enviada or time.time() - self.ultimo_envio > self.LATIDO
                if self._recrear:
                    self._recrear = False
                    self._cerrar_conn()
            if activo:
                try:
                    self._ciclo(url, sala, pid, mios, version, enviar)
                    with self.lock:
                        self.fallos = 0
                except Exception as e:
                    self._cerrar_conn()
                    with self.lock:
                        self.fallos += 1
                        # un fallo suelto no se enseña: solo si fallan varios seguidos
                        if self.fallos >= self.FALLOS_PARA_ERROR:
                            self.nivel = "error"
                            self.texto = self._explicar(e)
            else:
                self._cerrar_conn()
                with self.lock:
                    self.nivel = "off"
                    self.amigos = []
                    self.lider = ""
            self.evento.wait(self.PERIODO)
            self.evento.clear()

    def _vaciar_cola(self, url):
        """Órdenes pendientes (expulsar, borrar...). Si la red falla se reintentan; si el servidor
        las rechaza se descartan, para que una orden mala nunca bloquee la sincronización."""
        while True:
            with self.lock:
                cmd = self.cola[0] if self.cola else None
            if cmd is None:
                return
            metodo, ruta, cuerpo = cmd
            try:
                self._http(metodo, url + ruta + ".json", cuerpo)
            except ErrorHTTP:
                pass                      # rechazada: se descarta
            with self.lock:
                if self.cola and self.cola[0] == cmd:
                    self.cola.pop(0)

    def _ciclo(self, url, sala, pid, mios, version, enviar):
        base = "%s/salas/%s" % (url, sala)
        self._vaciar_cola(url)
        with self.lock:
            expulsado = self.expulsado
        if enviar and not expulsado:
            cuerpo = dict(mios)
            cuerpo["t"] = {".sv": "timestamp"}   # hora del servidor de Firebase
            self._http("PUT", "%s/j/%s.json" % (base, pid), cuerpo)
            with self.lock:
                self.enviada = version
                self.ultimo_envio = time.time()
        _, datos = self._http("GET", base + ".json")
        self._procesar(datos, base, pid)

    # --- red ---
    def _cerrar_conn(self):
        c, self._conn = self._conn, None
        self._conn_clave = None
        if c is not None:
            try:
                c.close()
            except Exception:
                pass

    def _conexion(self, p):
        clave = (p.scheme, p.netloc)
        if self._conn is None or self._conn_clave != clave:
            self._cerrar_conn()
            clase = http.client.HTTPSConnection if p.scheme == "https" else http.client.HTTPConnection
            self._conn = clase(p.netloc, timeout=8)
            self._conn_clave = clave
        return self._conn

    def _http(self, metodo, url, cuerpo=None, cab_extra=None):
        p = urllib.parse.urlsplit(url)
        ruta = p.path + ("?" + p.query if p.query else "")
        datos = None
        cab = {}
        if cuerpo is not None:
            datos = json.dumps(cuerpo).encode("utf-8")
            cab["Content-Type"] = "application/json"
        if cab_extra:
            cab.update(cab_extra)
        for intento in (0, 1):
            try:
                c = self._conexion(p)
                c.request(metodo, ruta, body=datos, headers=cab)
                r = c.getresponse()
                txt = r.read().decode("utf-8")
                break
            except (http.client.HTTPException, OSError):
                self._cerrar_conn()       # la conexión abierta pudo caducar: se reintenta una vez
                if intento:
                    raise
        if r.status >= 400:
            raise ErrorHTTP(r.status)
        return r.status, (json.loads(txt) if txt else None)

    # --- interpretar lo que llega ---
    def _procesar(self, datos, base, pid):
        datos = datos if isinstance(datos, dict) else {}
        j = datos.get("j") if isinstance(datos.get("j"), dict) else {}
        meta = datos.get("meta") if isinstance(datos.get("meta"), dict) else {}
        exp = meta.get("expulsados") if isinstance(meta.get("expulsados"), dict) else {}
        lider = str(meta.get("lider") or "")
        expulsado = pid in exp
        with self.lock:
            mi_nombre = (self.mios.get("nombre") or "").strip().lower()

        def marca(v):
            t = v.get("t") if isinstance(v, dict) else None
            return t if isinstance(t, (int, float)) else 0

        mi_t = marca(j.get(pid)) if pid in j else None
        todos_t = [marca(v) for k, v in j.items() if isinstance(v, dict) and k not in exp]
        ref = mi_t if mi_t else (max(todos_t) if todos_t else 0)

        candidatos = []
        for k, v in j.items():
            if k == pid or k in exp or not isinstance(v, dict):
                continue
            t = marca(v)
            candidatos.append({"pid": k, "nombre": str(v.get("nombre") or "")[:20],
                               "total": entero(v.get("total")), "partida": entero(v.get("partida")),
                               "online": (ref - t) < self.ONLINE_MS, "t": t})

        # Entradas "fantasma": si alguien reinstala o borra sus datos, aparece con otro id.
        # Se ocultan las desconectadas que repiten el nombre de otra más reciente (o el tuyo).
        por_nombre = {}
        for a in candidatos:
            por_nombre.setdefault(a["nombre"].strip().lower(), []).append(a)
        amigos, ocultos = [], []
        for nombre, grupo in por_nombre.items():
            grupo.sort(key=lambda a: a["t"], reverse=True)
            for i, a in enumerate(grupo):
                fantasma = (not a["online"]) and (i > 0 or (nombre != "" and nombre == mi_nombre))
                (ocultos if fantasma else amigos).append(a["pid"] if fantasma else a)
        amigos.sort(key=lambda a: (a["nombre"].lower(), a["pid"]))

        if not expulsado:
            if not lider:
                # nadie manda todavía: el primero que llega se queda con la sala
                try:
                    try:
                        self._http("PUT", base + "/meta/lider.json", pid, {"if-match": "null_etag"})
                    except ErrorHTTP as e:
                        if e.codigo == 412:
                            raise
                        self._http("PUT", base + "/meta/lider.json", pid)   # sin condición
                    lider = pid
                except ErrorHTTP as e:
                    if e.codigo != 412:
                        raise
            elif lider != pid and mi_t:
                lt = marca(j.get(lider)) if lider in j else None
                ausente = lt is None or (ref - lt) > self.LIDER_AUSENTE_MS
                if ausente and time.time() > self._promo_hasta:
                    candidatos_l = sorted([pid] + [a["pid"] for a in amigos if a["online"]])
                    if candidatos_l[0] == pid:        # el de menor id entre los conectados
                        self._promo_hasta = time.time() + 15
                        self._http("PUT", base + "/meta/lider.json", pid)
                        lider = pid

        with self.lock:
            self.amigos = amigos
            self.ocultos = ocultos
            self.lider = lider
            self.expulsados = set(exp)
            self.expulsado = expulsado
            self.nivel = "ok"
            self.texto = ""

    @staticmethod
    def _explicar(e):
        if isinstance(e, ErrorHTTP):
            if e.codigo in (401, 403):
                return "Sin permiso: revisa las reglas de la base de datos."
            if e.codigo == 404:
                return "No encuentro esa base de datos: revisa la dirección."
            return "Error del servidor (%d). Reintentando..." % e.codigo
        if isinstance(e, TimeoutError):
            return "La conexión va muy lenta. Reintentando..."
        if isinstance(e, OSError):
            return "Sin conexión con el servidor. Reintentando..."
        return "Error: %s" % e


# ---------------------------------------------------------------- número flotante
class Overlay:
    """Número flotante sin marco de ventana, siempre encima del juego."""

    def __init__(self, app, cfg):
        self.app = app
        self.win = tk.Toplevel(app.root)
        w = self.win
        w.overrideredirect(True)
        w.attributes("-topmost", True)
        w.configure(bg=TRANSPARENTE)
        try:
            w.attributes("-transparentcolor", TRANSPARENTE)
        except tk.TclError:
            pass
        self.canvas = tk.Canvas(w, bg=TRANSPARENTE, highlightthickness=0, bd=0)
        self.canvas.pack()
        x = cfg.get("x", 60)
        y = cfg.get("y", 60)
        w.geometry("+%d+%d" % (x, y))
        self._dx = 0
        self._dy = 0
        self.canvas.bind("<ButtonPress-1>", self._ini)
        self.canvas.bind("<B1-Motion>", self._mov)
        self.canvas.bind("<ButtonRelease-1>", self._fin)
        self.dibujar()
        w.update_idletasks()
        self.aplicar_estilo()
        self.mantener()

    # --- arrastre (solo en modo mover) ---
    def _ini(self, e):
        if self.app.var_mover.get():
            self._dx = e.x_root - self.win.winfo_x()
            self._dy = e.y_root - self.win.winfo_y()

    def _mov(self, e):
        if self.app.var_mover.get():
            self.win.geometry("+%d+%d" % (e.x_root - self._dx, e.y_root - self._dy))

    def _fin(self, e):
        if self.app.var_mover.get():
            self.app.guardar()

    # --- ventana ---
    def aplicar_estilo(self):
        """Sin icono en la barra de tareas, sin robar el foco al juego y, si está bloqueado,
        los clics lo atraviesan para no molestar mientras juegas."""
        try:
            user32 = ctypes.windll.user32
            hwnd = user32.GetParent(self.win.winfo_id()) or self.win.winfo_id()
            estilo = user32.GetWindowLongW(hwnd, -20)
            estilo |= 0x00080000 | 0x00000080 | 0x08000000
            if self.app.var_mover.get():
                estilo &= ~0x00000020
            else:
                estilo |= 0x00000020
            user32.SetWindowLongW(hwnd, -20, estilo)
        except Exception:
            pass

    def mantener(self):
        try:
            if self.win.winfo_viewable():
                self.win.attributes("-topmost", True)
                self.win.lift()
            self.win.after(1500, self.mantener)
        except tk.TclError:
            pass

    def mostrar(self):
        self.win.deiconify()
        self.win.update_idletasks()
        self.dibujar()
        self.aplicar_estilo()

    def ocultar(self):
        self.win.withdraw()

    # --- dibujo ---
    def dibujar(self, color=None):
        c = self.canvas
        app = self.app
        c.delete("all")
        s = TAMANOS.get(app.var_tam.get(), 54)
        texto = str(app.total)
        fuente = tkfont.Font(family="Segoe UI Black", size=-s)
        tw = fuente.measure(texto)
        th = fuente.metrics("linespace")
        pad = max(6, s // 6)
        iw = int(s * 1.05) if app.var_icono.get() else 0
        gap = pad if iw else 0
        w1 = pad + iw + gap + tw + pad
        h1 = th + pad

        # número de la partida, al lado del total
        ver_partida = bool(app.var_partida.get())
        if ver_partida:
            s2 = max(14, int(s * 0.62))
            texto2 = str(app.sesion)
            fuente2 = tkfont.Font(family="Segoe UI Black", size=-s2)
            tw2 = fuente2.measure(texto2)
            gap2 = pad
            w1 += gap2 + tw2

        # cartel de celebración (arriba)
        ban = app.banner_actual()
        hb = 0
        wb = 0
        if ban:
            sb = max(16, int(s * 0.5))
            fuente_b = tkfont.Font(family="Segoe UI Black", size=-sb)
            wb = pad + fuente_b.measure(ban[0]) + pad
            hb = fuente_b.metrics("linespace") + pad // 2

        # barra de la meta
        meta = app.meta_info() if app.var_meta.get() else None
        hm = 0
        wm = 0
        hbar = 0
        if meta:
            hbar = max(16, int(s * 0.4))
            hm = hbar + pad
            wm = max(int(s * 4.6), 150)

        # filas con los números de los amigos (una por amigo) y el total del grupo
        filas = []
        amigos = app.amigos_overlay()
        if app.var_amigo.get():
            for am in amigos:
                t = [(am["nombre"], CIAN if am["online"] else APAGADO), (str(am["total"]), ORO)]
                if ver_partida:
                    t.append((str(am["partida"]), COLOR_PARTIDA))
                filas.append(t)
        if app.var_grupo.get() and amigos:
            filas.append([("GRUPO", VERDE), (str(app.total_grupo()), COLOR_PARTIDA)])
        w3 = 0
        h3 = 0
        lh = 0
        if filas:
            s3 = max(14, int(s * 0.5))
            fuente3 = tkfont.Font(family="Segoe UI Black", size=-s3)
            gap3 = max(8, s3 // 2)
            ancho3 = max(sum(fuente3.measure(t) for t, _ in f) + gap3 * (len(f) - 1) for f in filas)
            lh = fuente3.metrics("linespace") + pad // 2
            h3 = lh * len(filas)
            w3 = pad + ancho3 + pad

        w = max(w1, wb, wm, w3)
        h = hb + h1 + hm + h3
        y_fila1 = hb
        y_meta = hb + h1
        y_amigo = hb + h1 + hm

        c.config(width=w, height=h)
        if app.var_mover.get():
            c.create_rectangle(2, 2, w - 2, h - 2, fill=CARD, outline=ORO, width=2, dash=(4, 3))
        if ban:
            texto_contorno(c, pad, hb / 2.0, ban[0], fuente_b, ban[1], sb)
        if iw:
            k = iw / 46.0
            dibujar_cofre(c, pad, y_fila1 + (h1 - 38 * k) / 2.0, k)
        tx = pad + iw + gap
        ty = y_fila1 + h1 / 2.0
        texto_contorno(c, tx, ty, texto, fuente, color or ORO, s)
        if ver_partida:
            texto_contorno(c, tx + tw + gap2, ty, texto2, fuente2, COLOR_PARTIDA, s2)
        if meta:
            x0, x1 = pad, w - pad
            y0, y1 = y_meta, y_meta + hbar
            c.create_rectangle(x0, y0, x1, y1, fill="#2a2342", outline=CONTORNO, width=2)
            pct = min(1.0, meta["total"] / float(meta["valor"]))
            if pct > 0:
                c.create_rectangle(x0 + 1, y0 + 1, x0 + 1 + (x1 - x0 - 2) * pct, y1 - 1,
                                   fill=VERDE if meta["hecho"] else ORO, outline="")
            tam_m = max(10, hbar - 6)
            fuente_m = tkfont.Font(family="Segoe UI Black", size=-tam_m)
            txt_m = "%d / %d" % (meta["total"], meta["valor"])
            texto_contorno(c, (x0 + x1) / 2.0 - fuente_m.measure(txt_m) / 2.0, (y0 + y1) / 2.0,
                           txt_m, fuente_m, "#ffffff", tam_m)
        for i, fila in enumerate(filas):
            x3 = pad
            y3 = y_amigo + lh * i + lh / 2.0 - pad // 4
            for t, col in fila:
                texto_contorno(c, x3, y3, t, fuente3, col, s3)
                x3 += fuente3.measure(t) + gap3

    def destello(self, ciclos=1):
        colores = (["#ffffff", "#fff3b0", "#ffe27a", "#ffd24d"] * ciclos) + [None]

        def paso(i):
            try:
                self.dibujar(colores[i])
                if i < len(colores) - 1:
                    self.win.after(90, lambda: paso(i + 1))
            except tk.TclError:
                pass

        paso(0)


# ---------------------------------------------------------------- ventana de estadísticas
def grafico_barras(c, barras, color, color_ult, etiqueta_media, ancho=520, alto=175):
    """barras = [(valor, texto_linea1, texto_linea2), ...]. Dibujado a mano, sin librerías."""
    c.delete("all")
    n = len(barras)
    mx = max((b[0] for b in barras), default=0)
    if n == 0 or mx == 0:
        c.create_text(ancho / 2.0, alto / 2.0, text="Todavía no hay datos: juega una partida.",
                      font=("Segoe UI", 10), fill=APAGADO)
        return
    top, bot, izq, der = 26, 36, 8, 8
    area = alto - top - bot
    base = alto - bot
    paso = (ancho - izq - der) / float(n)
    bw = paso * 0.62
    c.create_line(izq, base, ancho - der, base, fill=APAGADO)
    media = sum(b[0] for b in barras) / float(n)
    ym = base - area * media / mx
    c.create_line(izq, ym, ancho - der, ym, fill=CIAN, dash=(4, 3))
    c.create_text(izq + 2, 10, text="%s %s" % (etiqueta_media, f1(media)), anchor="w",
                  font=("Segoe UI", 8), fill=CIAN)
    for i, (v, l1, l2) in enumerate(barras):
        x0 = izq + i * paso + (paso - bw) / 2.0
        ultimo = (i == n - 1)
        if v > 0:
            h = area * v / float(mx)
            c.create_rectangle(x0, base - h, x0 + bw, base, fill=color_ult if ultimo else color,
                               outline=CONTORNO)
            c.create_text(x0 + bw / 2.0, base - h - 8, text=str(v), font=("Segoe UI Semibold", 8),
                          fill=TEXTO)
        col = ORO if ultimo else APAGADO
        c.create_text(x0 + bw / 2.0, base + 9, text=l1, font=("Segoe UI", 8), fill=col)
        c.create_text(x0 + bw / 2.0, base + 22, text=l2, font=("Segoe UI", 8), fill=col)


class Estadisticas:
    def __init__(self, app):
        self.app = app
        self.sig = None
        self.v = {}
        w = self.win = tk.Toplevel(app.root)
        w.title("Estadísticas de cofres")
        w.configure(bg=BG)
        w.attributes("-topmost", True)
        w.resizable(False, False)
        w.protocol("WM_DELETE_WINDOW", self.cerrar)
        try:
            w.geometry("+%d+%d" % (app.root.winfo_rootx() + app.root.winfo_width() + 12,
                                   app.root.winfo_rooty()))
        except tk.TclError:
            pass

        marco = tk.Frame(w, bg=CARD, highlightbackground=ORO, highlightthickness=2)
        marco.pack(padx=8, pady=8)
        cab = tk.Frame(marco, bg=CARD)
        cab.pack(fill="x", padx=12, pady=(10, 0))
        tk.Label(cab, text="ESTADÍSTICAS", font=("Segoe UI Semibold", 13), fg=ORO, bg=CARD).pack(side="left")
        tk.Label(cab, text="Cada día va de 00:00 a 00:00 (hora de España)", font=("Segoe UI", 9),
                 fg=CIAN, bg=CARD).pack(side="right")
        tk.Label(marco, text="Solo cuenta lo que el programa ha contado desde que lo usas: "
                             "el total que escribes a mano no entra aquí.",
                 font=("Segoe UI", 8), fg=APAGADO, bg=CARD, anchor="w").pack(fill="x", padx=12)

        cuerpo = tk.Frame(marco, bg=CARD)
        cuerpo.pack(padx=10, pady=8)
        izq = tk.Frame(cuerpo, bg=CARD)
        izq.pack(side="left", anchor="n")
        der = tk.Frame(cuerpo, bg=CARD)
        der.pack(side="left", anchor="n", padx=(10, 0))

        self.tarjetas(izq, "HOY", (("hoy", "COFRES", ORO), ("partidas_hoy", "PARTIDAS", COLOR_PARTIDA),
                                    ("media_hoy", "MEDIA/PARTIDA", CIAN)))
        self.tarjetas(izq, "RÉCORDS", (("mejor_partida", "MEJOR PARTIDA", VERDE), ("mejor_dia", "MEJOR DÍA", VERDE),
                                       ("racha", "RACHA (días)", ORO), ("media_total", "MEDIA TOTAL", CIAN)))
        caja = self.tarjetas(izq, "ESTA SEMANA", (("sem", "ESTA SEMANA", ORO), ("sem_ant", "SEM. ANTERIOR", TEXTO),
                                                  ("sem_pct", "CAMBIO", VERDE)))
        tk.Label(caja, text="Se comparan los mismos días: de lunes a hoy, frente a esos días de la semana pasada.",
                 font=("Segoe UI", 8), fg=APAGADO, bg=PANEL, wraplength=330, justify="left",
                 anchor="w").pack(fill="x", padx=10, pady=(0, 6))
        caja = tk.Frame(izq, bg=PANEL)
        caja.pack(fill="x", pady=(0, 8))
        tk.Label(caja, text="OTROS DATOS", font=("Segoe UI Semibold", 9), fg=ORO_OSC, bg=PANEL).pack(
            anchor="w", padx=10, pady=(6, 2))
        for clave in ("gap", "cph", "hora", "autos", "racha_max"):
            lbl = tk.Label(caja, text="", font=("Segoe UI", 9), fg=TEXTO, bg=PANEL, anchor="w", justify="left")
            lbl.pack(fill="x", padx=10)
            self.v[clave] = lbl
        tk.Frame(caja, bg=PANEL, height=6).pack()

        self.cv_dias = self.grafica(der, "COFRES POR DÍA · últimos 14 días")
        self.cv_part = self.grafica(der, "COFRES POR PARTIDA · últimas 20 partidas")

        pie = tk.Frame(marco, bg=CARD)
        pie.pack(pady=(0, 10))
        app.boton(pie, "Exportar a CSV", self.exportar, MORADO, 16).pack(side="left", padx=4)
        app.boton(pie, "🗑 Restablecer", self.restablecer, "#c0394b", 14).pack(side="left", padx=4)
        app.boton(pie, "Cerrar", self.cerrar, "#4a4468", 10).pack(side="left", padx=4)
        w.bind("<Escape>", lambda ev: self.cerrar())
        self.refrescar(True)

    def tarjetas(self, padre, titulo, items):
        caja = tk.Frame(padre, bg=PANEL)
        caja.pack(fill="x", pady=(0, 8))
        tk.Label(caja, text=titulo, font=("Segoe UI Semibold", 9), fg=ORO_OSC, bg=PANEL).pack(
            anchor="w", padx=10, pady=(6, 0))
        fila = tk.Frame(caja, bg=PANEL)
        fila.pack(fill="x", padx=6, pady=(0, 6))
        for clave, nombre, color in items:
            col = tk.Frame(fila, bg=PANEL)
            col.pack(side="left", expand=True, fill="x", padx=5)
            tk.Label(col, text=nombre, font=("Segoe UI", 8), fg=APAGADO, bg=PANEL).pack()
            lbl = tk.Label(col, text="–", font=("Segoe UI Black", 20), fg=color, bg=PANEL)
            lbl.pack()
            self.v[clave] = lbl
        return caja

    def grafica(self, padre, titulo):
        caja = tk.Frame(padre, bg=PANEL)
        caja.pack(fill="x", pady=(0, 8))
        tk.Label(caja, text=titulo, font=("Segoe UI Semibold", 9), fg=ORO_OSC, bg=PANEL).pack(
            anchor="w", padx=10, pady=(6, 0))
        cv = tk.Canvas(caja, width=520, height=175, bg=PANEL, highlightthickness=0)
        cv.pack(padx=6, pady=(0, 6))
        return cv

    def vivo(self):
        try:
            return bool(self.win.winfo_exists())
        except tk.TclError:
            return False

    def cerrar(self):
        try:
            self.win.destroy()
        except tk.TclError:
            pass

    def refrescar(self, forzar=False):
        if not self.vivo():
            return
        st = self.app.estadisticas()
        sig = (self.app.hist.version, st["hoy_fecha"])
        if sig == self.sig and not forzar:
            return
        self.sig = sig
        v = self.v
        v["hoy"].config(text=str(st["hoy"]))
        v["partidas_hoy"].config(text=str(st["partidas_hoy"]))
        v["media_hoy"].config(text=f1(st["media_hoy"]) if st["media_hoy"] is not None else "–")
        v["mejor_partida"].config(text=str(st["mejor_partida"]))
        v["mejor_dia"].config(text=str(st["mejor_dia"]))
        v["racha"].config(text=str(st["racha"]))
        v["media_total"].config(text=f1(st["media_total"]) if st["media_total"] is not None else "–")
        v["sem"].config(text=str(st["semana"]))
        v["sem_ant"].config(text=str(st["semana_ant"]))
        p = st["semana_pct"]
        if p is None:
            v["sem_pct"].config(text="–", fg=APAGADO)
        else:
            txt = ("%+.0f %%" % p).replace("-", "−")
            v["sem_pct"].config(text=txt, fg=VERDE if p >= 0 else ROJO)
        v["gap"].config(text="Tiempo medio entre cofres:  %s" % (duracion(st["gap"]) if st["gap"] else "–"))
        v["autos"].config(text="Contados solos: %d   ·   Sumados a mano: %d" % (st["autos"], st["manuales"]))
        v["racha_max"].config(text="Mejor racha de días seguidos jugando:  %d" % st["mejor_racha"])
        v["cph"].config(text="Ritmo medio:  %s cofres/hora" % (f1(st["cph"]) if st["cph"] else "–"))
        mh = st["mejor_hora"]
        v["hora"].config(text="Tu mejor hora:  %s  (%d cofres)" % (("%02d:00 - %02d:00" % (mh, (mh + 1) % 24)), st["mejor_hora_n"])
                         if mh is not None else "Tu mejor hora:  –")

        dias = [(n, "LMXJVSD"[d.weekday()], str(d.day)) for d, n in st["dias14"]]
        grafico_barras(self.cv_dias, dias, ORO_OSC, ORO, "media/día")
        parts = [(n, "%02d" % dt.day, "%02dh" % dt.hour) for n, dt in st["ultimas"]]
        grafico_barras(self.cv_part, parts, MORADO, COLOR_PARTIDA, "media/partida")

    def restablecer(self):
        if not messagebox.askyesno(
                "Restablecer estadísticas",
                "Se borrará TODO el historial: partidas, cofres por día, rachas y récords.\n\n"
                "Tu TOTAL de cofres y el número de la partida actual NO cambian.\n\n¿Seguro?",
                parent=self.win, icon="warning"):
            return
        self.app.hist.borrar_todo()
        self.app._st = None
        self.app._res_clave = None
        self.app.pintar_resumen()
        self.refrescar(True)

    def exportar(self):
        ruta = filedialog.asksaveasfilename(parent=self.win, title="Guardar CSV", defaultextension=".csv",
                                            initialdir=os.path.expanduser("~"), initialfile="cofres_partidas.csv",
                                            filetypes=[("CSV (Excel)", "*.csv")])
        if not ruta:
            return
        base, ext = os.path.splitext(ruta)
        ruta_dias = base + "_dias" + (ext or ".csv")
        try:
            self.app.hist.exportar(ruta, ruta_dias)
        except OSError as e:
            messagebox.showerror("Exportar", "No se pudo guardar: %s" % e, parent=self.win)
            return
        messagebox.showinfo("Exportar", "Guardados dos archivos:\n\n%s\n(una fila por partida)\n\n%s\n(una fila por día)"
                            % (ruta, ruta_dias), parent=self.win)


# ---------------------------------------------------------------- aplicación
class App:
    def __init__(self, root):
        self.root = root
        root.title("Contador de cofres  v%s" % VERSION)
        root.configure(bg=BG)
        root.attributes("-topmost", True)
        root.resizable(False, False)

        threading.Thread(target=asegurar_sonidos, daemon=True).start()
        copia_diaria()

        datos = self.cargar()
        self.total = entero(datos.get("total", 0))
        self.sesion = entero(datos.get("partida", 0))
        self.cfg_ov = dict(datos.get("overlay", {})) if isinstance(datos.get("overlay"), dict) else {}
        self.cfg_on = dict(datos.get("online", {})) if isinstance(datos.get("online"), dict) else {}
        self.cfg_meta = dict(datos.get("meta", {})) if isinstance(datos.get("meta"), dict) else {}
        self.cfg_meta["valor"] = entero(self.cfg_meta.get("valor", 0))
        self.cfg_ui = dict(datos.get("ui", {})) if isinstance(datos.get("ui"), dict) else {}
        self.cfg_son = dict(datos.get("sonido", {})) if isinstance(datos.get("sonido"), dict) else {}
        if self.cfg_son.get("elegido") not in OPCIONES_SONIDO:
            self.cfg_son["elegido"] = "Moneda"
        # el sonido propio se guarda como nombre de archivo dentro de la carpeta de datos
        personal = str(self.cfg_son.get("personal") or "")
        self.cfg_son["personal"] = os.path.basename(personal.replace("\\", "/"))
        self.ini_lobby = bool(datos.get("lobby", True))
        self.ini_celebrar = bool(datos.get("celebrar", True))
        self.ini_pitido = bool(datos.get("pitido", True))
        self.ini_pantalla = str(datos.get("pantalla", "Auto"))
        self.ini_solo = bool(datos.get("solo_cofre", True))
        self.cfg_teclas = dict(TECLAS_DEF)
        guardadas = datos.get("teclas")
        if isinstance(guardadas, dict):
            for accion, nombre in guardadas.items():
                if accion in TECLAS_DEF and isinstance(nombre, str) and \
                        (nombre == "Ninguna" or parsear_combo(nombre)):
                    self.cfg_teclas[accion] = nombre
        if not self.cfg_on.get("id"):
            self.cfg_on["id"] = uuid.uuid4().hex[:12]
        if not self.cfg_on.get("nombre"):
            self.cfg_on["nombre"] = nombre_por_defecto()
        if not isinstance(self.cfg_on.get("alias"), dict):
            self.cfg_on["alias"] = {}

        self.hist = Historial(ARCHIVO_HIST)
        self._st = None
        self._st_clave = None
        self._res_clave = None

        # estado del detector de avisos
        self.avisos_conf = 0      # cuántos avisos de cofre damos por "ya contados" ahora mismo
        self.cand_n = 0
        self.sube = 0
        self.baja = 0
        self.ultimo_aviso = None
        self.activo = False
        self.seguidos = 0
        self.perdidos = 0
        self.hwnd = None
        self.ultima_busqueda = 0.0
        self.ultima_img = None
        self.ultima_rect = None
        self.dlg = None
        self.dlg_teclas = None
        self.dlg_gestion = None
        self.fr_gestion = None
        self.btn_perdonar = None
        self._gest_clave = None
        self.stats = None
        self.overlay = None
        self.teclas_antes = {}
        self.atajos = {}
        self.capturando = None
        self.vk_espera = 0
        self.btn_tecla = {}
        self.amigo_render = None
        self._gest_visible = False
        self.banner = None
        self.meta_flash = False
        self.tick_n = 0
        self.lobby_si = 0
        self.lobby_no = 0
        self.en_lobby = False
        self.lobby_info = (0.0, 0.0)
        self.t_inicio = time.time()
        self.t_otros = 0.0
        self.aviso_txt = ""
        self.aviso_hasta = 0.0
        self.ult_guardado = time.time()
        self.cfg_sucio = False
        self.error_guardado = False
        self._salir_visible = False
        self.pestana = "amigos"
        self.sct = MSS()
        self.upd_info = None
        self.upd_buscando = False
        self.upd_descargando = False
        self.upd_manual = False
        self.upd_ultima = time.time()
        self.upd_dlg = None
        self.upd_resultado = None
        self.upd_pospuesta = ""
        self._ritmo_txt = None
        self.nov_resultado = None
        self.compacto = False

        if datos.get("geometria"):
            try:
                root.geometry(datos["geometria"])
            except tk.TclError:
                pass

        self.sync = Sincronizador()
        self.aplicar_conexion()
        self.sync.start()

        self.construir()
        self.recalcular_atajos()
        if self.var_ov.get():
            self.overlay = Overlay(self, self.cfg_ov)
        root.protocol("WM_DELETE_WINDOW", self.cerrar)
        self.guardar()          # deja los archivos creados desde el primer momento
        self.tick()
        self.revisar_teclas()
        self.ciclo_amigo()
        self.root.after(1500, lambda: self.buscar_actualizaciones(False))
        self.root.after(3000, self.pedir_novedades)

    # ---------- piezas de interfaz ----------
    def boton(self, padre, texto, comando, color, ancho=7):
        b = tk.Button(padre, text=texto, command=comando, bg=color, fg="white", activebackground=color,
                      activeforeground="white", relief="flat", bd=0, width=ancho, cursor="hand2",
                      font=("Segoe UI Semibold", 11), pady=4)
        claro = self.aclarar(color)
        b.bind("<Enter>", lambda e: b.config(bg=claro))
        b.bind("<Leave>", lambda e: b.config(bg=color))
        return b

    @staticmethod
    def aclarar(hexcolor):
        r, g, b = int(hexcolor[1:3], 16), int(hexcolor[3:5], 16), int(hexcolor[5:7], 16)
        r, g, b = [min(255, int(v + (255 - v) * 0.22)) for v in (r, g, b)]
        return "#%02x%02x%02x" % (r, g, b)

    def check(self, padre, texto, var, comando=None, color=TEXTO, bg=PANEL):
        return tk.Checkbutton(padre, text=texto, variable=var, command=comando, bg=bg, fg=color,
                              selectcolor=bg, activebackground=bg, activeforeground=ORO,
                              font=("Segoe UI", 9), bd=0, highlightthickness=0, cursor="hand2")

    def boton_texto(self, padre, texto, comando, bg=PANEL, fg=TEXTO):
        return tk.Button(padre, text=texto, command=comando, bg=bg, fg=fg, activebackground=bg,
                         activeforeground=ORO, relief="flat", bd=0, font=("Segoe UI", 9), cursor="hand2")

    def menu_opciones(self, padre, var, valores, comando=None):
        om = tk.OptionMenu(padre, var, *valores, command=comando)
        om.config(bg=PANEL, fg=TEXTO, activebackground=PANEL, activeforeground=ORO,
                  highlightthickness=0, bd=0, relief="flat", font=("Segoe UI", 9))
        om["menu"].config(bg=PANEL, fg=TEXTO, font=("Segoe UI", 9))
        return om

    # ---------- interfaz ----------
    def construir(self):
        self.marco = tk.Frame(self.root, bg=CARD, highlightbackground=ORO, highlightthickness=2)
        self.marco.pack(padx=8, pady=8)
        marco = self.marco

        # --- cabecera ---
        cab = tk.Frame(marco, bg=CARD)
        cab.pack(fill="x", padx=12, pady=(8, 2))
        icono = tk.Canvas(cab, width=46, height=38, bg=CARD, highlightthickness=0)
        icono.pack(side="left", padx=(0, 8))
        dibujar_cofre(icono)
        tk.Label(cab, text="CONTADOR DE COFRES", font=("Segoe UI Semibold", 12),
                 fg=ORO, bg=CARD).pack(side="left")
        est = tk.Frame(cab, bg=CARD)
        est.pack(side="right")
        self.luz = tk.Label(est, text="●", font=("Segoe UI", 13), fg=APAGADO, bg=CARD)
        self.luz.pack(side="left")
        self.lbl_luz = tk.Label(est, text="esperando", font=("Segoe UI", 9), fg=APAGADO, bg=CARD)
        self.lbl_luz.pack(side="left", padx=(2, 0))
        self.btn_compacto = self.boton_texto(cab, "▴", self.alternar_compacto, bg=CARD, fg=APAGADO)
        self.btn_compacto.config(font=("Segoe UI", 12))
        self.btn_compacto.pack(side="right", padx=(0, 8))

        # --- números grandes: total y partida ---
        self.panel_num = tk.Frame(marco, bg=PANEL)
        self.panel_num.pack(fill="x", padx=12, pady=4)
        col_t = tk.Frame(self.panel_num, bg=PANEL)
        col_t.pack(side="left", expand=True, fill="both", padx=(8, 4), pady=4)
        tk.Label(col_t, text="TOTAL", font=("Segoe UI Semibold", 9), fg=ORO_OSC, bg=PANEL).pack()
        self.lbl_total = tk.Label(col_t, text=str(self.total), font=("Segoe UI Black", 42),
                                  fg=ORO, bg=PANEL, width=5, cursor="hand2")
        self.lbl_total.pack()
        self.lbl_total.bind("<Double-Button-1>", self.editar)
        tk.Frame(self.panel_num, bg=ORO_OSC, width=1).pack(side="left", fill="y", pady=12)
        col_p = tk.Frame(self.panel_num, bg=PANEL)
        col_p.pack(side="left", expand=True, fill="both", padx=(4, 8), pady=4)
        tk.Label(col_p, text="ESTA PARTIDA", font=("Segoe UI Semibold", 9), fg=ORO_OSC, bg=PANEL).pack()
        self.lbl_sesion = tk.Label(col_p, text=str(self.sesion), font=("Segoe UI Black", 42),
                                   fg=COLOR_PARTIDA, bg=PANEL, width=4, cursor="hand2")
        self.lbl_sesion.pack()
        self.lbl_sesion.bind("<Double-Button-1>", self.editar_partida)

        # --- resumen rápido ---
        res = tk.Frame(marco, bg=PANEL)
        res.pack(fill="x", padx=12, pady=(0, 0))
        self.res = {}
        for clave, nombre, color in (("hoy", "HOY", ORO), ("media", "MEDIA / PARTIDA", CIAN),
                                     ("record", "RÉCORD PARTIDA", VERDE)):
            col = tk.Frame(res, bg=PANEL)
            col.pack(side="left", expand=True, fill="x", pady=2)
            tk.Label(col, text=nombre, font=("Segoe UI Semibold", 8), fg=ORO_OSC, bg=PANEL).pack()
            lbl = tk.Label(col, text="–", font=("Segoe UI Black", 16), fg=color, bg=PANEL)
            lbl.pack()
            self.res[clave] = lbl
        self.lbl_ritmo = tk.Label(marco, text="", font=("Segoe UI", 9), fg=CIAN, bg=CARD)
        self.lbl_ritmo.pack(pady=(4, 0))

        # --- meta (barra siempre visible) ---
        fm = tk.Frame(marco, bg=CARD)
        fm.pack(fill="x", padx=12, pady=(8, 0))
        self.cv_meta = tk.Canvas(fm, width=BARRA_META_W, height=26, bg=CARD, highlightthickness=0)
        self.cv_meta.pack(side="left")
        self.boton_texto(fm, "✎ Cambiar meta", self.editar_meta, bg=CARD, fg=ORO).pack(side="right")
        self.lbl_meta = tk.Label(marco, text="", font=("Segoe UI", 8), fg=APAGADO, bg=CARD,
                                 wraplength=400, justify="left", anchor="w")
        self.lbl_meta.pack(fill="x", padx=14)

        # --- botones ---
        botones = tk.Frame(marco, bg=CARD)
        botones.pack(pady=(6, 2))
        self.btn_menos = self.boton(botones, "−1", lambda: self.sumar(-1, False), "#c0394b", 14)
        self.btn_menos.pack(side="left", padx=3)
        self.btn_mas = self.boton(botones, "+1", lambda: self.sumar(1, False), "#2e9e5b", 14)
        self.btn_mas.pack(side="left", padx=3)
        self.boton(botones, "✎ Editar", self.editar, MORADO, 9).pack(side="left", padx=3)
        botones2 = tk.Frame(marco, bg=CARD)
        botones2.pack(pady=(2, 0))
        self.btn_nueva = self.boton(botones2, "↺ Nueva partida", self.nueva_partida, "#4a4468", 20)
        self.btn_nueva.pack(side="left", padx=3)
        self.btn_stats = self.boton(botones2, "▥ Estadísticas", self.alternar_stats, AZUL, 15)
        self.btn_stats.pack(side="left", padx=3)
        tk.Label(marco, text="Doble clic en un número para editarlo  ·  «Nueva partida» la guarda en el "
                             "historial (se hace sola al volver al lobby)", font=("Segoe UI", 8),
                 fg=APAGADO, bg=CARD, wraplength=400, justify="center").pack(pady=(2, 0))

        # --- pestañas: Amigos / En pantalla / Ajustes ---
        self.barra_tabs = tk.Frame(marco, bg=CARD)
        self.barra_tabs.pack(fill="x", padx=12, pady=(8, 0))
        self.zona = tk.Frame(marco, bg=PANEL)
        self.zona.pack(fill="x", padx=12)
        self.zona.grid_rowconfigure(0, weight=1)
        self.zona.grid_columnconfigure(0, weight=1)
        self.tabs = {}
        self.btn_tabs = {}
        for clave, texto in (("amigos", "👥 Amigos"), ("pantalla", "🖥 En pantalla"), ("ajustes", "⚙ Ajustes")):
            fr = tk.Frame(self.zona, bg=PANEL)
            self.tabs[clave] = fr
            b = tk.Button(self.barra_tabs, text=texto, command=lambda c=clave: self.mostrar_pestana(c),
                          relief="flat", bd=0, font=("Segoe UI Semibold", 10), cursor="hand2", pady=4)
            b.pack(side="left", expand=True, fill="x")
            self.btn_tabs[clave] = b
        self.construir_amigos(self.tabs["amigos"])
        self.construir_pantalla(self.tabs["pantalla"])
        self.construir_ajustes(self.tabs["ajustes"])

        # --- estado ---
        self.lbl_estado = tk.Label(marco, text="Iniciando...", font=("Segoe UI", 8), fg=APAGADO,
                                   bg=CARD, wraplength=400)
        self.lbl_estado.pack(fill="x", padx=8, pady=(6, 8))

        self.actualizar_textos_teclas()
        self.pintar_meta()
        self.pintar_resumen()
        self.pintar_amigo(forzar=True)
        ini = self.cfg_ui.get("pestana")
        self.mostrar_pestana(ini if ini in self.tabs else "amigos", guardar=False)
        self.aplicar_compacto(bool(self.cfg_ui.get("compacto")), guardar=False)

    def mostrar_pestana(self, clave, guardar=True):
        self.pestana = clave
        for c, fr in self.tabs.items():
            if c != clave:
                fr.pack_forget()
        self.tabs[clave].pack(fill="x")
        for c, b in self.btn_tabs.items():
            if c == clave:
                b.config(bg=PANEL, fg=ORO, activebackground=PANEL, activeforeground=ORO)
            else:
                b.config(bg=CARD, fg=APAGADO, activebackground=CARD, activeforeground=ORO)
        if guardar:
            self.guardar()

    def construir_amigos(self, fa):
        cab = tk.Frame(fa, bg=PANEL)
        cab.pack(fill="x", padx=10, pady=(6, 2))
        tk.Label(cab, text="COMPAÑEROS EN LÍNEA", font=("Segoe UI Semibold", 9), fg=ORO_OSC,
                 bg=PANEL).pack(side="left")
        self.boton_texto(cab, "⚙ Conectar", self.dialogo_conexion).pack(side="right")
        self.cab_amigos = cab
        self.btn_gestion = self.boton_texto(cab, "👑 Gestionar", self.dialogo_gestion, fg=ORO)
        self.btn_salir = self.boton_texto(cab, "🚪 Salir de la sala", self.salir_de_sala, fg=ROJO)
        self.fr_amigos = tk.Frame(fa, bg=PANEL)
        self.fr_amigos.pack(fill="x", padx=10, pady=(0, 2))
        self.lbl_sync = tk.Label(fa, text="Sin conectar.", font=("Segoe UI", 8), fg=APAGADO,
                                 bg=PANEL, wraplength=380, justify="left", anchor="w")
        self.lbl_sync.pack(fill="x", padx=10, pady=(0, 6))

    def chip(self, padre, texto, var, comando=None, valor=None):
        """Botón tipo interruptor: se ilumina en morado cuando está activado."""
        comun = dict(text=texto, variable=var, command=comando, indicatoron=False, bg="#2e2850",
                     fg=TEXTO, selectcolor=MORADO, activebackground="#40377a", activeforeground="white",
                     relief="flat", bd=0, highlightthickness=0, font=("Segoe UI Semibold", 9),
                     padx=10, pady=6, cursor="hand2")
        if valor is None:
            return tk.Checkbutton(padre, **comun)
        return tk.Radiobutton(padre, value=valor, **comun)

    def titulo_seccion(self, padre, texto):
        f = tk.Frame(padre, bg=PANEL)
        f.pack(fill="x", pady=(6, 2))
        tk.Label(f, text=texto, font=("Segoe UI Semibold", 9), fg=ORO_OSC, bg=PANEL).pack(side="left")
        tk.Frame(f, bg="#3a3363", height=1).pack(side="left", fill="x", expand=True, padx=(8, 0), pady=(2, 0))

    def rejilla_chips(self, padre, chips, columnas=3):
        """chips = [(texto, var, comando)]; los reparte en columnas del mismo ancho."""
        f = tk.Frame(padre, bg=PANEL)
        f.pack(fill="x")
        for c in range(columnas):
            f.grid_columnconfigure(c, weight=1, uniform="chips")
        for k, (texto, var, comando) in enumerate(chips):
            self.chip(f, texto, var, comando).grid(row=k // columnas, column=k % columnas, sticky="ew",
                                                   padx=3, pady=3)

    def construir_pantalla(self, fp):
        self.var_ov = tk.BooleanVar(value=bool(self.cfg_ov.get("visible", False)))
        self.var_mover = tk.BooleanVar(value=False)
        self.var_tam = tk.StringVar(value=self.cfg_ov.get("tam", "Mediano"))
        self.var_icono = tk.BooleanVar(value=bool(self.cfg_ov.get("icono", True)))
        self.var_partida = tk.BooleanVar(value=bool(self.cfg_ov.get("partida", False)))
        self.var_amigo = tk.BooleanVar(value=bool(self.cfg_ov.get("amigo", False)))
        self.var_grupo = tk.BooleanVar(value=bool(self.cfg_ov.get("grupo", False)))
        self.var_meta = tk.BooleanVar(value=bool(self.cfg_ov.get("meta", False)))
        caja = tk.Frame(fp, bg=PANEL)
        caja.pack(fill="x", padx=14, pady=(2, 8))

        self.titulo_seccion(caja, "NÚMERO FLOTANTE SOBRE EL JUEGO")
        self.rejilla_chips(caja, [("👁  Mostrar en pantalla", self.var_ov, self.alternar_overlay),
                                  ("✥  Mover", self.var_mover, self.cambiar_mover)], columnas=2)

        self.titulo_seccion(caja, "TAMAÑO")
        f = tk.Frame(caja, bg=PANEL)
        f.pack(fill="x")
        for c in range(len(TAMANOS)):
            f.grid_columnconfigure(c, weight=1, uniform="tam")
        for c, nombre in enumerate(TAMANOS):
            self.chip(f, nombre, self.var_tam, self.refrescar_overlay, valor=nombre).grid(
                row=0, column=c, sticky="ew", padx=3, pady=3)

        self.titulo_seccion(caja, "QUÉ ENSEÑAR")
        self.rejilla_chips(caja, [("🧰  Cofre", self.var_icono, self.refrescar_overlay),
                                  ("🎮  Partida", self.var_partida, self.refrescar_overlay),
                                  ("🎯  Meta", self.var_meta, self.refrescar_overlay),
                                  ("👥  Amigos", self.var_amigo, self.refrescar_overlay),
                                  ("🏆  Grupo", self.var_grupo, self.refrescar_overlay)], columnas=3)
        tk.Label(caja, text="«Mover»: arrastra el número donde quieras y luego desmárcalo para que los "
                            "clics lo atraviesen.", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL,
                 wraplength=370, justify="left", anchor="w").pack(fill="x", pady=(8, 0))

    def construir_ajustes(self, fj):
        n_mon = max(1, len(self.sct.monitors) - 1)
        opciones_pantalla = ["Auto"] + ["Pantalla %d" % i for i in range(1, n_mon + 1)]
        self.var_pitido = tk.BooleanVar(value=self.ini_pitido)
        self.var_celebrar = tk.BooleanVar(value=self.ini_celebrar)
        self.var_lobby = tk.BooleanVar(value=self.ini_lobby)
        self.var_solo_cofre = tk.BooleanVar(value=self.ini_solo)
        self.var_pantalla = tk.StringVar(
            value=self.ini_pantalla if self.ini_pantalla in opciones_pantalla else "Auto")
        self.var_sonido = tk.StringVar(value=self.cfg_son["elegido"])
        caja = tk.Frame(fj, bg=PANEL)
        caja.pack(fill="x", padx=14, pady=(2, 8))

        # --- juego ---
        self.titulo_seccion(caja, "JUEGO")
        f = tk.Frame(caja, bg=PANEL)
        f.pack(fill="x")
        tk.Label(f, text="Pantalla del juego", font=("Segoe UI", 9), fg=TEXTO, bg=PANEL).pack(side="left")
        self.menu_opciones(f, self.var_pantalla, opciones_pantalla, lambda v: self.guardar()).pack(
            side="left", padx=6)
        self.rejilla_chips(caja, [("🏁  Terminar partida en el lobby", self.var_lobby, self.guardar),
                                  ("🔍  Solo avisos de COFRE", self.var_solo_cofre, self.guardar)], columnas=2)

        # --- sonido ---
        self.titulo_seccion(caja, "SONIDO")
        f = tk.Frame(caja, bg=PANEL)
        f.pack(fill="x")
        tk.Label(f, text="Sonido del cofre", font=("Segoe UI", 9), fg=TEXTO, bg=PANEL).pack(side="left")
        self.menu_opciones(f, self.var_sonido, OPCIONES_SONIDO, self.al_elegir_sonido).pack(side="left", padx=6)
        self.boton_texto(f, "▶ Probar", self.probar_sonido, fg=ORO).pack(side="left", padx=2)
        self.boton_texto(f, "📂 Mi sonido…", self.elegir_sonido, fg=ORO).pack(side="left", padx=2)
        self.lbl_sonido = tk.Label(caja, text="", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL,
                                   anchor="w", wraplength=370, justify="left")
        self.lbl_sonido.pack(fill="x", pady=(2, 0))
        self.actualizar_lbl_sonido()
        self.rejilla_chips(caja, [("🔔  Sonar al sumar", self.var_pitido, self.guardar),
                                  ("🎉  Celebrar hitos", self.var_celebrar, self.guardar)], columnas=2)

        # --- atajos y datos ---
        self.titulo_seccion(caja, "ATAJOS Y DATOS")
        f = tk.Frame(caja, bg=PANEL)
        f.pack(fill="x")
        for c in range(3):
            f.grid_columnconfigure(c, weight=1, uniform="bt")
        self.boton(f, "⌨ Atajos", self.dialogo_teclas, MORADO, 8).grid(row=0, column=0, sticky="ew", padx=3)
        self.boton(f, "📁 Datos", self.abrir_carpeta_datos, AZUL, 8).grid(row=0, column=1, sticky="ew", padx=3)
        self.boton(f, "🩺 Diagnóstico", self.diagnostico, "#4a4468", 8).grid(row=0, column=2, sticky="ew", padx=3)
        self.lbl_detalle = tk.Label(caja, text="", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL,
                                    wraplength=370, justify="left", anchor="w")
        self.lbl_detalle.pack(fill="x", pady=(2, 0))

        self.titulo_seccion(caja, "ACTUALIZACIONES")
        f = tk.Frame(caja, bg=PANEL)
        f.pack(fill="x")
        self.boton(f, "🔄 Buscar", lambda: self.buscar_actualizaciones(True), MORADO, 10).pack(side="left", padx=3)
        self.lbl_upd = tk.Label(f, text="Versión %s · se busca sola al abrir." % VERSION, font=("Segoe UI", 8),
                                fg=APAGADO, bg=PANEL, anchor="w", wraplength=270, justify="left")
        self.lbl_upd.pack(side="left", padx=6)

    def abrir_carpeta_datos(self):
        try:
            os.startfile(DATOS)
        except Exception:
            messagebox.showinfo("Datos", "Tus datos están en:\n\n%s" % DATOS, parent=self.root)

    # ---------- sonido del cofre ----------
    def ruta_personal(self):
        nombre = self.cfg_son.get("personal", "")
        return os.path.join(CARPETA_SONIDOS, nombre) if nombre else ""

    def actualizar_lbl_sonido(self):
        p = self.ruta_personal()
        if p and os.path.isfile(p):
            self.lbl_sonido.config(text="Tu sonido: %s  (vale WAV, MP3, WMA o M4A)" % os.path.basename(p))
        else:
            self.lbl_sonido.config(text="Admite WAV, MP3, WMA o M4A.")

    def al_elegir_sonido(self, valor=None):
        self.cfg_son["elegido"] = self.var_sonido.get()
        p = self.ruta_personal()
        if self.var_sonido.get() == "Mi sonido" and not (p and os.path.isfile(p)):
            self.elegir_sonido()
            return
        self.guardar()
        self.probar_sonido()

    def elegir_sonido(self):
        ruta = filedialog.askopenfilename(
            parent=self.root, title="Elige tu sonido para los cofres",
            filetypes=[("Audio", "*.wav *.mp3 *.wma *.m4a"), ("Todos", "*.*")])
        if not ruta:
            p = self.ruta_personal()
            if not (p and os.path.isfile(p)):
                self.var_sonido.set("Moneda")
                self.cfg_son["elegido"] = "Moneda"
            return
        try:
            os.makedirs(CARPETA_SONIDOS, exist_ok=True)
            ext = os.path.splitext(ruta)[1].lower()
            for f in os.listdir(CARPETA_SONIDOS):
                if f.lower().startswith("mi_sonido."):
                    try:
                        os.remove(os.path.join(CARPETA_SONIDOS, f))
                    except OSError:
                        pass
            destino = os.path.join(CARPETA_SONIDOS, "mi_sonido" + ext)
            shutil.copy2(ruta, destino)      # se guarda una copia: aunque borres el original, sigue sonando
        except OSError as e:
            messagebox.showerror("Sonido", "No se pudo copiar el archivo: %s" % e, parent=self.root)
            return
        self.cfg_son["personal"] = "mi_sonido" + ext
        self.cfg_son["elegido"] = "Mi sonido"
        self.var_sonido.set("Mi sonido")
        self.actualizar_lbl_sonido()
        self.guardar()
        self.probar_sonido()

    def sonido_cofre(self):
        el = self.var_sonido.get()
        if el == "Ninguno":
            return
        try:
            if el == "Windows":
                if winsound:
                    winsound.PlaySound("SystemAsterisk", winsound.SND_ALIAS | winsound.SND_ASYNC)
                return
            if el == "Mi sonido":
                if reproducir_archivo(self.ruta_personal()):
                    return
                el = "Moneda"
            reproducir_archivo(ruta_sonido(el))
        except Exception:
            pass

    def probar_sonido(self):
        self.sonido_cofre()

    # ---------- estadísticas ----------
    def estadisticas(self):
        ahora = time.time()
        clave = (self.hist.version, fecha_madrid(ahora))
        if clave != self._st_clave or self._st is None:
            self._st = calcular_stats(self.hist.partidas, self.hist.actual, ahora)
            self._st_clave = clave
        return self._st

    def pintar_resumen(self):
        st = self.estadisticas()
        clave = (st["hoy"], st["media_total"], st["mejor_partida"])
        if clave == self._res_clave:
            return
        self._res_clave = clave
        self.res["hoy"].config(text=str(st["hoy"]))
        self.res["media"].config(text=f1(st["media_total"]) if st["media_total"] is not None else "–")
        self.res["record"].config(text=str(st["mejor_partida"]))

    def alternar_stats(self):
        if self.stats is not None and self.stats.vivo():
            self.stats.cerrar()
            self.stats = None
        else:
            self.stats = Estadisticas(self)

    # ---------- modo compacto, ritmo y novedades ----------
    def aplicar_compacto(self, valor, guardar=True):
        self.compacto = bool(valor)
        self.barra_tabs.pack_forget()
        self.zona.pack_forget()
        if not self.compacto:
            self.barra_tabs.pack(fill="x", padx=12, pady=(8, 0), before=self.lbl_estado)
            self.zona.pack(fill="x", padx=12, before=self.lbl_estado)
        self.btn_compacto.config(text="▾" if self.compacto else "▴")
        self.cfg_ui["compacto"] = self.compacto
        if guardar:
            self.guardar()

    def alternar_compacto(self):
        self.aplicar_compacto(not self.compacto)

    def pintar_ritmo(self):
        ev = self.hist.actual
        if ev:
            seg = max(0.0, time.time() - ev[0][0])
            txt = "⏱ %s" % hms(seg)
            if len(ev) >= 2 and seg >= 60:
                txt += "   ·   %s cofres/hora" % f1(len(ev) * 3600.0 / seg)
        else:
            txt = "⏱ Sin partida en curso"
        if txt != self._ritmo_txt:
            self._ritmo_txt = txt
            self.lbl_ritmo.config(text=txt)

    def pedir_novedades(self):
        if self.cfg_ui.get("ver_vista") == VERSION:
            return

        def tarea():
            try:
                d = json.loads(_get_raw("version.json").decode("utf-8-sig"))
                self.nov_resultado = d if isinstance(d, dict) else {}
            except Exception:
                self.nov_resultado = {}

        threading.Thread(target=tarea, daemon=True).start()

    def revisar_novedades(self):
        d = self.nov_resultado
        if d is None:
            return
        self.nov_resultado = None
        if str(d.get("version")) != VERSION:
            return
        self.cfg_ui["ver_vista"] = VERSION
        self.guardar()
        notas = str(d.get("notas") or "").strip()
        if notas:
            messagebox.showinfo("Novedades de la versión %s" % VERSION, notas, parent=self.root)

    # ---------- meta ----------
    def meta_info(self):
        valor = self.cfg_meta.get("valor", 0)
        if valor <= 0:
            return None
        return {"total": self.total, "valor": valor, "hecho": self.total >= valor}

    def banner_actual(self):
        if self.banner and time.time() < self.banner[2]:
            return self.banner
        return None

    def pintar_meta(self):
        c = self.cv_meta
        c.delete("all")
        W, H = BARRA_META_W, 26
        c.create_rectangle(1, 1, W - 1, H - 1, fill=BG, outline=ORO_OSC)
        meta = self.meta_info()
        ban = self.banner_actual()
        if meta:
            pct = min(1.0, self.total / float(meta["valor"]))
            if pct > 0:
                col = "#ffffff" if self.meta_flash else (VERDE if meta["hecho"] else ORO)
                c.create_rectangle(2, 2, 2 + (W - 4) * pct, H - 2, fill=col, outline="")
            txt = "%d / %d   ·   %d %%" % (self.total, meta["valor"], int(pct * 100))
        else:
            txt = "Sin meta"
        for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            c.create_text(W / 2 + dx, H / 2 + dy, text=txt, font=("Segoe UI Black", 10), fill=CONTORNO)
        c.create_text(W / 2, H / 2, text=txt, font=("Segoe UI Black", 10), fill="#ffffff")
        if ban:
            self.lbl_meta.config(text=ban[0], fg=ban[1], font=("Segoe UI Semibold", 10))
        elif not meta:
            self.lbl_meta.config(text="Pulsa «✎ Cambiar meta» para ponerte un objetivo (por ejemplo 500).",
                                 fg=APAGADO, font=("Segoe UI", 8))
        elif meta["hecho"]:
            self.lbl_meta.config(text="¡Meta conseguida! Pon una nueva con «✎ Cambiar meta».",
                                 fg=VERDE, font=("Segoe UI", 8))
        else:
            self.lbl_meta.config(text="Te faltan %d cofres. Se celebra en cada 100 y 250." %
                                 (meta["valor"] - self.total), fg=APAGADO, font=("Segoe UI", 8))

    def editar_meta(self, event=None):
        def ok(texto):
            n = parsear_numero(texto)
            if n is None:
                return "Escribe solo un número (0 para quitar la meta)."
            self.cfg_meta["valor"] = n
            self.pintar_meta()
            self.refrescar_overlay()
            return None

        actual = self.cfg_meta.get("valor", 0)
        self.dialogo_texto("Editar meta", "¿A cuántos cofres quieres llegar?", str(actual or 500),
                           "Cuenta sobre tu TOTAL. Pon 0 para quitar la meta.", ok, grande=True, ancho=7,
                           sugerencias=(100, 250, 500, 1000, 2000))

    def celebrar(self, texto, grande):
        if not self.var_celebrar.get():
            self.refrescar_overlay()
            return
        self.banner = (texto, VERDE if grande else ORO, time.time() + 4.0)
        self.flash_meta(0)
        self.pintar_meta()
        if self.overlay is not None:
            self.overlay.dibujar()
            self.overlay.destello(ciclos=4 if grande else 2)
        if grande:
            sonar([(523, 110), (659, 110), (784, 110), (1047, 120), (1319, 380)])
        else:
            sonar([(784, 90), (988, 90), (1319, 220)])
        self.root.after(4100, self.fin_banner)

    def flash_meta(self, paso=0):
        self.meta_flash = paso < 10 and paso % 2 == 0
        self.pintar_meta()
        if paso < 10:
            self.root.after(150, lambda: self.flash_meta(paso + 1))

    def fin_banner(self):
        if self.banner_actual() is None:
            self.pintar_meta()
            if self.overlay is not None:
                self.overlay.dibujar()

    # ---------- teclas ----------
    def texto_tecla(self, accion):
        t = self.cfg_teclas.get(accion, "Ninguna")
        if t == "Ninguna":
            return ""
        t = (t.replace("Ratón: lateral 1", "Ratón 4").replace("Ratón: lateral 2", "Ratón 5")
              .replace("Ratón: rueda (clic)", "Rueda").replace("Bloq Mayús", "BloqMay"))
        return "  [%s]" % t

    def actualizar_textos_teclas(self):
        self.btn_menos.config(text="−1" + self.texto_tecla("restar"))
        self.btn_mas.config(text="+1" + self.texto_tecla("sumar"))
        self.btn_nueva.config(text="↺ Nueva partida" + self.texto_tecla("nueva"))
        self.btn_stats.config(text="▥ Estadísticas" + self.texto_tecla("stats"))

    def recalcular_atajos(self):
        self.atajos = {}
        for accion, nombre in self.cfg_teclas.items():
            combo = parsear_combo(nombre)
            if combo:
                self.atajos[accion] = combo
        self.teclas_antes = {}

    def asignar_tecla(self, accion, valor):
        self.cfg_teclas[accion] = valor
        if valor != "Ninguna":
            for otra, v in list(self.cfg_teclas.items()):
                if otra != accion and v == valor:
                    self.cfg_teclas[otra] = "Ninguna"
        self.recalcular_atajos()
        self.actualizar_textos_teclas()
        self.refrescar_dialogo_teclas()
        self.guardar()

    def foco_en_texto(self):
        try:
            return isinstance(self.root.focus_get(), tk.Entry)
        except Exception:
            return False

    def revisar_teclas(self):
        try:
            if not self.capturando:
                u = ctypes.windll.user32
                if self.vk_espera:
                    if not (u.GetAsyncKeyState(self.vk_espera) & 0x8000):
                        self.vk_espera = 0
                if not self.vk_espera:
                    mods_ahora = frozenset(vk for _, vk in MODS if u.GetAsyncKeyState(vk) & 0x8000)
                    en_texto = self.foco_en_texto()
                    # Un atajo vale aunque tengas pulsadas más teclas modificadoras (por ejemplo, Ctrl
                    # para correr en el juego). Solo si hay otro atajo MÁS específico con la misma
                    # tecla (p. ej. Ctrl+F9 frente a F9) y está activo, gana el más específico.
                    candidatas = {}
                    for accion, (mods, vk) in self.atajos.items():
                        if mods <= mods_ahora and (u.GetAsyncKeyState(vk) & 0x8000):
                            candidatas[accion] = (mods, vk)
                    for accion, (mods, vk) in self.atajos.items():
                        activa = accion in candidatas and not any(
                            o != accion and ov == vk and omods > mods for o, (omods, ov) in candidatas.items())
                        if activa and not self.teclas_antes.get(accion, False) and not en_texto:
                            self.ejecutar_tecla(accion)
                        self.teclas_antes[accion] = activa
        except Exception:
            pass
        self.root.after(30, self.revisar_teclas)

    def ejecutar_tecla(self, accion):
        try:
            if accion == "sumar":
                self.sumar(1, False)
            elif accion == "restar":
                self.sumar(-1, False)
            elif accion == "nueva":
                self.nueva_partida()
            elif accion == "overlay":
                self.var_ov.set(not self.var_ov.get())
                self.alternar_overlay(mover=False)
            elif accion == "meta":
                self.var_meta.set(not self.var_meta.get())
                self.refrescar_overlay()
            elif accion == "mover":
                self.var_mover.set(not self.var_mover.get())
                self.cambiar_mover()
            elif accion == "stats":
                self.alternar_stats()
        except Exception as e:
            self.aviso("Error al ejecutar el atajo: %s" % e)

    # --- ventana para elegir las teclas ---
    def dialogo_teclas(self):
        if self.dlg_teclas is not None and self.dlg_teclas.winfo_exists():
            self.dlg_teclas.lift()
            return
        d = tk.Toplevel(self.root)
        self.dlg_teclas = d
        d.title("Atajos de teclado")
        d.configure(bg=BG)
        d.attributes("-topmost", True)
        d.resizable(False, False)
        d.transient(self.root)
        d.geometry("+%d+%d" % (self.root.winfo_rootx() + 20, self.root.winfo_rooty() + 40))
        d.protocol("WM_DELETE_WINDOW", self.cerrar_dialogo_teclas)

        caja = tk.Frame(d, bg=CARD, highlightbackground=ORO, highlightthickness=2)
        caja.pack(padx=8, pady=8)
        tk.Label(caja, text="ATAJOS DE TECLADO", font=("Segoe UI Semibold", 13), fg=ORO,
                 bg=CARD).pack(padx=20, pady=(12, 2))
        tk.Label(caja, text="Funcionan también dentro del juego. Pulsa el botón de una función y luego\n"
                            "la tecla o el botón del ratón que quieras (o una combinación como Ctrl+F9).\n"
                            "Esc = cancelar   ·   Retroceso = quitar la tecla",
                 font=("Segoe UI", 9), fg=APAGADO, bg=CARD, justify="center").pack(padx=16)
        tabla = tk.Frame(caja, bg=PANEL)
        tabla.pack(fill="x", padx=14, pady=10)
        self.btn_tecla = {}
        for accion, etiqueta in ETIQUETAS_TECLA:
            fila = tk.Frame(tabla, bg=PANEL)
            fila.pack(fill="x", padx=8, pady=3)
            tk.Label(fila, text=etiqueta, font=("Segoe UI", 10), fg=TEXTO, bg=PANEL, width=36,
                     anchor="w").pack(side="left")
            b = self.boton(fila, "", lambda a=accion: self.capturar_tecla(a), MORADO, 14)
            b.config(font=("Segoe UI Semibold", 10), pady=2)
            b.pack(side="left", padx=(4, 2))
            self.btn_tecla[accion] = b
            self.boton_texto(fila, "✕", lambda a=accion: self.asignar_tecla(a, "Ninguna")).pack(side="left", padx=2)
        tk.Label(caja, text="Consejo: usa teclas que no uses para jugar (F-teclas, bloque numérico...).\n"
                            "Mientras escribes en una casilla del programa, los atajos se pausan.",
                 font=("Segoe UI", 8), fg=APAGADO, bg=CARD, justify="center").pack(padx=16)
        fila = tk.Frame(caja, bg=CARD)
        fila.pack(pady=12)
        self.boton(fila, "Restaurar", self.restaurar_teclas, "#4a4468", 10).pack(side="left", padx=4)
        self.boton(fila, "Listo", self.cerrar_dialogo_teclas, "#2e9e5b", 10).pack(side="left", padx=4)
        d.bind("<Escape>", lambda ev: self.cerrar_dialogo_teclas() if not self.capturando else None)
        self.refrescar_dialogo_teclas()

    def cerrar_dialogo_teclas(self):
        self.capturando = None
        try:
            self.dlg_teclas.destroy()
        except Exception:
            pass
        self.dlg_teclas = None
        self.btn_tecla = {}

    def refrescar_dialogo_teclas(self):
        for accion, b in self.btn_tecla.items():
            try:
                if accion == self.capturando:
                    b.config(text="Pulsa una tecla...")
                else:
                    t = self.cfg_teclas.get(accion, "Ninguna")
                    b.config(text="— ninguna —" if t == "Ninguna" else t)
            except tk.TclError:
                pass

    def restaurar_teclas(self):
        self.cfg_teclas = dict(TECLAS_DEF)
        self.recalcular_atajos()
        self.actualizar_textos_teclas()
        self.refrescar_dialogo_teclas()
        self.guardar()

    def capturar_tecla(self, accion):
        if self.capturando:
            return
        self.capturando = accion
        self.cap_fin = time.time() + 10.0
        self.cap_liberado = False
        self.refrescar_dialogo_teclas()
        self.sondear_captura()

    def sondear_captura(self):
        accion = self.capturando
        if not accion:
            return
        u = ctypes.windll.user32
        pulsada = None
        try:
            for vk in RANGO_CAPTURA:
                if u.GetAsyncKeyState(vk) & 0x8000:
                    pulsada = vk
                    break
        except Exception:
            pulsada = None
        if not self.cap_liberado:          # primero esperar a que no haya ninguna tecla apretada
            if pulsada is None:
                self.cap_liberado = True
        elif pulsada == 0x1B:              # Esc: cancelar
            self.fin_captura(None, 0x1B)
            return
        elif pulsada == 0x08:              # Retroceso: quitar tecla
            self.fin_captura("Ninguna", 0x08)
            return
        elif pulsada is not None:
            mods = "".join(p for p, vk in MODS if u.GetAsyncKeyState(vk) & 0x8000)
            self.fin_captura(mods + nombre_vk(pulsada), pulsada)
            return
        if time.time() > self.cap_fin:
            self.fin_captura(None, 0)
            return
        self.root.after(25, self.sondear_captura)

    def fin_captura(self, valor, vk):
        accion = self.capturando
        self.capturando = None
        self.vk_espera = vk       # no disparar la acción hasta soltar la tecla
        if valor is not None and accion:
            self.asignar_tecla(accion, valor)
        else:
            self.refrescar_dialogo_teclas()

    # ---------- overlay ----------
    def alternar_overlay(self, mover=True):
        if self.var_ov.get():
            if mover:
                self.var_mover.set(True)  # al abrirlo, queda listo para colocarlo donde quieras
            if self.overlay is None:
                self.overlay = Overlay(self, self.cfg_ov)
            else:
                self.overlay.mostrar()
            self.cambiar_mover()
        elif self.overlay is not None:
            self.overlay.ocultar()
        self.guardar()

    def cambiar_mover(self):
        if self.overlay is not None:
            self.overlay.aplicar_estilo()
            self.overlay.dibujar()
        self.guardar()

    def refrescar_overlay(self, destello=False, guardar=True):
        if self.overlay is not None:
            if destello:
                self.overlay.destello()
            else:
                self.overlay.dibujar()
        if guardar:
            self.guardar()
        else:
            self.cfg_sucio = True

    # ---------- animaciones ----------
    def destello(self, paso=0):
        colores = ["#ffffff", "#fff3b0", "#ffe27a", "#ffd24d", ORO]
        if paso < len(colores):
            self.lbl_total.config(fg=colores[paso])
            self.root.after(90, lambda: self.destello(paso + 1))

    def popup(self, texto, color):
        lbl = tk.Label(self.panel_num, text=texto, font=("Segoe UI Black", 18), fg=color, bg=PANEL)

        def paso(i):
            if i >= 10:
                lbl.destroy()
                return
            lbl.place(relx=0.40, y=60 - i * 4)
            self.root.after(45, lambda: paso(i + 1))

        paso(0)

    def aviso(self, texto, seg=8.0):
        self.aviso_txt = texto
        self.aviso_hasta = time.time() + seg

    # ---------- diálogos ----------
    def dialogo_texto(self, titulo, pregunta, valor, ayuda, al_aceptar, grande=False, ancho=24,
                      sugerencias=None):
        """Ventanita con una casilla. al_aceptar(texto) devuelve None si todo bien o el error a mostrar."""
        if self.dlg is not None and self.dlg.winfo_exists():
            self.dlg.lift()
            return
        d = tk.Toplevel(self.root)
        self.dlg = d
        d.title(titulo)
        d.configure(bg=BG)
        d.attributes("-topmost", True)
        d.resizable(False, False)
        d.transient(self.root)
        d.geometry("+%d+%d" % (self.root.winfo_rootx() + 20, self.root.winfo_rooty() + 70))

        caja = tk.Frame(d, bg=CARD, highlightbackground=ORO, highlightthickness=2)
        caja.pack(padx=8, pady=8)
        tk.Label(caja, text=pregunta, font=("Segoe UI Semibold", 11), fg=ORO, bg=CARD).pack(padx=20, pady=(14, 6))
        var = tk.StringVar(value=valor)
        fuente = ("Segoe UI Black", 30) if grande else ("Segoe UI Semibold", 14)
        entrada = tk.Entry(caja, textvariable=var, font=fuente, justify="center", width=ancho,
                           bg=BG, fg=ORO, insertbackground=ORO, relief="flat",
                           highlightthickness=2, highlightbackground=APAGADO, highlightcolor=ORO)
        entrada.pack(padx=20, pady=4)
        aviso = tk.Label(caja, text=ayuda, font=("Segoe UI", 8), fg=APAGADO, bg=CARD)
        aviso.pack()

        if sugerencias:
            fs = tk.Frame(caja, bg=CARD)
            fs.pack(pady=(8, 0))

            def poner(n):
                var.set(str(n))
                entrada.focus_force()
                entrada.select_range(0, "end")

            for n in sugerencias:
                b = self.boton_texto(fs, str(n), lambda n=n: poner(n))
                b.config(padx=8, pady=2)
                b.pack(side="left", padx=2)

        def aceptar(ev=None):
            error = al_aceptar(var.get())
            if error:
                aviso.config(text=error, fg=ROJO)
                return
            d.destroy()

        fila = tk.Frame(caja, bg=CARD)
        fila.pack(pady=12)
        self.boton(fila, "Guardar", aceptar, "#2e9e5b", 8).pack(side="left", padx=4)
        self.boton(fila, "Cancelar", d.destroy, "#4a4468", 8).pack(side="left", padx=4)

        entrada.bind("<Return>", aceptar)
        d.bind("<Escape>", lambda ev: d.destroy())
        entrada.focus_force()
        entrada.select_range(0, "end")

    def editar(self, event=None):
        def ok(texto):
            n = parsear_numero(texto)
            if n is None:
                return "Escribe solo un número (0 o más)."
            self.total = n
            self.lbl_total.config(text=str(self.total))
            self.pintar_meta()
            self.refrescar_overlay()
            return None

        self.dialogo_texto("Editar contador", "¿Cuántos cofres llevas ya?", str(self.total),
                           "Desde ese número seguirá contando solo.", ok, grande=True, ancho=7)

    def editar_partida(self, event=None):
        def ok(texto):
            n = parsear_numero(texto)
            if n is None:
                return "Escribe solo un número (0 o más)."
            self.sesion = n
            self.lbl_sesion.config(text=str(self.sesion))
            self.refrescar_overlay()
            return None

        self.dialogo_texto("Editar partida", "¿Cuántos cofres llevas en esta partida?", str(self.sesion),
                           "Solo cambia el contador de la partida, no el total.", ok, grande=True, ancho=7)

    # ---------- compañeros ----------
    def nombre_amigo(self, amigo=None):
        alias = ""
        if amigo:
            alias = (self.cfg_on["alias"].get(amigo.get("pid", "")) or "").strip()
        if alias:
            return alias
        if amigo and amigo.get("nombre"):
            return amigo["nombre"]
        return "Amigo"

    def renombrar_amigo(self, amigo):
        pid = amigo["pid"]

        def ok(texto):
            t = texto.strip()[:20]
            if t:
                self.cfg_on["alias"][pid] = t
            else:
                self.cfg_on["alias"].pop(pid, None)
            self.guardar()
            self.pintar_amigo(forzar=True)
            return None

        self.dialogo_texto("Renombrar amigo", "¿Cómo quieres llamarle?", self.nombre_amigo(amigo),
                           "Solo cambia cómo lo ves tú. Vacío = usar su propio nombre.", ok, ancho=22)

    def total_grupo(self, st=None):
        """Cofres de la partida actual de todo el grupo (tú + los que están en línea)."""
        st = st or self.sync.estado()
        return self.sesion + sum(a["partida"] for a in st["amigos"] if a["online"])

    def dialogo_conexion(self):
        if self.dlg is not None and self.dlg.winfo_exists():
            self.dlg.lift()
            return
        d = tk.Toplevel(self.root)
        self.dlg = d
        d.title("Conectar con tus amigos")
        d.configure(bg=BG)
        d.attributes("-topmost", True)
        d.resizable(False, False)
        d.transient(self.root)
        d.geometry("+%d+%d" % (self.root.winfo_rootx() + 20, self.root.winfo_rooty() + 40))

        caja = tk.Frame(d, bg=CARD, highlightbackground=ORO, highlightthickness=2)
        caja.pack(padx=8, pady=8)
        tk.Label(caja, text="Conectar con tus amigos", font=("Segoe UI Semibold", 13), fg=ORO,
                 bg=CARD).pack(padx=20, pady=(12, 2))
        tk.Label(caja, text="Todos ponéis la misma dirección y el mismo código de sala.\n"
                            "Quien entre primero en la sala es el líder.",
                 font=("Segoe UI", 8), fg=APAGADO, bg=CARD, justify="center").pack()

        def campo(texto, valor, ancho):
            tk.Label(caja, text=texto, font=("Segoe UI", 9), fg=TEXTO, bg=CARD).pack(anchor="w", padx=20, pady=(8, 0))
            var = tk.StringVar(value=valor)
            e = tk.Entry(caja, textvariable=var, font=("Segoe UI", 11), width=ancho, bg=BG, fg=ORO,
                         insertbackground=ORO, relief="flat", highlightthickness=2,
                         highlightbackground=APAGADO, highlightcolor=ORO)
            e.pack(padx=20, pady=(2, 0))
            return var

        v_nombre = campo("Tu nombre (así te verán tus amigos)", self.cfg_on.get("nombre", ""), 40)
        v_url = campo("Dirección de la base de datos (Firebase)", self.cfg_on.get("url", ""), 40)
        v_sala = campo("Código de sala (inventa uno, igual para todos)", self.cfg_on.get("sala", ""), 40)
        v_act = tk.BooleanVar(value=bool(self.cfg_on.get("activo", False)))
        self.check(caja, "Conexión activada", v_act, color=TEXTO, bg=CARD).pack(anchor="w", padx=16, pady=(8, 0))
        aviso = tk.Label(caja, text="Tip: si alguien te pasa una «invitación», pégala en la dirección.",
                         font=("Segoe UI", 8), fg=APAGADO, bg=CARD, wraplength=330, justify="left")
        aviso.pack(padx=20, pady=(6, 0))

        def leer():
            url_txt = v_url.get().strip()
            sala_txt = v_sala.get()
            if "|" in url_txt:                      # invitación completa: dirección|sala
                url_txt, extra = url_txt.split("|", 1)
                if extra.strip():
                    sala_txt = extra
            return limpiar_url(url_txt), limpiar_sala(sala_txt)

        def guardar_conexion():
            url, sala = leer()
            activo = bool(v_act.get())
            if activo and (not url or not sala):
                aviso.config(text="Para activarlo hace falta la dirección y el código de sala.", fg=ROJO)
                return
            # si cambias de sala, te quitas de la anterior (para no dejar un "fantasma" tuyo allí)
            antes = (self.cfg_on.get("url", ""), self.cfg_on.get("sala", ""))
            if self.cfg_on.get("activo") and antes[0] and antes[1] and antes != (url, sala):
                Sincronizador.borrar_entrada(antes[0], antes[1], self.cfg_on.get("id", ""))
            self.cfg_on["nombre"] = v_nombre.get().strip()[:20] or nombre_por_defecto()
            self.cfg_on["url"] = url
            self.cfg_on["sala"] = sala
            self.cfg_on["activo"] = activo
            self.aplicar_conexion()
            self.guardar()
            self.pintar_amigo(forzar=True)
            d.destroy()

        def copiar_invitacion():
            url, sala = leer()
            if not url or not sala:
                aviso.config(text="Primero rellena la dirección y el código de sala.", fg=ROJO)
                return
            self.root.clipboard_clear()
            self.root.clipboard_append("%s|%s" % (url, sala))
            self.root.update()
            aviso.config(text="Invitación copiada. Pásasela a tus amigos: la pegan en «Dirección».", fg=VERDE)

        fila = tk.Frame(caja, bg=CARD)
        fila.pack(pady=12)
        self.boton(fila, "Guardar", guardar_conexion, "#2e9e5b", 8).pack(side="left", padx=4)
        self.boton(fila, "Copiar invitación", copiar_invitacion, MORADO, 15).pack(side="left", padx=4)
        self.boton(fila, "Cancelar", d.destroy, "#4a4468", 8).pack(side="left", padx=4)
        d.bind("<Escape>", lambda ev: d.destroy())

    def salir_de_sala(self):
        """Te saca de la sala en la que estás: te quita de ella, desconecta y deja libre el código
        para que pongas otro."""
        c = self.cfg_on
        sala, url = c.get("sala", ""), c.get("url", "")
        if not (c.get("activo") and sala):
            return
        if not messagebox.askyesno(
                "Salir de la sala",
                "¿Salir de la sala «%s»?\n\nDejarás de ver a los demás y ellos dejarán de verte.\n"
                "Después podrás entrar en otra (o volver a esta) con «⚙ Conectar»." % sala, parent=self.root):
            return
        Sincronizador.borrar_entrada(url, sala, c.get("id", ""))
        c["activo"] = False
        c["sala"] = ""
        self.aplicar_conexion()
        self.guardar()
        self.pintar_amigo(forzar=True)
        self.aviso("Has salido de la sala «%s»." % sala)

    def aplicar_conexion(self):
        c = self.cfg_on
        self.sync.configurar(c.get("url", ""), c.get("sala", ""), c.get("id", ""), c.get("activo", False))
        self.sync.publicar(c.get("nombre", ""), self.total, self.sesion)

    def amigos_overlay(self):
        st = self.sync.estado()
        if st["nivel"] != "ok" or st["expulsado"]:
            return []
        return [{"nombre": self.nombre_amigo(a), "total": a["total"], "partida": a["partida"],
                 "online": a["online"]} for a in st["amigos"]]

    def fila_amigo(self, a, lider):
        f = tk.Frame(self.fr_amigos, bg=PANEL)
        f.pack(fill="x", pady=1)
        tk.Label(f, text="●", font=("Segoe UI", 12), fg=VERDE if a["online"] else APAGADO,
                 bg=PANEL).pack(side="left")
        nombre = self.nombre_amigo(a) + (" 👑" if a["pid"] == lider else "")
        lb = tk.Label(f, text=nombre, font=("Segoe UI Semibold", 11), fg=CIAN if a["online"] else APAGADO,
                      bg=PANEL, cursor="hand2", anchor="w", width=12)
        lb.pack(side="left", padx=(2, 4))
        lb.bind("<Button-1>", lambda e, am=a: self.renombrar_amigo(am))
        tk.Label(f, text="Total", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL).pack(side="left")
        tk.Label(f, text=str(a["total"]), font=("Segoe UI Black", 16), fg=ORO, bg=PANEL,
                 width=5).pack(side="left")
        tk.Label(f, text="Partida", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL).pack(side="left")
        tk.Label(f, text=str(a["partida"]), font=("Segoe UI Black", 16), fg=COLOR_PARTIDA, bg=PANEL,
                 width=3).pack(side="left")

    def pintar_amigo(self, forzar=False):
        st = self.sync.estado()
        nivel, amigos = st["nivel"], st["amigos"]
        sala = self.cfg_on.get("sala", "")
        filas = tuple((a["pid"], self.nombre_amigo(a), a["total"], a["partida"], a["online"]) for a in amigos)
        clave = (nivel, st["texto"], st["lider"], st["soy_lider"], st["expulsado"], filas, self.sesion, sala,
                 st["activo"])
        if clave == self.amigo_render and not forzar:
            return
        self.amigo_render = clave

        for w in self.fr_amigos.winfo_children():
            w.destroy()
        if amigos and nivel in ("ok", "error") and not st["expulsado"]:
            for a in amigos:
                self.fila_amigo(a, st["lider"])
            g = tk.Frame(self.fr_amigos, bg=CARD)
            g.pack(fill="x", pady=(6, 2))
            tk.Label(g, text="TOTAL DEL GRUPO · ESTA PARTIDA", font=("Segoe UI Semibold", 8),
                     fg=ORO_OSC, bg=CARD).pack(side="left", padx=8, pady=4)
            tk.Label(g, text=str(self.total_grupo(st)), font=("Segoe UI Black", 22), fg=VERDE,
                     bg=CARD).pack(side="right", padx=10)
        else:
            tk.Label(self.fr_amigos, text="Aún no hay nadie más en la sala.", font=("Segoe UI", 9),
                     fg=APAGADO, bg=PANEL, anchor="w").pack(fill="x", pady=2)

        if nivel == "off":
            msg, col = "Sin conectar. Pulsa «⚙ Conectar» para configurarlo.", APAGADO
        elif nivel == "trabajando":
            msg, col = "Conectando...", APAGADO
        elif st["expulsado"]:
            msg, col = "El líder te ha expulsado de esta sala. Usa otro código de sala para entrar en otra.", ROJO
        elif nivel == "error":
            msg, col = st["texto"], ROJO
        else:
            if st["soy_lider"]:
                quien = "Eres el líder."
            else:
                nom = next((self.nombre_amigo(a) for a in amigos if a["pid"] == st["lider"]), None)
                quien = ("Líder: %s." % nom) if nom else ""
            en_linea = sum(1 for a in amigos if a["online"])
            if not amigos:
                msg = "Conectado a la sala «%s». Esperando a tus amigos... %s" % (sala, quien)
                col = APAGADO
            else:
                msg = "Conectado a «%s» · %d amigo(s) en línea. %s" % (sala, en_linea, quien)
                col = VERDE if en_linea else APAGADO
        self.lbl_sync.config(text=msg.strip(), fg=col)

        mostrar = bool(st["soy_lider"] and nivel == "ok")
        if mostrar != self._gest_visible:
            self._gest_visible = mostrar
            if mostrar:
                self.btn_gestion.pack(side="right", padx=4)
            else:
                self.btn_gestion.pack_forget()
        dentro = bool(st["activo"])
        if dentro != self._salir_visible:
            self._salir_visible = dentro
            if dentro:
                self.btn_salir.pack(side="right", padx=4)
            else:
                self.btn_salir.pack_forget()

        if self.overlay is not None and (self.var_amigo.get() or self.var_grupo.get()):
            self.overlay.dibujar()

    # ---------- gestión de la sala (líder) ----------
    def dialogo_gestion(self):
        if self.dlg_gestion is not None and self.dlg_gestion.winfo_exists():
            self.dlg_gestion.lift()
            return
        d = tk.Toplevel(self.root)
        self.dlg_gestion = d
        d.title("Gestionar sala")
        d.configure(bg=BG)
        d.attributes("-topmost", True)
        d.resizable(False, False)
        d.transient(self.root)
        d.geometry("+%d+%d" % (self.root.winfo_rootx() + 20, self.root.winfo_rooty() + 40))
        d.protocol("WM_DELETE_WINDOW", self.cerrar_gestion)

        caja = tk.Frame(d, bg=CARD, highlightbackground=ORO, highlightthickness=2)
        caja.pack(padx=8, pady=8)
        tk.Label(caja, text="👑 GESTIONAR SALA", font=("Segoe UI Semibold", 13), fg=ORO,
                 bg=CARD).pack(padx=20, pady=(12, 2))
        tk.Label(caja, text="Solo el líder ve esto. Los expulsados no pueden volver a esta sala\n"
                            "(salvo que los perdones).",
                 font=("Segoe UI", 8), fg=APAGADO, bg=CARD, justify="center").pack(padx=16)
        self.fr_gestion = tk.Frame(caja, bg=PANEL)
        self.fr_gestion.pack(fill="x", padx=14, pady=10)
        fila = tk.Frame(caja, bg=CARD)
        fila.pack(pady=(0, 4))
        self.btn_perdonar = self.boton(fila, "Perdonar expulsados", self.perdonar, "#4a4468", 20)
        self.btn_perdonar.pack(side="left", padx=4)
        self.boton(fila, "🧹 Limpiar desconectados", self.limpiar_sala_gestion, "#c0394b", 24).pack(side="left", padx=4)
        fila2 = tk.Frame(caja, bg=CARD)
        fila2.pack(pady=(0, 12))
        self.boton(fila2, "Cerrar", self.cerrar_gestion, "#2e9e5b", 10).pack()
        d.bind("<Escape>", lambda ev: self.cerrar_gestion())
        self._gest_clave = None
        self.pintar_gestion(True)

    def cerrar_gestion(self):
        try:
            self.dlg_gestion.destroy()
        except Exception:
            pass
        self.dlg_gestion = None

    def pintar_gestion(self, forzar=False):
        d = self.dlg_gestion
        if d is None:
            return
        try:
            if not d.winfo_exists():
                self.dlg_gestion = None
                return
        except tk.TclError:
            self.dlg_gestion = None
            return
        st = self.sync.estado()
        if not st["soy_lider"]:
            self.cerrar_gestion()
            return
        clave = (tuple((a["pid"], self.nombre_amigo(a), a["online"]) for a in st["amigos"]), st["n_exp"])
        if clave == self._gest_clave and not forzar:
            return
        self._gest_clave = clave
        for w in self.fr_gestion.winfo_children():
            w.destroy()
        if not st["amigos"]:
            tk.Label(self.fr_gestion, text="No hay nadie más en la sala.", font=("Segoe UI", 10),
                     fg=APAGADO, bg=PANEL).pack(padx=16, pady=12)
        for a in st["amigos"]:
            f = tk.Frame(self.fr_gestion, bg=PANEL)
            f.pack(fill="x", padx=8, pady=3)
            tk.Label(f, text="●", font=("Segoe UI", 12), fg=VERDE if a["online"] else APAGADO,
                     bg=PANEL).pack(side="left")
            tk.Label(f, text=self.nombre_amigo(a), font=("Segoe UI Semibold", 11), fg=TEXTO, bg=PANEL,
                     width=16, anchor="w").pack(side="left", padx=(2, 4))
            tk.Label(f, text="en línea" if a["online"] else "desconectado", font=("Segoe UI", 8),
                     fg=VERDE if a["online"] else APAGADO, bg=PANEL, width=11, anchor="w").pack(side="left")
            self.boton(f, "👑 Líder", lambda am=a: self.hacer_lider(am), MORADO, 8).pack(side="left", padx=2)
            self.boton(f, "⛔ Expulsar", lambda am=a: self.expulsar(am), "#c0394b", 10).pack(side="left", padx=2)
        self.btn_perdonar.config(text="Perdonar expulsados (%d)" % st["n_exp"])

    def expulsar(self, a):
        if messagebox.askyesno("Expulsar", "¿Expulsar a %s de la sala?" % self.nombre_amigo(a),
                               parent=self.dlg_gestion):
            self.sync.expulsar(a["pid"])
            self.pintar_amigo(forzar=True)
            self.pintar_gestion(True)

    def hacer_lider(self, a):
        if messagebox.askyesno("Pasar el liderazgo",
                               "¿Hacer líder a %s?\n\nDejarás de poder gestionar la sala." % self.nombre_amigo(a),
                               parent=self.dlg_gestion):
            self.sync.hacer_lider(a["pid"])
            self.pintar_amigo(forzar=True)

    def perdonar(self):
        self.sync.perdonar_expulsados()
        self.pintar_gestion(True)

    def limpiar_sala_gestion(self):
        if messagebox.askyesno("Limpiar sala", "Se quitarán de la sala los que están desconectados y las "
                               "entradas antiguas repetidas.\n\n¿Seguir?", parent=self.dlg_gestion):
            n = self.sync.limpiar_desconectados()
            self.aviso("Sala limpiada: %d entrada(s) quitada(s)." % n)
            self.pintar_amigo(forzar=True)
            self.pintar_gestion(True)

    def ciclo_amigo(self):
        try:
            self.sync.publicar(self.cfg_on.get("nombre", ""), self.total, self.sesion)
            self.pintar_amigo()
            self.pintar_gestion()
            self.pintar_resumen()
            self.revisar_resultado_actualizacion()
            self.pintar_ritmo()
            self.revisar_novedades()
            if self.stats is not None:
                if self.stats.vivo():
                    self.stats.refrescar()
                else:
                    self.stats = None
            if self.hist.sucio:                            # guardado diferido tras contar cofres
                self.hist.guardar()
            if self.cfg_sucio or time.time() - self.ult_guardado > 20:     # y guardado automático
                self.guardar()
        except tk.TclError:
            pass
        self.root.after(250, self.ciclo_amigo)

    # ---------- actualización ----------
    def buscar_actualizaciones(self, manual=False):
        if self.upd_buscando or self.upd_descargando:
            return
        self.upd_buscando = True
        self.upd_manual = manual
        self.upd_ultima = time.time()
        if manual:
            self.lbl_upd.config(text="Buscando actualizaciones...", fg=APAGADO)

        def tarea():
            try:
                self.upd_resultado = ("ok", buscar_actualizacion())
            except Exception as e:
                self.upd_resultado = ("error", str(e))

        threading.Thread(target=tarea, daemon=True).start()

    def revisar_resultado_actualizacion(self):
        r = self.upd_resultado
        if r is None:
            if not self.upd_buscando and not self.upd_descargando and time.time() - self.upd_ultima > 1800:
                self.buscar_actualizaciones(False)
            return
        self.upd_resultado = None
        self.upd_buscando = False
        tipo, dato = r
        if tipo == "ok" and dato:
            self.upd_info = dato
            self.lbl_upd.config(text="Hay una versión nueva: %s" % dato.get("version"), fg=ORO)
            ya_dicho = (not dato.get("obligatoria")) and str(dato.get("version")) == self.upd_pospuesta
            if self.upd_manual or not ya_dicho:
                self.dialogo_actualizacion(dato)
        elif tipo == "ok":
            self.upd_info = None
            if self.upd_manual:
                self.lbl_upd.config(text="Estás al día (versión %s)." % VERSION, fg=VERDE)
        elif self.upd_manual:
            self.lbl_upd.config(text="No se pudo comprobar (¿sin internet?).", fg=ROJO)

    def dialogo_actualizacion(self, info):
        if self.upd_dlg is not None:
            try:
                if self.upd_dlg.winfo_exists():
                    self.upd_dlg.lift()
                    return
            except tk.TclError:
                pass
        obligatoria = bool(info.get("obligatoria"))
        d = tk.Toplevel(self.root)
        self.upd_dlg = d
        d.title("Actualización disponible")
        d.configure(bg=BG)
        d.attributes("-topmost", True)
        d.resizable(False, False)
        d.transient(self.root)
        d.geometry("+%d+%d" % (self.root.winfo_rootx() + 20, self.root.winfo_rooty() + 40))
        caja = tk.Frame(d, bg=CARD, highlightbackground=ORO, highlightthickness=2)
        caja.pack(padx=8, pady=8)
        tk.Label(caja, text="🚀 NUEVA VERSIÓN", font=("Segoe UI Semibold", 14), fg=ORO, bg=CARD).pack(
            padx=26, pady=(14, 2))
        tk.Label(caja, text="Tienes la %s y ya está la %s." % (VERSION, info.get("version")),
                 font=("Segoe UI", 10), fg=TEXTO, bg=CARD).pack()
        notas = str(info.get("notas") or "").strip()[:900]
        if notas:
            tk.Label(caja, text=notas, font=("Segoe UI", 9), fg=TEXTO, bg=PANEL, wraplength=380,
                     justify="left", anchor="w", padx=10, pady=8).pack(fill="x", padx=14, pady=(10, 0))
        tk.Label(caja, text=("Esta actualización es obligatoria para seguir usando el programa."
                             if obligatoria else
                             "Se descarga sola en unos segundos y el programa se reinicia.\n"
                             "No pierdes ningún dato."),
                 font=("Segoe UI", 8), fg=ROJO if obligatoria else APAGADO, bg=CARD, justify="center").pack(
            padx=16, pady=(8, 0))
        lbl_est = tk.Label(caja, text="", font=("Segoe UI", 9), fg=ORO, bg=CARD, wraplength=380)
        lbl_est.pack(pady=(4, 0))
        fila = tk.Frame(caja, bg=CARD)
        fila.pack(pady=12)

        def no():
            self.upd_pospuesta = str(info.get("version"))
            try:
                d.destroy()
            except tk.TclError:
                pass
            self.upd_dlg = None
            if obligatoria:
                self.cerrar()

        def si():
            btn_ok.config(state="disabled")
            btn_no.config(state="disabled")
            self.upd_descargando = True
            lbl_est.config(text="Descargando...", fg=ORO)
            est = {"r": None}

            def tarea():
                try:
                    descargar_actualizacion(info)
                    est["r"] = ("ok", "")
                except Exception as e:
                    est["r"] = ("error", str(e))

            def esperar():
                try:
                    if est["r"] is None:
                        d.after(150, esperar)
                        return
                    if est["r"][0] == "ok":
                        lbl_est.config(text="¡Listo! Reiniciando...", fg=VERDE)
                        d.after(700, self.reiniciar_tras_actualizar)
                    else:
                        self.upd_descargando = False
                        lbl_est.config(text="No se pudo actualizar: %s" % est["r"][1], fg=ROJO)
                        btn_ok.config(state="normal", text="Reintentar")
                        btn_no.config(state="normal")
                except tk.TclError:
                    pass

            threading.Thread(target=tarea, daemon=True).start()
            esperar()

        btn_ok = self.boton(fila, "⬇ Actualizar ahora", si, "#2e9e5b", 18)
        btn_ok.pack(side="left", padx=4)
        btn_no = self.boton(fila, "Salir" if obligatoria else "Más tarde", no, "#4a4468", 10)
        btn_no.pack(side="left", padx=4)
        d.protocol("WM_DELETE_WINDOW", no)
        if obligatoria:
            try:
                d.grab_set()
            except tk.TclError:
                pass

    def reiniciar_tras_actualizar(self):
        try:
            self.guardar()
            self.hist.guardar()
            reiniciar_programa()
        except Exception as e:
            self.upd_descargando = False
            messagebox.showinfo("Actualizado", "La actualización está lista.\nCierra el programa y vuelve a abrirlo."
                                "\n\n(%s)" % e, parent=self.root)
            return
        self.cerrar()

    # ---------- guardado ----------
    def cargar(self):
        return leer_json(ARCHIVO)

    def guardar(self):
        self.ult_guardado = time.time()
        g = self.root.geometry()
        datos = {"total": self.total, "partida": self.sesion}
        if "+" in g:
            datos["geometria"] = "+" + g.split("+", 1)[1]
        ov = dict(self.cfg_ov)
        ov["visible"] = bool(self.var_ov.get())
        ov["tam"] = self.var_tam.get()
        ov["icono"] = bool(self.var_icono.get())
        ov["partida"] = bool(self.var_partida.get())
        ov["amigo"] = bool(self.var_amigo.get())
        ov["grupo"] = bool(self.var_grupo.get())
        ov["meta"] = bool(self.var_meta.get())
        if self.overlay is not None:
            try:
                ov["x"] = self.overlay.win.winfo_x()
                ov["y"] = self.overlay.win.winfo_y()
            except tk.TclError:
                pass
        self.cfg_ov = ov
        datos["overlay"] = ov
        datos["online"] = self.cfg_on
        datos["teclas"] = self.cfg_teclas
        datos["meta"] = self.cfg_meta
        datos["sonido"] = self.cfg_son
        self.cfg_ui["pestana"] = self.pestana
        datos["ui"] = self.cfg_ui
        datos["lobby"] = bool(self.var_lobby.get())
        datos["celebrar"] = bool(self.var_celebrar.get())
        datos["pitido"] = bool(self.var_pitido.get())
        datos["pantalla"] = self.var_pantalla.get()
        datos["solo_cofre"] = bool(self.var_solo_cofre.get())
        self.cfg_sucio = False
        self.error_guardado = not guardar_json(ARCHIVO, datos)

    def cerrar(self):
        try:
            self.guardar()
            self.hist.guardar()
        finally:
            self.sync.parar()
            self.root.destroy()

    # ---------- contador ----------
    def sumar(self, n, automatico):
        previo = self.total
        self.total = max(0, self.total + n)
        self.sesion = max(0, self.sesion + n)

        # ¿hito o meta conseguida?
        hito = None
        if n > 0 and self.total > previo:
            meta = self.cfg_meta.get("valor", 0)
            if meta > 0 and previo < meta <= self.total:
                hito = ("¡META CONSEGUIDA!", True)
            elif es_hito(self.total):
                hito = ("¡%d COFRES!" % self.total, self.total % 500 == 0)
            if hito is None:
                rec = max((len(pt) for pt in self.hist.partidas), default=0)
                if rec >= 5 and self.sesion == rec + 1:
                    hito = ("¡RÉCORD DE PARTIDA! %d" % self.sesion, True)

        # 1) lo que se oye y se ve, al instante (suena también al sumar a mano)
        if n > 0 and self.var_pitido.get() and not hito:
            self.sonido_cofre()
        self.lbl_total.config(text=str(self.total))
        self.lbl_sesion.config(text=str(self.sesion))
        if n > 0:
            self.destello()
            self.popup("+%d" % n, VERDE)
        else:
            self.popup("%d" % n, ROJO)
        if hito:
            self.celebrar(hito[0], hito[1])
            self.cfg_sucio = True
        else:
            self.refrescar_overlay(destello=(n > 0), guardar=False)
        self.pintar_meta()

        # 2) lo que se guarda: se apunta ya, pero se escribe en disco un instante después
        ts = int(time.time())
        if n > 0:
            for _ in range(n):
                self.hist.sumar(ts, automatico)
        else:
            for _ in range(-n):
                self.hist.quitar()
        self.pintar_resumen()
        self.sync.publicar(self.cfg_on.get("nombre", ""), self.total, self.sesion)

    def nueva_partida(self, auto=False):
        """Guarda la partida en el historial y pone a 0 solo el contador de la partida;
        el total no se toca."""
        resumen = ""
        ev = self.hist.actual
        if ev:
            dur = max(0, ev[-1][0] - ev[0][0])
            resumen = "Partida: %d cofres en %s" % (len(ev), hms(dur))
            if len(ev) >= 2 and dur >= 60:
                resumen += " (%s/hora)" % f1(len(ev) * 3600.0 / dur)
        guardada = self.hist.cerrar()
        self.sesion = 0
        self.lbl_sesion.config(text="0")
        self.activo = False
        self.seguidos = 0
        self.perdidos = 0
        self.pintar_resumen()
        self.refrescar_overlay()
        self.sync.publicar(self.cfg_on.get("nombre", ""), self.total, self.sesion)
        if resumen:
            self.aviso(("Lobby detectado. " if auto else "") + resumen + " · guardada.", 20)
        elif auto:
            self.aviso("Lobby detectado: nueva partida.")

    # ---------- captura ----------
    def region_juego(self):
        sel = self.var_pantalla.get()
        if sel != "Auto":
            idx = int(sel.split()[-1])
            m = self.sct.monitors[idx]
            return (m["left"], m["top"], m["width"], m["height"]), "Mirando la %s" % sel.lower()
        ahora = time.time()
        if self.hwnd is None or ahora - self.ultima_busqueda > 2.0:
            self.hwnd = buscar_ventana_fortnite()
            self.ultima_busqueda = ahora
        if self.hwnd is None:
            return None, "No encuentro la ventana de Fortnite (ábrelo o elige la pantalla en Ajustes)"
        rect = rect_cliente(self.hwnd)
        if rect is None or rect[2] < 300 or rect[3] < 200:
            self.hwnd = None
            return None, "Fortnite está minimizado o no visible"
        return rect, "Fortnite detectado"

    def tapar_ventanas_propias(self, img, x0, y0):
        """Pinta de negro lo que ocupan las ventanas de ESTE programa (el número flotante, los
        paneles...) para que nunca se confundan con un aviso de cofre del juego. Los números
        lavanda de «partida» se parecen mucho al texto del aviso."""
        d = None
        ventanas = [self.root] + [w for w in self.root.winfo_children() if isinstance(w, tk.Toplevel)]
        for v in ventanas:
            try:
                if not v.winfo_viewable():
                    continue
                izq, arr = v.winfo_rootx(), v.winfo_rooty()
                der, aba = izq + v.winfo_width(), arr + v.winfo_height()
            except tk.TclError:
                continue
            ax, ay = max(izq, x0) - x0, max(arr, y0) - y0
            bx, by = min(der, x0 + img.width) - x0, min(aba, y0 + img.height) - y0
            if bx > ax and by > ay:
                if d is None:
                    d = ImageDraw.Draw(img)
                d.rectangle([ax, ay, bx, by], fill=(0, 0, 0))

    def capturar(self, rect):
        left, top, w, h = rect
        x = left + int(FX0 * w)
        y = top + int(FY0 * h)
        rw = max(32, int(FW * w))
        rh = max(32, int(FH * h))
        shot = self.sct.grab({"left": x, "top": y, "width": rw, "height": rh})
        img = Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")
        base = img.copy()
        self.tapar_ventanas_propias(base, x, y)
        esc = ANCHO_ANALISIS_BASE / float(w)         # el texto se analiza siempre al mismo tamaño
        pequena = base.resize((max(40, int(round(rw * esc))), max(40, int(round(rh * esc)))), Image.BICUBIC)
        # la zona exacta que miraba el detector de siempre (0.62, 0.26, 0.13 x 0.09)
        ox = int(0.62 * w) - int(FX0 * w)
        oy = int(0.26 * h) - int(FY0 * h)
        ow, oh = max(8, int(0.13 * w)), max(4, int(0.09 * h))
        vieja = base.crop((ox, oy, ox + ow, oy + oh)).resize((84, 32), Image.BICUBIC)
        return pequena, img, vieja

    def capturar_caja(self, rect, caja):
        left, top, w, h = rect
        fx, fy, fw, fh = caja
        shot = self.sct.grab({"left": left + int(fx * w), "top": top + int(fy * h),
                              "width": max(4, int(fw * w)), "height": max(4, int(fh * h))})
        return Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")

    def revisar_lobby(self, rect):
        try:
            ok, fa, fp = hay_lobby(self.capturar_caja(rect, LOBBY_BOTON),
                                   self.capturar_caja(rect, LOBBY_PASTILLA))
        except Exception:
            return
        self.lobby_info = (fa, fp)
        if ok:
            self.lobby_no = 0
            self.lobby_si += 1
            if self.lobby_si >= LOBBY_CONFIRMAR and not self.en_lobby:
                self.en_lobby = True
                # Si acabas de abrir el programa y ya estás en el lobby, NO se cierra la partida:
                # así, al reabrirlo, conservas los mismos datos que tenías al cerrarlo.
                recien_abierto = (time.time() - self.t_inicio) < LOBBY_GRACIA_ARRANQUE
                if self.var_lobby.get() and not recien_abierto and (self.sesion > 0 or self.hist.actual):
                    self.nueva_partida(auto=True)
        else:
            self.lobby_si = 0
            if self.en_lobby:
                self.lobby_no += 1
                if self.lobby_no >= LOBBY_REARMAR:
                    self.en_lobby = False
                    self.lobby_no = 0

    def guardar_deteccion(self, n, origen=""):
        """Guarda la imagen de cada cofre contado solo: si alguna vez cuenta uno "de más",
        ahí tienes la foto de qué vio el programa (carpeta «detecciones»). Va en segundo plano
        para no retrasar el sonido."""
        if self.ultima_img is None:
            return
        img = self.ultima_img.copy()
        nombre = time.strftime("%Y%m%d_%H%M%S") + "_x%d_%s.png" % (n, origen or "x")

        def tarea():
            try:
                os.makedirs(CARPETA_DETECCIONES, exist_ok=True)
                img.save(os.path.join(CARPETA_DETECCIONES, nombre))
                ficheros = sorted(f for f in os.listdir(CARPETA_DETECCIONES) if f.endswith(".png"))
                for f in ficheros[:-MAX_DETECCIONES_GUARDADAS]:
                    os.remove(os.path.join(CARPETA_DETECCIONES, f))
            except Exception:
                pass

        threading.Thread(target=tarea, daemon=True).start()

    def guardar_otros(self, otros):
        """Foto de los avisos de experiencia que NO se han tomado por cofre (con lo que se parecían
        a la palabra «COFRE»): si algún cofre tuyo no cuenta, ahí está la prueba (carpeta
        «detecciones\\otros»)."""
        if not otros or self.ultima_img is None:
            return
        ahora = time.time()
        if ahora - self.t_otros < 15:
            return
        self.t_otros = ahora
        img = self.ultima_img.copy()
        nombre = time.strftime("%Y%m%d_%H%M%S") + "_otro_%d.png" % int(max(a["cofre"] for a in otros) * 100)

        def tarea():
            try:
                carpeta = os.path.join(CARPETA_DETECCIONES, "otros")
                os.makedirs(carpeta, exist_ok=True)
                img.save(os.path.join(carpeta, nombre))
                ficheros = sorted(f for f in os.listdir(carpeta) if f.endswith(".png"))
                for f in ficheros[:-15]:
                    os.remove(os.path.join(carpeta, f))
            except Exception:
                pass

        threading.Thread(target=tarea, daemon=True).start()

    def procesar(self, n, origen=""):
        """n = cuántos avisos de cofre se ven ahora mismo. Se cuenta un cofre cada vez que n
        SUBE respecto a los ya contados (así, si coges otro cofre mientras el anterior sigue en
        pantalla, el aviso nuevo se apila y también cuenta). Hay que verlo varios fotogramas
        seguidos para fiarse, y también varios sin verlo para dar un aviso por terminado."""
        conf = self.avisos_conf
        if n > conf:
            self.baja = 0
            if n == self.cand_n:
                self.sube += 1
            else:
                self.cand_n = n
                self.sube = 1
            if self.sube >= FRAMES_PARA_CONTAR:
                nuevos = min(n - conf, 4)
                self.avisos_conf = n
                self.sube = 0
                for _ in range(nuevos):
                    self.sumar(1, True)
                self.guardar_deteccion(nuevos, origen)
        elif n < conf:
            self.sube = 0
            self.baja += 1
            if self.baja >= FRAMES_PARA_REARMAR:
                self.avisos_conf = n
                self.baja = 0
        else:
            self.sube = 0
            self.baja = 0

    def poner_estado(self, msg):
        """Línea de estado de abajo. Si no se pueden guardar los datos, eso tiene prioridad (en rojo)."""
        if self.error_guardado or self.hist.error:
            self.lbl_estado.config(text="⚠ NO SE PUEDEN GUARDAR TUS DATOS en: %s  — cierra otras copias "
                                        "del programa o revisa el antivirus." % DATOS, fg=ROJO)
        elif time.time() < self.aviso_hasta:
            self.lbl_estado.config(text=self.aviso_txt, fg=VERDE)
        else:
            self.lbl_estado.config(text=msg, fg=APAGADO)

    def tick(self):
        try:
            t_ini = time.time()
            rect, msg = self.region_juego()
            if rect is None:
                self.luz.config(fg=APAGADO)
                self.lbl_luz.config(text="sin juego", fg=APAGADO)
                self.poner_estado(msg)
                self.lbl_detalle.config(text="")
                self.en_lobby = False
                self.lobby_si = 0
                self.avisos_conf = 0
                self.sube = self.baja = 0
            else:
                self.tick_n += 1
                if self.tick_n % LOBBY_CADA == 0:
                    self.revisar_lobby(rect)
                pequena, grande, vieja = self.capturar(rect)
                self.ultima_img = grande
                self.ultima_rect = rect
                todos = buscar_avisos(pequena)
                solo = bool(self.var_solo_cofre.get())
                # con "solo COFRE" (lo normal) la experiencia de la partida y demás avisos se ignoran
                avisos = [a for a in todos if a["cofre"] >= UMBRAL_COFRE] if solo else todos
                otros = [a for a in todos if a not in avisos]
                ok_v, v1, v2, vw = hay_aviso_clasico(vieja)
                n_av = len(avisos)
                origen = "nuevo"
                # El detector de siempre (el de los cofres normales) sigue valiendo, SALVO que el
                # detector nuevo haya visto en pantalla un aviso con OTRA palabra (la experiencia
                # que da la partida): entonces ese aviso no es un cofre.
                if ok_v and n_av == 0 and not (solo and otros):
                    n_av = 1
                    origen = "clasico"
                if self.en_lobby:       # en el lobby no sale ningún aviso de cofre
                    avisos = []
                    otros = []
                    n_av = 0
                self.ultimo_aviso = avisos[0] if avisos else (otros[0] if otros else None)
                self.guardar_otros(otros)
                self.procesar(n_av, origen)
                visto = n_av > 0
                if self.en_lobby:
                    self.luz.config(fg=CIAN)
                    self.lbl_luz.config(text="en el lobby", fg=CIAN)
                else:
                    self.luz.config(fg=VERDE if visto else ORO_OSC)
                    self.lbl_luz.config(text=("¡cofre!" if n_av < 2 else "¡%d cofres!" % n_av)
                                        if visto else "en partida",
                                        fg=VERDE if visto else APAGADO)
                self.poner_estado(msg)
                a = self.ultimo_aviso
                det = ("aviso: parece COFRE %d%%" % int(a["cofre"] * 100)) if a else "sin aviso"
                ms = int((time.time() - t_ini) * 1000)
                self.lbl_detalle.config(text="Avisos: %d (%s · clásico %s l1=%d l2=%d ancho=%d)  ·  Lobby: botón=%d%% menú=%d%%  ·  ciclo %d ms"
                                        % (n_av, det, "SÍ" if ok_v else "no", v1, v2, vw,
                                           int(self.lobby_info[0] * 100), int(self.lobby_info[1] * 100), ms))
        except Exception as e:
            self.lbl_estado.config(text="Error: %s" % e)
        self.root.after(INTERVALO_MS, self.tick)

    # ---------- diagnóstico ----------
    def diagnostico(self):
        if self.ultima_img is None or self.ultima_rect is None:
            messagebox.showinfo("Diagnóstico", "Todavía no hay captura. Abre Fortnite primero.", parent=self.root)
            return
        carpeta = os.path.join(DATOS, "diagnostico")
        os.makedirs(carpeta, exist_ok=True)
        marca = time.strftime("%H%M%S")
        self.ultima_img.save(os.path.join(carpeta, "zona_%s.png" % marca))
        try:
            self.capturar_caja(self.ultima_rect, LOBBY_BOTON).save(os.path.join(carpeta, "lobby_boton_%s.png" % marca))
            self.capturar_caja(self.ultima_rect, LOBBY_PASTILLA).save(
                os.path.join(carpeta, "lobby_menu_%s.png" % marca))
        except Exception:
            pass
        left, top, w, h = self.ultima_rect
        shot = self.sct.grab({"left": left, "top": top, "width": w, "height": h})
        pantalla = Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")
        pantalla.thumbnail((1280, 720))
        pantalla.save(os.path.join(carpeta, "pantalla_%s.png" % marca))
        messagebox.showinfo("Diagnóstico", "Guardado en:\n%s" % carpeta, parent=self.root)


if __name__ == "__main__":
    if _lanzar_codigo_nuevo():
        sys.exit(0)
    _ok = instancia_unica()
    if not _ok and os.environ.get("CONTADOR_REINICIO"):
        for _ in range(40):                 # tras actualizar: espera a que se cierre la copia anterior
            time.sleep(0.25)
            if instancia_unica():
                _ok = True
                break
    os.environ.pop("CONTADOR_REINICIO", None)
    if not _ok:
        _r = tk.Tk()
        _r.withdraw()
        messagebox.showinfo("Contador de cofres", "El programa ya está abierto.\n\nBusca su ventana en la "
                            "barra de tareas (abrirlo dos veces mezclaría los datos).")
        _r.destroy()
    else:
        root = tk.Tk()
        App(root)
        root.mainloop()

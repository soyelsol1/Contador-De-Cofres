import io
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
import struct
import calendar
import threading
import http.client
import urllib.parse
from collections import Counter, deque
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
VERSION = "1.3.8"
REPO_RAW = "https://raw.githubusercontent.com/soyelsol1/Contador-De-Cofres/main"
# Base de datos de las salas: la misma para todo el mundo, ya viene dentro del programa.
URL_SALAS = "https://cofres-7beb6-default-rtdb.europe-west1.firebasedatabase.app"
CARPETA_CODIGO = os.path.join(DATOS, "codigo")
ARCHIVO_CODIGO = os.path.join(CARPETA_CODIGO, "contador_cofres.py")
CARPETA_COPIAS = os.path.join(DATOS, "copias")
# Archivos de apoyo que el programa necesita además de este. Se bajan solos a «codigo» (dentro de la carpeta de datos).
ARCHIVOS_EXTRA = ("lector_repeticiones.py",)


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


# ---------------------------------------------------------------- código local cifrado
# El código que se descarga (el programa nuevo y sus archivos de apoyo) se guarda SIEMPRE cifrado en la
# carpeta de datos: en el disco nunca queda un ".py" en claro que alguien pueda abrir y leer sin más.
# Usa AES-256-CBC con la librería de cifrado que trae Windows (bcrypt.dll); no hace falta nada aparte.
# Ojo: la clave vive en este mismo programa, así que esto frena a quien cotillee la carpeta, no a quien
# desmonte el programa a propósito. El código fuente de verdad sigue público, sin cifrar, en GitHub.
_CLAVE_CODIGO = bytes.fromhex("cf8862ebdb0ce77a84ed8265eac8f9e7791a909a926444d3bc7ab9ca25f460b3")
_MARCA_CIFRADO = b"CC01"


def _bcrypt_aes(clave, datos, iv, cifrar):
    bc = ctypes.WinDLL("bcrypt")
    VP = ctypes.c_void_p
    bc.BCryptOpenAlgorithmProvider.argtypes = [ctypes.POINTER(VP), ctypes.c_wchar_p, ctypes.c_wchar_p, ctypes.c_ulong]
    bc.BCryptSetProperty.argtypes = [VP, ctypes.c_wchar_p, ctypes.c_wchar_p, ctypes.c_ulong, ctypes.c_ulong]
    bc.BCryptGenerateSymmetricKey.argtypes = [VP, ctypes.POINTER(VP), VP, ctypes.c_ulong, ctypes.c_char_p,
                                              ctypes.c_ulong, ctypes.c_ulong]
    bc.BCryptEncrypt.argtypes = [VP, ctypes.c_char_p, ctypes.c_ulong, VP, ctypes.c_char_p, ctypes.c_ulong,
                                 ctypes.c_char_p, ctypes.c_ulong, ctypes.POINTER(ctypes.c_ulong), ctypes.c_ulong]
    bc.BCryptDecrypt.argtypes = bc.BCryptEncrypt.argtypes
    bc.BCryptDestroyKey.argtypes = [VP]
    bc.BCryptCloseAlgorithmProvider.argtypes = [VP, ctypes.c_ulong]
    BCRYPT_BLOCK_PADDING = 0x00000001
    alg, key = VP(), VP()
    if bc.BCryptOpenAlgorithmProvider(ctypes.byref(alg), "AES", None, 0):
        raise ValueError("Windows no deja usar AES")
    try:
        modo = "ChainingModeCBC"
        bc.BCryptSetProperty(alg, "ChainingMode", modo, (len(modo) + 1) * 2, 0)
        if bc.BCryptGenerateSymmetricKey(alg, ctypes.byref(key), None, 0, bytes(clave), len(clave), 0):
            raise ValueError("clave no válida")
        iv_buf = ctypes.create_string_buffer(bytes(iv), 16)
        fn = bc.BCryptEncrypt if cifrar else bc.BCryptDecrypt
        tam = len(datos) + (16 if cifrar else 0)
        out = ctypes.create_string_buffer(max(tam, 16))
        hecho = ctypes.c_ulong(0)
        r = fn(key, bytes(datos), len(datos), None, iv_buf, 16, out, len(out), ctypes.byref(hecho),
              BCRYPT_BLOCK_PADDING)
        bc.BCryptDestroyKey(key)
        if r:
            raise ValueError("no se pudo %s (código %d)" % ("cifrar" if cifrar else "descifrar", r))
        return out.raw[:hecho.value]
    finally:
        bc.BCryptCloseAlgorithmProvider(alg, 0)


def _cifrar_codigo(datos):
    iv = os.urandom(16)
    return _MARCA_CIFRADO + iv + _bcrypt_aes(_CLAVE_CODIGO, datos, iv, True)


def _descifrar_codigo(datos):
    if not datos.startswith(_MARCA_CIFRADO):
        raise ValueError("el archivo no está en el formato cifrado esperado")
    iv, cuerpo = datos[4:20], datos[20:]
    return _bcrypt_aes(_CLAVE_CODIGO, cuerpo, iv, False)


def _cargar_modulo_cifrado(ruta, nombre):
    """Descifra un archivo de código en memoria y lo registra como módulo, sin escribir nunca el texto
    en claro en el disco."""
    with open(ruta, "rb") as f:
        cifrado = f.read()
    texto = _descifrar_codigo(cifrado).decode("utf-8")
    import types
    mod = types.ModuleType(nombre)
    mod.__file__ = ruta
    codigo = compile(texto, ruta, "exec")
    sys.modules[nombre] = mod
    try:
        exec(codigo, mod.__dict__)
    except Exception:
        sys.modules.pop(nombre, None)
        raise
    return mod


def _nombre_extra_valido(nombre):
    n = os.path.basename(str(nombre or ""))
    ok = re.fullmatch(r"[A-Za-z0-9_]+\.py", n) and n.lower() != "contador_cofres.py"
    return n if ok else ""


def _extras_de(info):
    """Archivos de apoyo de esta versión: [(nombre, sha256, obligatorio)].
    Si version.json no los lista (publicador antiguo), se usan los de siempre, sin ser obligatorios."""
    lista = info.get("extras") if isinstance(info, dict) else None
    if not isinstance(lista, list):
        return [(n, "", False) for n in ARCHIVOS_EXTRA]
    res = []
    for x in lista:
        d = x if isinstance(x, dict) else {"archivo": x}
        n = _nombre_extra_valido(d.get("archivo"))
        if n:
            res.append((n, str(d.get("sha256") or "").lower(), True))
    return res


def _bajar_extra(nombre, sha="", timeout=40):
    """Baja un archivo de apoyo y lo comprueba (tamaño, firma y que sea Python válido)."""
    datos = _get_raw(nombre, timeout).replace(b"\r\n", b"\n")
    if len(datos) < 500:
        raise ValueError("«%s» ha llegado incompleto" % nombre)
    if sha and hashlib.sha256(datos).hexdigest() != sha:
        raise ValueError("«%s» no coincide con su firma (reintenta en unos minutos)" % nombre)
    compile(datos.decode("utf-8"), nombre, "exec")
    return datos


def _escribir_codigo(ruta, datos):
    """Guarda el código SIEMPRE cifrado: en el disco no queda nunca el texto en claro."""
    os.makedirs(os.path.dirname(ruta), exist_ok=True)
    tmp = ruta + ".tmp"
    with open(tmp, "wb") as f:
        f.write(_cifrar_codigo(datos))
    os.replace(tmp, ruta)


def _sha_de_codigo_guardado(ruta):
    """sha256 del contenido en claro de un archivo de código ya guardado (cifrado). "" si no se puede leer."""
    try:
        with open(ruta, "rb") as f:
            return hashlib.sha256(_descifrar_codigo(f.read())).hexdigest()
    except Exception:
        return ""


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
    # Archivos de apoyo (lector de repeticiones...): primero se bajan y comprueban TODOS; solo si todo está bien
    # se escribe algo, y el programa va el último, así una descarga a medias nunca deja una mezcla rota.
    extras = []
    for n, sha_x, obligatorio in _extras_de(info):
        ruta = os.path.join(CARPETA_CODIGO, n)
        if sha_x and os.path.isfile(ruta) and _sha_de_codigo_guardado(ruta) == sha_x:
            continue                        # ya lo tienes igual: no se vuelve a bajar
        try:
            extras.append((ruta, _bajar_extra(n, sha_x)))
        except Exception as e:
            if obligatorio:
                raise ValueError("no se pudo bajar «%s»: %s" % (n, e))
    for ruta, d in extras:
        _escribir_codigo(ruta, d)
    _escribir_codigo(ARCHIVO_CODIGO, datos)


def asegurar_extras():
    """Si falta algún archivo de apoyo (por ejemplo al actualizar desde una versión antigua que solo bajaba el
    programa), lo baja una vez. Si no hay internet no pasa nada: se intentará en el próximo arranque."""
    for n in ARCHIVOS_EXTRA:
        if os.path.isfile(os.path.join(CARPETA_CODIGO, n)) or os.path.isfile(os.path.join(CARPETA, n)):
            continue
        try:
            _escribir_codigo(os.path.join(CARPETA_CODIGO, n), _bajar_extra(n, "", 8))
        except Exception as e:
            registrar_error("no se pudo bajar %s: %s" % (n, e))


def _lanzar_codigo_nuevo():
    # Si hay una versión descargada más nueva que este archivo, se ejecuta esa.
    if globals().get("_ES_ACTUALIZADA"):
        return False
    try:
        if not os.path.isfile(ARCHIVO_CODIGO):
            return False
        with open(ARCHIVO_CODIGO, "rb") as f:
            texto = _descifrar_codigo(f.read()).decode("utf-8")
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
ARCHIVO_LOG = os.path.join(DATOS, "errores.log")
CARPETA_SONIDOS = os.path.join(DATOS, "sonidos")
CARPETA_DETECCIONES = os.path.join(DATOS, "detecciones")
CARPETA_FALLOS = os.path.join(DATOS, "fallos")

# Zona de la pantalla donde salen los avisos "+N PE / COFRE ..." (fracciones de la ventana del juego).
# Es una franja alta para ver TODOS los avisos a la vez (si cogés dos cofres seguidos, se apilan).
FX0, FY0, FW, FH = 0.60, 0.14, 0.19, 0.34
# El análisis se hace siempre con el texto al mismo tamaño: 84 px de ancho para el 13 % de la pantalla.
ANCHO_ANALISIS_BASE = 1456.0

INTERVALO_MS = 80
FRAMES_PARA_CONTAR = 2      # fotogramas seguidos viendo un aviso nuevo para darlo por bueno (~0,15 s)
FRAMES_PARA_REARMAR = 4     # (ya no se usa: ahora se rearma por tiempo, ver TIEMPO_REARMAR)
UMBRAL_SOSTENER = 0.62      # un aviso ya contado se mantiene con parecido >= 0,62 (en la misma posición)
TIEMPO_REARMAR = 0.30       # segundos sin ver un aviso para darlo por terminado
MAX_DETECCIONES_GUARDADAS = 25

# Detección del lobby (medido sobre tu captura): (x, y, ancho, alto) en fracciones de la ventana
LOBBY_BOTON = (0.060, 0.815, 0.150, 0.060)      # botón amarillo grande "JUGAR"
LOBBY_PASTILLA = (0.112, 0.048, 0.053, 0.034)   # pastilla gris clara "JUGAR" del menú de arriba
LOBBY_CADA = 5          # se mira el lobby cada 5 vueltas (~0,4 s)
LOBBY_CONFIRMAR = 3     # veces seguidas que hay que verlo para darlo por bueno (~1,2 s)
LOBBY_REARMAR = 4       # veces seguidas sin verlo para poder detectar otro lobby
LOBBY_GRACIA_ARRANQUE = 12.0   # si al abrir el programa ya estás en el lobby, no se cierra la partida

# Colores
BG = "#0a0e17"
CARD = "#0e1420"
PANEL = "#111826"
ORO = "#35d3f2"
ORO_OSC = "#7a879c"
TEXTO = "#eef2fa"
APAGADO = "#8791a5"
VERDE = "#3ddc84"
ROJO = "#ff5a67"
MORADO = "#35d3f2"
CIAN = "#6fd3ff"
CONTORNO = "#070a12"
TRANSPARENTE = "#010101"
COLOR_PARTIDA = "#ffb347"
AZUL = "#3b6fd9"

TAMANOS = {"Pequeño": 34, "Mediano": 54, "Grande": 80}

MAX_NUMERO = 9999999
BARRA_META_W = 300

# ---------------------------------------------------------------- teclas
# Acciones con atajo de teclado. Se puede asignar CUALQUIER tecla (o Ctrl/Alt/Mayús + tecla).
TECLAS_DEF = {"sumar": "F9", "restar": "F7", "nueva": "F8",
              "overlay": "Ninguna", "meta": "Ninguna", "mover": "Ninguna", "stats": "Ninguna",
              "manual": "Ninguna"}
ETIQUETAS_TECLA = (
    ("sumar", "Sumar +1 cofre"),
    ("restar", "Restar −1 cofre"),
    ("nueva", "Fin de partida / nueva partida"),
    ("overlay", "Mostrar / ocultar el número en pantalla"),
    ("meta", "Mostrar / ocultar la meta en pantalla"),
    ("mover", "Activar / desactivar «Mover»"),
    ("stats", "Abrir / cerrar estadísticas"),
    ("manual", "Conteo automático: encender / apagar"),
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


def nombre_por_defecto():
    n = (os.environ.get("USERNAME") or "").strip()
    return (n or "Jugador")[:20]


def nombre_epic(carpeta=None):
    """Nombre de la cuenta de Epic con la que se ha abierto Fortnite, leído del registro del juego
    (FortniteGame.log y las copias anteriores). Devuelve "" si no se encuentra."""
    try:
        base = carpeta or os.path.join(os.environ.get("LOCALAPPDATA", ""), "FortniteGame", "Saved", "Logs")
        logs = [os.path.join(base, f) for f in os.listdir(base)
                if f.lower().startswith("fortnitegame") and f.lower().endswith(".log")]
        logs.sort(key=os.path.getmtime, reverse=True)
    except OSError:
        return ""
    patron = re.compile(r"Successfully logged in user\..*?DisplayName=\[([^\]\r\n]+)\]")
    for ruta in logs[:6]:
        try:
            with open(ruta, "rb") as fh:
                txt = fh.read(8 * 1024 * 1024).decode("utf-8", "replace")      # el inicio de sesión está al principio
        except OSError:
            continue
        m = patron.findall(txt)
        if m:
            return m[-1].strip().rstrip(".").strip()[:20]
    return ""


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


def registrar_error(texto):
    """Apunta un error en errores.log (carpeta de datos) para poder revisarlo luego."""
    try:
        if os.path.isfile(ARCHIVO_LOG) and os.path.getsize(ARCHIVO_LOG) > 200000:
            os.replace(ARCHIVO_LOG, ARCHIVO_LOG + ".old")
        with open(ARCHIVO_LOG, "a", encoding="utf-8") as f:
            f.write("%s  v%s  %s\n" % (time.strftime("%Y-%m-%d %H:%M:%S"), VERSION, texto))
    except OSError:
        pass


# ---------------------------------------------------------------- iniciar con Windows
CLAVE_INICIO = r"Software\Microsoft\Windows\CurrentVersion\Run"
NOMBRE_INICIO = "ContadorDeCofres"


def _comando_inicio():
    if getattr(sys, "frozen", False):
        return '"%s"' % sys.executable
    exe = sys.executable
    pyw = os.path.join(os.path.dirname(exe), "pythonw.exe")
    if os.path.isfile(pyw):
        exe = pyw
    return '"%s" "%s"' % (exe, os.path.abspath(sys.argv[0]))


def inicio_windows_activo():
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, CLAVE_INICIO) as k:
            winreg.QueryValueEx(k, NOMBRE_INICIO)
        return True
    except Exception:
        return False


def poner_inicio_windows(activar):
    """Añade o quita el programa del arranque de Windows. Devuelve True si se pudo."""
    try:
        import winreg
        with winreg.CreateKey(winreg.HKEY_CURRENT_USER, CLAVE_INICIO) as k:
            if activar:
                winreg.SetValueEx(k, NOMBRE_INICIO, 0, winreg.REG_SZ, _comando_inicio())
            else:
                try:
                    winreg.DeleteValue(k, NOMBRE_INICIO)
                except FileNotFoundError:
                    pass
        return True
    except Exception:
        return False


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


# ---------------------------------------------------------------- zona horaria
# (horas respecto a UTC en invierno, regla de horario de verano)
ZONAS = {
    "España (Península)": (1, "eu"),
    "Canarias / Portugal / Reino Unido": (0, "eu"),
    "Europa del Este (Atenas)": (2, "eu"),
    "México (Centro)": (-6, None),
    "Colombia / Perú / Ecuador": (-5, None),
    "Argentina / Uruguay / Brasil": (-3, None),
    "Nueva York (EE. UU. Este)": (-5, "us"),
    "Los Ángeles (EE. UU. Oeste)": (-8, "us"),
    "UTC": (0, None),
}
ZONA_AUTO = "Automática (la de este PC)"
ZONA_DEF = "España (Península)"
OPCIONES_ZONA = [ZONA_AUTO] + list(ZONAS)
_zona = [ZONA_DEF]


def poner_zona(nombre):
    _zona[0] = nombre if (nombre == ZONA_AUTO or nombre in ZONAS) else ZONA_DEF


def nombre_zona():
    return _zona[0]


def etiqueta_zona():
    return "hora de este PC" if _zona[0] == ZONA_AUTO else "hora: " + _zona[0]


@lru_cache(maxsize=32)
def _limites_dst(anio, regla, base):
    """Inicio y fin del horario de verano (marcas UTC). UE: último domingo de marzo a último
    de octubre, 01:00 UTC. EE. UU.: segundo domingo de marzo a primer domingo de noviembre, 02:00 locales."""
    def domingo(mes, n):
        if n == -1:
            d = date(anio, mes, 31)
            while d.weekday() != 6:
                d -= timedelta(days=1)
            return d.day
        d = date(anio, mes, 1)
        while d.weekday() != 6:
            d += timedelta(days=1)
        return d.day + 7 * (n - 1)

    if regla == "us":
        ini = calendar.timegm((anio, 3, domingo(3, 2), 2 - base, 0, 0))
        fin = calendar.timegm((anio, 11, domingo(11, 1), 2 - (base + 1), 0, 0))
        return ini, fin
    return (calendar.timegm((anio, 3, domingo(3, -1), 1, 0, 0)),
            calendar.timegm((anio, 10, domingo(10, -1), 1, 0, 0)))


def a_madrid(ts):
    """Marca de tiempo (UTC) -> fecha y hora en la zona elegida (sin zona). El nombre se mantiene
    por compatibilidad, pero ya no es siempre la hora de España."""
    z = _zona[0]
    if z == ZONA_AUTO:
        try:
            return datetime.fromtimestamp(ts)
        except (OverflowError, OSError, ValueError):
            z = ZONA_DEF
    base, regla = ZONAS[z]
    dt = datetime.fromtimestamp(ts, timezone.utc)
    horas = base
    if regla:
        ini, fin = _limites_dst(dt.year, regla, base)
        if ini <= ts < fin:
            horas += 1
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

    def deshacer_cierre(self):
        """Reabre la última partida guardada (por si se cerró sin querer). Si ya has empezado
        otra, sus cofres se juntan con los de la reabierta."""
        if not self.partidas:
            return False
        ultima = self.partidas.pop()
        self.actual = ultima + self.actual
        self.version += 1
        self.guardar()
        return True

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
    usadas = set()
    i = 0
    while i < len(bandas) - 1:
        A, B = bandas[i], bandas[i + 1]
        hueco = B["y0"] - A["y1"] - 1
        info = {"y": A["y0"], "l1": A["n"], "l2": B["n"], "hA": A["h"], "hB": B["h"],
                "wA": A["cmax"] - A["cmin"] + 1, "wB": B["cmax"] - B["cmin"] + 1, "hueco": hueco,
                "tA": A["tramos"], "tB": B["tramos"], "dx": B["cmin"] - A["cmin"], "cofre": 0.0}
        info["yb"] = B["y0"]
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
            usadas.update((i, i + 1))
            i += 2
        else:
            if depurar:
                avisos.append(info)
            i += 1
    if not depurar:
        # Red de seguridad: una línea suelta que parece «COFRE ...» aunque no encaje en una pareja
        # (por ejemplo, cuando otro aviso de experiencia está pegado y se funden las líneas).
        for k, C in enumerate(bandas):
            if k in usadas:
                continue
            wc = C["cmax"] - C["cmin"] + 1
            if not (6 <= C["h"] <= 28 and 30 <= wc <= 330 and C["n"] >= 80
                    and 0.15 <= C["n"] / float(wc * C["h"]) <= 0.9):
                continue
            if any(abs(a.get("yb", a.get("yc", -999)) - C["y0"]) <= 12 for a in avisos):
                continue
            n_arriba, _ = _region(datos, w, h, C["cmin"] - 14, C["cmax"] + 14, C["y0"] - 34, C["y0"] - 1)
            if n_arriba < 40:
                continue
            if F is None:
                gris = img.convert("L").point(_L_CONTRASTE)
                F = ImageChops.multiply(gris, m.filter(ImageFilter.MaxFilter(7)).point(_L_BIN))
            clave = (C["y0"], C["cmin"], C["cmax"], C["n"] // 15)
            ahora = time.time()
            c = _CACHE_COFRE.get(clave)
            if c is not None and ahora - c[0] < 1.0:
                sc = c[1]
            else:
                sc = puntuacion_cofre(F, C["cmin"] - 2, C["y0"], C["cmax"])
                if len(_CACHE_COFRE) > 40:
                    _CACHE_COFRE.clear()
                _CACHE_COFRE[clave] = (ahora, sc)
            if sc >= UMBRAL_COFRE:
                avisos.append({"y": max(0, C["y0"] - 30), "yb": C["y0"], "l1": n_arriba, "l2": C["n"],
                               "cofre": sc, "suelta": True, "ok": True})
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


def y_cofre(a):
    """Posición vertical de un aviso (para reconocer el mismo aviso de un fotograma al siguiente)."""
    for k in ("yc", "yb", "y"):
        if k in a:
            return a[k]
    return 0


# --- aviso APILADO: cuando abres varios cofres seguidos el juego los junta en una sola lista ------
#       +5750 PE
#       COFRE RARO
#       ESPÍRITU AL MÁXIMO
#       COFRE DE ESPÍRITU
#       COFRE RARO X3          <- «X3» = tres cofres de ese tipo
#       MUNICIÓN MÁXIMA
# Se cuentan las líneas que EMPIEZAN por «COFRE» (sumando el multiplicador «X3», «X2»...) y se
# ignoran las demás (munición, espíritu...).
DIG_W, DIG_H = 10, 14
_DIGITOS_PLANT = []


def _plantillas_digitos():
    """Dígitos 2-9 dibujados con fuentes gruesas de Windows (rectas e inclinadas), para reconocer
    el número del «X3». Impact se parece mucho a la letra del juego. Si no hay ninguna fuente
    disponible, devuelve vacío y se asume «X2»."""
    if _DIGITOS_PLANT:
        return _DIGITOS_PLANT[0]
    res = {}
    try:
        from PIL import ImageFont
        fuentes = []
        for nombre in ("impact.ttf", "arialbi.ttf", "arialbd.ttf", "ariblk.ttf", "segoeuib.ttf"):
            try:
                fuentes.append(ImageFont.truetype(nombre, 48))
            except Exception:
                continue
        for d in range(2, 10):
            variantes = []
            for fu in fuentes:
                im = Image.new("L", (96, 80), 0)
                ImageDraw.Draw(im).text((20, 8), str(d), font=fu, fill=255)
                for sh in (0.0, 0.22):          # recto e inclinado (cursiva)
                    im2 = im if sh == 0 else im.transform(im.size, Image.AFFINE, (1, sh, -sh * 40, 0, 1, 0),
                                                          Image.BILINEAR)
                    bb = im2.getbbox()
                    if bb:
                        variantes.append(list(im2.crop(bb).resize((DIG_W, DIG_H), Image.BILINEAR).tobytes()))
            if variantes:
                res[d] = variantes
    except Exception:
        res = {}
    _DIGITOS_PLANT.append(res)
    return res


def _ncc_listas(a, b):
    n = len(a)
    ma = sum(a) / float(n)
    mb = sum(b) / float(n)
    va = sum(map(mul, a, a)) / float(n) - ma * ma
    vb = sum(map(mul, b, b)) / float(n) - mb * mb
    if va <= 1e-6 or vb <= 1e-6:
        return 0.0
    return (sum(map(mul, a, b)) / float(n) - ma * mb) / math.sqrt(va * vb)


def _leer_digito(m, x0, x1, y0, y1):
    """Reconoce el dígito (2-9) que hay en ese rectángulo de la máscara. None si no se fía."""
    plant = _plantillas_digitos()
    if not plant:
        return None
    c = m.crop((max(0, x0), y0, x1 + 1, y1 + 1))
    bb = c.getbbox()
    if not bb:
        return None
    v = list(c.crop(bb).resize((DIG_W, DIG_H), Image.BILINEAR).tobytes())
    mejor, mejor_d = 0.0, None
    for d, variantes in plant.items():
        for t in variantes:
            s = _ncc_listas(v, t)
            if s > mejor:
                mejor, mejor_d = s, d
    return mejor_d if mejor >= 0.40 else None


def _multiplicador_linea(m, B):
    """1 si la línea no lleva «X3» al final; si lo lleva, el número (2 si no se puede leer)."""
    w = m.size[0]
    bh = B["h"]
    bd = m.crop((0, B["y0"], w, B["y1"] + 1)).transpose(Image.TRANSPOSE).tobytes()
    cuenta = [bd[x * bh:(x + 1) * bh].count(255) for x in range(w)]
    palabras = _tramos([c > 0 for c in cuenta], max(2, int(bh * 0.28)))
    if len(palabras) < 2:
        return 1
    ini, fin = palabras[-1]
    ancho = fin - ini + 1
    if ancho > 2.2 * bh or ancho < 0.8 * bh:
        return 1                         # la última palabra es una palabra normal, no «X3»
    glifos = _tramos([c > 0 for c in cuenta[ini:fin + 1]], 0)
    if len(glifos) >= 2:
        gi, gf = glifos[-1]
        x0, x1 = ini + gi, ini + gf
    else:
        x0, x1 = ini + int(ancho * 0.5), fin
    d = _leer_digito(m, x0, x1, B["y0"], B["y1"])
    return d if d and d >= 2 else 2


def buscar_lista_cofres(img):
    """Aviso apilado de varios cofres. Devuelve None si no hay ninguna línea «COFRE...»; si la hay:
    {"n": cofres en total, "lineas": líneas de cofre, "activo": True si es un aviso apilado de verdad}."""
    m = mascara_aviso(img)
    bandas = _bandas_mascara(m)
    if len(bandas) < 2:
        return None
    cab = None
    lineas = []
    for i, A in enumerate(bandas):
        wa = A["cmax"] - A["cmin"] + 1
        if not (8 <= A["h"] <= 34 and A["n"] >= 40 and A["tramos"] >= 3 and 20 <= wa <= 220):
            continue
        cand = []
        prev = A
        for B in bandas[i + 1:]:
            if B["y0"] - prev["y1"] - 1 > 12:
                break
            wb = B["cmax"] - B["cmin"] + 1
            if 5 <= B["h"] <= 30 and B["n"] >= 40 and 20 <= wb <= 330 and abs(B["cmin"] - A["cmin"]) <= 70:
                cand.append(B)
            prev = B
        if cand:
            cab, lineas = A, cand
            break
    if cab is None:
        return None
    F = None
    cofres = 0
    n_lineas = 0
    for B in lineas:
        if F is None:
            gris = img.convert("L").point(_L_CONTRASTE)
            F = ImageChops.multiply(gris, m.filter(ImageFilter.MaxFilter(7)).point(_L_BIN))
        clave = ("L", B["y0"], B["cmin"], B["cmax"], B["n"] // 15)
        ahora = time.time()
        c = _CACHE_COFRE.get(clave)
        if c is not None and ahora - c[0] < 1.0:
            sc = c[1]
        else:
            # «COFRE» puede estar en CUALQUIER punto de la línea (al principio, en medio o al final)
            if B["cmax"] - B["cmin"] + 1 < PLANTILLA_COFRE_TAM[0] - 6:
                sc = 0.0                  # demasiado corta para contener la palabra
            else:
                sc = puntuacion_cofre(F, B["cmin"] - 2, B["y0"], B["cmax"])
            if len(_CACHE_COFRE) > 60:
                _CACHE_COFRE.clear()
            _CACHE_COFRE[clave] = (ahora, sc)
        if sc >= UMBRAL_COFRE:
            n_lineas += 1
            cofres += _multiplicador_linea(m, B)
    if n_lineas == 0:
        return None
    return {"n": cofres, "lineas": n_lineas, "activo": (len(lineas) >= 2 or cofres > n_lineas)}


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


# ---------------------------------------------------------------- lector de texto (OCR de Windows)
# Además de comparar el aviso con la plantilla de la palabra «COFRE», el programa LEE el aviso con
# el reconocedor de texto que trae Windows 10/11 (no hay que instalar nada). Con eso:
#   · cuenta cualquier línea con la palabra COFRE («COFRE», «COFRE RARO», «COFRE DE ESPÍRITU»...)
#   · NO cuenta las demás («ELIMINACIÓN», «CAJA DE MUNICIÓN», «MUNICIÓN MÁXIMA»...)
#   · sigue cada línea por separado: cuando su «X2» pasa a «X3» suma uno, sin tener que acertar la cifra
# Si el PC no tiene ese reconocedor, todo sigue funcionando con el detector de siempre.
class _GUID(ctypes.Structure):
    _fields_ = [("a", ctypes.c_uint32), ("b", ctypes.c_uint16), ("c", ctypes.c_uint16),
                ("d", ctypes.c_ubyte * 8)]


def _guid(texto):
    h = texto.replace("-", "")
    g = _GUID(int(h[0:8], 16), int(h[8:12], 16), int(h[12:16], 16))
    for i in range(8):
        g.d[i] = int(h[16 + 2 * i:18 + 2 * i], 16)
    return g


class _RectF(ctypes.Structure):
    _fields_ = [("x", ctypes.c_float), ("y", ctypes.c_float), ("w", ctypes.c_float), ("h", ctypes.c_float)]


class ErrorOCR(Exception):
    pass


_PV = ctypes.POINTER(ctypes.c_void_p)


def _vt(p, n, *tipos):
    """Función número n de la tabla de un objeto de Windows (COM)."""
    tabla = ctypes.cast(p, ctypes.POINTER(ctypes.POINTER(ctypes.c_void_p)))[0]
    return ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_void_p, *tipos)(tabla[n])


def _exigir(hr, que=""):
    if hr < 0:
        raise ErrorOCR("%s (0x%08X)" % (que, hr & 0xFFFFFFFF))


def _soltar(p):
    try:
        if p:
            _vt(p, 2)(p)
    except Exception:
        pass


class MotorOCR:
    """Windows.Media.Ocr llamado directamente con ctypes. Hay que crearlo y usarlo en el mismo hilo."""

    IDIOMAS = ("es-ES", "es-MX", "es", "en-US", "en-GB", "en", "pt-BR", "pt-PT", "fr-FR", "it-IT", "de-DE")
    GRIS8 = 62

    def __init__(self):
        cb = self.cb = ctypes.WinDLL("combase")
        cb.RoInitialize.argtypes = [ctypes.c_int]
        cb.RoInitialize.restype = ctypes.c_long
        cb.WindowsCreateString.argtypes = [ctypes.c_wchar_p, ctypes.c_uint32, _PV]
        cb.WindowsCreateString.restype = ctypes.c_long
        cb.WindowsDeleteString.argtypes = [ctypes.c_void_p]
        cb.WindowsDeleteString.restype = ctypes.c_long
        cb.WindowsGetStringRawBuffer.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_uint32)]
        cb.WindowsGetStringRawBuffer.restype = ctypes.c_void_p
        cb.RoGetActivationFactory.argtypes = [ctypes.c_void_p, ctypes.POINTER(_GUID), _PV]
        cb.RoGetActivationFactory.restype = ctypes.c_long
        cb.RoInitialize(1)
        self._iid_info = _guid("00000036-0000-0000-c000-000000000046")
        self.f_bufer = self._fabrica("Windows.Security.Cryptography.CryptographicBuffer",
                                     "320b7e22-3cb0-4cdf-8663-1d28910065eb")
        self.f_bitmap = self._fabrica("Windows.Graphics.Imaging.SoftwareBitmap",
                                      "df0385db-672f-4a9d-806e-c2442f343e86")
        f_ocr = self._fabrica("Windows.Media.Ocr.OcrEngine", "5bffa85a-3384-3540-9940-699120d428a8")
        f_idioma = self._fabrica("Windows.Globalization.Language", "9b0252ac-0c27-44f8-b792-9793fb66c63e")
        self.motor = None
        self.idioma = ""
        try:
            for tag in self.IDIOMAS:
                leng = ctypes.c_void_p()
                h = self._cadena(tag)
                try:
                    hr = _vt(f_idioma, 6, ctypes.c_void_p, _PV)(f_idioma, h, ctypes.byref(leng))
                finally:
                    cb.WindowsDeleteString(h)
                if hr < 0 or not leng:
                    continue
                m = ctypes.c_void_p()
                hr = _vt(f_ocr, 9, ctypes.c_void_p, _PV)(f_ocr, leng, ctypes.byref(m))
                _soltar(leng)
                if hr >= 0 and m:
                    self.motor, self.idioma = m, tag
                    break
            if self.motor is None:        # ninguno de la lista: el idioma que tenga Windows
                m = ctypes.c_void_p()
                if _vt(f_ocr, 10, _PV)(f_ocr, ctypes.byref(m)) >= 0 and m:
                    self.motor, self.idioma = m, "el de Windows"
        finally:
            _soltar(f_ocr)
            _soltar(f_idioma)
        if self.motor is None:
            raise ErrorOCR("Windows no tiene instalado ningún idioma de reconocimiento de texto")

    def _cadena(self, texto):
        h = ctypes.c_void_p()
        _exigir(self.cb.WindowsCreateString(texto, len(texto), ctypes.byref(h)), "cadena")
        return h

    def _fabrica(self, clase, iid):
        f = ctypes.c_void_p()
        h = self._cadena(clase)
        try:
            _exigir(self.cb.RoGetActivationFactory(h, ctypes.byref(_guid(iid)), ctypes.byref(f)), clase)
        finally:
            self.cb.WindowsDeleteString(h)
        return f

    def _texto(self, p, indice):
        h = ctypes.c_void_p()
        _exigir(_vt(p, indice, _PV)(p, ctypes.byref(h)), "texto")
        try:
            n = ctypes.c_uint32(0)
            ptr = self.cb.WindowsGetStringRawBuffer(h, ctypes.byref(n))
            return ctypes.wstring_at(ptr, n.value) if (ptr and n.value) else ""
        finally:
            self.cb.WindowsDeleteString(h)

    def leer(self, datos, ancho, alto, espera=1.5):
        """datos = imagen en gris (1 byte por píxel). Devuelve una lista de líneas; cada línea es una
        lista de palabras (texto, x, y, ancho, alto)."""
        buf = ctypes.c_void_p()
        bmp = ctypes.c_void_p()
        op = ctypes.c_void_p()
        info = ctypes.c_void_p()
        res = ctypes.c_void_p()
        lineas = ctypes.c_void_p()
        try:
            _exigir(_vt(self.f_bufer, 9, ctypes.c_uint32, ctypes.c_char_p, _PV)(
                self.f_bufer, len(datos), datos, ctypes.byref(buf)), "búfer")
            _exigir(_vt(self.f_bitmap, 9, ctypes.c_void_p, ctypes.c_int, ctypes.c_int, ctypes.c_int, _PV)(
                self.f_bitmap, buf, self.GRIS8, ancho, alto, ctypes.byref(bmp)), "imagen")
            _exigir(_vt(self.motor, 6, ctypes.c_void_p, _PV)(self.motor, bmp, ctypes.byref(op)), "reconocer")
            _exigir(_vt(op, 0, ctypes.POINTER(_GUID), _PV)(op, ctypes.byref(self._iid_info), ctypes.byref(info)),
                "seguimiento")
            estado = ctypes.c_int(0)
            fin = time.time() + espera
            while True:
                _exigir(_vt(info, 7, ctypes.POINTER(ctypes.c_int))(info, ctypes.byref(estado)), "estado")
                if estado.value != 0:
                    break
                if time.time() > fin:
                    raise ErrorOCR("el reconocedor tarda demasiado")
                time.sleep(0.002)
            if estado.value != 1:
                raise ErrorOCR("el reconocedor no pudo leer la imagen (estado %d)" % estado.value)
            _exigir(_vt(op, 8, _PV)(op, ctypes.byref(res)), "resultado")
            _exigir(_vt(res, 6, _PV)(res, ctypes.byref(lineas)), "líneas")
            n = ctypes.c_uint32(0)
            _exigir(_vt(lineas, 7, ctypes.POINTER(ctypes.c_uint32))(lineas, ctypes.byref(n)), "número de líneas")
            out = []
            for i in range(n.value):
                lin = ctypes.c_void_p()
                _exigir(_vt(lineas, 6, ctypes.c_uint32, _PV)(lineas, i, ctypes.byref(lin)), "línea")
                try:
                    out.append(self._palabras(lin))
                finally:
                    _soltar(lin)
            return out
        finally:
            for p in (lineas, res, info, op, bmp, buf):
                _soltar(p)

    def _palabras(self, lin):
        pal = ctypes.c_void_p()
        out = []
        _exigir(_vt(lin, 6, _PV)(lin, ctypes.byref(pal)), "palabras")
        try:
            n = ctypes.c_uint32(0)
            _exigir(_vt(pal, 7, ctypes.POINTER(ctypes.c_uint32))(pal, ctypes.byref(n)), "número de palabras")
            for i in range(n.value):
                w = ctypes.c_void_p()
                _exigir(_vt(pal, 6, ctypes.c_uint32, _PV)(pal, i, ctypes.byref(w)), "palabra")
                try:
                    r = _RectF()
                    _exigir(_vt(w, 6, ctypes.POINTER(_RectF))(w, ctypes.byref(r)), "posición")
                    out.append((self._texto(w, 7), r.x, r.y, r.w, r.h))
                finally:
                    _soltar(w)
        finally:
            _soltar(pal)
        return out


class HiloOCR(threading.Thread):
    """El reconocedor va en su propio hilo: si alguna vez se atasca, la ventana no se queda colgada."""

    def __init__(self):
        super().__init__(daemon=True)
        self.estado = "iniciando"      # iniciando / ok / no
        self.motivo = ""
        self.idioma = ""
        self.fallos = 0
        self.ocupado = False
        self._pet = None
        self._res = None
        self._n = 0
        self._hay = threading.Event()
        self._hecho = threading.Event()

    def run(self):
        try:
            motor = MotorOCR()
            self.idioma = motor.idioma
            self.estado = "ok"
        except Exception as e:
            self.motivo = str(e) or type(e).__name__
            self.estado = "no"
            return
        while self.estado == "ok":
            self._hay.wait()
            self._hay.clear()
            pet = self._pet
            if pet is None:
                continue
            ident, datos, w, h = pet
            res = None
            try:
                res = motor.leer(datos, w, h)
                self.fallos = 0
            except Exception as e:
                self.fallos += 1
                self.motivo = str(e) or type(e).__name__
                if self.fallos >= 8:
                    self.estado = "no"
            self._res = (ident, res)
            self.ocupado = False
            self._hecho.set()

    def pedir(self, datos, w, h):
        """Encarga una lectura. Devuelve su número, o None si el reconocedor está ocupado o no existe."""
        if self.estado != "ok" or self.ocupado:
            return None
        self._n += 1
        self._hecho.clear()
        self.ocupado = True
        self._pet = (self._n, datos, w, h)
        self._hay.set()
        return self._n

    def recoger(self, ident, espera=0.0):
        """(True, líneas) si esa lectura ya ha terminado (líneas = None si falló); (False, None) si
        todavía no. Con «espera» aguarda como mucho ese tiempo: así la ventana nunca se queda colgada."""
        if espera > 0:
            self._hecho.wait(espera)
        r = self._res
        if r and r[0] == ident:
            return True, r[1]
        return False, None


# --- interpretar lo leído ---------------------------------------------------------------------
_SIN_TILDES = str.maketrans("ÁÀÄÂÃÉÈËÊÍÌÏÎÓÒÖÔÕÚÙÜÛÑÇ", "AAAAAEEEEIIIIOOOOOUUUUNC")
_CIFRA_A_LETRA = str.maketrans("01358", "OIESB")
_LETRA_A_CIFRA = str.maketrans("OQDILZSBG", "000112586")
PALABRA_COFRE = "COFRE"
# letras que el OCR confunde entre sí: se acepta «COFRE» aunque lea mal UNA de ellas
_CONFUSIONES = {"C": "GOQ", "O": "QDUCG", "F": "EPT", "R": "PKBAH", "E": "FBCL"}
# «X3» tal y como puede leerlo el OCR: a veces confunde la cifra con una letra («XA», «XE»...)
_RE_MULT = re.compile(r"[X×][0-9A-Z]{0,2}$")
_RE_CIFRAS = re.compile(r"[0-9OQDILZSBG]{1,2}$")
_RE_CABECERA = re.compile(r"\bP ?E\b")


def normalizar_texto(t):
    return (t or "").upper().translate(_SIN_TILDES)


def es_palabra_cofre(tok):
    """¿Es la palabra COFRE (o COFRES), aunque el OCR haya leído mal una letra?"""
    t = tok.replace("×", "X").translate(_CIFRA_A_LETRA)
    p = PALABRA_COFRE
    if t == p + "S":
        return True
    if t == p:
        return True
    if len(t) == len(p):
        dif = [i for i in range(len(p)) if t[i] != p[i]]
        return len(dif) == 1 and t[dif[0]] in _CONFUSIONES.get(p[dif[0]], "")
    if len(t) == len(p) - 1:              # le falta una letra
        return any(p[:i] + p[i + 1:] == t for i in range(len(p)))
    if len(t) == len(p) + 1:              # le sobra una letra
        return any(t[:i] + t[i + 1:] == p for i in range(len(t)))
    return False


def se_parece_a_cofre(tok):
    """Parecido flojo: sirve para NO dar por «otra cosa» una línea que quizá sea COFRE mal leído."""
    t = tok.replace("×", "X").translate(_CIFRA_A_LETRA)
    if not (3 <= len(t) <= 8):
        return False
    p = PALABRA_COFRE
    tabla = [[0] * (len(p) + 1) for _ in range(len(t) + 1)]
    for i in range(len(t)):
        for j in range(len(p)):
            tabla[i + 1][j + 1] = tabla[i][j] + 1 if t[i] == p[j] else max(tabla[i][j + 1], tabla[i + 1][j])
    return tabla[-1][-1] >= 3


def es_cabecera(norm):
    """La línea de arriba del aviso: «+600 PE»."""
    return bool(re.search(r"\d", norm)) and ("+" in norm or bool(_RE_CABECERA.search(norm)))


def _buscar_cofre(toks):
    """toks = palabras de una línea (en mayúsculas, sin tildes ni signos).
    Devuelve (índice de la palabra COFRE, cuántas palabras ocupa, índice donde acaba el nombre,
    multiplicador leído o None, True si al final hay algo con pinta de «X3»). Sin COFRE: (None, ...)."""
    i_c, ocupa = None, 1
    pegado = ""
    for i, t in enumerate(toks):
        if es_palabra_cofre(t):
            i_c = i
            break
        for corte in (5, 4, 6):               # el OCR pegó el multiplicador a la palabra: «COFREX3»
            if len(t) > corte and es_palabra_cofre(t[:corte]) and _RE_MULT.match(t[corte:]):
                i_c, pegado = i, t[corte:]
                break
        if i_c is not None:
            break
        if i + 1 < len(toks) and 1 <= len(t) <= 4 and 1 <= len(toks[i + 1]) <= 4 \
                and es_palabra_cofre(t + toks[i + 1]) and (t + toks[i + 1]).translate(_CIFRA_A_LETRA) == PALABRA_COFRE:
            i_c, ocupa = i, 2             # el OCR la partió en dos: «CO FRE»
            break
    if i_c is None:
        return None, 1, 0, None, False
    fin = len(toks)
    cola = [pegado] if pegado else []
    while fin > i_c + ocupa:
        t = toks[fin - 1]
        if _RE_MULT.match(t):
            cola.insert(0, t)
            fin -= 1
        elif _RE_CIFRAS.match(t) and fin - 2 >= i_c + ocupa and _RE_MULT.match(toks[fin - 2]):
            cola.insert(0, t)
            fin -= 1
        else:
            break
    n = None
    if cola:
        d = "".join(cola).replace("×", "X")
        d = d[1:].translate(_LETRA_A_CIFRA) if d[:1] == "X" else ""
        if d.isdigit() and 2 <= int(d) <= 99:
            n = int(d)
    return i_c, ocupa, fin, n, bool(cola)


# --- la imagen que se le da al OCR: solo el relleno lila de las letras del aviso ---------------
def _rampa(a, b):
    return [0 if v <= a else 255 if v >= b else int((v - a) * 255.0 / (b - a)) for v in range(256)]


_T_B = _rampa(198, 222)
_T_R = [min(x, 255 - y) for x, y in zip(_rampa(150, 172), _rampa(246, 254))]
_T_G = [min(x, 255 - y) for x, y in zip(_rampa(115, 138), _rampa(222, 234))]
_T_BG = _rampa(24, 42)
_T_RG = _rampa(2, 14)
_L_T96 = _lut(lambda v: v >= 96)
_L_NO0 = _lut(lambda v: v > 0)


def _engordar(mascara, radio):
    """Ensancha lo blanco de una máscara «radio» píxeles (más rápido que MaxFilter en tamaños grandes)."""
    return mascara.filter(ImageFilter.BoxBlur(radio)).point(_L_NO0)


def _mascara_base(img):
    """Primera pasada (rápida). Devuelve (lila claro pegado a un borde morado, borde morado)."""
    r, g, b = img.convert("RGB").split()
    oscuro = ImageChops.darker
    mul_ = ImageChops.multiply
    bg = ImageChops.subtract(b, g)
    m = oscuro(oscuro(b.point(_T_B), r.point(_T_R)), g.point(_T_G))
    m = oscuro(oscuro(m, bg.point(_T_BG)), ImageChops.subtract(r, g).point(_T_RG))
    borde = mul_(mul_(b.point(_L_B170), bg.point(_L_BG85)),
                 mul_(r.point(_L_R70_200), ImageChops.subtract(b, r).point(_L_BR30)))
    return mul_(m, _engordar(borde, 4)), borde


def _afinar_mascara(m, borde):
    """Segunda pasada: deja solo el RELLENO de las letras.
    Sobre un fondo claro (cielo, nieve...), el filo exterior del borde morado se mezcla con el fondo
    y también sale lila: un cerco de 1 píxel alrededor de cada letra que las engorda y las pega. El
    relleno de verdad nunca toca el fondo (lo separa el borde), así que se quita todo el lila que
    esté pegado a algo que no sea ni lila ni morado."""
    fuera = ImageChops.invert(ImageChops.lighter(m.point(_L_T96), borde))
    return ImageChops.multiply(m, ImageChops.invert(_engordar(fuera, 1)))


def mascara_texto(img):
    """Cuánto tiene cada píxel del relleno lila de las letras del aviso (0-255), con los bordes suaves:
    el OCR ve letras limpias sobre fondo liso, sin el paisaje del juego detrás."""
    return _afinar_mascara(*_mascara_base(img))


def _caja_tinta(m, x0, y0, x1, y1):
    """Caja ajustada de lo que hay «pintado» en la máscara dentro de un rectángulo (o None)."""
    x0, y0 = max(0, int(math.floor(x0))), max(0, int(math.floor(y0)))
    x1, y1 = min(m.width, int(math.ceil(x1))), min(m.height, int(math.ceil(y1)))
    if x1 - x0 < 2 or y1 - y0 < 2:
        return None
    bb = m.crop((x0, y0, x1, y1)).point(_L_T96).getbbox()
    if not bb:
        return None
    return (x0 + bb[0], y0 + bb[1], x0 + bb[2], y0 + bb[3])


def _empieza_por_x(datos, w, h, x0, hc):
    """¿Lo pintado a partir de la columna x0 empieza por una «X»? Una X es la única letra con dos
    trazos separados arriba, dos abajo y, a media altura, uno solo, estrecho y centrado. No depende
    del tipo de letra, y vale aunque la X toque a la cifra que lleva detrás."""
    tope = min(w, x0 + int(1.3 * hc) + 2)
    filas = [y for y in range(h) if any(datos[y * w + x] for x in range(x0, tope))]
    if len(filas) < 6:
        return False
    y0 = filas[0]
    ch = filas[-1] - y0 + 1
    for ancho in range(max(4, int(0.6 * hc)), int(1.3 * hc) + 2):
        x1 = min(w, x0 + ancho)
        cw = float(x1 - x0)

        def trozos(fr):
            y = y0 + min(ch - 1, max(0, int(round(fr * (ch - 1)))))
            return _tramos([datos[y * w + x] for x in range(x0, x1)], 0)

        if not any(len(trozos(f)) == 2 for f in (0.0, 0.08, 0.16)):
            continue
        if not any(len(trozos(f)) == 2 for f in (0.84, 0.92, 1.0)):
            continue
        for f in (0.42, 0.5, 0.58):
            t = trozos(f)
            if len(t) == 1:
                a, b = t[0]
                if a >= 0.18 * cw and (b + 1) <= 0.88 * cw and (b - a + 1) <= 0.62 * cw:
                    return True
    return False


def _medir_cofre(m, palabras, i, ocupa, o):
    """Añade a la línea «o» la firma de la palabra COFRE y la del multiplicador («X3»), si lo lleva.
    La firma es el dibujo reducido de esas letras: sirve para saber si la cifra ha cambiado de un
    fotograma al siguiente sin necesidad de reconocerla (el OCR falla a menudo con «X2», «X3»...).
    El multiplicador se busca por su forma (una «X» seguida de algo, al final de la línea), no por
    lo que haya leído el OCR."""
    pc = palabras[i:i + ocupa]
    c = _caja_tinta(m, min(p[1] for p in pc) - 2, min(p[2] for p in pc) - 2,
                    max(p[1] + p[3] for p in pc) + 2, max(p[2] + p[4] for p in pc) + 2)
    if c is None:
        return
    cx0, cy0, cx1, cy1 = c
    hc = cy1 - cy0
    if hc < 5 or cx1 - cx0 < 2 * hc:
        return
    o["y"] = (cy0 + cy1) / 2.0
    o["h"] = float(hc)
    # las primeras letras («COF»): si esto cambia es que la línea entera se mueve o se apaga
    o["fn"] = m.crop((cx0, cy0, min(m.width, cx0 + int(2.2 * hc)), cy1)).resize((32, 16), Image.BILINEAR).tobytes()
    # la franja de la línea, desde donde empieza COFRE hasta donde acaba lo pintado
    ry0, ry1 = max(0, cy0 - 1), min(m.height, cy1 + 1)
    reg = m.crop((cx0, ry0, min(m.width, cx0 + int(16 * hc)), ry1)).point(_L_T96)
    rw, rh = reg.size
    datos = reg.tobytes()
    cols = [any(datos[y * rw + x] for y in range(rh)) for x in range(rw)]
    grupos = _tramos(cols, int(hc))
    if not grupos or grupos[0][0] > 2:
        return
    fin_linea = grupos[0][1]
    o["ancho"] = (fin_linea + 1) / float(hc)
    for a, _b in _tramos(cols[:fin_linea + 1], 0):
        tw = fin_linea - a + 1
        if a < 2.2 * hc or tw > 4.0 * hc:
            continue                         # todavía dentro de la palabra COFRE, o queda demasiado detrás
        if tw < 1.15 * hc:
            break                            # ya no cabe una «X» con su cifra
        if _empieza_por_x(datos, rw, rh, a, hc):
            filas = [y for y in range(rh) if any(datos[y * rw + x] for x in range(a, fin_linea + 1))]
            o["ancho"] = a / float(hc)
            o["ta"] = tw / float(hc)
            o["nd"] = 1 if tw < 2.45 * hc else 2
            # la firma es solo el final (la última cifra, que es la que cambia siempre): la X no cambia
            corte = 0.58 if o["nd"] == 1 else 0.70
            o["fm"] = m.crop((cx0 + a + int(corte * tw), ry0 + filas[0], cx0 + fin_linea + 1,
                              ry0 + filas[-1] + 1)).resize((20, 20), Image.BILINEAR).tobytes()
            break


def interpretar_lectura(m, lineas):
    """Convierte lo que ha leído el OCR (palabras con su posición, en coordenadas de la máscara m)
    en líneas del aviso: cuáles son de cofre, cuáles la cabecera «+N PE» y cuáles otra cosa."""
    obs = []
    for palabras in lineas:
        palabras = sorted((p for p in palabras if p[0] and p[0].strip()), key=lambda p: p[1])
        if not palabras:
            continue
        texto = " ".join(p[0].strip() for p in palabras)
        norm = normalizar_texto(texto)
        if len(re.findall(r"[A-Z0-9]", norm)) < 2:
            continue
        x0 = min(p[1] for p in palabras)
        y0 = min(p[2] for p in palabras)
        x1 = max(p[1] + p[3] for p in palabras)
        y1 = max(p[2] + p[4] for p in palabras)
        alto = float(max(1.0, y1 - y0))
        toks = [re.sub(r"[^A-Z0-9×]", "", normalizar_texto(p[0])) for p in palabras]
        o = {"txt": texto, "clave": " ".join(t for t in toks if t), "y": (y0 + y1) / 2.0, "h": alto,
             "ancho": (x1 - x0) / alto, "cofre": False, "cab": False, "dudosa": False,
             "fn": None, "fm": None, "nd": 0, "ta": 0.0, "n": None, "mult_ocr": False}
        i, ocupa, fin, n, hay_mult = _buscar_cofre(toks)
        if i is not None:
            o["cofre"] = True
            o["n"] = n
            o["mult_ocr"] = hay_mult
            o["clave"] = " ".join(t for t in toks[i:fin] if t)
            try:
                _medir_cofre(m, palabras, i, ocupa, o)
            except Exception:
                pass
        elif es_cabecera(norm):
            o["cab"] = True
        else:
            o["dudosa"] = any(se_parece_a_cofre(t) for t in toks)
        obs.append(o)
    obs.sort(key=lambda o: o["y"])
    cofres = sum(1 for o in obs if o["cofre"])
    otros = sum(1 for o in obs if not (o["cofre"] or o["cab"] or o["dudosa"])
                and len(re.findall(r"[A-Z]", o["clave"])) >= 4)
    return {"ok": True, "lineas": obs, "texto": " | ".join(o["txt"] for o in obs), "cofres": cofres,
            "otros": otros,
            "solo_otros": otros > 0 and cofres == 0 and not any(o["dudosa"] for o in obs)}


class LectorAvisos:
    """Prepara la imagen del aviso, la pasa por el OCR y devuelve sus líneas ya interpretadas."""

    AMPLIAR = 4.0          # el texto se amplía x4 (respecto a 1080p) antes de leerlo
    MAX_LADO = 1500

    def __init__(self):
        self.hilo = HiloOCR()
        self.hilo.start()
        self.clave = None
        self.cache = None
        self.pendiente = None      # lectura encargada que aún no ha terminado: (número, clave, geometría)
        self.vacias = 0
        self.t_ultima = 0.0
        self.ms = 0
        self.ruido = False

    def disponible(self):
        return self.hilo.estado == "ok"

    def _terminar(self, m, res, geom, clave):
        x0, y0, kx, ky, marco = geom
        lineas = [[(t, (x - marco) / kx + x0, (y - marco) / ky + y0, w / kx, h / ky) for (t, x, y, w, h) in pal]
                  for pal in res]
        lec = interpretar_lectura(m, lineas)
        self.vacias = 0 if lec["lineas"] else self.vacias + 1
        self.clave, self.cache = clave, lec
        return lec

    def leer(self, base, ancho_juego):
        """base = recorte de pantalla de la zona de avisos (sin las ventanas del programa).
        Devuelve None si ahí no hay texto de aviso; {"ok": False} si lo hay pero ahora no se puede
        leer; o el resultado de interpretar_lectura()."""
        f = min(1.0, 1920.0 / max(1.0, float(ancho_juego)))
        if f < 0.999:          # pantallas de más de 1080p: se trabaja siempre a tamaño de 1080p
            base = base.resize((max(8, int(round(base.width * f))), max(8, int(round(base.height * f)))),
                               Image.BICUBIC)
        rel = max(0.3, min(1.0, ancho_juego * f / 1920.0))
        m, borde = _mascara_base(base)
        self.ruido = False
        if sum(m.histogram()[96:]) < 150 * rel * rel:
            self.clave = None
            return None                        # ni rastro del lila del aviso: no hay nada que leer
        m = _afinar_mascara(m, borde)
        n_on = sum(m.histogram()[96:])
        if n_on < 150 * rel * rel:
            self.clave = None
            return None
        if n_on > 0.16 * m.width * m.height:
            self.ruido = True                  # media pantalla es lila (tormenta, cielo...): ilegible
            return {"ok": False}
        binaria = m.point(_L_T96)
        caja = binaria.getbbox()
        if not caja or (caja[3] - caja[1]) < 8 * rel:
            self.clave = None
            return None
        x0, y0 = max(0, caja[0] - 8), max(0, caja[1] - 8)
        x1, y1 = min(m.width, caja[2] + 8), min(m.height, caja[3] + 8)
        clave = (x0, y0, x1, y1, zlib.crc32(binaria.crop((x0, y0, x1, y1)).tobytes()))
        if clave == self.clave and self.cache is not None:
            return self.cache                  # el aviso no ha cambiado: vale la lectura anterior
        ahora = time.time()
        if self.pendiente is not None:         # una lectura anterior tardó más de la cuenta
            ident, clave_p, geom = self.pendiente
            hecho, res = self.hilo.recoger(ident)
            if not hecho:
                return {"ok": False}           # el reconocedor sigue con ella
            self.pendiente = None
            if res is not None and clave_p == clave:
                return self._terminar(m, res, geom, clave)
        if self.vacias >= 4 and ahora - self.t_ultima < 0.30:
            return {"ok": False}               # lleva un rato sin leerse nada ahí: se insiste menos
        rec = m.crop((x0, y0, x1, y1))
        k = min(self.AMPLIAR / rel, self.MAX_LADO / float(max(rec.size)))
        gw, gh = max(8, int(rec.width * k)), max(8, int(rec.height * k))
        marco = 24
        lienzo = Image.new("L", (gw + 2 * marco, gh + 2 * marco), 255)
        lienzo.paste(ImageChops.invert(rec.resize((gw, gh), Image.BICUBIC)), (marco, marco))
        geom = (x0, y0, gw / float(rec.width), gh / float(rec.height), marco)
        ident = self.hilo.pedir(lienzo.tobytes(), lienzo.width, lienzo.height)
        if ident is None:
            return {"ok": False}
        hecho, res = self.hilo.recoger(ident, 0.12)
        self.ms = int((time.time() - ahora) * 1000)
        self.t_ultima = ahora
        if not hecho:
            self.pendiente = (ident, clave, geom)      # se recoge en el siguiente fotograma
            return {"ok": False}
        if res is None:
            return {"ok": False}
        return self._terminar(m, res, geom, clave)


class SeguidorCofres:
    """Sigue, línea a línea, el aviso de experiencia que lee el OCR y dice cuántos cofres NUEVOS hay.

    Cuenta un cofre cuando aparece una línea de cofre que antes no estaba, y otro cada vez que cambia
    el multiplicador («X2» -> «X3») de una que ya estaba. Que otras líneas desaparezcan no descuenta
    nada, y una línea ya contada no vuelve a contar aunque algún fotograma se lea mal."""

    T_OLVIDO = 0.45        # segundos sin ver una línea para darla por terminada

    def __init__(self):
        self.pistas = []
        self.total = 0

    def reiniciar(self):
        self.pistas = []
        self.total = 0

    def visibles(self):
        return sum(1 for p in self.pistas if p["contada"])

    def aplazar(self, dt):
        """Fotograma ilegible: las líneas seguidas no envejecen (durante un rato)."""
        for p in self.pistas:
            if p["gracia"] < 2.5:
                p["t"] += dt
                p["gracia"] += dt

    @staticmethod
    def _compatibles(p, o):
        """¿Puede ser la misma línea? (solo sirve para calcular cuánto se ha desplazado el aviso)"""
        if p["cofre"] != o["cofre"]:
            return False
        if p["fm"] is not None and o["fm"] is None and not o["n"]:
            return False                       # un «X2» no desaparece: es otra línea de cofre distinta
        a, b = p["clave"], o["clave"]
        if a == b:
            return True
        if abs(p["ancho"] - o["ancho"]) <= 0.12 * max(p["ancho"], o["ancho"], 1.0):
            return True
        if abs(len(a) - len(b)) <= 2 and min(len(a), len(b)) >= 3:
            return sum(1 for x, y in zip(a, b) if x != y) <= 2
        return False

    @staticmethod
    def _misma(cand, o):
        if cand["fm"] is not None and o["fm"] is not None:
            return (cand["nd"] == o["nd"] and abs(cand["ta"] - o["ta"]) <= 0.15
                    and _ncc_listas(cand["fm"], o["fm"]) >= 0.90)
        return cand["fm"] is None and o["fm"] is None and bool(o["n"]) and cand["n"] == o["n"]

    @staticmethod
    def _cambio(p, o):
        """¿Ha cambiado el multiplicador de la línea? None = sigue igual."""
        if o["fm"] is None and not o["n"]:
            return None                        # ahora no se le ve multiplicador: nada que comparar
        if p["fm"] is None and not p["n"]:
            return "cambio"                    # antes no llevaba «X2» y ahora sí
        if o["fm"] is not None and p["fm"] is not None:
            nn = _ncc_listas(p["fn"], o["fn"]) if (p["fn"] and o["fn"]) else 0.0
            if nn < 0.80:
                return "ruido"                 # la línea entera se mueve o se apaga: no es la cifra
            if o["nd"] != p["nd"] or abs(o["ta"] - p["ta"]) > 0.22:
                return "cambio"                # ha cambiado de ancho: «X9» -> «X10»
            nt = _ncc_listas(p["fm"], o["fm"])
            return "cambio" if (nt < 0.82 and nt < nn - 0.07) else None
        if o["n"] and p["n"] and o["n"] == p["n"] + 1:
            return "cambio"                    # sin dibujo que comparar: vale la cifra que lee el OCR
        return None

    def _ver(self, p, o, ahora):
        p["t"] = ahora
        p["gracia"] = 0.0
        p["y"] = o["y"]
        p["clave"], p["ancho"], p["cofre"] = o["clave"], o["ancho"], o["cofre"]
        if not o["cofre"]:
            if not p["contada"]:
                p["v_cofre"] = 0
            return 0
        p["v_cofre"] += 1
        if not p["contada"]:
            if p["v_cofre"] < 2:
                return 0                       # hay que leerla dos veces para fiarse
            p["contada"] = True
            p["fn"], p["fm"], p["nd"], p["ta"], p["n"], p["cand"] = o["fn"], o["fm"], o["nd"], o["ta"], o["n"], None
            if o["fm"] is not None or o["n"]:  # ya salía con «X3» la primera vez que se vio
                return o["n"] if (o["n"] and 2 <= o["n"] <= 9) else 2
            return 1
        c = self._cambio(p, o)
        if c == "cambio":
            cand = p["cand"]
            if cand is not None and self._misma(cand, o):
                cand["veces"] += 1
            else:
                cand = p["cand"] = {"fm": o["fm"], "nd": o["nd"], "ta": o["ta"], "n": o["n"], "veces": 1}
            if cand["veces"] >= 2:             # el multiplicador nuevo se ha visto igual dos veces
                p["fn"], p["fm"], p["nd"], p["ta"], p["n"], p["cand"] = (o["fn"], o["fm"], o["nd"], o["ta"],
                                                                         o["n"], None)
                return 1
        elif c is None:
            p["cand"] = None
            if o["fm"] is not None and (p["fm"] is None or o["nd"] == p["nd"]):
                p["fn"], p["fm"], p["nd"], p["ta"] = o["fn"], o["fm"], o["nd"], o["ta"]
            if o["n"] and not p["n"]:
                p["n"] = o["n"]
        return 0

    def actualizar(self, obs, ahora):
        """obs = líneas leídas en este fotograma (de arriba abajo). Devuelve los cofres nuevos."""
        pistas = self.pistas
        nuevos = 0
        pareja = {}
        usadas = set()
        if obs and pistas:
            # el aviso puede haberse desplazado entero (al irse la línea de arriba suben las demás)
            tol = 0.6 * sorted(o["h"] for o in obs)[len(obs) // 2]
            mejor, despl = -1, 0.0
            for d in [0.0] + [o["y"] - p["y"] for p in pistas for o in obs if self._compatibles(p, o)]:
                s = sum(1 for p in pistas for o in obs
                        if abs(o["y"] - p["y"] - d) <= tol and self._compatibles(p, o))
                if s > mejor or (s == mejor and abs(d) < abs(despl)):
                    mejor, despl = s, d
            for j, o in enumerate(obs):
                cand = None
                for i, p in enumerate(pistas):
                    if i in usadas:
                        continue
                    dist = abs(o["y"] - p["y"] - despl)
                    if dist <= tol and (cand is None or dist < cand[0]):
                        cand = (dist, i)
                if cand is not None:
                    usadas.add(cand[1])
                    pareja[j] = cand[1]
            for i, p in enumerate(pistas):
                if i not in usadas:
                    p["y"] += despl
        nuevas = []
        for j, o in enumerate(obs):
            if j in pareja:
                nuevos += self._ver(pistas[pareja[j]], o, ahora)
            else:
                nuevas.append({"y": o["y"], "t": ahora, "gracia": 0.0, "clave": o["clave"], "ancho": o["ancho"],
                               "cofre": o["cofre"], "v_cofre": 1 if o["cofre"] else 0, "contada": False,
                               "fn": o["fn"], "fm": o["fm"], "nd": o["nd"], "ta": o["ta"], "n": o["n"],
                               "cand": None})
        self.pistas = sorted((p for p in pistas + nuevas if ahora - p["t"] <= self.T_OLVIDO),
                             key=lambda p: p["y"])
        nuevos = min(nuevos, 4)
        self.total += nuevos
        return nuevos


# ---------------------------------------------------------------- recuento con la repetición del juego
# Fortnite graba cada partida en un archivo .replay (carpeta Demos). Ahí queda escrito, para cada cofre
# cercano, cuándo se abrió, QUIÉN lo abrió y si lo rompieron. Al terminar la partida el programa lee ese
# archivo y cuenta los cofres del jugador que grabó la repetición (abiertos y rotos): sirve de recuento
# exacto para confirmar lo que se contó en directo.
CARPETA_DEMOS = os.path.join(os.environ.get("LOCALAPPDATA", ""), "FortniteGame", "Saved", "Demos")
_OODLE = []


class ErrorRepeticion(Exception):
    pass


class _FinBits(Exception):
    pass


class _LectorBytes:
    def __init__(self, d, p=0):
        self.d, self.p = d, p

    def u8(self):
        v = self.d[self.p]
        self.p += 1
        return v

    def u32(self):
        v = struct.unpack_from("<I", self.d, self.p)[0]
        self.p += 4
        return v

    def i32(self):
        v = struct.unpack_from("<i", self.d, self.p)[0]
        self.p += 4
        return v

    def u64(self):
        v = struct.unpack_from("<Q", self.d, self.p)[0]
        self.p += 8
        return v

    def f32(self):
        v = struct.unpack_from("<f", self.d, self.p)[0]
        self.p += 4
        return v

    def packed(self):
        v = s = 0
        while True:
            b = self.d[self.p]
            self.p += 1
            v |= (b >> 1) << s
            s += 7
            if not b & 1:
                return v

    def fstr(self):
        n = self.i32()
        if n == 0:
            return ""
        if n < 0:
            s = self.d[self.p:self.p - n * 2 - 2].decode("utf-16le", "replace")
            self.p += -n * 2
            return s
        if n > 8192:
            raise ErrorRepeticion("formato desconocido")
        s = self.d[self.p:self.p + n - 1].decode("latin1")
        self.p += n
        return s


class _LectorBits:
    """Lector de bits sobre un entero grande (el bit menos significativo va primero)."""

    def __init__(self, v, n):
        self.v, self.n, self.p = v, n, 0

    def bit(self):
        if self.p >= self.n:
            raise _FinBits()
        b = (self.v >> self.p) & 1
        self.p += 1
        return b

    def bits(self, k):
        if self.p + k > self.n:
            raise _FinBits()
        v = (self.v >> self.p) & ((1 << k) - 1)
        self.p += k
        return v

    def u8(self):
        return self.bits(8)

    def u32(self):
        return self.bits(32)

    def i32(self):
        v = self.bits(32)
        return v - (1 << 32) if v & 0x80000000 else v

    def packed(self):
        v = s = 0
        while True:
            b = self.bits(8)
            v |= (b >> 1) << s
            s += 7
            if not b & 1:
                return v

    def serint(self, mx):
        v, m = 0, 1
        while v + m < mx:
            if self.bit():
                v |= m
            m <<= 1
        return v

    def fstr(self):
        n = self.i32()
        if n == 0:
            return ""
        if abs(n) > 2048:
            raise _FinBits()
        if n < 0:
            return self.bits(-n * 16).to_bytes(-n * 2, "little")[:-2].decode("utf-16le", "replace")
        return self.bits(n * 8).to_bytes(n, "little")[:-1].decode("latin1")

    def sub(self, k):
        if self.p + k > self.n:
            raise _FinBits()
        r = _LectorBits((self.v >> self.p) & ((1 << k) - 1), k)
        self.p += k
        return r

    def fin(self):
        return self.p >= self.n


def buscar_oodle():
    """La repetición va comprimida con «Oodle»: hace falta su librería (oo2core_*_win64.dll). Se busca en
    la carpeta de datos del programa, junto al programa y en Descargas\\REPETICIONES."""
    if _OODLE:
        return _OODLE[0]
    fn = None
    sitios = [DATOS, CARPETA, os.path.join(os.path.expanduser("~"), "Downloads", "REPETICIONES", "TEMPORAL"),
              os.path.join(os.path.expanduser("~"), "Downloads", "REPETICIONES")]
    for sitio in sitios:
        try:
            for f in sorted(os.listdir(sitio)):
                if f.lower().startswith("oo2core") and f.lower().endswith(".dll"):
                    try:
                        fn = ctypes.WinDLL(os.path.join(sitio, f)).OodleLZ_Decompress
                        fn.restype = ctypes.c_int64
                        fn.argtypes = [ctypes.c_char_p, ctypes.c_int64, ctypes.c_char_p, ctypes.c_int64, ctypes.c_int,
                                       ctypes.c_int, ctypes.c_int, ctypes.c_void_p, ctypes.c_int64, ctypes.c_void_p,
                                       ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int64, ctypes.c_int]
                        if sitio != DATOS:         # se guarda una copia con los datos del programa
                            try:
                                shutil.copy2(os.path.join(sitio, f), os.path.join(DATOS, f))
                            except OSError:
                                pass
                        break
                    except Exception:
                        fn = None
        except OSError:
            continue
        if fn is not None:
            break
    _OODLE.append(fn)
    return fn


def _descifrar_aes(clave, datos):
    """AES-256 (ECB) con el cifrado que trae Windows."""
    n = len(datos) // 16 * 16
    if n == 0:
        return b""
    bc = ctypes.WinDLL("bcrypt")
    VP = ctypes.c_void_p
    bc.BCryptOpenAlgorithmProvider.argtypes = [ctypes.POINTER(VP), ctypes.c_wchar_p, ctypes.c_wchar_p, ctypes.c_ulong]
    bc.BCryptSetProperty.argtypes = [VP, ctypes.c_wchar_p, ctypes.c_wchar_p, ctypes.c_ulong, ctypes.c_ulong]
    bc.BCryptGenerateSymmetricKey.argtypes = [VP, ctypes.POINTER(VP), VP, ctypes.c_ulong, ctypes.c_char_p,
                                              ctypes.c_ulong, ctypes.c_ulong]
    bc.BCryptDecrypt.argtypes = [VP, ctypes.c_char_p, ctypes.c_ulong, VP, VP, ctypes.c_ulong, ctypes.c_char_p,
                                 ctypes.c_ulong, ctypes.POINTER(ctypes.c_ulong), ctypes.c_ulong]
    bc.BCryptDestroyKey.argtypes = [VP]
    bc.BCryptCloseAlgorithmProvider.argtypes = [VP, ctypes.c_ulong]
    alg, key = VP(), VP()
    if bc.BCryptOpenAlgorithmProvider(ctypes.byref(alg), "AES", None, 0):
        raise ErrorRepeticion("Windows no deja usar AES")
    try:
        modo = "ChainingModeECB"
        bc.BCryptSetProperty(alg, "ChainingMode", modo, (len(modo) + 1) * 2, 0)
        if bc.BCryptGenerateSymmetricKey(alg, ctypes.byref(key), None, 0, bytes(clave), len(clave), 0):
            raise ErrorRepeticion("clave de la repetición no válida")
        out = ctypes.create_string_buffer(n)
        hecho = ctypes.c_ulong(0)
        r = bc.BCryptDecrypt(key, bytes(datos[:n]), n, None, None, 0, out, n, ctypes.byref(hecho), 0)
        bc.BCryptDestroyKey(key)
        if r:
            raise ErrorRepeticion("no se pudo descifrar la repetición")
        return out.raw[:hecho.value]
    finally:
        bc.BCryptCloseAlgorithmProvider(alg, 0)


def _trozos_repeticion(f):
    """Cabecera del archivo .replay: devuelve (clave, comprimida, cifrada, [(tipo, posición, tamaño)])."""
    b = _LectorBytes(f)
    if b.u32() != 0x1CA2E27F:
        raise ErrorRepeticion("no es una repetición de Fortnite")
    ver = b.u32()
    if ver >= 7:
        n = b.u32()
        b.p += 20 * n
    b.p += 12
    b.fstr()
    b.p += 12
    comp, enc, klen = b.u32(), b.u32(), b.u32()
    clave = f[b.p:b.p + klen]
    b.p += klen
    trozos = []
    while b.p + 8 <= len(f):
        t = b.u32()
        s = b.i32()
        if s < 0 or b.p + s > len(f):
            break                          # el juego aún la está escribiendo
        trozos.append((t, b.p, s))
        b.p += s
    return clave, comp, enc, trozos


class AnalizadorRepeticion:
    """Interpreta los datos de red de la repetición lo justo para seguir los cofres y saber de quién son."""

    PROPS_MIAS = ("MovementInputPacked", "PreRecoilInputDeltaPacked")     # solo llegan del jugador que graba

    def __init__(self):
        self.grupos = {}            # nº de clase -> [ruta, {nº de propiedad: nombre}]
        self.guids = {}             # nº de objeto -> nombre
        self.sufijos = {}           # «Tiered_Chest_Athena_C» -> nº de clase
        self.canales = {}
        self.parciales = {}
        self.eventos = []           # (segundo, cofre, tipo, abierto, roto, peón)
        self.peones = {}            # peón -> [veces que llegan sus mandos, paquetes mirados]
        self.paq_ok = self.paq_mal = 0

    # --- tablas de nombres ---
    def _objeto(self, b, exportando):
        g = b.packed()
        if g == 0:
            return 0
        fl = b.u8() if (g == 1 or exportando) else 0
        if fl & 1:
            self._objeto(b, True)
            ruta = b.fstr()
            if fl & 4:
                b.u32()
            self.guids[g] = ruta
        return g

    def _exportaciones(self, b):
        for _ in range(b.packed()):
            pi = b.packed()
            if b.packed() == 1:
                ruta = b.fstr()
                b.packed()
                self.grupos.setdefault(pi, [ruta, {}])[0] = ruta
                self.sufijos[ruta.rsplit(".", 1)[-1]] = pi
            g = self.grupos.setdefault(pi, ["", {}])
            if b.u8():
                h = b.packed()
                b.u32()
                if b.u8():
                    g[1][h] = "#%d" % b.packed()
                else:
                    g[1][h] = b.fstr()
                    b.i32()
        for _ in range(b.packed()):
            fin = b.i32()
            fin += b.p
            self._objeto(b, True)
            b.p = fin

    # --- un actor (cofre o jugador) ---
    def _abrir(self, b):
        g = self._objeto(b, False)
        c = {"guid": g, "tipo": "", "clase": None, "peon": False, "vistos": 0}
        if g & 1:                                           # actor del mapa (los cofres normales)
            nombre = self.guids.get(g, "")
            m = re.match(r"(.+?_C)_(?:UAID_|[0-9a-f]{12,}_|\d+$)", nombre)
            suf = m.group(1) if m else ""
            c["nombre"] = nombre
        else:                                               # actor creado durante la partida
            ruta = self.guids.get(self._objeto(b, False), "")
            suf = ruta[9:] if ruta.startswith("Default__") else ruta.rsplit(".", 1)[-1]
            c["nombre"] = "%s#%d" % (suf, g)
        if suf == "PlayerPawn_Athena_C":
            c["peon"] = True
        elif "Chest" not in suf:
            return c
        c["clase"], c["tipo"] = suf, suf
        if not g & 1:                                       # posición, giro, escala y velocidad iniciales
            self._objeto(b, False)
            for que in range(4):
                if not b.bit():
                    continue
                if que == 1:
                    for _ in range(3):
                        if b.bit():
                            b.bits(16)
                else:
                    info = b.serint(128)
                    b.bits((info & 63) * 3 if info & 63 else (192 if info >> 6 else 96))
        return c

    def _cuerpo(self, t, ch, b, abre, cierra):
        c = self.canales.get(ch)
        if c is None:
            if not abre:
                return
            c = self.canales[ch] = self._abrir(b)
        if cierra:
            self.canales.pop(ch, None)
        if c["clase"] is None:
            return
        if c["peon"]:
            est = self.peones.setdefault(c["guid"], [0, 0])
            if est[0] >= 25 or est[1] >= 600:
                return                                      # ya se sabe si es el jugador que graba o no
            est[1] += 1
        clase = self.sufijos.get(c["clase"])
        nombres = self.grupos[clase][1] if clase is not None else {}
        abierto = roto = False
        peon = None
        while not b.fin():
            con_props = b.bit()
            if not b.bit():
                break                                       # una pieza del actor: no interesa
            p = b.sub(b.packed())
            if not con_props:
                continue
            p.bit()
            while True:
                h = p.packed()
                if h == 0:
                    break
                v = p.sub(p.packed())
                nom = nombres.get(h - 1, "")
                if c["peon"]:
                    if nom in self.PROPS_MIAS:
                        self.peones[c["guid"]][0] += 1
                elif nom == "bAlreadySearched" or nom == "ChestOpened":
                    abierto = abierto or v.v == 1
                elif nom == "bDestroyed":
                    roto = True
                elif nom in ("SearchingPawn", "InteractingPawn") or (h - 1 == 80 and not nom):
                    try:
                        peon = v.packed()
                    except _FinBits:
                        pass
        if abierto or roto:
            self.eventos.append((t, c["nombre"], c["tipo"], abierto, roto, peon))

    # --- paquetes ---
    def _paquete(self, t, dat):
        ult = dat[-1]
        if not ult:
            return
        b = _LectorBits(int.from_bytes(dat, "little"), len(dat) * 8 - (9 - ult.bit_length()))
        try:
            while not b.fin():
                ctrl = b.bit()
                abre = b.bit() if ctrl else 0
                cierra = b.bit() if ctrl else 0
                if cierra:
                    b.serint(15)
                b.bit()
                fiable = b.bit()
                ch = b.packed()
                exporta, mapea, parcial = b.bit(), b.bit(), b.bit()
                pini = pfin = 0
                if parcial:
                    pini = b.bit()
                    b.bit()
                    pfin = b.bit()
                if fiable or abre:
                    if b.bit():
                        b.packed()
                    else:
                        b.fstr()
                        b.i32()
                datos = b.sub(b.serint(16384))
                if parcial:
                    if pini:
                        self.parciales[ch] = [datos.v, datos.n, abre, exporta, mapea]
                    elif ch in self.parciales:
                        pp = self.parciales[ch]
                        pp[0] |= datos.v << pp[1]
                        pp[1] += datos.n
                    else:
                        continue
                    if not pfin:
                        continue
                    pp = self.parciales.pop(ch)
                    datos = _LectorBits(pp[0], pp[1])
                    abre, exporta, mapea = pp[2], pp[3], pp[4]
                try:
                    if exporta:
                        if datos.bit():
                            continue
                        for _ in range(datos.i32()):
                            self._objeto(datos, True)
                    if mapea:
                        for _ in range(datos.bits(16)):
                            datos.packed()
                    self._cuerpo(t, ch, datos, abre, cierra)
                except _FinBits:
                    pass
            self.paq_ok += 1
        except _FinBits:
            self.paq_mal += 1

    def bloque(self, d):
        """Un bloque de datos ya descifrado y descomprimido."""
        b = _LectorBytes(d)
        while b.p < len(d):
            b.i32()
            t = b.f32()
            self._exportaciones(b)
            for _ in range(b.packed()):
                b.fstr()
            b.u64()
            while True:
                nb = b.packed()
                if nb == 0:
                    break
                b.packed()
                b.p += (nb + 7) >> 3
            salto = b.u64()
            b.p += salto
            while True:
                b.packed()
                tam = b.i32()
                if tam == 0:
                    break
                self._paquete(t, d[b.p:b.p + tam])
                b.p += tam

    def resultado(self):
        total = self.paq_ok + self.paq_mal
        if total == 0 or self.paq_mal > 0.03 * total:
            raise ErrorRepeticion("el juego ha cambiado el formato de las repeticiones")
        mios = set(g for g, (n, _v) in self.peones.items() if n >= 25)
        if not mios:
            raise ErrorRepeticion("no se reconoce al jugador que grabó la repetición")
        cofres = [(t, nom, tipo, ab, ro) for t, nom, tipo, ab, ro, peon in self.eventos if peon in mios]
        cofres.sort()
        return {"abiertos": sum(1 for c in cofres if c[3] and not c[4]), "rotos": sum(1 for c in cofres if c[4]),
                "total": len(cofres), "momentos": [round(c[0], 1) for c in cofres],
                "tipos": dict(Counter(re.sub(r"^AlwaysSpawn_|_C$|_Athena", "", c[2]) for c in cofres)),
                "de_otros": sum(1 for e in self.eventos if e[5] and e[5] not in mios)}


def analizar_repeticion(ruta, parar=None):
    """Lee un archivo .replay y devuelve el recuento de cofres del jugador que lo grabó."""
    with open(ruta, "rb") as fh:
        f = fh.read()
    clave, comp, enc, trozos = _trozos_repeticion(f)
    oodle = buscar_oodle() if comp else None
    if comp and oodle is None:
        raise ErrorRepeticion("falta la librería oo2core_9_win64.dll (cópiala en la carpeta de datos del programa)")
    an = AnalizadorRepeticion()
    n = 0
    for t, p, s in trozos:
        if t != 1:
            continue
        if parar is not None and parar():
            raise ErrorRepeticion("cancelado")
        d = f[p + 16:p + s]
        if enc:
            d = _descifrar_aes(clave, d)
        if comp:
            tam, tam_c = struct.unpack_from("<ii", d, 0) if len(d) >= 8 else (0, 0)
            salida = ctypes.create_string_buffer(tam + 64) if 0 < tam <= 80000000 else None
            if salida is None or oodle(d[8:8 + tam_c], tam_c, salida, tam, 1, 0, 0, None, 0, None, None, None, 0, 3) != tam:
                if n:
                    break                  # último bloque a medio escribir: vale lo leído hasta aquí
                raise ErrorRepeticion("no se pudo descomprimir la repetición")
            d = salida.raw[:tam]
        an.bloque(d)
        n += 1
    if n == 0:
        raise ErrorRepeticion("la repetición está vacía")
    res = an.resultado()
    res["archivo"] = os.path.basename(ruta)
    return res


def repeticion_reciente(desde=0.0):
    """La repetición más nueva de la carpeta Demos (modificada después de «desde»), o None."""
    try:
        lista = [os.path.join(CARPETA_DEMOS, f) for f in os.listdir(CARPETA_DEMOS) if f.lower().endswith(".replay")]
        lista = [f for f in lista if os.path.getsize(f) > 500000 and os.path.getmtime(f) >= desde]
        return max(lista, key=os.path.getmtime) if lista else None
    except OSError:
        return None


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


# --- detector de lobby TOLERANTE ------------------------------------------------------------
# El de arriba mira dos cajas en posiciones fijas. Falla si el botón amarillo lleva un texto largo
# («TODO LISTO» cuando estás en grupo), si la pantalla no es 16:9, o si la ventana del propio
# programa tapa esa zona. Este busca los elementos por la pantalla entera, sin posiciones fijas.
_RE_RUN = re.compile(b"\xff+")
_L_G185 = _lut(lambda v: v > 185)
_L_G215 = _lut(lambda v: v > 215)
_L_B90 = _lut(lambda v: v < 90)
_L_D35 = _lut(lambda v: v < 35)


def _mask_amarillo(img):
    r, g, b = img.split()
    mul_ = ImageChops.multiply
    return mul_(mul_(r.point(_L_G215), g.point(_L_G215)), b.point(_L_B90))


def _mask_claro(img, lut):
    """Píxeles claros y sin color (blanco / gris claro)."""
    r, g, b = img.split()
    mul_ = ImageChops.multiply
    claro = mul_(mul_(r.point(lut), g.point(lut)), b.point(lut))
    gris = mul_(mul_(ImageChops.difference(r, g).point(_L_D35), ImageChops.difference(g, b).point(_L_D35)),
                ImageChops.difference(r, b).point(_L_D35))
    return mul_(claro, gris)


def _filas_largas(mask, x0, y0, x1, y1, min_run):
    """Por cada fila, la tira continua más larga de píxeles encendidos (si mide al menos min_run)."""
    w = mask.size[0]
    d = mask.tobytes()
    out = []
    for y in range(y0, y1):
        fila = d[y * w + x0:y * w + x1]
        mejor = None
        for m in _RE_RUN.finditer(fila):
            n = m.end() - m.start()
            if n >= min_run and (mejor is None or n > mejor[1]):
                mejor = (m.start(), n)
        if mejor:
            out.append((y, mejor[0], mejor[1]))
    return out


def _hay_bloque(filas, min_filas, ventana, tol=6):
    """¿Hay al menos min_filas filas parecidas (mismo inicio y largo) dentro de una ventana vertical?
    Así un rectángulo con texto en medio (botón, pastilla) se reconoce por sus márgenes."""
    for i, (y, s, n) in enumerate(filas):
        c = 0
        for y2, s2, n2 in filas[i:]:
            if y2 - y > ventana:
                break
            if abs(s2 - s) <= tol and abs(n2 - n) <= max(5, n * 0.25):
                c += 1
        if c >= min_filas:
            return True
    return False


def _palabras_barra(mask, x0, x1, y0, y1):
    banda = mask.crop((x0, y0, x1, y1))
    bw, bh = banda.size
    t = banda.transpose(Image.TRANSPOSE).tobytes()
    cols = [t[x * bh:(x + 1) * bh].count(255) >= 2 for x in range(bw)]
    return sum(1 for a, b in _tramos(cols, 3) if 14 <= b - a + 1 <= 45)


def hay_lobby_amplio(img):
    """Lobby = (botón amarillo grande abajo a la izquierda Y pastilla gris clara arriba a la izquierda)
    O la barra de menús de arriba (JUGAR · TIENDA · TAQUILLA · PASES...) con varias palabras blancas.
    Se analiza la pantalla entera reducida a 270 px de alto. Devuelve (ok, boton, pastilla, palabras)."""
    h0 = 270
    w0 = max(120, int(round(img.width * h0 / float(img.height))))
    p = img.convert("RGB").resize((w0, h0), Image.BOX)
    xr = int(w0 * 0.55)
    boton = _hay_bloque(_filas_largas(_mask_amarillo(p), 0, int(h0 * 0.55), xr, h0, int(h0 * 0.10)), 6, 24)
    pastilla = _hay_bloque(_filas_largas(_mask_claro(p, _L_G185), 0, 0, xr, int(h0 * 0.12), 14), 4, 14)
    palabras = _palabras_barra(_mask_claro(p, _L_G215), 0, int(w0 * 0.85), int(h0 * 0.035), int(h0 * 0.095))
    return ((boton and pastilla) or palabras >= 4), boton, pastilla, palabras


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


# ---------------------------------------------------------------- icono del programa
# El cofre va incrustado aquí (PNG en base64): así el programa sigue siendo un único archivo y el
# icono vale para la ventana, la barra de tareas, la cabecera y el número flotante.
ICONO_B64 = (
    "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")
_ICONO = []
_FOTOS = {}            # imágenes de Tk ya preparadas (botones, iconos...), para no repetir el trabajo


def foto_tk(im):
    """Imagen de PIL -> imagen de Tk."""
    try:
        from PIL import ImageTk
        return ImageTk.PhotoImage(im)
    except Exception:
        b = io.BytesIO()
        im.save(b, "PNG")
        return tk.PhotoImage(data=base64.b64encode(b.getvalue()))


def icono_base():
    if not _ICONO:
        try:
            im = Image.open(io.BytesIO(base64.b64decode(ICONO_B64)))
            _ICONO.append(im.convert("RGBA"))
        except Exception:
            _ICONO.append(None)
    return _ICONO[0]


def icono_ajustado(ancho, alto):
    """El cofre, lo más grande que quepa en ancho x alto."""
    base = icono_base()
    k = min(ancho / float(base.width), alto / float(base.height))
    return base.resize((max(1, int(round(base.width * k))), max(1, int(round(base.height * k)))), Image.LANCZOS)


def icono_cuadrado(lado):
    """El cofre centrado en un cuadrado transparente (para el icono de la ventana)."""
    p = icono_ajustado(lado, lado)
    im = Image.new("RGBA", (lado, lado), (0, 0, 0, 0))
    im.alpha_composite(p, ((lado - p.width) // 2, (lado - p.height) // 2))
    if lado <= 24:
        im = im.filter(ImageFilter.UnsharpMask(radius=0.6, percent=60, threshold=0))
    return im


def poner_icono_ventana(root):
    """Icono de la ventana y de la barra de tareas (y, por defecto, de todas las ventanas del programa)."""
    try:
        if icono_base() is None:
            return
        fotos = [foto_tk(icono_cuadrado(t)) for t in (16, 20, 24, 32, 40, 48, 64)]
        root.iconphoto(True, *fotos)
        root._iconos = fotos              # hay que guardarlas: si no, Tk las borra
    except Exception:
        pass


def icono_cabecera(alto, fondo):
    """El cofre sobre el color de la cabecera, con un resplandor dorado muy suave detrás."""
    try:
        if icono_base() is None:
            return None
        cofre = icono_ajustado(alto * 3, alto)
        m = max(4, alto // 5)
        lienzo = Image.new("RGBA", (cofre.width + 2 * m, cofre.height + 2 * m), _rgb(fondo) + (255,))
        halo = Image.new("L", lienzo.size, 0)
        halo.paste(cofre.split()[3], (m, m))
        halo = halo.filter(ImageFilter.GaussianBlur(m * 0.6)).point([int(v * 0.40) for v in range(256)])
        lienzo.paste(Image.new("RGBA", lienzo.size, _rgb(ORO) + (255,)), (0, 0), halo)
        lienzo.alpha_composite(cofre, (m, m))
        return foto_tk(lienzo.convert("RGB"))
    except Exception:
        return None


def icono_flotante(ancho, alto):
    """El cofre para el número flotante: con contorno oscuro y sin bordes semitransparentes (esa
    ventana usa un color «transparente» y un borde suave dejaría un cerco alrededor)."""
    clave = ("flot", ancho, alto)
    if clave not in _FOTOS:
        foto = None
        try:
            if icono_base() is not None:
                g = 1 if alto < 44 else 2
                cofre = icono_ajustado(max(4, ancho - 2 * g), max(4, alto - 2 * g))
                tam = (cofre.width + 2 * g, cofre.height + 2 * g)
                silueta = Image.new("L", tam, 0)
                silueta.paste(cofre.split()[3], (g, g))
                silueta = silueta.point(_lut(lambda v: v >= 90)).filter(ImageFilter.MaxFilter(2 * g + 1))
                im = Image.new("RGBA", tam, _rgb(CONTORNO) + (255,))
                im.alpha_composite(cofre, (g, g))
                im.putalpha(silueta)
                foto = foto_tk(im)
        except Exception:
            foto = None
        _FOTOS[clave] = foto
    return _FOTOS[clave]


def identidad_app():
    """Sin esto, al ejecutar el .py con Python la barra de tareas enseña el icono de Python."""
    try:
        if not getattr(sys, "frozen", False):
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("ContadorDeCofres.App")
    except Exception:
        pass


def estilo_barra_titulo(ventana):
    """Barra de título oscura, a juego con el programa (Windows 10/11). Si no se puede, no pasa nada."""
    try:
        hwnd = ctypes.windll.user32.GetParent(ventana.winfo_id()) or ventana.winfo_id()
        dwm = ctypes.windll.dwmapi.DwmSetWindowAttribute
        dwm.argtypes = [wintypes.HWND, wintypes.DWORD, ctypes.c_void_p, wintypes.DWORD]
        dwm.restype = ctypes.c_long

        def poner(atributo, valor):
            v = ctypes.c_int(valor)
            return dwm(hwnd, atributo, ctypes.byref(v), 4)

        def colorref(c):
            r, g, b = _rgb(c)
            return (b << 16) | (g << 8) | r

        if poner(20, 1) != 0:             # modo oscuro (el 19 es el de los Windows 10 antiguos)
            poner(19, 1)
        poner(35, colorref(BG))           # Windows 11: color de la barra...
        poner(36, colorref(TEXTO))        # ...de su texto...
        poner(34, colorref("#3a3363"))    # ...y del borde de la ventana
    except Exception:
        pass


# ---------------------------------------------------------------- aspecto: colores, animaciones y botones
ANIM = [None]          # el reloj de animaciones de la ventana (lo crea App)
_DEGRADADO = Image.frombytes("L", (1, 256), bytes(range(256)))
_FUENTES = {}


def _rgb(c):
    return (int(c[1:3], 16), int(c[3:5], 16), int(c[5:7], 16))


def mezclar(c1, c2, t):
    """Color intermedio entre c1 y c2 ('#rrggbb'): t va de 0 (c1) a 1 (c2)."""
    t = 0.0 if t < 0 else 1.0 if t > 1 else t
    a, b = _rgb(c1), _rgb(c2)
    return "#%02x%02x%02x" % tuple(int(round(a[i] + (b[i] - a[i]) * t)) for i in range(3))


def suave(t):
    """Curva de frenado: arranca rápido y termina despacio."""
    t = 0.0 if t < 0 else 1.0 if t > 1 else t
    return 1.0 - (1.0 - t) ** 3


def fuente_tk(f):
    """Fuente de Tk (guardada para medir textos sin crearla cada vez)."""
    obj = _FUENTES.get(f)
    if obj is None:
        obj = _FUENTES[f] = tkfont.Font(font=f)
    return obj


class Animador:
    """Un único reloj para todas las animaciones: solo trabaja mientras hay alguna en marcha."""

    PASO_MS = 16

    def __init__(self, root):
        self.root = root
        self.activas = {}
        self.en_marcha = False

    def lanzar(self, clave, ms, funcion, al_terminar=None):
        """funcion(t) se llama con t de 0 a 1 durante «ms» milisegundos. Una animación nueva con la
        misma clave sustituye a la anterior."""
        self.activas[clave] = [time.time(), max(1, ms) / 1000.0, funcion, al_terminar]
        if not self.en_marcha:
            self.en_marcha = True
            self.root.after(self.PASO_MS, self._paso)

    def parar(self, clave):
        self.activas.pop(clave, None)

    def _paso(self):
        ahora = time.time()
        for clave, dato in list(self.activas.items()):
            t0, dur, funcion, fin = dato
            t = min(1.0, (ahora - t0) / dur)
            try:
                funcion(t)
            except Exception:              # lo normal: la ventana o el botón ya no existen
                t, fin = 1.0, None
            if t >= 1.0 and self.activas.get(clave) is dato:
                del self.activas[clave]
                if fin is not None:
                    try:
                        fin()
                    except Exception:
                        pass
        if self.activas:
            try:
                self.root.after(self.PASO_MS, self._paso)
            except Exception:
                self.en_marcha = False
        else:
            self.en_marcha = False


def pintar_pastilla(w, h, fondo, color, radio=8.0, margen=3, brillo=0.0, hundido=0.0, halo=0.0):
    """Dibuja un botón: rectángulo redondeado con degradado, filo de luz arriba y, si se pide, un
    resplandor suave alrededor. Se pinta al triple de tamaño y se reduce, para que los bordes
    queden finos. Devuelve la imagen (w x h) sobre el color de fondo."""
    s = 3
    ancho, alto = w * s, h * s
    m = margen * s
    r = max(s, int(round(radio * s)))
    caja = [m, m, ancho - m - 1, alto - m - 1]
    im = Image.new("RGB", (ancho, alto), fondo)
    if halo > 0.01 and m > 0:
        capa = Image.new("L", (ancho, alto), 0)
        ImageDraw.Draw(capa).rounded_rectangle(caja, radius=r, fill=int(255 * min(1.0, halo)))
        capa = capa.filter(ImageFilter.GaussianBlur(m * 0.62))
        im.paste(Image.new("RGB", (ancho, alto), mezclar(color, "#ffffff", 0.35)), (0, 0), capa)
    arriba = mezclar(color, "#ffffff", 0.13 + 0.12 * brillo)
    abajo = mezclar(color, "#000000", 0.16 - 0.06 * brillo)
    if hundido > 0:
        arriba = mezclar(arriba, mezclar(color, "#000000", 0.26), hundido)
        abajo = mezclar(abajo, mezclar(color, "#000000", 0.10), hundido)
    grad = _DEGRADADO.resize((ancho, alto))
    forma = Image.new("L", (ancho, alto), 0)
    ImageDraw.Draw(forma).rounded_rectangle(caja, radius=r, fill=255)
    im.paste(Image.composite(Image.new("RGB", (ancho, alto), abajo), Image.new("RGB", (ancho, alto), arriba), grad),
             (0, 0), forma)
    # filo: más claro arriba (le da la luz) y más oscuro abajo
    dentro = Image.new("L", (ancho, alto), 0)
    ImageDraw.Draw(dentro).rounded_rectangle([m + s, m + s, ancho - m - 1 - s, alto - m - 1 - s],
                                             radius=max(1, r - s), fill=255)
    luz = Image.composite(Image.new("RGB", (ancho, alto), mezclar(color, "#000000", 0.30)),
                          Image.new("RGB", (ancho, alto), mezclar(color, "#ffffff", 0.36 + 0.24 * brillo)), grad)
    im.paste(luz, (0, 0), ImageChops.subtract(forma, dentro))
    return im.resize((w, h), Image.LANCZOS)


def pintar_barra(w, h, fondo, fraccion, color, destello=None):
    """Barra de progreso redondeada con degradado. «destello» (0-1) es por dónde va el brillo que la
    recorre cuando avanza."""
    s = 2
    ancho, alto = w * s, h * s
    r = (alto - 2 * s) // 2
    im = Image.new("RGB", (ancho, alto), fondo)
    pista = Image.new("L", (ancho, alto), 0)
    ImageDraw.Draw(pista).rounded_rectangle([s, s, ancho - s - 1, alto - s - 1], radius=r, fill=255)
    im.paste(Image.new("RGB", (ancho, alto), BG), (0, 0), pista)
    fraccion = max(0.0, min(1.0, fraccion))
    lleno = int(round((ancho - 4 * s) * fraccion))
    if lleno > 0:
        interior = Image.new("L", (ancho, alto), 0)
        ImageDraw.Draw(interior).rounded_rectangle([2 * s, 2 * s, ancho - 2 * s - 1, alto - 2 * s - 1],
                                                   radius=max(1, r - s), fill=255)
        tramo = Image.new("L", (ancho, alto), 0)
        ImageDraw.Draw(tramo).rounded_rectangle([2 * s - 4 * r, 2 * s, 2 * s + lleno, alto - 2 * s - 1],
                                                radius=max(1, r - s), fill=255)
        tramo = ImageChops.multiply(tramo, interior)
        cuerpo = Image.composite(Image.new("RGB", (ancho, alto), mezclar(color, "#000000", 0.20)),
                                 Image.new("RGB", (ancho, alto), mezclar(color, "#ffffff", 0.30)),
                                 _DEGRADADO.resize((ancho, alto)))
        if destello is not None:
            x = (-0.15 + 1.3 * destello) * ancho
            luz = Image.new("L", (ancho, alto), 0)
            ImageDraw.Draw(luz).polygon([(x - ancho * 0.07, alto), (x + ancho * 0.02, 0), (x + ancho * 0.09, 0),
                                         (x, alto)], fill=int(150 * (1.0 - abs(2 * destello - 1.0) ** 2)))
            cuerpo.paste(Image.new("RGB", (ancho, alto), "#ffffff"), (0, 0), luz.filter(ImageFilter.GaussianBlur(s * 3)))
        im.paste(cuerpo, (0, 0), tramo)
    ImageDraw.Draw(im).rounded_rectangle([s, s, ancho - s - 1, alto - s - 1], radius=r, outline=ORO_OSC, width=s)
    return im.resize((w, h), Image.LANCZOS)


class _Pastilla(tk.Canvas):
    """Base de los botones dibujados: un lienzo con la imagen del botón y su texto encima, que se
    aclara con suavidad al pasar el ratón y se hunde al pulsar."""

    M = 2                  # margen alrededor del botón, para el resplandor

    def __init__(self, padre, texto, fuente, padx, pady, ancho=0, fondo=None):
        self._fondo = fondo or padre.cget("bg")
        tk.Canvas.__init__(self, padre, highlightthickness=0, bd=0, bg=self._fondo, cursor="hand2", takefocus=0)
        self._texto = texto
        self._fuente = fuente
        self._padx, self._pady, self._ancho = padx, pady, ancho
        self._estado = "normal"
        self._hover = 0.0
        self._pulso = 0.0
        self._hundido = 0.0
        self._dentro = False
        self._apretado = False
        self._pw = self._ph = 0            # tamaño en píxeles (ojo: «_w» es un nombre que usa Tk por dentro)
        self._foto = None
        self._img = self.create_image(0, 0, anchor="nw")
        self._txt = self.create_text(0, 0, text=texto, font=fuente, fill="#ffffff")
        self._medir()
        self.bind("<Configure>", self._al_cambiar_tam)
        self.bind("<Enter>", self._entra)
        self.bind("<Leave>", self._sale)
        self.bind("<ButtonPress-1>", self._aprieta)
        self.bind("<ButtonRelease-1>", self._suelta)

    # --- tamaño y dibujo ---
    def _medir(self):
        f = fuente_tk(self._fuente)
        w = max(self._ancho * f.measure("0"), f.measure(self._texto)) + 2 * self._padx
        h = f.metrics("linespace") + 2 * self._pady + 2
        tk.Canvas.configure(self, width=w + 2 * self.M, height=h + 2 * self.M)

    def _al_cambiar_tam(self, e):
        if (e.width, e.height) != (self._pw, self._ph):
            self._pw, self._ph = e.width, e.height
            self._pintar()

    def _aspecto(self):
        """(clave para la caché, color del cuerpo, brillo, halo, color del texto). Lo define cada tipo."""
        raise NotImplementedError

    def _pintar(self):
        w, h = self._pw, self._ph
        if w < 8 or h < 8:
            return
        clave, color, brillo, halo, color_txt = self._aspecto()
        hundido = int(round(self._hundido * 2))
        clave = (w, h, self._fondo, hundido) + clave
        foto = _FOTOS.get(clave)
        if foto is None:
            if len(_FOTOS) > 1500:
                _FOTOS.clear()
            radio = min(9.0, (h - 2 * self.M) / 2.4)
            foto = _FOTOS[clave] = foto_tk(pintar_pastilla(w, h, self._fondo, color, radio, self.M, brillo,
                                                           hundido / 2.0, halo))
        self._foto = foto
        self.itemconfigure(self._img, image=foto)
        self.coords(self._txt, w / 2.0, h / 2.0 + (1 if hundido else 0))
        self.itemconfigure(self._txt, fill=color_txt)

    def _animar(self, atributo, destino, ms):
        ini = getattr(self, atributo)
        if ANIM[0] is None or abs(destino - ini) < 0.01:
            setattr(self, atributo, destino)
            self._pintar()
            return

        def paso(t):
            setattr(self, atributo, ini + (destino - ini) * suave(t))
            self._pintar()

        ANIM[0].lanzar((str(self), atributo), ms, paso)

    # --- ratón ---
    def _activo(self):
        return self._estado != "disabled"

    def _entra(self, e=None):
        self._dentro = True
        if self._activo():
            self._animar("_hover", 1.0, 130)

    def _sale(self, e=None):
        self._dentro = False
        self._animar("_hover", 0.0, 240)
        if self._apretado:
            self._animar("_hundido", 0.0, 120)

    def _aprieta(self, e=None):
        if not self._activo():
            return
        self._apretado = True
        self._hundido = 1.0
        self._pintar()

    def _suelta(self, e=None):
        if not self._apretado:
            return
        self._apretado = False
        self._animar("_hundido", 0.0, 140)
        if e is not None and not (0 <= e.x <= self._pw and 0 <= e.y <= self._ph):
            return                          # soltó fuera del botón: no cuenta como pulsación
        self._pulso = 1.0                   # destello breve que se apaga solo
        self._animar("_pulso", 0.0, 420)
        self._pulsado()

    def _pulsado(self):
        pass

    # --- lo mismo que acepta un botón normal de Tk ---
    def configure(self, cnf=None, **kw):
        if cnf:
            kw = dict(cnf, **kw)
        if not kw:
            return tk.Canvas.configure(self)
        medir = pintar = False
        if "text" in kw:
            self._texto = kw.pop("text")
            self.itemconfigure(self._txt, text=self._texto)
            medir = True
        if "font" in kw:
            self._fuente = kw.pop("font")
            self.itemconfigure(self._txt, font=self._fuente)
            medir = True
        if "pady" in kw:
            self._pady = int(kw.pop("pady"))
            medir = True
        if "padx" in kw:
            self._padx = int(kw.pop("padx"))
            medir = True
        if "state" in kw:
            self._estado = str(kw.pop("state"))
            tk.Canvas.configure(self, cursor="hand2" if self._activo() else "arrow")
            pintar = True
        if "command" in kw:
            self._comando = kw.pop("command")
        if kw:
            tk.Canvas.configure(self, **kw)
        if medir:
            self._medir()
        if medir or pintar:
            self._pintar()

    config = configure


class BotonSuave(_Pastilla):
    """Botón de color con esquinas redondeadas."""

    def __init__(self, padre, texto, comando, color, ancho=7, fuente=("Segoe UI Semibold", 11), pady=3, padx=6):
        self._comando = comando
        self._color = color
        _Pastilla.__init__(self, padre, texto, fuente, padx, pady, ancho)

    def _aspecto(self):
        if not self._activo():
            return (("b", self._color, "off"), mezclar(self._color, self._fondo, 0.55), 0.0, 0.0,
                    mezclar("#ffffff", self._fondo, 0.5))
        hv = int(round(self._hover * 4))
        pu = int(round(self._pulso * 4))
        return (("b", self._color, hv, pu), self._color, hv / 4.0 + pu / 4.0 * 0.7,
                0.30 * hv / 4.0 + 0.55 * pu / 4.0, "#ffffff")

    def _pulsado(self):
        if self._comando is not None:
            self._comando()


class Chip(_Pastilla):
    """Interruptor: se ilumina en morado, con una transición suave, cuando está activado."""

    APAGADO = "#2e2850"

    def __init__(self, padre, texto, var, comando=None, valor=None):
        self._var, self._valor, self._comando = var, valor, comando
        self._on = 1.0 if self._encendido() else 0.0
        _Pastilla.__init__(self, padre, texto, ("Segoe UI Semibold", 9), 10, 5)
        self._traza = var.trace_add("write", self._al_cambiar_var)
        self.bind("<Destroy>", self._al_destruir, add="+")

    def _encendido(self):
        try:
            return bool(self._var.get()) if self._valor is None else self._var.get() == self._valor
        except tk.TclError:
            return False

    def _al_cambiar_var(self, *a):
        try:
            self._animar("_on", 1.0 if self._encendido() else 0.0, 190)
        except tk.TclError:
            pass

    def _al_destruir(self, e=None):
        try:
            self._var.trace_remove("write", self._traza)
        except Exception:
            pass

    def _aspecto(self):
        on = int(round(self._on * 5))
        if not self._activo():
            return (("c", on, "off"), mezclar(mezclar(self.APAGADO, MORADO, on / 5.0), self._fondo, 0.5), 0.0, 0.0,
                    mezclar(TEXTO, self._fondo, 0.5))
        hv = int(round(self._hover * 3))
        pu = int(round(self._pulso * 3))
        return (("c", on, hv, pu), mezclar(self.APAGADO, MORADO, on / 5.0), hv / 3.0 * 0.8 + pu / 3.0 * 0.6,
                0.22 * on / 5.0 + 0.22 * hv / 3.0 + 0.40 * pu / 3.0, mezclar(TEXTO, "#ffffff", on / 5.0))

    def _pulsado(self):
        if self._valor is None:
            self._var.set(not self._encendido())
        else:
            self._var.set(self._valor)
        if self._comando is not None:
            self._comando()


# ---------------------------------------------------------------- piezas de la interfaz nueva
LINEA = "#2f2852"          # rayas finas entre filas de ajustes
PISTA = "#3a3363"          # fondo de los interruptores apagados


def _foto_cacheada(clave, crear):
    foto = _FOTOS.get(clave)
    if foto is None:
        if len(_FOTOS) > 1500:
            _FOTOS.clear()
        foto = _FOTOS[clave] = foto_tk(crear())
    return foto


def pintar_tarjeta(w, h, fondo, color, radio=14, brillo=0.0):
    """Tarjeta redondeada con un filo de luz muy suave; con «brillo» el borde se enciende en dorado."""
    s = 2
    W, H = w * s, h * s
    im = Image.new("RGB", (W, H), fondo)
    d = ImageDraw.Draw(im)
    filo = mezclar(mezclar(color, "#ffffff", 0.07), ORO, brillo)
    r = radio * s
    d.rounded_rectangle([0, 0, W - 1, H - 1], radius=r, fill=filo)
    g = s * (2 if brillo > 0.05 else 1)
    d.rounded_rectangle([g, g, W - 1 - g, H - 1 - g], radius=max(1, r - g), fill=color)
    return im.resize((w, h), Image.LANCZOS)


_ESQUINAS = {}


def esquinas_tarjeta(r, fondo, color, b):
    """Las 4 esquinas suavizadas (r x r) de una tarjeta: arriba-izq, arriba-der, abajo-izq, abajo-der."""
    clave = (r, fondo, color, b)
    v = _ESQUINAS.get(clave)
    if v is None:
        n = 2 * r + 4
        im = pintar_tarjeta(n, n, fondo, color, r, b / 6.0)
        v = _ESQUINAS[clave] = tuple(foto_tk(im.crop(c)) for c in (
            (0, 0, r, r), (n - r, 0, n, r), (0, n - r, r, n), (n - r, n - r, n, n)))
    return v


class Tarjeta(tk.Canvas):
    """Caja redondeada (como las de las apps modernas). Lo de dentro va en «.cuerpo», un Frame normal."""

    def __init__(self, padre, color=PANEL, pad=12, radio=14, fondo=None):
        self._fondo = fondo or padre.cget("bg")
        tk.Canvas.__init__(self, padre, bg=self._fondo, highlightthickness=0, bd=0, takefocus=0)
        self.color, self.pad, self.radio = color, pad, radio
        self.brillo = 0.0
        self._pw = self._ph = 0
        self._req = (2 * pad, 2 * pad)
        tk.Canvas.configure(self, width=2 * pad, height=2 * pad)
        self._fotos = None
        self._b = None
        # La tarjeta se monta con 4 esquinas (imágenes suavizadas, guardadas) y rectángulos lisos: al cambiar
        # de tamaño solo se mueven piezas, sin volver a dibujar nada, y la ventana se estira sin tirones.
        self._rel = [self.create_rectangle(0, 0, 0, 0, fill=color, outline="") for _ in range(2)]
        self._bor = [self.create_rectangle(0, 0, 0, 0, outline="") for _ in range(4)]
        self._esq = [self.create_image(0, 0, anchor="nw") for _ in range(4)]
        self.cuerpo = tk.Frame(self, bg=color)
        self._win = self.create_window(pad, pad, anchor="nw", window=self.cuerpo)
        self.cuerpo.bind("<Configure>", self._al_cuerpo)
        self.bind("<Configure>", self._al_tam)

    def _al_cuerpo(self, e=None):
        w = self.cuerpo.winfo_reqwidth() + 2 * self.pad
        h = self.cuerpo.winfo_reqheight() + 2 * self.pad
        if self._req != (w, h):
            self._req = (w, h)
            tk.Canvas.configure(self, width=w, height=h)

    def _al_tam(self, e):
        if e.width != self._pw:
            self.itemconfigure(self._win, width=max(1, e.width - 2 * self.pad))
        if (e.width, e.height) != (self._pw, self._ph):
            self._pw, self._ph = e.width, e.height
            self._pintar()

    def _pintar(self):
        w, h = self._pw, self._ph
        r = self.radio
        if w < 2 * r + 2 or h < 2 * r + 2:
            return
        b = int(round(self.brillo * 6))
        g = 2 if b / 6.0 > 0.05 else 1
        if b != self._b:
            self._b = b
            self._fotos = esquinas_tarjeta(r, self._fondo, self.color, b)
            filo = mezclar(mezclar(self.color, "#ffffff", 0.07), ORO, b / 6.0)
            for i in range(4):
                self.itemconfigure(self._esq[i], image=self._fotos[i])
                self.itemconfigure(self._bor[i], fill=filo)
        for i, (x, y) in enumerate(((0, 0), (w - r, 0), (0, h - r), (w - r, h - r))):
            self.coords(self._esq[i], x, y)
        self.coords(self._rel[0], r, 0, w - r, h)
        self.coords(self._rel[1], 0, r, w, h - r)
        self.coords(self._bor[0], r, 0, w - r, g)
        self.coords(self._bor[1], r, h - g, w - r, h)
        self.coords(self._bor[2], 0, r, g, h - r)
        self.coords(self._bor[3], w - g, r, w, h - r)

    def poner_brillo(self, v):
        antes = int(round(self.brillo * 6))
        self.brillo = max(0.0, min(1.0, v))
        if int(round(self.brillo * 6)) != antes:
            self._pintar()


def pintar_interruptor(w, h, fondo, pos, hover, activo):
    s = 4
    W, H = w * s, h * s
    im = Image.new("RGB", (W, H), fondo)
    d = ImageDraw.Draw(im)
    pista = mezclar(PISTA, MORADO, pos)
    if hover:
        pista = mezclar(pista, "#ffffff", 0.10)
    perilla = "#ffffff" if pos > 0.5 else "#d9d3ee"
    if not activo:
        pista, perilla = mezclar(pista, fondo, 0.6), mezclar(perilla, fondo, 0.6)
    if pos > 0.02 and activo:              # un halo suave cuando está encendido
        halo = Image.new("L", (W, H), 0)
        ImageDraw.Draw(halo).rounded_rectangle([s, s, W - 1 - s, H - 1 - s], radius=H // 2, fill=int(110 * pos))
        im.paste(Image.new("RGB", (W, H), MORADO), (0, 0), halo.filter(ImageFilter.GaussianBlur(s * 1.5)))
    m = 2 * s
    d.rounded_rectangle([m, m, W - 1 - m, H - 1 - m], radius=(H - 2 * m) // 2, fill=pista)
    k = 3 * s
    dk = H - 2 * k
    x = k + (W - 2 * k - dk) * pos
    d.ellipse([x, k + s * 0.6, x + dk, k + dk + s * 0.6], fill=mezclar(pista, "#000000", 0.35))
    d.ellipse([x, k, x + dk, k + dk], fill=perilla)
    return im.resize((w, h), Image.LANCZOS)


class Interruptor(tk.Canvas):
    """Interruptor deslizante (encendido = morado). Va unido a una BooleanVar."""

    ANCHO, ALTO = 44, 26
    PASOS = 10

    def __init__(self, padre, var, comando=None, fondo=None):
        self._fondo = fondo or padre.cget("bg")
        tk.Canvas.__init__(self, padre, width=self.ANCHO, height=self.ALTO, bg=self._fondo,
                           highlightthickness=0, bd=0, cursor="hand2", takefocus=0)
        self._var, self._comando = var, comando
        self._pos = 1.0 if self._encendido() else 0.0
        self._hover = False
        self._activo = True
        self._foto = None
        self._img = self.create_image(0, 0, anchor="nw")
        self._pintar()
        self._traza = var.trace_add("write", self._al_cambiar_var)
        self.bind("<Destroy>", self._al_destruir, add="+")
        self.bind("<ButtonRelease-1>", lambda e: self.pulsar())
        self.bind("<Enter>", lambda e: self.encima(True))
        self.bind("<Leave>", lambda e: self.encima(False))

    def _encendido(self):
        try:
            return bool(self._var.get())
        except tk.TclError:
            return False

    def _pintar(self):
        p = int(round(self._pos * self.PASOS))
        hv = bool(self._hover and self._activo)
        self._foto = _foto_cacheada(("int", self._fondo, p, hv, self._activo),
                                    lambda: pintar_interruptor(self.ANCHO, self.ALTO, self._fondo, p / float(self.PASOS),
                                                               hv, self._activo))
        self.itemconfigure(self._img, image=self._foto)

    def _al_cambiar_var(self, *a):
        destino = 1.0 if self._encendido() else 0.0
        ini = self._pos
        if ANIM[0] is None or abs(destino - ini) < 0.01:
            self._pos = destino
            self._pintar()
            return

        def paso(t):
            self._pos = ini + (destino - ini) * suave(t)
            self._pintar()

        ANIM[0].lanzar((str(self), "pos"), 200, paso)

    def _al_destruir(self, e=None):
        try:
            self._var.trace_remove("write", self._traza)
        except Exception:
            pass

    def encima(self, si):
        self._hover = si
        self._pintar()

    def pulsar(self):
        if not self._activo:
            return
        self._var.set(not self._encendido())
        if self._comando is not None:
            self._comando()

    def activar(self, si):
        self._activo = bool(si)
        tk.Canvas.configure(self, cursor="hand2" if si else "arrow")
        self._pintar()


class FilaAjuste(tk.Frame):
    """Una fila de ajustes: título (y una explicación corta debajo) a la izquierda y el interruptor a la
    derecha. Se puede pulsar en cualquier parte de la fila."""

    def __init__(self, padre, texto, var, comando=None, detalle=None):
        self._bg = padre.cget("bg")
        tk.Frame.__init__(self, padre, bg=self._bg, cursor="hand2")
        self.inter = Interruptor(self, var, comando, fondo=self._bg)
        self.inter.pack(side="right", padx=(10, 0), pady=4)
        izq = tk.Frame(self, bg=self._bg)
        izq.pack(side="left", fill="x", expand=True)
        self.lbl = tk.Label(izq, text=texto, font=("Segoe UI Semibold", 10), fg=TEXTO, bg=self._bg, anchor="w")
        self.lbl.pack(fill="x")
        self.det = None
        if detalle:
            self.det = tk.Label(izq, text=detalle, font=("Segoe UI", 8), fg=APAGADO, bg=self._bg, anchor="w",
                                justify="left", wraplength=250)
            self.det.pack(fill="x")
            envolver(self.det, izq, 4, 120)
        for w in (self, izq, self.lbl) + ((self.det,) if self.det else ()):
            if w is not self.inter:
                w.bind("<ButtonRelease-1>", lambda e: self.inter.pulsar(), add="+")
                w.bind("<Enter>", lambda e: self.inter.encima(True), add="+")
                w.bind("<Leave>", lambda e: self.inter.encima(False), add="+")

    def ajustar(self, texto=None, activo=None):
        if texto is not None:
            self.lbl.config(text=texto)
        if activo is not None:
            self.inter.activar(activo)
            self.lbl.config(fg=TEXTO if activo else APAGADO)


class Segmentado(tk.Canvas):
    """Botones unidos para elegir una opción (como «Preguntar / Automáticas / Nunca»). La pastilla morada
    se desliza hasta la opción elegida."""

    ALTO = 32

    def __init__(self, padre, var, opciones, comando=None, fondo=None):
        self._fondo = fondo or padre.cget("bg")
        tk.Canvas.__init__(self, padre, height=self.ALTO, bg=self._fondo, highlightthickness=0, bd=0,
                           cursor="hand2", takefocus=0)
        self._var, self._ops, self._comando = var, list(opciones), comando
        f = fuente_tk(("Segoe UI Semibold", 9))
        tk.Canvas.configure(self, width=max(f.measure(t) for t, _v in self._ops) * len(self._ops) + 30 * len(self._ops))
        self._pw = 0
        self._x = None
        self._hover = -1
        self._f_pista = self._f_pild = None
        self._pista = self.create_image(0, 0, anchor="nw")
        self._pild = self.create_image(0, 0, anchor="nw")
        self._txt = [self.create_text(0, self.ALTO / 2.0, text=t, font=("Segoe UI Semibold", 9), fill=APAGADO)
                     for t, _v in self._ops]
        self._traza = var.trace_add("write", lambda *a: self._mover(True))
        self.bind("<Destroy>", self._al_destruir, add="+")
        self.bind("<Configure>", self._al_tam)
        self.bind("<ButtonRelease-1>", self._clic)
        self.bind("<Motion>", self._movimiento)
        self.bind("<Leave>", lambda e: self._poner_hover(-1))

    def _al_destruir(self, e=None):
        try:
            self._var.trace_remove("write", self._traza)
        except Exception:
            pass

    def _elegido(self):
        try:
            v = self._var.get()
        except tk.TclError:
            return 0
        for i, (_t, valor) in enumerate(self._ops):
            if valor == v:
                return i
        return 0

    def _seg(self):
        return self._pw / float(len(self._ops))

    def _al_tam(self, e):
        if e.width == self._pw:
            return
        self._pw = w = e.width
        h = self.ALTO
        sw = int(self._seg())
        self._f_pista = _foto_cacheada(("pista", w, h, self._fondo),
                                       lambda: pintar_tarjeta(w, h, self._fondo, CARD, h // 2 - 2))
        self.itemconfigure(self._pista, image=self._f_pista)
        self._f_pild = _foto_cacheada(("pild", sw, h, CARD),
                                      lambda: pintar_pastilla(sw, h, CARD, MORADO, h / 2.0 - 4, 3, 0.2, 0.0, 0.5))
        self.itemconfigure(self._pild, image=self._f_pild)
        for i, t in enumerate(self._txt):
            self.coords(t, (i + 0.5) * self._seg(), h / 2.0)
        self._mover(False)

    def _colores(self):
        el = self._elegido()
        for i, t in enumerate(self._txt):
            self.itemconfigure(t, fill="#ffffff" if i == el else (TEXTO if i == self._hover else APAGADO))

    def _mover(self, animar):
        if self._pw <= 1:
            return
        dest = self._elegido() * self._seg()
        ini = self._x
        self._colores()
        if not animar or ini is None or ANIM[0] is None:
            self._x = dest
            self.coords(self._pild, int(dest), 0)
            return

        def paso(t):
            self._x = ini + (dest - ini) * suave(t)
            self.coords(self._pild, int(round(self._x)), 0)

        ANIM[0].lanzar((str(self), "pild"), 220, paso)

    def _indice(self, x):
        if self._pw <= 1:
            return -1
        return max(0, min(len(self._ops) - 1, int(x / self._seg())))

    def _movimiento(self, e):
        self._poner_hover(self._indice(e.x))

    def _poner_hover(self, i):
        if i != self._hover:
            self._hover = i
            self._colores()

    def _clic(self, e):
        i = self._indice(e.x)
        if i < 0 or not (0 <= e.y <= self.ALTO):
            return
        valor = self._ops[i][1]
        if self._var.get() != valor:
            self._var.set(valor)
            if self._comando is not None:
                self._comando()


class MiniGrafica(tk.Canvas):
    """Barras de los últimos 7 días (la de hoy en dorado). Crecen con suavidad cuando cambian."""

    ALTO = 92

    def __init__(self, padre, fondo=None):
        self._fondo = fondo or padre.cget("bg")
        tk.Canvas.__init__(self, padre, height=self.ALTO, width=150, bg=self._fondo, highlightthickness=0, bd=0)
        self._dias = []
        self._ant = []
        self._pw = 0
        self._ph = self.ALTO
        self._alto_pedido = self.ALTO
        self.bind("<Configure>", self._al_tam)

    def _al_tam(self, e):
        if (e.width, e.height) != (self._pw, self._ph):
            self._pw, self._ph = e.width, e.height
            self._dibujar(1.0)

    def poner_alto(self, alto):
        """La gráfica crece hacia abajo cuando la ventana es más alta que lo que ocupa todo."""
        alto = int(alto)
        if alto != self._alto_pedido:
            self._alto_pedido = alto
            tk.Canvas.configure(self, height=alto)

    def poner(self, dias):
        """dias = [(fecha, cofres)] de más antiguo a hoy."""
        dias = list(dias)
        if dias == self._dias:
            return
        self._ant = [v for _d, v in self._dias] if len(self._dias) == len(dias) else [0] * len(dias)
        self._dias = dias
        if ANIM[0] is None or self._pw <= 1:
            self._dibujar(1.0)
            return
        ANIM[0].lanzar((str(self), "barras"), 520, lambda t: self._dibujar(suave(t)))

    def _dibujar(self, k):
        self.delete("all")
        w, h = self._pw, max(40, self._ph)
        n = len(self._dias)
        if w <= 1 or not n:
            return
        mx = max([1] + [v for _d, v in self._dias] + self._ant)
        arriba, abajo = 16, 18
        area = h - arriba - abajo
        paso = w / float(n)
        bw = min(26.0, paso * 0.58)
        letras = "LMXJVSD"
        for i, (d, v) in enumerate(self._dias):
            ant = self._ant[i] if i < len(self._ant) else 0
            val = ant + (v - ant) * k
            cx = (i + 0.5) * paso
            hoy = i == n - 1
            col = ORO if hoy else MORADO
            y1 = h - abajo
            alto = max(3.0, area * val / mx) if v or ant else 3.0
            fill = col if v else mezclar(self._fondo, "#ffffff", 0.10)
            self.create_rectangle(cx - bw / 2, y1 - alto, cx + bw / 2, y1, fill=fill, outline="")
            if v:
                self.create_line(cx - bw / 2 + 1, y1 - alto, cx + bw / 2 - 1, y1 - alto,
                                 fill=mezclar(col, "#ffffff", 0.45))
                self.create_text(cx, y1 - alto - 7, text=str(v), font=("Segoe UI Semibold", 8),
                                 fill=TEXTO if hoy else APAGADO)
            self.create_text(cx, h - 8, text="Hoy" if hoy else letras[d.weekday()], font=("Segoe UI", 8),
                             fill=ORO if hoy else APAGADO)


class BarraFina(tk.Canvas):
    """Barra de desplazamiento fina, oscura y redondeada (la de Windows es blanca y no pega)."""

    ANCHO = 10

    def __init__(self, padre, comando):
        self._fondo = padre.cget("bg")
        tk.Canvas.__init__(self, padre, width=self.ANCHO, bg=self._fondo, highlightthickness=0, bd=0,
                           takefocus=0, cursor="arrow")
        self._cmd = comando
        self._a, self._b = 0.0, 1.0
        self._hover = False
        self._arr = None
        self._pom = self.create_line(0, 0, 0, 0, width=6, capstyle="round", fill=mezclar(self._fondo, "#ffffff", 0.2))
        self.bind("<Configure>", lambda e: self._dib())
        self.bind("<Enter>", lambda e: self._encima(True))
        self.bind("<Leave>", lambda e: self._encima(False))
        self.bind("<ButtonPress-1>", self._clic)
        self.bind("<B1-Motion>", self._mover)
        self.bind("<ButtonRelease-1>", lambda e: self._soltar())

    def set(self, a, b):
        self._a, self._b = float(a), float(b)
        self._dib()

    def _alto(self):
        return max(1, self.winfo_height() - 8)

    def _dib(self):
        x = self.ANCHO / 2.0
        y0 = 4 + self._alto() * self._a + 3
        y1 = 4 + self._alto() * self._b - 3
        self.coords(self._pom, x, y0, x, max(y0 + 1, y1))
        vivo = self._hover or self._arr is not None
        self.itemconfigure(self._pom, fill=mezclar(self._fondo, "#ffffff", 0.34 if vivo else 0.18))

    def _encima(self, si):
        self._hover = si
        self._dib()

    def _clic(self, e):
        pos = (e.y - 4) / float(self._alto())
        if self._a <= pos <= self._b:
            self._arr = (e.y, self._a)
        else:                                  # clic fuera de la barra: salta hasta ahí
            self._cmd("moveto", pos - (self._b - self._a) / 2.0)
        self._dib()

    def _mover(self, e):
        if self._arr is not None:
            self._cmd("moveto", self._arr[1] + (e.y - self._arr[0]) / float(self._alto()))

    def _soltar(self):
        self._arr = None
        self._dib()


class Desplazable(tk.Frame):
    """Hueco con desplazamiento vertical: si la ventana es más baja que su contenido aparece una barra fina
    a la derecha y la rueda del ratón lo mueve con suavidad. Lo de dentro va en «.interior» y siempre
    ocupa todo el ancho disponible."""

    def __init__(self, padre, bg=BG):
        tk.Frame.__init__(self, padre, bg=bg)
        self.grid_rowconfigure(0, weight=1)
        self.grid_columnconfigure(0, weight=1)
        self.cv = tk.Canvas(self, bg=bg, highlightthickness=0, bd=0, takefocus=0, width=10, height=10)
        self.cv.grid(row=0, column=0, sticky="nsew")
        self.barra = BarraFina(self, self.cv.yview)
        self.cv.configure(yscrollcommand=self.barra.set)
        self.interior = tk.Frame(self.cv, bg=bg)
        self._win = self.cv.create_window(0, 0, anchor="nw", window=self.interior)
        self._barra_vis = False
        self._dest = None
        self.al_cambiar = None                 # al_cambiar(ancho, alto) cuando cambia el hueco visible
        self._tam = (0, 0)
        self._pend = None
        self._ancho_aplicado = 0
        self.interior.bind("<Configure>", self._al_interior)
        self.cv.bind("<Configure>", self._al_cv)

    def alto_contenido(self):
        return self.interior.winfo_reqheight()

    def _al_interior(self, e=None):
        self.cv.configure(scrollregion=(0, 0, max(1, self.cv.winfo_width()), max(1, self.alto_contenido())))
        self._revisar()
        if self.al_cambiar is not None:
            self.al_cambiar(*self._tam)

    def _al_cv(self, e):
        # Mientras se arrastra el borde de la ventana, el contenido no se recoloca a cada píxel (en Windows
        # eso es lento con tantas piezas y la ventana iría a tirones): se recoloca una vez, al parar.
        primero = self._tam == (0, 0)
        self._tam = (e.width, e.height)
        if self._pend is not None:
            self.after_cancel(self._pend)
            self._pend = None
        if primero:
            self._aplicar_tam()
        else:
            self._pend = self.after(self.ESPERA_MS, self._aplicar_tam)

    ESPERA_MS = 90

    def _aplicar_tam(self, intentos=0):
        self._pend = None
        # Si aún se está arrastrando el borde (botón del ratón pulsado), se espera a soltarlo
        # (como mucho unos segundos, por si el botón se queda pulsado por otra cosa).
        if intentos < 60 and raton_pulsado():
            self._pend = self.after(60, lambda: self._aplicar_tam(intentos + 1))
            return
        w, h = self._tam
        if w != self._ancho_aplicado:
            self._ancho_aplicado = w
            self.cv.itemconfigure(self._win, width=w)
        self.cv.configure(scrollregion=(0, 0, max(1, w), max(1, self.alto_contenido())))
        self._revisar()
        if self.al_cambiar is not None:
            self.al_cambiar(w, h)

    def _revisar(self):
        alto, vis = self.alto_contenido(), self.cv.winfo_height()
        if vis <= 1:
            return
        # con un pequeño margen, para que la barra no aparezca y desaparezca sin parar
        if not self._barra_vis and alto > vis + 1:
            self._barra_vis = True
            self.barra.grid(row=0, column=1, sticky="ns", padx=(2, 2), pady=4)
        elif self._barra_vis and alto < vis - 14:
            self._barra_vis = False
            self.barra.grid_remove()
            self.cv.yview_moveto(0)

    def rueda(self, e):
        if not self._barra_vis:
            return
        total = float(max(1, self.alto_contenido()))
        vis = self.cv.winfo_height()
        ahora = self.cv.yview()[0] * total
        base = self._dest if self._dest is not None else ahora
        dest = max(0.0, min(total - vis, base - e.delta / 120.0 * 72))
        ini = ahora
        self._dest = dest

        def paso(t):
            self.cv.yview_moveto((ini + (dest - ini) * suave(t)) / total)

        def fin():
            self._dest = None

        if ANIM[0] is None:
            paso(1.0)
            fin()
        else:
            ANIM[0].lanzar((str(self), "rueda"), 170, paso, fin)


def raton_pulsado():
    try:
        return bool(ctypes.windll.user32.GetAsyncKeyState(0x01) & 0x8000)
    except Exception:
        return False


def quitar_capa(w):
    """Tras el fundido de entrada, Windows deja la ventana como «capa» (para la transparencia) y así cada
    cambio de tamaño o movimiento cuesta varias veces más. Si ya es opaca, se le quita."""
    try:
        if str(w.attributes("-transparentcolor") or "") or float(w.attributes("-alpha")) < 0.999:
            return
        hwnd = int(w.wm_frame(), 16)
        u32 = ctypes.windll.user32
        ex = u32.GetWindowLongW(hwnd, -20)
        if ex & 0x80000:
            u32.SetWindowLongW(hwnd, -20, ex & ~0x80000)
            u32.SetWindowPos(hwnd, 0, 0, 0, 0, 0, 0x27)     # sin mover ni cambiar tamaño ni orden: solo refresca
    except Exception:
        pass


def envolver(lbl, contenedor, menos=0, minimo=80):
    """El texto de «lbl» se parte en renglones según el ancho que tenga «contenedor» en cada momento.
    (La etiqueta pide un ancho mínimo, así no empuja al contenedor y no se forma un bucle de tamaños.)"""
    lbl.config(width=1)

    def ajustar(e):
        w = max(minimo, e.width - menos)
        if int(lbl.cget("wraplength") or 0) != w:
            lbl.config(wraplength=w)

    contenedor.bind("<Configure>", ajustar, add="+")


# ---------------------------------------------------------------- conexión online
class ErrorHTTP(Exception):
    def __init__(self, codigo):
        super().__init__("HTTP %d" % codigo)
        self.codigo = codigo


def _pedir(metodo, ruta, cuerpo=None, timeout=8):
    """Una consulta suelta a la base de datos de las salas (para crear / unirse)."""
    p = urllib.parse.urlsplit(URL_SALAS)
    c = http.client.HTTPSConnection(p.netloc, timeout=timeout)
    try:
        datos = None
        cab = {}
        if cuerpo is not None:
            datos = json.dumps(cuerpo).encode("utf-8")
            cab["Content-Type"] = "application/json"
        c.request(metodo, p.path.rstrip("/") + ruta + ".json", body=datos, headers=cab)
        r = c.getresponse()
        txt = r.read().decode("utf-8")
        if r.status >= 400:
            raise ErrorHTTP(r.status)
        return json.loads(txt) if txt else None
    finally:
        c.close()


def estado_sala(sala):
    """'libre' (no existe), 'vacia' (sin jugadores), 'vieja' (solo entradas de hace rato)
    o 'viva' (alguien se ha conectado en los últimos 5 minutos)."""
    d = _pedir("GET", "/salas/%s" % sala)
    if not isinstance(d, dict):
        return "libre"
    j = d.get("j")
    if not isinstance(j, dict) or not j:
        return "vacia"
    ahora = time.time() * 1000.0
    for v in j.values():
        t = v.get("t") if isinstance(v, dict) else None
        if isinstance(t, (int, float)) and ahora - t < 300000:
            return "viva"
    return "vieja"


def preparar_sala(modo, sala, pid):
    """Comprueba la sala y, si crea, la deja lista con este jugador de líder.
    Devuelve (True, "") o (False, mensaje para mostrar)."""
    try:
        estado = estado_sala(sala)
        if modo == "crear":
            if estado == "viva":
                return False, "Ya existe una sala «%s» con gente dentro. Elige otro nombre, o pulsa «Unirse a sala»." % sala
            if estado != "libre":
                _pedir("DELETE", "/salas/%s" % sala)      # restos antiguos: se empieza limpio
            _pedir("PUT", "/salas/%s/meta/lider" % sala, pid)
            return True, ""
        if estado in ("libre", "vacia"):
            return False, "No existe ninguna sala «%s». Pídele el nombre exacto a quien la creó (o créala tú)." % sala
        return True, ""
    except ErrorHTTP as e:
        if e.codigo in (401, 403):
            return False, "El servidor no deja entrar (reglas de la base de datos)."
        return False, "Error del servidor (%d). Inténtalo en un momento." % e.codigo
    except Exception:
        return False, "No hay conexión con el servidor. Revisa tu internet e inténtalo otra vez."


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
            foto = icono_flotante(iw, int(round(38 * k)))
            if foto is not None:
                c.create_image(pad + iw / 2.0, y_fila1 + h1 / 2.0, image=foto)
            else:
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


# ---------------------------------------------------------------- análisis en segundo plano
def tapar_rects(img, x0, y0, rects):
    """Pinta de negro, en una captura que empieza en (x0, y0), los rectángulos de pantalla dados."""
    d = None
    for izq, arr, der, aba in rects:
        ax, ay = max(izq, x0) - x0, max(arr, y0) - y0
        bx, by = min(der, x0 + img.width) - x0, min(aba, y0 + img.height) - y0
        if bx > ax and by > ay:
            if d is None:
                d = ImageDraw.Draw(img)
            d.rectangle([ax, ay, bx, by], fill=(0, 0, 0))


def captura_zona(sct, rect, tapas):
    """Captura la zona de los avisos. Devuelve (pequeña para analizar, original, zona del detector de
    siempre, original sin las ventanas del programa)."""
    left, top, w, h = rect
    x = left + int(FX0 * w)
    y = top + int(FY0 * h)
    rw = max(32, int(FW * w))
    rh = max(32, int(FH * h))
    shot = sct.grab({"left": x, "top": y, "width": rw, "height": rh})
    img = Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")
    base = img.copy()
    tapar_rects(base, x, y, tapas)
    esc = ANCHO_ANALISIS_BASE / float(w)         # el texto se analiza siempre al mismo tamaño
    pequena = base.resize((max(40, int(round(rw * esc))), max(40, int(round(rh * esc)))), Image.BICUBIC)
    # la zona exacta que miraba el detector de siempre (0.62, 0.26, 0.13 x 0.09)
    ox = int(0.62 * w) - int(FX0 * w)
    oy = int(0.26 * h) - int(FY0 * h)
    ow, oh = max(8, int(0.13 * w)), max(4, int(0.09 * h))
    vieja = base.crop((ox, oy, ox + ow, oy + oh)).resize((84, 32), Image.BICUBIC)
    return pequena, img, vieja, base


def captura_caja(sct, rect, caja):
    left, top, w, h = rect
    fx, fy, fw, fh = caja
    shot = sct.grab({"left": left + int(fx * w), "top": top + int(fy * h),
                     "width": max(4, int(fw * w)), "height": max(4, int(fh * h))})
    return Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")


def mirar_lobby(sct, rect):
    """¿Se ve el lobby? Devuelve (sí/no, fracción botón, fracción pastilla, modo) o None si falla."""
    try:
        ok, fa, fp = hay_lobby(captura_caja(sct, rect, LOBBY_BOTON), captura_caja(sct, rect, LOBBY_PASTILLA))
    except Exception:
        return None
    modo = "fijo" if ok else ""
    if not ok:
        # el detector de cajas fijas no lo ve: se prueba el tolerante (pantalla entera)
        try:
            ok2, _b, _p, _pal = hay_lobby_amplio(captura_caja(sct, rect, (0.0, 0.0, 1.0, 1.0)))
            if ok2:
                ok, modo = True, "amplio"
        except Exception:
            pass
    return ok, fa, fp, modo


def analizar_fotograma(sct, rect, tapas, lobby, lector):
    """Todo lo que pesa de un fotograma: capturar, buscar avisos, leer el texto y mirar el lobby."""
    t0 = time.time()
    pequena, grande, vieja, base = captura_zona(sct, rect, tapas)
    r = {"rect": rect, "pequena": pequena, "grande": grande, "base": base,
         "todos": buscar_avisos(pequena), "clasico": hay_aviso_clasico(vieja), "lec": None, "err_lec": ""}
    try:
        r["lista"] = buscar_lista_cofres(pequena)
    except Exception:
        r["lista"] = None
    if lector is not None:
        try:
            r["lec"] = lector.leer(base, rect[2])
        except Exception as e:
            r["lec"] = {"ok": False}
            r["err_lec"] = "%s: %s" % (type(e).__name__, e)
    r["lobby"] = mirar_lobby(sct, rect) if lobby else None
    r["ms"] = int((time.time() - t0) * 1000)
    return r


class Trabajador(threading.Thread):
    """Hace en segundo plano lo que pesa (capturar la pantalla, analizarla y esperar al lector de texto),
    para que la ventana vaya siempre fluida: nada de eso se hace en el hilo de la interfaz."""

    def __init__(self):
        threading.Thread.__init__(self, daemon=True)
        self.ev = threading.Event()
        self.tarea = None
        self.res = None
        self.start()

    def libre(self):
        return self.tarea is None and self.res is None

    def pedir(self, funcion, *args):
        if not self.libre():
            return False
        self.tarea = (funcion, args)
        self.ev.set()
        return True

    def recoger(self):
        """(True, resultado) o (False, error) si ya ha terminado; None si aún no."""
        r = self.res
        if r is not None:
            self.res = None
        return r

    def run(self):
        sct = None
        while True:
            self.ev.wait()
            self.ev.clear()
            t = self.tarea
            if t is None:
                continue
            try:
                if sct is None:
                    sct = MSS()          # cada hilo necesita su propio capturador
                r = (True, t[0](sct, *t[1]))
            except Exception as e:
                import traceback
                r = (False, "%s: %s | %s" % (type(e).__name__, e,
                                            " | ".join(traceback.format_exc().strip().splitlines()[-3:])))
                sct = None
            self.res = r
            self.tarea = None


# ---------------------------------------------------------------- ventana de estadísticas
def grafico_barras(c, barras, color, color_ult, etiqueta_media, ancho=520, alto=175, crecer=1.0):
    """barras = [(valor, texto_linea1, texto_linea2), ...]. Dibujado a mano, sin librerías.
    «crecer» (0-1) es la animación de entrada: las barras suben desde abajo."""
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
            h = area * v / float(mx) * crecer
            relleno = color_ult if ultimo else color
            c.create_rectangle(x0, base - h, x0 + bw, base, fill=relleno, outline=CONTORNO)
            if h > 4:                      # filo de luz arriba de cada barra
                c.create_line(x0 + 1, base - h + 1, x0 + bw - 1, base - h + 1, fill=mezclar(relleno, "#ffffff", 0.45))
            if crecer > 0.85:
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
        self._dias = []
        self._parts = []
        w = self.win = tk.Toplevel(app.root)
        w.title("Estadísticas de cofres")
        w.configure(bg=BG)
        app.preparar_ventana(w)
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
        self.lbl_zona = tk.Label(cab, text="", font=("Segoe UI", 9), fg=CIAN, bg=CARD)
        self.lbl_zona.pack(side="right")
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
        # al abrir, las barras de las gráficas suben desde abajo
        self.pintar_graficas(0.0)
        app.anim.lanzar(("stats", str(w)), 620, lambda t: self.pintar_graficas(suave(t)))

    def pintar_graficas(self, crecer=1.0):
        grafico_barras(self.cv_dias, self._dias, ORO_OSC, ORO, "media/día", crecer=crecer)
        grafico_barras(self.cv_part, self._parts, MORADO, COLOR_PARTIDA, "media/partida", crecer=crecer)

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
        sig = (self.app.hist.version, st["hoy_fecha"], nombre_zona())
        if sig == self.sig and not forzar:
            return
        self.sig = sig
        v = self.v
        self.lbl_zona.config(text="Cada día va de 00:00 a 00:00 (%s)" % etiqueta_zona())
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

        self._dias = [(n, "LMXJVSD"[d.weekday()], str(d.day)) for d, n in st["dias14"]]
        self._parts = [(n, "%02d" % dt.day, "%02dh" % dt.hour) for n, dt in st["ultimas"]]
        self.pintar_graficas()

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
        root.resizable(True, True)
        poner_icono_ventana(root)
        self.anim = Animador(root)
        ANIM[0] = self.anim

        threading.Thread(target=asegurar_sonidos, daemon=True).start()
        copia_diaria()

        datos = self.cargar()
        if not datos:      # instalación nueva (no hay archivo de datos): el modo «Replays» viene activado por defecto
            datos = {"ui": {"modo_conteo": "replays"}, "manual": True, "repeticion": True}
        # ajustes nuevos: ventana encima de las demás o no, conteo solo manual y lector de texto
        self.ini_encima = bool(datos.get("encima", False))
        self.ini_manual = bool(datos.get("manual", False))
        self.ini_ocr = bool(datos.get("ocr", True))
        self.ini_rep = bool(datos.get("repeticion", True))
        self.cfg_tam = str(datos.get("tam_ventana") or "")          # tamaño de la ventana («ancho x alto»)
        self.cfg_tam_aj = str(datos.get("tam_ajustes") or "")       # y el de la ventana de ajustes
        self.rec = None                # recuento pendiente con la repetición de la partida recién cerrada
        self.ult_recuento = ""
        root.attributes("-topmost", self.ini_encima)
        poner_zona(str(datos.get("zona", ZONA_DEF)))
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
        self.ini_fotos = bool(datos.get("fotos", False))
        self.ini_obs = bool(datos.get("obs", False))
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
        try:                                  # el nombre de Epic con el que juegas, si no has puesto otro tú
            epic = nombre_epic()
            actual = self.cfg_on.get("nombre")
            if epic and actual in ("", "Jugador", nombre_por_defecto(), self.cfg_on.get("nombre_epic")):
                self.cfg_on["nombre"] = epic
            if epic:
                self.cfg_on["nombre_epic"] = epic
        except Exception:
            pass
        if not isinstance(self.cfg_on.get("alias"), dict):
            self.cfg_on["alias"] = {}
        self.cfg_on["url"] = URL_SALAS        # la base de datos es siempre la misma
        self.cfg_on["sala"] = limpiar_sala(self.cfg_on.get("sala", ""))

        self.hist = Historial(ARCHIVO_HIST)
        self._st = None
        self._st_clave = None
        self._res_clave = None

        # estado del detector de avisos
        self.avisos_conf = 0      # cuántos avisos de cofre damos por "ya contados" ahora mismo
        self.cand_n = 0
        self.sube_hueco = 0
        self.lista_max = 0        # máximo de cofres vistos en el aviso apilado que sigue en pantalla
        self.lista_cero = 0       # fotogramas seguidos sin aviso apilado
        self.lista_hist = deque(maxlen=3)   # últimas lecturas del aviso apilado (para ignorar lecturas sueltas mal hechas)
        self.t_visto = 0.0        # última vez que se vio el aviso (para saber cuándo da por terminado)
        self.pos_avisos = []      # posición vertical de los avisos ya contados
        self.n_visto = 0          # avisos vistos en el último fotograma
        self.visto_seg = 0        # fotogramas seguidos viendo algún aviso
        self.frames_recientes = deque(maxlen=8)
        self.t_frame = 0.0
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
        self.lobby_modo = ""
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
        self.trab = Trabajador()       # captura y análisis en segundo plano (la ventana no se traba)
        self.t_lobby = 0.0
        self.ms_fondo = 0
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
        self.sesion_previa = None      # cofres de la partida que se cerró la última vez (para «Deshacer»)
        self._obs_clave = None
        self._ult_err = ""
        # lector de texto (OCR de Windows) y seguimiento de las líneas del aviso
        self.seguidor = SeguidorCofres()
        self.ses_leg = 0               # cofres que ha visto el detector de siempre en el aviso actual
        self.ses_extra = 0             # multiplicadores que solo ha visto el detector de siempre
        self.ses_cont = 0              # cofres ya sumados del aviso actual
        self.t_ses = 0.0
        self.t_ocr_ve = 0.0            # última vez que el lector leyó algo
        self.t_tick = time.time()
        self.ocr_txt = ""
        self.lecturas = deque(maxlen=16)
        self.ultima_base = None
        self._err_ocr = ""
        try:
            self.lector = LectorAvisos()
        except Exception:
            self.lector = None
        # interfaz
        self.luz_estado = None
        self.luz_color = APAGADO
        self.meta_frac = None
        self.meta_dest = None
        self.meta_brillo = None
        self._foto_meta = None
        self._ind_tab = None
        self._era_manual = False


        self.sync = Sincronizador()
        self.aplicar_conexion()
        self.sync.start()

        self.construir()
        self.tamano_inicial(datos)
        self.recalcular_atajos()
        if self.var_ov.get():
            self.overlay = Overlay(self, self.cfg_ov)
        self.preparar_ventana(root)
        root.protocol("WM_DELETE_WINDOW", self.cerrar)
        self.guardar()          # deja los archivos creados desde el primer momento
        self.tick()
        self.revisar_teclas()
        self.ciclo_amigo()
        self.root.after(1500, lambda: self.buscar_actualizaciones(False))
        self.root.after(3000, self.pedir_novedades)
        if not self.var_fotos.get():
            self.borrar_fotos()          # limpia las fotos antiguas al abrir

    # ---------- piezas de interfaz ----------
    def boton(self, padre, texto, comando, color, ancho=7):
        """Botón de color: redondeado, con brillo suave al pasar el ratón y un destello al pulsarlo."""
        return BotonSuave(padre, texto, comando, color, ancho)

    def color_suave(self, widget, opcion, normal, encima, ms=150):
        """Hace que un color del widget (el del texto, normalmente) cambie con suavidad al pasar el ratón."""
        est = {"v": 0.0}

        def ir(destino):
            ini = est["v"]

            def paso(t):
                est["v"] = ini + (destino - ini) * suave(t)
                widget.config(**{opcion: mezclar(normal, encima, est["v"])})

            self.anim.lanzar((str(widget), opcion), ms, paso)

        widget.bind("<Enter>", lambda e: ir(1.0), add="+")
        widget.bind("<Leave>", lambda e: ir(0.0), add="+")

    def preparar_ventana(self, w, aparecer=True):
        """Lo común a todas las ventanas del programa: encima de las demás o no (según el ajuste),
        barra de título oscura y aparición suave."""
        try:
            w.attributes("-topmost", bool(self.var_encima.get()))
        except tk.TclError:
            pass
        try:
            w.after(40, lambda: estilo_barra_titulo(w))
        except tk.TclError:
            pass
        if aparecer:
            self.aparecer(w)

    def aparecer(self, w, ms=180):
        try:
            w.attributes("-alpha", 0.0)
        except tk.TclError:
            return

        def fin():
            try:
                w.attributes("-alpha", 1.0)
                quitar_capa(w)
            except tk.TclError:
                pass

        self.anim.lanzar(("alfa", str(w)), ms, lambda t: w.attributes("-alpha", suave(t)), fin)
        try:
            w.after(ms + 500, fin)             # por si la animación no llegara a terminar
        except tk.TclError:
            pass

    def aplicar_encima(self):
        """Pone (o quita) «siempre encima» en la ventana principal y en las demás del programa.
        El número flotante no se toca: ese va siempre encima del juego."""
        encima = bool(self.var_encima.get())
        for w in [self.root] + [x for x in self.root.winfo_children() if isinstance(x, tk.Toplevel)]:
            if self.overlay is not None and w is self.overlay.win:
                continue
            try:
                w.attributes("-topmost", encima)
            except tk.TclError:
                pass

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
        b = tk.Button(padre, text=texto, command=comando, bg=bg, fg=fg, activebackground=bg,
                      activeforeground=ORO, relief="flat", bd=0, font=("Segoe UI", 9), cursor="hand2")
        self.color_suave(b, "fg", fg, "#fff0b8" if fg == ORO else ("#ffb3bb" if fg == ROJO else ORO))
        return b

    def menu_opciones(self, padre, var, valores, comando=None):
        om = tk.OptionMenu(padre, var, *valores, command=comando)
        om.config(bg=CARD, fg=TEXTO, activebackground=mezclar(CARD, "#ffffff", 0.08), activeforeground=ORO,
                  highlightthickness=0, bd=0, relief="flat", font=("Segoe UI", 9), padx=8, pady=3, cursor="hand2",
                  indicatoron=False)
        om["menu"].config(bg=CARD, fg=TEXTO, activebackground=MORADO, activeforeground="#ffffff",
                          font=("Segoe UI", 9), bd=0)
        try:
            om.config(textvariable="")
        except tk.TclError:
            pass
        self._menu_con_flecha(om, var)
        return om

    @staticmethod
    def _menu_con_flecha(om, var):
        """El desplegable enseña la opción elegida con una flechita al lado."""
        def poner(*a):
            try:
                om.config(text="%s  ▾" % var.get())
            except tk.TclError:
                pass
        traza = var.trace_add("write", poner)
        om.bind("<Destroy>", lambda e: var.trace_remove("write", traza) if e.widget is om else None, add="+")
        poner()
        return om

    # ---------- interfaz ----------
    ANCHO_UI = 410

    def construir(self):
        # todo va dentro de un hueco con desplazamiento: la ventana se puede hacer del tamaño que quieras
        self.vista = Desplazable(self.root)
        self.vista.pack(fill="both", expand=True)
        self.marco = tk.Frame(self.vista.interior, bg=BG)
        self.marco.pack(padx=12, pady=(8, 10), fill="both", expand=True)
        marco = self.marco
        self.f_grande = tkfont.Font(family="Segoe UI Black", size=44)
        self._resp = None
        self._resp_pend = False
        self._graf_pend = None
        self.root.bind("<MouseWheel>", self.vista.rueda, add="+")

        # --- cabecera ---
        cab = tk.Frame(marco, bg=BG)
        cab.pack(fill="x", pady=(0, 8))
        self.img_cab = icono_cabecera(max(30, int(fuente_tk(("Segoe UI Semibold", 13)).metrics("linespace") * 1.7)), BG)
        if self.img_cab is not None:
            tk.Label(cab, image=self.img_cab, bg=BG, bd=0).pack(side="left", padx=(0, 6))
        else:                                  # sin el icono (no debería pasar): el cofre dibujado de antes
            icono = tk.Canvas(cab, width=46, height=38, bg=BG, highlightthickness=0)
            icono.pack(side="left", padx=(0, 8))
            dibujar_cofre(icono)
        tit = tk.Frame(cab, bg=BG)
        tit.pack(side="left")
        tk.Label(tit, text="Contador de cofres", font=("Segoe UI Semibold", 13), fg=ORO, bg=BG).pack(anchor="w")
        tk.Label(tit, text="versión %s" % VERSION, font=("Segoe UI", 8), fg=APAGADO, bg=BG).pack(anchor="w")
        self.btn_compacto = self.boton_texto(cab, "▴", self.alternar_compacto, bg=BG, fg=APAGADO)
        self.btn_compacto.config(font=("Segoe UI", 12))
        self.btn_compacto.pack(side="right", padx=(6, 0))
        est = tk.Frame(cab, bg=BG)
        est.pack(side="right")
        # luz de estado: un punto con halo que cambia de color con suavidad y late al ver un cofre
        self.cv_luz = tk.Canvas(est, width=24, height=24, bg=BG, highlightthickness=0, bd=0)
        self.cv_luz.pack(side="left")
        self.luz_aro = self.cv_luz.create_oval(7, 7, 17, 17, outline=BG, width=2)
        self.luz_halo = self.cv_luz.create_oval(5, 5, 19, 19, fill=mezclar(BG, APAGADO, 0.28), outline="")
        self.luz_punto = self.cv_luz.create_oval(8, 8, 16, 16, fill=APAGADO, outline="")
        self.lbl_luz = tk.Label(est, text="esperando", font=("Segoe UI", 9), fg=APAGADO, bg=BG)
        self.lbl_luz.pack(side="left", padx=(2, 0))

        # --- tarjeta principal: total y partida ---
        self.t_hero = Tarjeta(marco, pad=16, radio=16)
        self.t_hero.pack(fill="x")
        h = self.panel_num = self.t_hero.cuerpo
        fila = tk.Frame(h, bg=PANEL)
        fila.pack(fill="x")
        col_t = tk.Frame(fila, bg=PANEL)
        col_t.pack(side="left", fill="both", expand=True)
        tk.Label(col_t, text="TOTAL DE COFRES", font=("Segoe UI Semibold", 9), fg=ORO_OSC, bg=PANEL).pack(anchor="w")
        self.lbl_total = tk.Label(col_t, text=str(self.total), font=self.f_grande, fg=ORO, bg=PANEL,
                                  width=5, anchor="w", cursor="hand2", bd=0, padx=0)
        self.lbl_total.pack(anchor="w")
        self.lbl_total.bind("<Double-Button-1>", self.editar)
        tk.Frame(fila, bg=LINEA, width=1).pack(side="left", fill="y", padx=14, pady=8)
        col_p = tk.Frame(fila, bg=PANEL)
        col_p.pack(side="left", fill="both")
        tk.Label(col_p, text="ESTA PARTIDA", font=("Segoe UI Semibold", 9), fg=ORO_OSC, bg=PANEL).pack(anchor="w")
        self.lbl_sesion = tk.Label(col_p, text=str(self.sesion), font=self.f_grande, fg=COLOR_PARTIDA,
                                   bg=PANEL, width=4, anchor="w", cursor="hand2", bd=0, padx=0)
        self.lbl_sesion.pack(anchor="w")
        self.lbl_sesion.bind("<Double-Button-1>", self.editar_partida)
        self.lbl_ritmo = tk.Label(h, text="", font=("Segoe UI", 9), fg=CIAN, bg=PANEL, anchor="w")
        self.lbl_ritmo.pack(fill="x", pady=(2, 0))

        # --- botones de contar ---
        fb = tk.Frame(marco, bg=BG)
        fb.pack(fill="x", pady=(10, 0))
        for c, peso in enumerate((2, 3, 2, 3)):
            fb.grid_columnconfigure(c, weight=peso)
        self.btn_menos = self.boton(fb, "−1", lambda: self.sumar(-1, False), "#c0394b", 3)
        self.btn_mas = self.boton(fb, "+1", lambda: self.sumar(1, False), "#2e9e5b", 3)
        self.btn_editar = self.boton(fb, "✎ Editar", self.editar, MORADO, 3)
        self.btn_nueva = self.boton(fb, "↺ Nueva partida", self.nueva_partida, "#4a4468", 3)
        for c, b in enumerate((self.btn_menos, self.btn_mas, self.btn_editar, self.btn_nueva)):
            b.grid(row=0, column=c, sticky="ew", padx=(0 if c == 0 else 3, 0))
        pista = tk.Frame(marco, bg=BG)
        pista.pack(fill="x", pady=(2, 0))
        self.boton_texto(pista, "↶ Deshacer cierre", self.deshacer_partida, bg=BG,
                         fg=ORO).pack(side="right")
        tk.Label(pista, text="Doble clic en un número para editarlo", font=("Segoe UI", 8), fg=APAGADO,
                 bg=BG, anchor="w", width=1).pack(side="left", fill="x", expand=True)

        # --- meta ---
        self.t_meta = Tarjeta(marco, pad=10)
        self.t_meta.pack(fill="x", pady=(8, 0))
        fm = tk.Frame(self.t_meta.cuerpo, bg=PANEL)
        fm.pack(fill="x")
        self.boton_texto(fm, "✎ Meta", self.editar_meta, bg=PANEL, fg=ORO).pack(side="right")
        self.cv_meta = tk.Canvas(fm, width=200, height=26, bg=PANEL, highlightthickness=0)
        self.cv_meta.pack(side="left", fill="x", expand=True, padx=(0, 8))
        self._meta_w = 0
        self.cv_meta.bind("<Configure>", self._al_tam_meta)
        self.lbl_meta = tk.Label(self.t_meta.cuerpo, text="", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL,
                                 wraplength=self.ANCHO_UI - 30, justify="left", anchor="w")
        self.lbl_meta.pack(fill="x")
        envolver(self.lbl_meta, self.t_meta.cuerpo)

        # --- lo que se esconde en el modo compacto ---
        self.extra = tk.Frame(marco, bg=BG)
        self.construir_resumen(self.extra)
        self.t_equipo = Tarjeta(self.extra, pad=12)
        self.t_equipo.pack(fill="x", pady=(8, 0))
        self.construir_amigos(self.t_equipo.cuerpo)

        # --- botones de abajo: número flotante, estadísticas y ajustes ---
        self.fila_acciones = tk.Frame(marco, bg=BG)
        self.fila_acciones.pack(fill="x", pady=(10, 0))
        for c in range(3):
            self.fila_acciones.grid_columnconfigure(c, weight=1, uniform="acciones")
        self.btn_overlay = self.boton(self.fila_acciones, "👁 Overlay", self.alternar_overlay_boton, "#4a4468", 3)
        self.btn_stats = self.boton(self.fila_acciones, "▥ Estadísticas", self.alternar_stats, AZUL, 3)
        self.btn_ajustes = self.boton(self.fila_acciones, "⚙ Ajustes", self.alternar_ajustes, MORADO, 3)
        for c, b in enumerate((self.btn_overlay, self.btn_stats, self.btn_ajustes)):
            b.grid(row=0, column=c, sticky="ew", padx=(0 if c == 0 else 3, 0))

        # --- estado ---
        self.lbl_estado = tk.Label(marco, text="Iniciando...", font=("Segoe UI", 8), fg=APAGADO,
                                   bg=BG, wraplength=self.ANCHO_UI, justify="center")
        self.lbl_estado.pack(fill="x", pady=(8, 0))
        envolver(self.lbl_estado, marco)

        # --- ventana de ajustes (se prepara ya, escondida, para que se abra al instante) ---
        self.construir_ventana_ajustes()
        self.var_ov.trace_add("write", lambda *a: self.pintar_btn_overlay())
        self.pintar_btn_overlay()

        self.actualizar_textos_teclas()
        self.pintar_meta()
        self.pintar_resumen()
        self.pintar_amigo(forzar=True)
        self.aplicar_compacto(bool(self.cfg_ui.get("compacto")), guardar=False, ajustar_alto=False)
        self.vista.al_cambiar = self.programar_adaptar

    # ---------- tamaño de la ventana (se adapta a cualquier tamaño) ----------
    def ancho_minimo(self):
        """El ancho más pequeño en el que cabe todo sin cortarse."""
        f0, c0 = self.f_grande.cget("size"), self._cols_cifras
        self.f_grande.configure(size=40)
        self.colocar_cifras(2)
        self.root.update_idletasks()
        w = self.marco.winfo_reqwidth() + 24 + BarraFina.ANCHO + 4
        self.f_grande.configure(size=f0)
        self.colocar_cifras(c0 or 3)
        return max(360, w)

    def tamano_inicial(self, datos):
        """Pone el tamaño guardado (o uno en el que se ve todo) y el mínimo permitido."""
        self.root.resizable(True, True)
        self.root.geometry("434x700")          # tamaño fijo provisional: sin él, la ventana seguiría a su contenido
        minw = self.ancho_minimo()
        self.root.minsize(minw, 260)
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        tam = str(datos.get("tam_ventana") or "")
        m = re.match(r"^(\d+)x(\d+)$", tam)
        if m:
            w, h = int(m.group(1)), int(m.group(2))
        else:
            w = max(minw, 434)
            h = self.vista.alto_contenido() + 2
        w = max(minw, min(w, sw))
        h = max(260, min(h, sh - 60))
        geo = "%dx%d" % (w, h)
        if datos.get("geometria"):
            geo += datos["geometria"]
        try:
            self.root.geometry(geo)
        except tk.TclError:
            self.root.geometry("%dx%d" % (w, h))

    def ajustar_alto_al_contenido(self):
        """Tras el modo compacto: la ventana pasa a medir justo lo que ocupa lo que se ve."""
        try:
            self.root.update_idletasks()
            sh = self.root.winfo_screenheight()
            h = max(260, min(self.vista.alto_contenido() + 2, sh - 60))
            self.root.geometry("%dx%d" % (self.root.winfo_width(), h))
        except tk.TclError:
            pass

    def programar_adaptar(self, ancho, alto):
        self._resp = (ancho, alto)
        if not self._resp_pend:
            self._resp_pend = True
            self.root.after_idle(self.adaptar)

    def adaptar(self):
        """Recoloca la ventana principal según su tamaño: números más grandes si hay sitio, las cifras en
        2, 3 o 6 columnas y la gráfica más alta si sobra espacio abajo."""
        self._resp_pend = False
        if not self._resp:
            return
        ancho, alto = self._resp
        if ancho <= 1:
            return
        dentro = ancho - 24
        tam = max(40, min(96, int(dentro / 10.0) // 4 * 4))      # de 4 en 4: menos cambios, menos trabajo
        if self.f_grande.cget("size") != tam:
            self.f_grande.configure(size=tam)
        cols = 2 if dentro < 350 else (3 if dentro < 640 else 6)
        if cols != self._cols_cifras:
            self.colocar_cifras(cols)
        # la altura de la gráfica se calcula cuando todo se ha colocado (si no, se lee un tamaño a medias
        # y la ventana podría ponerse a temblar)
        if self._graf_pend is not None:
            self.root.after_cancel(self._graf_pend)
        self._graf_pend = self.root.after(120, self.ajustar_grafica)

    def ajustar_grafica(self):
        self._graf_pend = None
        if not self._resp:
            return
        alto = self._resp[1]
        g = self.grafica7
        extra = 0
        if not self.compacto:
            try:
                actual = g.winfo_height() if g.winfo_ismapped() else g._alto_pedido
            except tk.TclError:
                return
            sin_extra = self.vista.alto_contenido() - (actual - MiniGrafica.ALTO)
            extra = max(0, min(240, alto - sin_extra - 2))
        nuevo = MiniGrafica.ALTO + extra
        if abs(nuevo - g._alto_pedido) >= 3 or extra == 0:
            g.poner_alto(nuevo)

    def colocar_cifras(self, cols):
        self._cols_cifras = cols
        rej = self.rej_cifras
        for c in range(6):
            rej.grid_columnconfigure(c, weight=1 if c < cols else 0, uniform="cifras" if c < cols else "")
        for k, t in enumerate(self.tarjetas_cifras):
            t.grid(row=k // cols, column=k % cols, sticky="ew", padx=(0 if k % cols == 0 else 6, 0),
                   pady=(0 if k < cols else 6, 0))

    def _al_tam_meta(self, e):
        if e.width != self._meta_w:
            self._meta_w = e.width
            self.dibujar_meta()

    def construir_resumen(self, padre):
        """Las cifras en tarjetitas, la última partida y la gráfica de los últimos 7 días."""
        rej = self.rej_cifras = tk.Frame(padre, bg=BG)
        rej.pack(fill="x", pady=(8, 0))
        self.res = {}
        self.tarjetas_cifras = []
        self._cols_cifras = 0
        for k, (clave, nombre, color) in enumerate((
                ("hoy", "HOY", ORO), ("media", "MEDIA / PARTIDA", CIAN), ("record", "MEJOR PARTIDA", VERDE),
                ("dia", "MEJOR DÍA", ORO), ("partidas", "PARTIDAS", COLOR_PARTIDA), ("racha", "RACHA", "#b89cff"))):
            t = Tarjeta(rej, pad=10, radio=12)
            self.tarjetas_cifras.append(t)
            tk.Label(t.cuerpo, text=nombre, font=("Segoe UI Semibold", 7), fg=APAGADO, bg=PANEL,
                     anchor="w").pack(fill="x")
            lbl = tk.Label(t.cuerpo, text="–", font=("Segoe UI Black", 16), fg=color, bg=PANEL, anchor="w")
            lbl.pack(fill="x")
            self.res[clave] = lbl
        self.colocar_cifras(3)

        t = Tarjeta(padre, pad=12)
        t.pack(fill="x", pady=(8, 0))
        c = t.cuerpo
        izq = tk.Frame(c, bg=PANEL, width=128)
        izq.pack(side="left", fill="y")
        izq.pack_propagate(False)
        tk.Label(izq, text="ÚLTIMA PARTIDA", font=("Segoe UI Semibold", 8), fg=ORO_OSC, bg=PANEL,
                 anchor="w").pack(fill="x")
        self.lbl_ult = tk.Label(izq, text="–", font=("Segoe UI Black", 26), fg=COLOR_PARTIDA, bg=PANEL, anchor="w")
        self.lbl_ult.pack(fill="x")
        self.lbl_ult_info = tk.Label(izq, text="", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL, anchor="w",
                                     justify="left", wraplength=124)
        self.lbl_ult_info.pack(fill="x")
        self.lbl_ult_rep = tk.Label(izq, text="", font=("Segoe UI", 8), fg=VERDE, bg=PANEL, anchor="w",
                                    justify="left", wraplength=124)
        self.lbl_ult_rep.pack(fill="x")
        tk.Frame(c, bg=LINEA, width=1).pack(side="left", fill="y", padx=(4, 12))
        der = tk.Frame(c, bg=PANEL)
        der.pack(side="left", fill="both", expand=True)
        f = tk.Frame(der, bg=PANEL)
        f.pack(fill="x")
        tk.Label(f, text="ÚLTIMOS 7 DÍAS", font=("Segoe UI Semibold", 8), fg=ORO_OSC, bg=PANEL).pack(side="left")
        self.lbl_7 = tk.Label(f, text="", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL)
        self.lbl_7.pack(side="right")
        self.grafica7 = MiniGrafica(der)
        self.grafica7.pack(fill="x", pady=(2, 0))

    def alternar_overlay_boton(self):
        self.var_ov.set(not self.var_ov.get())
        self.alternar_overlay()

    def pintar_btn_overlay(self):
        b = self.btn_overlay
        b._color = MORADO if self.var_ov.get() else "#4a4468"
        b.config(text="👁 Overlay: sí" if self.var_ov.get() else "👁 Overlay")

    # ---------- ventana de ajustes ----------
    def construir_ventana_ajustes(self):
        w = self.win_aj = tk.Toplevel(self.root)
        w.withdraw()
        w.title("Ajustes · Contador de cofres")
        w.configure(bg=BG)
        w.resizable(True, True)
        w.minsize(400, 300)
        poner_icono_ventana(w)
        w.protocol("WM_DELETE_WINDOW", self.cerrar_ajustes)
        w.bind("<Escape>", lambda e: self.cerrar_ajustes())
        cab = tk.Frame(w, bg=BG)
        cab.pack(side="top", fill="x", padx=18, pady=(14, 10))
        tk.Label(cab, text="Ajustes", font=("Segoe UI Semibold", 17), fg=TEXTO, bg=BG).pack(side="left")
        tk.Label(cab, text="Los cambios se guardan solos", font=("Segoe UI", 9), fg=APAGADO,
                 bg=BG).pack(side="left", padx=12, pady=(8, 0))
        pie = tk.Frame(w, bg=BG)
        pie.pack(side="bottom", fill="x", padx=18, pady=(8, 16))
        self.boton(pie, "Cerrar", self.cerrar_ajustes, MORADO, 9).pack(side="right")
        tk.Label(pie, text="Esc también cierra", font=("Segoe UI", 8), fg=APAGADO, bg=BG).pack(side="right", padx=10)
        # las tarjetas se colocan a mano (en 1 o 2 columnas según el ancho) dentro de un hueco con desplazamiento
        self.vista_aj = Desplazable(w)
        self.vista_aj.pack(side="top", fill="both", expand=True)
        w.bind("<MouseWheel>", self.vista_aj.rueda, add="+")
        self.aj_cont = tk.Frame(self.vista_aj.interior, bg=BG, height=10)
        self.aj_cont.pack(fill="x", padx=(18, 8))
        self.aj_tarjetas = []
        self._aj_pend = False
        self._aj_ancho = 0
        self.construir_ajustes("izq", "der")
        self.aj_cont.bind("<Configure>", self._al_tam_aj, add="+")

    def _al_tam_aj(self, e=None):
        if e is not None and e.widget is self.aj_cont:
            if e.width == self._aj_ancho:
                return
            self._aj_ancho = e.width
        if not self._aj_pend:
            self._aj_pend = True
            self.root.after_idle(self.colocar_ajustes)

    def colocar_ajustes(self):
        """Coloca las tarjetas de ajustes: dos columnas si hay sitio, una si la ventana es estrecha."""
        self._aj_pend = False
        W = self.aj_cont.winfo_width()
        if W <= 1:
            return
        cols = 2 if W >= 660 else 1
        hueco = 14
        cw = (W - hueco * (cols - 1)) // cols
        if cols == 1:
            orden = [(t, 0) for t, c in self.aj_tarjetas if c == "izq"] + \
                    [(t, 0) for t, c in self.aj_tarjetas if c == "der"]
        else:
            orden = [(t, 0 if c == "izq" else 1) for t, c in self.aj_tarjetas]
        ys = [0] * cols
        for t, k in orden:
            t.place(x=k * (cw + hueco), y=ys[k], width=cw)
            ys[k] += t.winfo_reqheight() + 12
        alto = max(ys)
        if int(self.aj_cont.cget("height")) != alto:
            self.aj_cont.configure(height=alto)

    def alternar_ajustes(self):
        w = self.win_aj
        try:
            if w.winfo_viewable():
                self.cerrar_ajustes()
                return
            m = re.match(r"^(\d+)x(\d+)$", self.cfg_tam_aj or "")
            if m:
                ww, wh = int(m.group(1)), int(m.group(2))
            else:
                ww, wh = 790, min(1000, w.winfo_screenheight() - 80)
            ww = max(400, min(ww, w.winfo_screenwidth()))
            wh = max(300, min(wh, w.winfo_screenheight() - 60))
            rx, ry, rw = self.root.winfo_rootx(), self.root.winfo_rooty(), self.root.winfo_width()
        except tk.TclError:
            return
        try:
            gsm = ctypes.windll.user32.GetSystemMetrics
            vx, vy, vw, vh = gsm(76), gsm(77), gsm(78), gsm(79)       # todo el escritorio (varias pantallas)
            if vw <= 0 or vh <= 0:
                raise OSError
        except Exception:
            vx, vy, vw, vh = 0, 0, w.winfo_screenwidth(), w.winfo_screenheight()
        x = rx + rw + 14
        if x + ww > vx + vw:
            x = max(vx, rx - ww - 14)
        y = max(vy, min(ry - 30, vy + vh - wh - 60))
        w.geometry("%dx%d+%d+%d" % (ww, wh, x, y))
        w.deiconify()
        self.preparar_ventana(w)
        try:
            w.lift()
            w.focus_force()
        except tk.TclError:
            pass

    def cerrar_ajustes(self):
        try:
            if self.win_aj.winfo_viewable():
                tam = self.win_aj.geometry().split("+", 1)[0]
                if re.match(r"^\d+x\d+$", tam):
                    self.cfg_tam_aj = tam
            self.win_aj.withdraw()
        except tk.TclError:
            pass
        self.guardar()

    def tarjeta_ajustes(self, padre, titulo, sub=None):
        t = Tarjeta(self.aj_cont, pad=14)
        self.aj_tarjetas.append((t, padre))
        t.bind("<Configure>", self._al_tam_aj, add="+")
        c = t.cuerpo
        tk.Label(c, text=titulo, font=("Segoe UI Semibold", 11), fg=ORO, bg=PANEL, anchor="w").pack(fill="x")
        if sub:
            tk.Label(c, text=sub, font=("Segoe UI", 8), fg=APAGADO, bg=PANEL, anchor="w", justify="left",
                     wraplength=300).pack(fill="x")
        c._filas = 0
        return c

    def fila(self, caja, texto, var, comando=None, detalle=None):
        if getattr(caja, "_filas", 0):
            tk.Frame(caja, bg=LINEA, height=1).pack(fill="x", pady=(3, 3))
        else:
            tk.Frame(caja, bg=PANEL, height=4).pack(fill="x")
        caja._filas = getattr(caja, "_filas", 0) + 1
        f = FilaAjuste(caja, texto, var, comando, detalle)
        f.pack(fill="x")
        return f

    def subtitulo(self, caja, texto):
        tk.Label(caja, text=texto, font=("Segoe UI Semibold", 8), fg=APAGADO, bg=PANEL, anchor="w").pack(
            fill="x", pady=(10, 4))

    def fila_control(self, caja, texto):
        """Fila con un texto a la izquierda; devuelve el hueco de la derecha para poner el control."""
        f = tk.Frame(caja, bg=PANEL)
        f.pack(fill="x", pady=(8, 0))
        tk.Label(f, text=texto, font=("Segoe UI Semibold", 10), fg=TEXTO, bg=PANEL).pack(side="left")
        d = tk.Frame(f, bg=PANEL)
        d.pack(side="right")
        return d

    def construir_ajustes(self, izq, der):
        n_mon = max(1, len(self.sct.monitors) - 1)
        opciones_pantalla = ["Auto"] + ["Pantalla %d" % i for i in range(1, n_mon + 1)]
        self.var_pitido = tk.BooleanVar(value=self.ini_pitido)
        self.var_celebrar = tk.BooleanVar(value=self.ini_celebrar)
        self.var_lobby = tk.BooleanVar(value=self.ini_lobby)
        self.var_solo_cofre = tk.BooleanVar(value=self.ini_solo)
        self.var_fotos = tk.BooleanVar(value=self.ini_fotos)
        self.var_obs = tk.BooleanVar(value=self.ini_obs)
        self.var_inicio = tk.BooleanVar(value=inicio_windows_activo())
        self.var_zona = tk.StringVar(value=nombre_zona())
        self.var_pantalla = tk.StringVar(
            value=self.ini_pantalla if self.ini_pantalla in opciones_pantalla else "Auto")
        self.var_sonido = tk.StringVar(value=self.cfg_son["elegido"])
        self.var_encima = tk.BooleanVar(value=self.ini_encima)
        self.var_manual = tk.BooleanVar(value=self.ini_manual)
        self.var_ocr = tk.BooleanVar(value=self.ini_ocr)
        self.var_rep = tk.BooleanVar(value=self.ini_rep)
        self.var_ov = tk.BooleanVar(value=bool(self.cfg_ov.get("visible", False)))
        self.var_mover = tk.BooleanVar(value=False)
        self.var_tam = tk.StringVar(value=self.cfg_ov.get("tam", "Mediano"))
        self.var_icono = tk.BooleanVar(value=bool(self.cfg_ov.get("icono", True)))
        self.var_partida = tk.BooleanVar(value=bool(self.cfg_ov.get("partida", False)))
        self.var_amigo = tk.BooleanVar(value=bool(self.cfg_ov.get("amigo", False)))
        self.var_grupo = tk.BooleanVar(value=bool(self.cfg_ov.get("grupo", False)))
        self.var_meta = tk.BooleanVar(value=bool(self.cfg_ov.get("meta", False)))

        # ===== columna izquierda =====
        c = self.tarjeta_ajustes(izq, "🧰  Conteo de cofres")
        Segmentado(c, self.var_manual, (("🤖  Automático", False), ("✋  Solo manual", True)),
                   self.al_cambiar_manual).pack(fill="x", pady=(8, 2))
        self.chip_ocr = self.fila(c, "Leer el texto del aviso", self.var_ocr, self.al_cambiar_ocr,
                                  "Cuenta raros, de espíritu, X2… nunca eliminaciones ni munición")
        self.fila(c, "Solo avisos de COFRE", self.var_solo_cofre, self.al_cambiar_solo,
                  "Apagado, cuenta cualquier aviso de experiencia")
        self.fila(c, "Recuento con la repetición", self.var_rep, self.al_cambiar_rep,
                  "Al acabar, confirma los cofres abiertos y rotos con la repetición del juego")
        self.fila(c, "Terminar partida en el lobby", self.var_lobby, self.guardar,
                  "La partida se guarda sola al volver al lobby")
        self.menu_opciones(self.fila_control(c, "Pantalla del juego"), self.var_pantalla, opciones_pantalla,
                           lambda v: self.guardar()).pack()
        self.pintar_modo()

        c = self.tarjeta_ajustes(izq, "🔔  Sonido")
        d = self.fila_control(c, "Sonido del cofre")
        self.menu_opciones(d, self.var_sonido, OPCIONES_SONIDO, self.al_elegir_sonido).pack(side="left")
        f = tk.Frame(c, bg=PANEL)
        f.pack(fill="x", pady=(4, 0))
        self.boton_texto(f, "▶ Probar", self.probar_sonido, fg=ORO).pack(side="left")
        self.boton_texto(f, "📂 Mi sonido…", self.elegir_sonido, fg=ORO).pack(side="left", padx=10)
        self.lbl_sonido = tk.Label(c, text="", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL,
                                   anchor="w", wraplength=300, justify="left")
        self.lbl_sonido.pack(fill="x", pady=(0, 2))
        envolver(self.lbl_sonido, c)
        self.actualizar_lbl_sonido()
        self.fila(c, "Sonar al sumar", self.var_pitido, self.guardar)
        self.fila(c, "Celebrar hitos", self.var_celebrar, self.guardar, "Récords, metas y cifras redondas")

        c = self.tarjeta_ajustes(izq, "🪟  Ventana")
        self.fila(c, "Siempre encima", self.var_encima, self.al_cambiar_encima,
                  "El número flotante va siempre encima del juego")
        self.fila(c, "Guardar fotos (diagnóstico)", self.var_fotos, self.al_cambiar_fotos,
                  "Capturas de los avisos para revisar fallos")

        # ===== columna derecha =====
        c = self.tarjeta_ajustes(der, "👁  Número flotante sobre el juego")
        self.fila(c, "Mostrar en pantalla", self.var_ov, self.alternar_overlay)
        self.fila(c, "Mover", self.var_mover, self.cambiar_mover,
                  "Arrástralo donde quieras y apágalo para que los clics lo atraviesen")
        self.subtitulo(c, "TAMAÑO")
        Segmentado(c, self.var_tam, [(n, n) for n in TAMANOS], self.refrescar_overlay).pack(fill="x")
        self.subtitulo(c, "QUÉ ENSEÑAR")
        self.rejilla_chips(c, [("🧰  Cofre", self.var_icono, self.refrescar_overlay),
                               ("🎮  Partida", self.var_partida, self.refrescar_overlay),
                               ("🎯  Meta", self.var_meta, self.refrescar_overlay),
                               ("👥  Amigos", self.var_amigo, self.refrescar_overlay),
                               ("🏆  Grupo", self.var_grupo, self.refrescar_overlay)], columnas=3)

        c = self.tarjeta_ajustes(der, "🕒  Hora y sistema")
        self.menu_opciones(self.fila_control(c, "Zona horaria"), self.var_zona, OPCIONES_ZONA,
                           self.al_cambiar_zona).pack()
        tk.Label(c, text="Decide dónde acaba cada día en las estadísticas.", font=("Segoe UI", 8), fg=APAGADO,
                 bg=PANEL, anchor="w").pack(fill="x", pady=(2, 4))
        self.fila(c, "Iniciar con Windows", self.var_inicio, self.al_cambiar_inicio)
        self.fila(c, "Archivos para OBS", self.var_obs, self.al_cambiar_obs,
                  "obs_total.txt y obs_partida.txt en tu carpeta de datos (en OBS: fuente «Texto» → "
                  "«Leer desde archivo»)")

        c = self.tarjeta_ajustes(der, "⌨  Atajos y datos")
        f = tk.Frame(c, bg=PANEL)
        f.pack(fill="x", pady=(8, 0))
        for k in range(3):
            f.grid_columnconfigure(k, weight=1, uniform="bt")
        self.boton(f, "⌨ Atajos", self.dialogo_teclas, MORADO, 3).grid(row=0, column=0, sticky="ew")
        self.boton(f, "📁 Datos", self.abrir_carpeta_datos, AZUL, 3).grid(row=0, column=1, sticky="ew", padx=4)
        self.boton(f, "🩺 Diagnóstico", self.diagnostico, "#4a4468", 3).grid(row=0, column=2, sticky="ew")
        # alto fijo (3 renglones): el texto cambia a cada instante y, si no, la ventana daría saltos
        self.lbl_detalle = tk.Label(c, text="", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL,
                                    wraplength=305, justify="left", anchor="nw", height=3)
        self.lbl_detalle.pack(fill="x", pady=(6, 0))
        envolver(self.lbl_detalle, c)

        c = self.tarjeta_ajustes(der, "🔄  Actualizaciones")
        f = tk.Frame(c, bg=PANEL)
        f.pack(fill="x", pady=(8, 0))
        self.boton(f, "Buscar", lambda: self.buscar_actualizaciones(True), MORADO, 6).pack(side="left")
        self.lbl_upd = tk.Label(f, text="Versión %s · se busca sola al abrir." % VERSION, font=("Segoe UI", 8),
                                fg=APAGADO, bg=PANEL, anchor="w", wraplength=210, justify="left")
        self.lbl_upd.pack(side="left", padx=10)

    def poner_luz(self, color, texto, color_texto=None, pulso=False):
        """Luz de estado de arriba a la derecha. Solo hace algo cuando cambia."""
        clave = (color, texto)
        if clave == self.luz_estado:
            return
        self.luz_estado = clave
        antes = self.luz_color
        self.luz_color = color
        self.lbl_luz.config(text=texto, fg=color_texto or color)
        cv = self.cv_luz

        def paso(t):
            c = mezclar(antes, color, suave(t))
            cv.itemconfigure(self.luz_punto, fill=c)
            cv.itemconfigure(self.luz_halo, fill=mezclar(BG, c, 0.30))

        self.anim.lanzar("luz", 240, paso)
        if pulso:
            def onda(t):
                r = 5 + 7 * suave(t)
                cv.coords(self.luz_aro, 12 - r, 12 - r, 12 + r, 12 + r)
                cv.itemconfigure(self.luz_aro, outline=mezclar(color, BG, suave(t)))

            self.anim.lanzar("luz_onda", 650, onda)

    def construir_amigos(self, fa):
        cab = tk.Frame(fa, bg=PANEL)
        cab.pack(fill="x", pady=(0, 4))
        tk.Label(cab, text="👥  EQUIPO", font=("Segoe UI Semibold", 10), fg=ORO,
                 bg=PANEL).pack(side="left")
        self.boton_texto(cab, "⚙ Conectar", self.dialogo_conexion).pack(side="right")
        self.cab_amigos = cab
        self.btn_gestion = self.boton_texto(cab, "👑 Gestionar", self.dialogo_gestion, fg=ORO)
        self.btn_salir = self.boton_texto(cab, "🚪 Salir de la sala", self.salir_de_sala, fg=ROJO)
        self.fr_amigos = tk.Frame(fa, bg=PANEL)
        self.fr_amigos.pack(fill="x", pady=(0, 2))
        self.lbl_sync = tk.Label(fa, text="Sin conectar.", font=("Segoe UI", 8), fg=APAGADO,
                                 bg=PANEL, wraplength=self.ANCHO_UI - 30, justify="left", anchor="w")
        self.lbl_sync.pack(fill="x")
        envolver(self.lbl_sync, fa)

    def chip(self, padre, texto, var, comando=None, valor=None):
        """Botón tipo interruptor: se ilumina en morado (con una transición suave) cuando está activado."""
        return Chip(padre, texto, var, comando, valor)

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

    def abrir_carpeta_datos(self):
        try:
            os.startfile(DATOS)
        except Exception:
            messagebox.showinfo("Datos", "Tus datos están en:\n\n%s" % DATOS, parent=self.root)

    # ---------- ventana encima, conteo manual y lector de texto ----------
    def al_cambiar_encima(self):
        self.aplicar_encima()
        self.aviso("La ventana se queda encima de las demás." if self.var_encima.get()
                   else "La ventana ya no se pone encima de las demás (el número flotante sí sigue encima del juego).")
        self.guardar()

    def al_cambiar_manual(self):
        self.reiniciar_detector()
        if self.var_manual.get():
            self.aviso("✋ Conteo manual: solo suman el botón «+1» y tu atajo. La detección automática queda apagada.", 10)
        else:
            self.aviso("Conteo automático encendido.")
        self.guardar()

    def al_cambiar_ocr(self):
        self.reiniciar_detector()
        if not self.var_ocr.get():
            self.aviso("Lector de texto apagado: se usa el detector de siempre (compara el aviso con la palabra «COFRE»).", 10)
        elif self.estado_lector() == "no":
            self.aviso("Este PC no tiene el lector de texto de Windows: se sigue usando el detector de siempre.", 10)
        else:
            self.aviso("Lector de texto activado: cuenta toda línea con la palabra COFRE (raro, de espíritu, X2...) "
                       "y no cuenta eliminaciones, munición ni otra experiencia.", 12)
        self.guardar()

    def al_cambiar_rep(self):
        if not self.var_rep.get():
            self.aviso("Recuento con la repetición apagado.")
        elif buscar_oodle() is None:
            self.aviso("🎞 Falta la librería oo2core_9_win64.dll: cópiala en la carpeta de datos (botón «📁 Datos»).", 20)
        else:
            self.aviso("🎞 Al terminar cada partida se leerá su repetición para confirmar los cofres (abiertos y "
                       "rotos). En Fortnite tiene que estar activado «Grabar repeticiones».", 15)
        self.guardar()

    def al_cambiar_solo(self):
        self.reiniciar_detector()
        if self.var_solo_cofre.get():
            self.aviso("Solo cuentan los avisos de cofre.")
        else:
            self.aviso("Ahora cuenta CUALQUIER aviso de experiencia, sea o no de un cofre.", 10)
        self.guardar()

    def estado_lector(self):
        """'ok', 'iniciando' o 'no' (este PC no tiene el reconocedor de texto de Windows)."""
        return self.lector.hilo.estado if self.lector is not None else "no"

    def pintar_modo(self):
        """Si este PC no tiene el lector de texto de Windows, su interruptor se queda apagado y en gris."""
        falta = self.estado_lector() == "no"
        if falta != getattr(self, "_lector_falta", None) and getattr(self, "chip_ocr", None) is not None:
            self._lector_falta = falta
            self.chip_ocr.ajustar(texto="Lector de texto no disponible" if falta else "Leer el texto del aviso",
                                  activo=not falta)

    def reiniciar_detector(self):
        """Olvida lo que se estaba siguiendo en pantalla (al cambiar de modo, al perder el juego...)."""
        self.avisos_conf = 0
        self.sube = self.baja = 0
        self.lista_max = 0
        self.lista_cero = 0
        self.lista_hist.clear()
        self.pos_avisos = []
        self.n_visto = 0
        self.visto_seg = 0
        self.seguidor.reiniciar()
        self.ses_leg = self.ses_cont = self.ses_extra = 0

    # ---------- zona horaria, inicio con Windows y archivos para OBS ----------
    def al_cambiar_zona(self, valor=None):
        poner_zona(self.var_zona.get())
        self._st = None
        self._st_clave = None
        self._res_clave = None
        self.pintar_resumen()
        if self.stats is not None and self.stats.vivo():
            self.stats.refrescar(True)
        self.guardar()

    def al_cambiar_inicio(self):
        if not poner_inicio_windows(self.var_inicio.get()):
            self.var_inicio.set(not self.var_inicio.get())
            messagebox.showerror("Iniciar con Windows", "No se pudo cambiar el inicio automático.",
                                 parent=self.root)

    def al_cambiar_obs(self):
        self._obs_clave = None
        if self.var_obs.get():
            self.escribir_obs()
            self.aviso("Archivos para OBS en la carpeta de datos (botón «📁 Datos»).")
        self.guardar()

    def escribir_obs(self):
        """obs_total.txt y obs_partida.txt: un número cada uno, para usarlos como fuente de texto en OBS."""
        if not self.var_obs.get():
            return
        clave = (self.total, self.sesion)
        if clave == self._obs_clave:
            return
        self._obs_clave = clave
        for nombre, valor in (("obs_total.txt", self.total), ("obs_partida.txt", self.sesion)):
            try:
                with open(os.path.join(DATOS, nombre), "w", encoding="utf-8") as f:
                    f.write(str(valor))
            except OSError:
                pass

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
        clave = (self.hist.version, fecha_madrid(ahora), nombre_zona())
        if clave != self._st_clave or self._st is None:
            self._st = calcular_stats(self.hist.partidas, self.hist.actual, ahora)
            self._st_clave = clave
        return self._st

    def pintar_resumen(self):
        st = self.estadisticas()
        ult = self.hist.partidas[-1] if self.hist.partidas else None
        rep = self.cfg_ui.get("ult_rep") if isinstance(self.cfg_ui.get("ult_rep"), dict) else None
        dias7 = st["dias14"][-7:]
        clave = (st["hoy"], st["media_total"], st["mejor_partida"], st["mejor_dia"], st["partidas"], st["racha"],
                 tuple(dias7), len(self.hist.partidas), len(ult) if ult else -1, ult[0][0] if ult else 0,
                 repr(rep))
        if clave == self._res_clave:
            return
        self._res_clave = clave
        self.res["hoy"].config(text=str(st["hoy"]))
        self.res["media"].config(text=f1(st["media_total"]) if st["media_total"] is not None else "–")
        self.res["record"].config(text=str(st["mejor_partida"]))
        self.res["dia"].config(text=str(st["mejor_dia"]))
        self.res["partidas"].config(text=str(st["partidas"]))
        self.res["racha"].config(text="%d día%s" % (st["racha"], "" if st["racha"] == 1 else "s"))
        self.grafica7.poner(dias7)
        self.lbl_7.config(text="%d en total" % sum(v for _d, v in dias7))
        if ult:
            ini = a_madrid(ult[0][0])
            dur = max(0, ult[-1][0] - ult[0][0])
            dia = "Hoy" if ini.date() == st["hoy_fecha"] else ini.strftime("%d/%m")
            info = "%s · %s" % (dia, ini.strftime("%H:%M"))
            if dur >= 60:
                info += " · %d min" % (dur // 60)
            self.lbl_ult.config(text=str(len(ult)))
            self.lbl_ult_info.config(text=info)
        else:
            self.lbl_ult.config(text="–")
            self.lbl_ult_info.config(text="Aún no hay partidas guardadas")
        if rep and rep.get("n") == len(self.hist.partidas) and ult:
            if rep.get("dif"):
                self.lbl_ult_rep.config(text="🎞 Corregida con la repetición (%+d)" % rep["dif"], fg=ORO)
            else:
                self.lbl_ult_rep.config(text="🎞 Confirmada con la repetición", fg=VERDE)
        else:
            self.lbl_ult_rep.config(text="")

    def alternar_stats(self):
        if self.stats is not None and self.stats.vivo():
            self.stats.cerrar()
            self.stats = None
        else:
            self.stats = Estadisticas(self)

    # ---------- modo compacto, ritmo y novedades ----------
    def aplicar_compacto(self, valor, guardar=True, ajustar_alto=True):
        self.compacto = bool(valor)
        self.extra.pack_forget()
        if not self.compacto:
            self.extra.pack(fill="x", before=self.fila_acciones)
            self.grafica7.poner_alto(MiniGrafica.ALTO)
        self.btn_compacto.config(text="▾" if self.compacto else "▴")
        self.cfg_ui["compacto"] = self.compacto
        if ajustar_alto:
            self.ajustar_alto_al_contenido()
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

    def dibujar_meta(self):
        """Pinta la barra de la meta tal y como va ahora mismo (la animación la mueve poco a poco)."""
        c = self.cv_meta
        W, H = max(80, self._meta_w or BARRA_META_W), 26
        meta = self.meta_info()
        if meta:
            pct = min(1.0, self.total / float(meta["valor"]))
            col = "#ffffff" if self.meta_flash else (VERDE if meta["hecho"] else ORO)
            txt = "%d / %d   ·   %d %%" % (self.total, meta["valor"], int(pct * 100))
            frac = self.meta_frac if self.meta_frac is not None else pct
        else:
            col, txt, frac = ORO, "Sin meta", 0.0
        self._foto_meta = foto_tk(pintar_barra(W, H, PANEL, frac, col, self.meta_brillo))
        c.delete("all")
        c.create_image(0, 0, anchor="nw", image=self._foto_meta)
        for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            c.create_text(W / 2 + dx, H / 2 + dy, text=txt, font=("Segoe UI Black", 10), fill=CONTORNO)
        c.create_text(W / 2, H / 2, text=txt, font=("Segoe UI Black", 10), fill="#ffffff")

    def pintar_meta(self):
        meta = self.meta_info()
        ban = self.banner_actual()
        pct = min(1.0, self.total / float(meta["valor"])) if meta else 0.0
        if self.meta_frac is None or self.meta_dest is None:
            self.meta_frac = self.meta_dest = pct          # la primera vez, sin animación
        elif abs(pct - self.meta_dest) > 1e-9:
            # la barra avanza con suavidad hasta su sitio y, si sube, la recorre un destello
            ini, sube = self.meta_frac, pct > self.meta_dest
            self.meta_dest = pct

            def paso(t):
                self.meta_frac = ini + (pct - ini) * suave(t)
                self.meta_brillo = t if sube else None
                self.dibujar_meta()

            def fin():
                self.meta_frac, self.meta_brillo = pct, None
                self.dibujar_meta()

            self.anim.lanzar("meta", 560, paso, fin)
        self.dibujar_meta()
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
            elif accion == "manual":
                self.var_manual.set(not self.var_manual.get())
                self.al_cambiar_manual()
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
        self.preparar_ventana(d)
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

    def overlay_tapa_zona(self, rect):
        """True si el número flotante está encima de la zona donde salen los avisos de cofre
        (se tapa en negro para el análisis y ese aviso no se podría ver)."""
        ov = self.overlay
        if ov is None or not self.var_ov.get():
            return False
        try:
            if not ov.win.winfo_viewable():
                return False
            ax, ay = ov.win.winfo_rootx(), ov.win.winfo_rooty()
            bx, by = ax + ov.win.winfo_width(), ay + ov.win.winfo_height()
        except tk.TclError:
            return False
        left, top, w, h = rect
        zx0, zy0 = left + FX0 * w, top + FY0 * h
        return ax < zx0 + FW * w and bx > zx0 and ay < zy0 + FH * h and by > zy0

    # ---------- animaciones ----------
    def destello(self, paso=0):
        """Al sumar: los dos números y el marco de la ventana se encienden y vuelven a su color."""
        def brillo(t):
            k = suave(t)
            self.lbl_total.config(fg=mezclar("#ffffff", ORO, k))
            self.lbl_sesion.config(fg=mezclar("#ffffff", COLOR_PARTIDA, k))
            self.t_hero.poner_brillo(1.0 - k)

        self.anim.lanzar("destello", 650, brillo)

    def popup(self, texto, color):
        """El «+1» que sube y se desvanece junto al total."""
        lbl = tk.Label(self.panel_num, text=texto, font=("Segoe UI Black", 18), fg=color, bg=PANEL)

        def paso(t):
            lbl.place(relx=0.40, y=62 - 46 * suave(t))
            lbl.config(fg=mezclar(color, PANEL, max(0.0, (t - 0.5) / 0.5)))

        def fin():
            try:
                lbl.destroy()
            except tk.TclError:
                pass

        self.anim.lanzar(("popup", str(lbl)), 620, paso, fin)

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
        self.preparar_ventana(d)
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
        """Ventana sencilla: tu nombre, el nombre de la sala y dos botones (crear / unirse).
        La base de datos ya viene dentro del programa."""
        if self.dlg is not None and self.dlg.winfo_exists():
            self.dlg.lift()
            return
        d = tk.Toplevel(self.root)
        self.dlg = d
        d.title("Conectar con tus amigos")
        d.configure(bg=BG)
        self.preparar_ventana(d)
        d.resizable(False, False)
        d.transient(self.root)
        d.geometry("+%d+%d" % (self.root.winfo_rootx() + 20, self.root.winfo_rooty() + 40))

        caja = tk.Frame(d, bg=CARD, highlightbackground=ORO, highlightthickness=2)
        caja.pack(padx=8, pady=8)
        tk.Label(caja, text="Conectar con tus amigos", font=("Segoe UI Semibold", 13), fg=ORO,
                 bg=CARD).pack(padx=30, pady=(12, 2))
        tk.Label(caja, text="Crea una sala nueva o únete a la de un amigo.\n"
                            "Quien crea la sala es el líder.",
                 font=("Segoe UI", 8), fg=APAGADO, bg=CARD, justify="center").pack()

        def estilo_entrada(e):
            e.config(font=("Segoe UI", 11), bg=BG, fg=ORO, insertbackground=ORO, relief="flat",
                     highlightthickness=2, highlightbackground=APAGADO, highlightcolor=ORO)

        tk.Label(caja, text="Tu nombre (así te verán tus amigos)", font=("Segoe UI", 9), fg=TEXTO,
                 bg=CARD).pack(anchor="w", padx=20, pady=(8, 0))
        v_nombre = tk.StringVar(value=self.cfg_on.get("nombre", ""))
        e_nombre = tk.Entry(caja, textvariable=v_nombre, width=36)
        estilo_entrada(e_nombre)
        e_nombre.pack(padx=20, pady=(2, 0))

        tk.Label(caja, text="Nombre de la sala", font=("Segoe UI", 9), fg=TEXTO,
                 bg=CARD).pack(anchor="w", padx=20, pady=(8, 0))
        fila_cod = tk.Frame(caja, bg=CARD)
        fila_cod.pack(padx=20, pady=(2, 0), fill="x")
        v_sala = tk.StringVar(value=self.cfg_on.get("sala") or "cofres")
        e_sala = tk.Entry(fila_cod, textvariable=v_sala, width=30)
        estilo_entrada(e_sala)
        e_sala.pack(side="left")
        b_copiar = tk.Button(fila_cod, text="📋", bg=PANEL, fg=ORO, activebackground="#40377a",
                             activeforeground=ORO, relief="flat", bd=0, cursor="hand2",
                             font=("Segoe UI Emoji", 12), padx=6)
        b_copiar.pack(side="left", padx=(6, 0), fill="y")

        aviso = tk.Label(caja, text="Crear: inventa un nombre y pásaselo a tus amigos (el icono 📋 lo copia).\n"
                                    "Unirse: escribe el nombre que te haya dado quien creó la sala.",
                         font=("Segoe UI", 8), fg=APAGADO, bg=CARD, wraplength=330, justify="left")
        aviso.pack(padx=20, pady=(8, 0))

        def copiar():
            s = limpiar_sala(v_sala.get())
            if not s:
                aviso.config(text="Escribe primero el nombre de la sala.", fg=ROJO)
                return
            self.root.clipboard_clear()
            self.root.clipboard_append(s)
            self.root.update()
            aviso.config(text="Nombre de sala «%s» copiado. Pégaselo a tus amigos." % s, fg=VERDE)

        b_copiar.config(command=copiar)

        def lanzar(modo):
            sala = limpiar_sala(v_sala.get())
            nombre = v_nombre.get().strip()[:20] or nombre_por_defecto()
            if not sala:
                aviso.config(text="Escribe el nombre de la sala (letras, números, - o _).", fg=ROJO)
                return
            v_sala.set(sala)
            if self.cfg_on.get("activo") and self.cfg_on.get("sala") == sala:
                self.entrar_en_sala(nombre, sala, "ya")          # ya estás dentro: solo se cambia el nombre
                d.destroy()
                return
            b_crear.config(state="disabled")
            b_unir.config(state="disabled")
            aviso.config(text="Comprobando la sala...", fg=ORO)
            res = {"r": None}
            pid = self.cfg_on.get("id", "")

            def tarea():
                res["r"] = preparar_sala(modo, sala, pid)

            def esperar():
                try:
                    if res["r"] is None:
                        d.after(120, esperar)
                        return
                    ok, msg = res["r"]
                    if not ok:
                        aviso.config(text=msg, fg=ROJO)
                        b_crear.config(state="normal")
                        b_unir.config(state="normal")
                        return
                    self.entrar_en_sala(nombre, sala, modo)
                    d.destroy()
                except tk.TclError:
                    pass

            threading.Thread(target=tarea, daemon=True).start()
            esperar()

        fila = tk.Frame(caja, bg=CARD)
        fila.pack(pady=12)
        b_crear = self.boton(fila, "Crear sala", lambda: lanzar("crear"), "#2e9e5b", 11)
        b_crear.pack(side="left", padx=4)
        b_unir = self.boton(fila, "Unirse a sala", lambda: lanzar("unirse"), MORADO, 13)
        b_unir.pack(side="left", padx=4)
        self.boton(fila, "Cancelar", d.destroy, "#4a4468", 8).pack(side="left", padx=4)
        d.bind("<Escape>", lambda ev: d.destroy())

    def entrar_en_sala(self, nombre, sala, modo):
        c = self.cfg_on
        antes = c.get("sala", "")
        # si cambias de sala, te quitas de la anterior (para no dejar un "fantasma" tuyo allí)
        if c.get("activo") and antes and antes != sala:
            Sincronizador.borrar_entrada(URL_SALAS, antes, c.get("id", ""))
        c["nombre"] = nombre
        c["url"] = URL_SALAS
        c["sala"] = sala
        c["activo"] = True
        self.aplicar_conexion()
        self.guardar()
        self.pintar_amigo(forzar=True)
        if modo == "crear":
            self.aviso("Sala «%s» creada. Pásales ese nombre a tus amigos (en «⚙ Conectar» está el icono 📋)." % sala, 15)
        elif modo == "unirse":
            self.aviso("Te has unido a la sala «%s»." % sala)

    def salir_de_sala(self):
        """Te saca de la sala en la que estás: te quita de ella, desconecta y deja libre el código
        para que pongas otro."""
        c = self.cfg_on
        sala = c.get("sala", "")
        if not (c.get("activo") and sala):
            return
        if not messagebox.askyesno(
                "Salir de la sala",
                "¿Salir de la sala «%s»?\n\nDejarás de ver a los demás y ellos dejarán de verte.\n"
                "Después podrás crear otra o unirte a una con «⚙ Conectar»." % sala, parent=self.root):
            return
        Sincronizador.borrar_entrada(URL_SALAS, sala, c.get("id", ""))
        c["activo"] = False
        c["sala"] = ""
        self.aplicar_conexion()
        self.guardar()
        self.pintar_amigo(forzar=True)
        self.aviso("Has salido de la sala «%s»." % sala)

    def aplicar_conexion(self):
        c = self.cfg_on
        self.sync.configurar(URL_SALAS, c.get("sala", ""), c.get("id", ""), c.get("activo", False))
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
            msg, col = "Sin conectar. Pulsa «⚙ Conectar» para crear una sala o unirte a la de un amigo.", APAGADO
        elif nivel == "trabajando":
            msg, col = "Conectando...", APAGADO
        elif st["expulsado"]:
            msg, col = "El líder te ha expulsado de esta sala. Crea otra o únete a una distinta con «⚙ Conectar».", ROJO
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
        self.preparar_ventana(d)
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
            self.pintar_modo()
            self.revisar_recuento()
            self.revisar_novedades()
            self.escribir_obs()
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
        self.preparar_ventana(d)
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
            tam = g.split("+", 1)[0]
            if re.match(r"^\d+x\d+$", tam) and self.root.winfo_viewable():
                datos["tam_ventana"] = tam
            elif self.cfg_tam:
                datos["tam_ventana"] = self.cfg_tam
        if hasattr(self, "win_aj") and self.cfg_tam_aj:
            datos["tam_ajustes"] = self.cfg_tam_aj
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
        datos["fotos"] = bool(self.var_fotos.get())
        datos["obs"] = bool(self.var_obs.get())
        datos["encima"] = bool(self.var_encima.get())
        datos["manual"] = bool(self.var_manual.get())
        datos["ocr"] = bool(self.var_ocr.get())
        datos["repeticion"] = bool(self.var_rep.get())
        datos["zona"] = nombre_zona()
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
        if n > 0 and not automatico:
            self.guardar_fallo()

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
        sesion_antes = self.sesion
        guardada = self.hist.cerrar()
        if guardada:
            self.sesion_previa = sesion_antes
        modo_rep = self.cfg_ui.get("modo_conteo") == "replays" and self.var_rep.get()
        self.programar_recuento(len(ev) if modo_rep else sesion_antes, guardada)
        if not modo_rep:                     # en modo replays el número se queda hasta que la repetición dé el nuevo
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

    # ---------- recuento con la repetición del juego ----------
    def programar_recuento(self, contados, guardada):
        """Al cerrar una partida: deja pendiente leer su repetición para confirmar el número de cofres."""
        if not self.var_rep.get() or (contados == 0 and not self.en_lobby):
            return
        self.rec = {"t": time.time(), "contados": contados, "estado": "esperando", "res": None, "ruta": None,
                    "mtime": 0.0, "visto": 0.0, "indice": (len(self.hist.partidas) - 1) if guardada else None}

    def vigilar_replay(self):
        """Modo replays: en cuanto Fortnite CIERRA la repetición (al salir de la partida) se lee y se pone el
        número, sin esperar a detectar el lobby."""
        ahora = time.time()
        v = self.__dict__.setdefault("_vig", {"t": 0.0, "hilo": None, "res": None, "ruta": None, "fallos": {}})
        if v["res"] is not None:                                   # resultado listo (se aplica en el hilo principal)
            res, ruta = v["res"], v["ruta"]
            v["res"] = v["ruta"] = v["hilo"] = None
            if "error" in res:
                n = v["fallos"][ruta] = v["fallos"].get(ruta, 0) + 1
                if n >= 3:
                    self.aplicar_recuento({"res": res, "contados": 0, "indice": None, "t": ahora})
                    self.cfg_ui.setdefault("rep_hechas", []).append(os.path.basename(ruta))
                return
            contados = len(self.hist.actual)                      # lo que hayas sumado a mano esta partida
            antes = self.sesion
            guardada = self.hist.cerrar()
            if guardada:
                self.sesion_previa = antes
            self.activo = False
            self.aplicar_recuento({"res": res, "contados": contados, "t": ahora,
                                   "indice": (len(self.hist.partidas) - 1) if guardada else None})
            return
        if v["hilo"] is not None or ahora - v["t"] < 0.25:
            return
        v["t"] = ahora
        ruta = repeticion_reciente(self.t_inicio - 5)              # solo repeticiones de partidas jugadas con el programa abierto
        if not ruta or os.path.basename(ruta) in self.cfg_ui.get("rep_hechas", []) or v["fallos"].get(ruta, 0) >= 3:
            return
        try:                                                       # mientras Fortnite no la cierra, la clave sale vacía
            if _lector_rep is None:
                return
            with open(ruta, "rb") as fh:
                cab = _lector_rep.leer_cabecera_replay(fh.read(8192))
            if cab["enc"] and not any(cab["key"]):
                return
        except Exception:
            return
        v["ruta"] = ruta

        def tarea():
            try:
                v["res"] = analizar_repeticion(ruta)
            except Exception as e:
                v["res"] = {"error": str(e) or type(e).__name__}

        v["hilo"] = threading.Thread(target=tarea, daemon=True)
        v["hilo"].start()

    def revisar_recuento(self):
        if self.cfg_ui.get("modo_conteo") == "replays" and self.var_rep.get():
            return self.vigilar_replay()
        r = self.rec
        if not r:
            return
        ahora = time.time()
        if r["estado"] == "esperando":
            if ahora - r["t"] > 300:
                self.rec = None
                self.aviso("🎞 No encuentro la repetición de esta partida (en Fortnite tiene que estar activado "
                           "«Grabar repeticiones»).", 15)
                return
            ruta = repeticion_reciente(r["t"] - 240)
            if not ruta or os.path.basename(ruta) in self.cfg_ui.get("rep_hechas", []):
                return
            try:
                m = os.path.getmtime(ruta)
            except OSError:
                return
            if ruta != r["ruta"] or m != r["mtime"]:
                r["ruta"], r["mtime"], r["visto"] = ruta, m, ahora
                return
            if ahora - r["visto"] < 4:               # el juego aún la está terminando de escribir
                return
            try:                                      # mientras Fortnite no la cierra, la clave sale vacía
                if _lector_rep:
                    with open(ruta, "rb") as fh:
                        cab = _lector_rep.leer_cabecera_replay(fh.read(8192))
                    if cab["enc"] and not any(cab["key"]):
                        return
            except Exception:
                pass
            r["estado"] = "leyendo"

            def tarea():
                try:
                    r["res"] = analizar_repeticion(ruta)
                except Exception as e:
                    r["res"] = {"error": str(e) or type(e).__name__}

            threading.Thread(target=tarea, daemon=True).start()
        elif r["res"] is not None:
            self.rec = None
            self.aplicar_recuento(r)

    def aplicar_recuento(self, r):
        """Compara lo contado en directo con lo que dice la repetición y corrige la diferencia."""
        res = r["res"]
        if "error" in res:
            registrar_error("repeticion: " + res["error"])
            self.aviso("🎞 No se pudo leer la repetición: %s" % res["error"], 20)
            return
        hechas = self.cfg_ui.setdefault("rep_hechas", [])
        hechas.append(res["archivo"])
        del hechas[:-20]
        dif = res["total"] - r["contados"]
        if self.cfg_ui.get("modo_conteo") == "replays":     # el número de partida pasa a ser el de esta repetición
            self.sesion = min(MAX_NUMERO, res["total"])
            self.lbl_sesion.config(text=str(self.sesion))
            self.sync.publicar(self.cfg_on.get("nombre", ""), self.total, self.sesion)
        detalle = "%d cofres (%d abiertos + %d rotos)" % (res["total"], res["abiertos"], res["rotos"])
        if "mano" in res:
            detalle = "%d cofres tuyos (a mano %d, a pico %d, de otros %d%s)" % (res["total"], res["mano"], res["pico"], res["dudosos"], "" if res["sepa"] else ", sin separar")
        idx = r["indice"]
        if dif == 0:
            msg = "🎞 Repetición: %s. Coincide con lo contado en directo." % detalle
            if idx is not None and idx == len(self.hist.partidas) - 1:
                self.cfg_ui["ult_rep"] = {"n": len(self.hist.partidas), "dif": 0, "total": res["total"]}
        else:
            self.total = max(0, self.total + dif)
            idx = r["indice"]
            if idx is not None and idx < len(self.hist.partidas):
                p = self.hist.partidas[idx]
            elif dif > 0:
                p = []
                self.hist.partidas.append(p)
                idx = len(self.hist.partidas) - 1
            else:
                p = None
            if p is not None:
                if dif > 0:
                    p.extend([int(r["t"]), 1] for _ in range(dif))
                else:
                    del p[max(0, len(p) + dif):]
                    if not p:
                        del self.hist.partidas[idx]
                        idx = None
                self.hist.version += 1
                self.hist.guardar()
                if idx is not None and idx == len(self.hist.partidas) - 1:
                    self.cfg_ui["ult_rep"] = {"n": len(self.hist.partidas), "dif": dif, "total": res["total"]}
            self._st = None
            self._res_clave = None
            self.lbl_total.config(text=str(self.total))
            self.destello()
            self.pintar_meta()
            self.pintar_resumen()
            self.refrescar_overlay(guardar=False)
            self.sync.publicar(self.cfg_on.get("nombre", ""), self.total, self.sesion)
            msg = "🎞 Repetición: %s. En directo se contaron %d: total corregido (%+d)." % (detalle, r["contados"], dif)
        self.ult_recuento = msg
        self.aviso(msg, 45)
        self.guardar()

    def deshacer_partida(self):
        """Reabre la última partida guardada (por si se cerró sin querer o el lobby se detectó mal)."""
        if not self.hist.partidas:
            messagebox.showinfo("Deshacer", "No hay ninguna partida guardada que reabrir.", parent=self.root)
            return
        ult = self.hist.partidas[-1]
        if not messagebox.askyesno(
                "Deshacer",
                "¿Reabrir la última partida guardada (%d cofres)?\n\nSus cofres volverán a la partida en curso."
                % len(ult), parent=self.root):
            return
        if not self.hist.deshacer_cierre():
            return
        previa = self.sesion_previa if self.sesion_previa is not None else len(ult)
        self.sesion_previa = None
        self.sesion = min(MAX_NUMERO, previa + self.sesion)
        self.lbl_sesion.config(text=str(self.sesion))
        self._st = None
        self._res_clave = None
        self.pintar_resumen()
        self.refrescar_overlay()
        self.sync.publicar(self.cfg_on.get("nombre", ""), self.total, self.sesion)
        self.aviso("Partida reabierta: ahora lleva %d cofres." % len(self.hist.actual))

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

    def rects_propios(self):
        """Lo que ocupan en pantalla las ventanas de ESTE programa (el número flotante, los paneles...),
        para taparlo en negro y que nunca se confunda con un aviso de cofre del juego. Los números
        lavanda de «partida» se parecen mucho al texto del aviso."""
        rects = []
        ventanas = [self.root] + [w for w in self.root.winfo_children() if isinstance(w, tk.Toplevel)]
        for v in ventanas:
            try:
                if not v.winfo_viewable():
                    continue
                izq, arr = v.winfo_rootx(), v.winfo_rooty()
                rects.append((izq, arr, izq + v.winfo_width(), arr + v.winfo_height()))
            except tk.TclError:
                continue
        return rects

    def tapar_ventanas_propias(self, img, x0, y0):
        tapar_rects(img, x0, y0, self.rects_propios())

    def capturar(self, rect):
        return captura_zona(self.sct, rect, self.rects_propios())

    def capturar_caja(self, rect, caja):
        return captura_caja(self.sct, rect, caja)

    def revisar_lobby(self, rect):
        self.aplicar_lobby(mirar_lobby(self.sct, rect))

    def aplicar_lobby(self, info):
        """info = lo que devuelve mirar_lobby() (se calcula en segundo plano)."""
        if info is None or self.cfg_ui.get("modo_conteo") == "replays":
            return          # en modo replays la partida se cierra al terminar la repetición, no con el lobby
        ok, fa, fp, modo = info
        self.lobby_info = (fa, fp)
        # Si hay un aviso de cofre sostenido en pantalla, no puede ser el lobby (falso positivo)
        if ok and not self.en_lobby and self.visto_seg >= 4:
            ok = False
            modo = ""
        self.lobby_modo = modo
        if ok:
            self.lobby_no = 0
            self.lobby_si += 1
            if self.lobby_si >= LOBBY_CONFIRMAR and not self.en_lobby:
                self.en_lobby = True
                # Si acabas de abrir el programa y ya estás en el lobby, NO se cierra la partida:
                # así, al reabrirlo, conservas los mismos datos que tenías al cerrarlo.
                recien_abierto = (time.time() - self.t_inicio) < LOBBY_GRACIA_ARRANQUE
                en_rep = self.cfg_ui.get("modo_conteo") == "replays" and getattr(self, "_hubo_partida", True)
                if self.var_lobby.get() and not recien_abierto and (self.sesion > 0 or self.hist.actual or en_rep):
                    self._hubo_partida = False
                    self.nueva_partida(auto=True)
        else:
            self.lobby_si = 0
            if self.en_lobby:
                self.lobby_no += 1
                if self.lobby_no >= LOBBY_REARMAR:
                    self.en_lobby = False
                    self._hubo_partida = True
                    self.lobby_no = 0

    def guardar_fallo(self):
        # Si sumas un cofre a mano (porque no te lo contó), guarda lo que veía el programa justo antes.
        if not self.var_fotos.get() or not self.frames_recientes:
            return
        frames = list(self.frames_recientes)
        marca = time.strftime("%Y%m%d_%H%M%S")
        ahora = time.time()
        leido = ["hace %4.1f s: %s" % (ahora - t, txt) for t, txt in self.lecturas if ahora - t < 12]
        modo = "lector de texto" if self.usa_lector() else "detector de siempre"

        def tarea():
            try:
                carpeta = os.path.join(CARPETA_FALLOS, marca)
                os.makedirs(carpeta, exist_ok=True)
                t0 = frames[-1][0]
                for i, (t, img) in enumerate(frames):
                    img.save(os.path.join(carpeta, "%d_hace_%.1fs.png" % (i, t0 - t)))
                # lo que había leído el programa justo antes de que sumaras a mano
                with open(os.path.join(carpeta, "lectura.txt"), "w", encoding="utf-8") as f:
                    f.write("Versión %s · %s\n" % (VERSION, modo))
                    f.write("\n".join(leido) if leido else "(el lector no había leído nada)")
                    f.write("\n")
                viejas = sorted(os.listdir(CARPETA_FALLOS))
                for d in viejas[:-12]:
                    shutil.rmtree(os.path.join(CARPETA_FALLOS, d), ignore_errors=True)
            except Exception:
                pass

        threading.Thread(target=tarea, daemon=True).start()

    def borrar_fotos(self):
        self.frames_recientes.clear()
        try:
            shutil.rmtree(CARPETA_DETECCIONES, ignore_errors=True)
            shutil.rmtree(CARPETA_FALLOS, ignore_errors=True)
        except Exception:
            pass

    def al_cambiar_fotos(self):
        if not self.var_fotos.get():
            self.borrar_fotos()
        self.guardar()

    def guardar_deteccion(self, n, origen=""):
        """Guarda la imagen de cada cofre contado solo: si alguna vez cuenta uno "de más",
        ahí tienes la foto de qué vio el programa (carpeta «detecciones»). Va en segundo plano
        para no retrasar el sonido."""
        if not self.var_fotos.get() or self.ultima_img is None:
            return
        img = self.ultima_img.copy()
        nombre = time.strftime("%Y%m%d_%H%M%S") + "_x%d_%s.png" % (n, origen or "x")
        linea = "%s  +%d  %-8s  leído: %s\n" % (time.strftime("%H:%M:%S"), n, origen or "x", self.ocr_txt or "-")

        def tarea():
            try:
                os.makedirs(CARPETA_DETECCIONES, exist_ok=True)
                img.save(os.path.join(CARPETA_DETECCIONES, nombre))
                ficheros = sorted(f for f in os.listdir(CARPETA_DETECCIONES) if f.endswith(".png"))
                for f in ficheros[:-MAX_DETECCIONES_GUARDADAS]:
                    os.remove(os.path.join(CARPETA_DETECCIONES, f))
                # un renglón por cada cofre contado solo, con lo que leyó el programa
                registro = os.path.join(CARPETA_DETECCIONES, "registro.txt")
                if os.path.isfile(registro) and os.path.getsize(registro) > 150000:
                    os.replace(registro, registro + ".old")
                with open(registro, "a", encoding="utf-8") as f:
                    f.write(linea)
            except Exception:
                pass

        threading.Thread(target=tarea, daemon=True).start()

    def guardar_otros(self, otros):
        """Foto de los avisos de experiencia que NO se han tomado por cofre (con lo que se parecían
        a la palabra «COFRE»): si algún cofre tuyo no cuenta, ahí está la prueba (carpeta
        «detecciones\\otros»)."""
        if not self.var_fotos.get() or not otros or self.ultima_img is None:
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

    def enfriar_sube(self):
        # Un aviso que parpadea (se pierde 1-2 fotogramas por la animación) no reinicia la cuenta.
        if self.sube > 0:
            self.sube_hueco += 1
            if self.sube_hueco > 2:
                self.sube = 0
                self.sube_hueco = 0

    def filtrar_avisos(self, todos, solo):
        """Avisos que se dan por cofre. Para uno NUEVO hace falta parecerse mucho a «COFRE»
        (UMBRAL_COFRE); para mantener uno que ya estaba contado, en la misma posición, basta un
        parecido menor (UMBRAL_SOSTENER): así la animación no lo da por perdido y lo cuenta dos veces."""
        if not solo:
            return list(todos)
        fijos = self.pos_avisos if self.avisos_conf > 0 else []
        out = []
        for a in todos:
            if a["cofre"] >= UMBRAL_COFRE:
                out.append(a)
            elif a["cofre"] >= UMBRAL_SOSTENER and any(abs(y_cofre(a) - y) <= 8 for y in fijos):
                out.append(a)
        if out:
            self.pos_avisos = [y_cofre(a) for a in out]
        elif self.avisos_conf == 0:
            self.pos_avisos = []
        return out

    def procesar(self, n, origen="", contar=True):
        """n = cuántos avisos de cofre se ven ahora mismo. Se cuenta un cofre cada vez que n
        SUBE respecto a los ya contados (así, si coges otro cofre mientras el anterior sigue en
        pantalla, el aviso nuevo se apila y también cuenta). Hay que verlo varios fotogramas
        seguidos para fiarse, y llevar un rato (TIEMPO_REARMAR) sin verlo para dar un aviso por
        terminado: se mide en tiempo y no en fotogramas, para que funcione igual si el PC va lento.
        Devuelve cuántos cofres nuevos ha visto; con contar=False no los suma (lo decide quien llama)."""
        ahora = time.time()
        conf = self.avisos_conf
        nuevos = 0
        if n > conf:
            self.t_visto = ahora
            self.baja = 0
            self.sube_hueco = 0
            if n == self.cand_n:
                self.sube += 1
            else:
                self.cand_n = n
                self.sube = 1
            if self.sube >= FRAMES_PARA_CONTAR:
                nuevos = min(n - conf, 8)
                self.avisos_conf = n
                self.sube = 0
                if contar:
                    for _ in range(nuevos):
                        self.sumar(1, True)
                    self.guardar_deteccion(nuevos, origen)
        elif n < conf:
            self.enfriar_sube()
            self.baja += 1
            if self.baja >= 2 and ahora - self.t_visto >= TIEMPO_REARMAR:
                self.avisos_conf = n
                self.baja = 0
                if n > 0:
                    self.t_visto = ahora
        else:
            self.t_visto = ahora
            self.enfriar_sube()
            self.baja = 0
        return nuevos

    def poner_estado(self, msg):
        """Línea de estado de abajo. Si no se pueden guardar los datos, eso tiene prioridad (en rojo)."""
        if self.error_guardado or self.hist.error:
            self.lbl_estado.config(text="⚠ NO SE PUEDEN GUARDAR TUS DATOS en: %s  — cierra otras copias "
                                        "del programa o revisa el antivirus." % DATOS, fg=ROJO)
        elif time.time() < self.aviso_hasta:
            self.lbl_estado.config(text=self.aviso_txt, fg=VERDE)
        else:
            self.lbl_estado.config(text=msg, fg=APAGADO)

    def usa_lector(self):
        """¿Se están contando los cofres leyendo el texto del aviso?"""
        return (not self.var_manual.get() and bool(self.var_solo_cofre.get()) and bool(self.var_ocr.get())
                and self.lector is not None and self.lector.disponible())

    def tick(self):
        t_ini = time.time()
        intervalo = INTERVALO_MS
        try:
            if self.var_manual.get():
                intervalo = 250                # en modo manual no hay nada que analizar: va más despacio
                self.tick_manual()
            else:
                self.tick_auto(t_ini)
        except Exception as e:
            msg_err = "%s: %s" % (type(e).__name__, e)
            if msg_err != self._ult_err:          # se apunta una vez, no 12 veces por segundo
                self._ult_err = msg_err
                try:
                    import traceback
                    registrar_error("tick: " + " | ".join(traceback.format_exc().strip().splitlines()[-3:]))
                except Exception:
                    pass
            self.lbl_estado.config(text="Error: %s" % e)
        self.t_tick = t_ini
        # el ciclo mide INTERVALO_MS en total (descontando lo que ha tardado el análisis)
        self.root.after(max(25, intervalo - int((time.time() - t_ini) * 1000)), self.tick)

    def tick_manual(self):
        """Modo «solo conteo manual»: no se mira la pantalla para contar cofres. Lo único automático
        que sigue (si lo tienes activado) es cerrar la partida al volver al lobby."""
        if self.avisos_conf or self.n_visto or self.seguidor.pistas or self.ses_cont:
            self.reiniciar_detector()
        if self.var_lobby.get() and self.cfg_ui.get("modo_conteo") != "replays":
            self.tick_n += 1
            r = self.trab.recoger()
            if r is not None and r[0]:
                self.aplicar_lobby(r[1]["lobby"] if isinstance(r[1], dict) else r[1])
            if self.tick_n % 2 == 0:               # cada medio segundo
                rect, _ = self.region_juego()
                if rect is not None:
                    self.ultima_rect = rect
                    self.trab.pedir(mirar_lobby, rect)     # se mira en segundo plano
                else:
                    self.en_lobby = False
                    self.lobby_si = 0
        else:
            self.en_lobby = False
            self.lobby_si = 0
        if self.en_lobby:
            self.poner_luz(CIAN, "en el lobby")
        else:
            self.poner_luz(MORADO, "manual", COLOR_PARTIDA)
        tecla = self.texto_tecla("sumar").strip()
        self.poner_estado("✋ Conteo manual: suma cada cofre con «+1»%s. La detección automática está apagada "
                          "(se cambia en ⚙ Ajustes)." % ((" o con tu atajo " + tecla) if tecla else ""))
        self.lbl_detalle.config(text="Modo manual: no se analiza la pantalla para contar cofres.")

    def contar_con_lector(self, lec, leido, n_av, origen, lista, ahora):
        """Cuenta los cofres con el lector de texto, con el detector de siempre como respaldo.
        Devuelve cuántos cofres se están viendo ahora mismo (para la luz de estado)."""
        nuevos_leg = self.procesar(n_av, origen, contar=False)
        seg = self.seguidor
        if lec is None:
            seg.actualizar([], ahora)
        elif leido:
            seg.actualizar(lec["lineas"], ahora)
            if lec["lineas"]:
                self.t_ocr_ve = ahora
                self.ocr_txt = lec["texto"]
                if not self.lecturas or self.lecturas[-1][1] != lec["texto"]:
                    self.lecturas.append((ahora, lec["texto"]))
        else:
            seg.aplazar(max(0.0, min(0.5, ahora - self.t_tick)))
        # El detector de siempre solo cuenta por su cuenta en dos casos: cuando el lector no consigue
        # leer nada, o cuando ve un multiplicador («X3») en una línea de cofre a la que el lector no
        # le ha encontrado ninguno.
        if nuevos_leg:
            contadas = [p for p in seg.pistas if p["contada"]]
            if ahora - self.t_ocr_ve > 0.35:
                self.ses_leg += nuevos_leg
            elif (origen == "lista" and lista and lista["n"] > lista["lineas"]
                  and contadas and len(contadas) == lista["lineas"]
                  and all(p["fm"] is None and not p["n"] for p in contadas)
                  and not any(p["cofre"] and not p["contada"] for p in seg.pistas)):
                self.ses_extra += nuevos_leg
        del_lector = seg.total + self.ses_extra
        objetivo = max(del_lector, self.ses_leg)
        pend = min(objetivo - self.ses_cont, 8)
        if pend > 0:
            self.ses_cont = objetivo
            for _ in range(pend):
                self.sumar(1, True)
            self.guardar_deteccion(pend, "lector" if del_lector >= self.ses_leg else origen)
        n_luz = max(n_av, seg.visibles())
        if n_luz > 0 or self.avisos_conf > 0 or seg.pistas:
            self.t_ses = ahora
        elif ahora - self.t_ses > 0.8 and (self.ses_cont or self.ses_leg or self.ses_extra or seg.total):
            self.ses_leg = self.ses_cont = self.ses_extra = 0      # el aviso terminó: cuenta nueva
            seg.reiniciar()
        return n_luz

    def tick_auto(self, t_ini):
        rect, msg = self.region_juego()
        if rect is not None and self.overlay_tapa_zona(rect):
            msg = "⚠ El número flotante está sobre la zona de los avisos: muévelo (se tapa y no se ve el cofre)"
        if rect is None:
            self.poner_luz(APAGADO, "sin juego")
            self.poner_estado(msg)
            self.lbl_detalle.config(text="")
            self.en_lobby = False
            self.lobby_si = 0
            self.reiniciar_detector()
            self.trab.recoger()
            return
        self.tick_n += 1
        # Lo que pesa (capturar, analizar, leer el texto, mirar el lobby) se hace en segundo plano:
        # aquí se recoge el fotograma que ya está analizado y se encarga el siguiente.
        r = self.trab.recoger()
        if self.trab.libre():
            ahora = time.time()
            mirar = ahora - self.t_lobby >= LOBBY_CADA * INTERVALO_MS / 1000.0
            if mirar:
                self.t_lobby = ahora
            lector = self.lector if (self.usa_lector() and not self.en_lobby) else None
            self.trab.pedir(analizar_fotograma, rect, self.rects_propios(), mirar, lector)
        if r is None:
            self.poner_estado(msg)
            return
        if not r[0]:
            raise RuntimeError(r[1])
        r = r[1]
        if not isinstance(r, dict):
            return                             # era una tarea del modo manual
        self.ms_fondo = r["ms"]
        if r["lobby"] is not None:
            self.aplicar_lobby(r["lobby"])
        pequena, grande, base = r["pequena"], r["grande"], r["base"]
        self.ultima_img = grande
        self.ultima_base = base
        self.ultima_rect = rect
        if self.var_fotos.get() and time.time() - self.t_frame > 0.5:
            self.t_frame = time.time()
            self.frames_recientes.append((self.t_frame, grande))
        todos = r["todos"]
        solo = bool(self.var_solo_cofre.get())
        # con "solo COFRE" (lo normal) la experiencia de la partida y demás avisos se ignoran
        avisos = self.filtrar_avisos(todos, solo)
        otros = [a for a in todos if a not in avisos]
        ok_v, v1, v2, vw = r["clasico"]
        n_av = len(avisos)
        origen = "nuevo"
        # El detector de siempre (el de los cofres normales) sigue valiendo, SALVO que el
        # detector nuevo haya visto en pantalla un aviso con OTRA palabra (la experiencia
        # que da la partida): entonces ese aviso no es un cofre.
        if ok_v and n_av == 0 and not (solo and otros):
            n_av = 1
            origen = "clasico"
        # Aviso APILADO (varios cofres abiertos seguidos: una lista bajo un solo «+N PE»).
        # Si lo hay, manda: se cuentan las líneas «COFRE...» y sus multiplicadores («X3»).
        lista = r["lista"]
        if lista and lista["activo"]:
            origen = "lista"
            otros = []
            self.lista_cero = 0
            # Mientras la lista siga en pantalla la cuenta solo sube. Para que una lectura
            # suelta mal hecha del «X3» no infle la cuenta, se toma el valor que se repite
            # (el segundo mayor de las últimas 3 lecturas); nunca por debajo de las líneas «COFRE».
            self.lista_hist.append(lista["n"])
            h = sorted(self.lista_hist)
            robusto = h[-2] if len(h) >= 2 else lista["lineas"]
            self.lista_max = max(self.lista_max, robusto, lista["lineas"])
            n_av = self.lista_max
        else:
            self.lista_cero += 1
            if self.lista_cero >= 2:
                self.lista_max = 0
                self.lista_hist.clear()
            elif self.lista_max > 0:
                n_av = max(n_av, self.lista_max)
                origen = "lista"
        # Lector de texto: lee el aviso entero. Si lo que ha leído son otras cosas (eliminación,
        # caja de munición...) y ninguna línea de cofre, ese aviso no cuenta diga lo que diga el
        # detector de siempre.
        usar = self.usa_lector()
        lec = r["lec"] if (usar and not self.en_lobby) else None
        err = r["err_lec"]
        if err and err != self._err_ocr:
            self._err_ocr = err
            registrar_error("lector: " + err)
        leido = bool(lec and lec.get("ok"))
        if leido and lec["solo_otros"]:
            n_av = 0
            origen = "otros"
        if self.en_lobby:       # en el lobby no sale ningún aviso de cofre
            avisos = []
            otros = []
            n_av = 0
        self.ultimo_aviso = avisos[0] if avisos else (otros[0] if otros else None)
        self.guardar_otros(otros)
        if usar:
            n_luz = self.contar_con_lector(lec, leido, n_av, origen, lista, time.time())
        else:
            self.procesar(n_av, origen)
            n_luz = n_av
        self.n_visto = n_luz
        self.visto_seg = self.visto_seg + 1 if n_luz > 0 else 0
        if self.en_lobby:
            self.poner_luz(CIAN, "en el lobby")
        elif n_luz > 0:
            self.poner_luz(VERDE, "¡cofre!" if n_luz < 2 else "¡%d cofres!" % n_luz, pulso=True)
        else:
            self.poner_luz(ORO_OSC, "en partida", APAGADO)
        self.poner_estado(msg)
        a = self.ultimo_aviso
        det = ("COFRE %d%%" % int(a["cofre"] * 100)) if a else "nada"
        if usar:
            if lec is None:
                leyo = "nada que leer"
            elif leido:
                leyo = "«%s»" % (lec["texto"][:44] or "nada legible")
            else:
                leyo = "ilegible ahora" + (" (demasiado lila)" if self.lector.ruido else "")
            lector = "Lector: %s → %d" % (leyo, self.ses_cont)
        elif not (solo and self.var_ocr.get()):
            lector = "Lector: apagado"
        else:
            lector = "Lector: " + ("arrancando" if self.estado_lector() == "iniciando" else "no disponible")
        ms = int((time.time() - t_ini) * 1000)
        self.lbl_detalle.config(text="%s  ·  Detector: %d (%s%s%s)  ·  Lobby %d%%/%d%% %s ·  análisis %d ms "
                                     "(en segundo plano) + %d ms"
                                % (lector, n_av, det, ", clásico" if ok_v else "",
                                   (", lista %d" % lista["n"]) if lista else "",
                                   int(self.lobby_info[0] * 100), int(self.lobby_info[1] * 100),
                                   ("(%s) " % self.lobby_modo) if self.lobby_modo else "", self.ms_fondo, ms))

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
        # lo que ve el lector de texto: la máscara (letras del aviso en blanco) y lo último que leyó
        try:
            if self.ultima_base is not None:
                mascara_texto(self.ultima_base).save(os.path.join(carpeta, "letras_%s.png" % marca))
            ahora = time.time()
            with open(os.path.join(carpeta, "lector_%s.txt" % marca), "w", encoding="utf-8") as f:
                f.write("Versión %s · juego %dx%d\n" % (VERSION, w, h))
                f.write("Lector de texto: %s%s%s\n" % (
                    self.estado_lector(),
                    (" (%s)" % self.lector.hilo.idioma) if (self.lector is not None and self.lector.hilo.idioma) else "",
                    (" · " + self.lector.hilo.motivo) if (self.lector is not None and self.lector.hilo.motivo) else ""))
                f.write("Modo: %s\n" % ("manual" if self.var_manual.get() else
                                         ("lector de texto" if self.usa_lector() else "detector de siempre")))
                f.write("Últimas lecturas:\n")
                for t, txt in self.lecturas:
                    f.write("  hace %5.1f s: %s\n" % (ahora - t, txt))
        except Exception:
            pass
        messagebox.showinfo("Diagnóstico", "Guardado en:\n%s" % carpeta, parent=self.root)



# PARCHE DE INTERFAZ (estilo capturas v2.0.25, con la paleta de colores original).
# Lo pega automáticamente crear_version_nueva.py justo antes del final de tu programa.
import webbrowser
import http.server

# Paleta morada de la captura. Se fija aquí entera, así da igual qué colores tuviera tu archivo antes.
BG = "#1b1730"
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
COLOR_PARTIDA = "#c4b0ff"
AZUL = "#3b6fb0"
LINEA = "#2f2852"
PISTA = "#3a3363"
Tarjeta.__init__.__defaults__ = (PANEL, 12, 14, None)   # el color por defecto de las tarjetas se guardó al arrancar

BTN = "#4a4468"

PAGINA_OBS = ("<!doctype html><meta charset=utf-8><body style='margin:0;background:transparent;"
              "font:900 64px Segoe UI,sans-serif;color:#35d3f2;text-shadow:0 0 6px #000,0 0 6px #000'>"
              "<span id=n>0</span><script>async function t(){try{let d=await(await fetch('/datos')).json();"
              "document.getElementById('n').textContent=d.total}catch(e){}}t();setInterval(t,500)</script>")

TECLAS_DEF["overlay"] = "Ctrl+Mayús+O"
TECLAS_DEF["mover"] = "Ctrl+Mayús+L"
TECLAS_DEF["manual"] = "Ctrl+Mayús+M"


def _dibujar_7(self, k):
    self.delete("all")
    w, h = self._pw, max(60, self._ph)
    n = len(self._dias)
    if w <= 1 or not n:
        return
    mx = max([1] + [v for _d, v in self._dias] + self._ant)
    arriba, abajo = 18, 20
    area = h - arriba - abajo
    paso = w / float(n)
    bw = min(30.0, paso * 0.62)
    nombres = ("lun", "mar", "mié", "jue", "vie", "sáb", "dom")
    for i, (d, v) in enumerate(self._dias):
        ant = self._ant[i] if i < len(self._ant) else 0
        val = ant + (v - ant) * k
        cx = (i + 0.5) * paso
        hoy = i == n - 1
        y1 = h - abajo
        alto = max(4.0, area * val / mx)
        col = ORO if hoy else MORADO
        if not v:
            col = mezclar(PANEL, "#ffffff", 0.12)
        self.create_rectangle(cx - bw / 2, y1 - alto, cx + bw / 2, y1, fill=col, outline="")
        self.create_text(cx, y1 - alto - 8, text=str(v), font=("Segoe UI Semibold", 9),
                         fill=TEXTO if (hoy or v) else APAGADO)
        self.create_text(cx, h - 8, text=nombres[d.weekday()], font=("Segoe UI", 9), fill=APAGADO)


MiniGrafica._dibujar = _dibujar_7
MiniGrafica.ALTO = 100


class _UI:
    # ---------- pequeñas ayudas ----------
    def caja(self, padre, titulo=None, pady=(0, 10)):
        t = Tarjeta(padre, pad=12, radio=14)
        t.pack(fill="x", pady=pady)
        if titulo:
            tk.Label(t.cuerpo, text=titulo, font=("Segoe UI Semibold", 9), fg=ORO_OSC, bg=PANEL, anchor="w").pack(fill="x")
        t.cuerpo._filas = 0
        return t.cuerpo

    def fila_ui(self, caja, texto, clave, defecto, detalle=None):
        v = tk.BooleanVar(value=bool(self.cfg_ui.get(clave, defecto)))
        setattr(self, "ui_" + clave, v)

        def al():
            self.cfg_ui[clave] = bool(v.get())
            self.guardar()
            self.aplicar_ui()

        return self.fila(caja, texto, v, al, detalle)

    def aplicar_ui(self):
        mostrar = bool(self.cfg_ui.get("mostrar_comp", True))
        if mostrar != getattr(self, "_extra_vis", None):
            self._extra_vis = mostrar
            self.extra.pack_forget()
            if mostrar:
                self.extra.pack(fill="x", pady=(10, 0), before=self.lbl_estado)

    def crear_vars(self):
        n = max(1, len(self.sct.monitors) - 1)
        ops = ["Auto"] + ["Pantalla %d" % i for i in range(1, n + 1)]
        B = lambda v: tk.BooleanVar(value=bool(v))
        c = self.cfg_ov
        self.var_pitido, self.var_celebrar, self.var_lobby = B(self.ini_pitido), B(self.ini_celebrar), B(self.ini_lobby)
        self.var_solo_cofre, self.var_fotos, self.var_obs = B(self.ini_solo), B(self.ini_fotos), B(self.ini_obs)
        self.var_inicio, self.var_encima, self.var_manual = B(inicio_windows_activo()), B(self.ini_encima), B(self.ini_manual)
        self.var_ocr, self.var_rep = B(self.ini_ocr), B(self.ini_rep)
        self.var_ov, self.var_mover = B(c.get("visible", False)), B(False)
        self.var_icono, self.var_partida = B(c.get("icono", True)), B(c.get("partida", False))
        self.var_amigo, self.var_grupo, self.var_meta = B(c.get("amigo", False)), B(c.get("grupo", False)), B(c.get("meta", False))
        self.var_zona = tk.StringVar(value=nombre_zona())
        self.var_pantalla = tk.StringVar(value=self.ini_pantalla if self.ini_pantalla in ops else "Auto")
        self.var_sonido = tk.StringVar(value=self.cfg_son["elegido"])
        self.var_tam = tk.StringVar(value=c.get("tam", "Mediano"))
        self.var_upd = tk.StringVar(value=self.cfg_ui.get("upd", "preguntar"))
        self.var_replays = tk.StringVar(value=self.cfg_ui.get("replays") or CARPETA_DEMOS)
        self.chip_ocr = None
        modo = self.cfg_ui.get("modo_conteo")
        if modo not in ("manual", "pantalla", "replays"):
            modo = "manual" if self.ini_manual else "pantalla"
        self.var_modo = tk.StringVar(value=modo)

    # ---------- ventana principal ----------
    def ancho_minimo(self):
        self.root.update_idletasks()
        return max(560, self.marco.winfo_reqwidth() + 24 + BarraFina.ANCHO + 4)

    def colocar_cifras(self, cols):
        self._cols_cifras = cols

    def adaptar(self):
        self._resp_pend = False
        if self._graf_pend is not None:
            self.root.after_cancel(self._graf_pend)
        self._graf_pend = self.root.after(120, self.ajustar_grafica)

    def stat(self, padre, clave, titulo, color, f, c):
        t = Tarjeta(padre, pad=12, radio=12)
        t.grid(row=f, column=c, sticky="nsew", padx=3, pady=3)
        lt = tk.Label(t.cuerpo, text=titulo, font=("Segoe UI Semibold", 8), fg=ORO_OSC, bg=PANEL, anchor="w")
        lt.pack(fill="x")
        fila = tk.Frame(t.cuerpo, bg=PANEL)
        fila.pack(fill="x", pady=(2, 0))
        if clave == "tesoros":
            cv = tk.Canvas(fila, width=26, height=22, bg=PANEL, highlightthickness=0)
            cv.create_polygon(13, 2, 24, 8, 13, 20, 2, 8, fill="", outline=TEXTO, width=2)
            cv.create_line(2, 8, 24, 8, fill=TEXTO, width=2)
            cv.pack(side="left", padx=(0, 8))
        lv = tk.Label(fila, text="–", font=("Segoe UI Semibold", 20), fg=color, bg=PANEL, anchor="w")
        lv.pack(side="left")
        self.res[clave], self.res_t[clave] = lv, lt

    def construir(self):
        globals()["CARPETA_DEMOS"] = self.cfg_ui.get("replays") or CARPETA_DEMOS
        for a in ("overlay", "mover", "manual"):
            if self.cfg_teclas.get(a) == "Ninguna" and TECLAS_DEF[a] not in self.cfg_teclas.values():
                self.cfg_teclas[a] = TECLAS_DEF[a]
        self.marco_ext = tk.Frame(self.root, bg=BG, highlightbackground=ORO, highlightcolor=ORO, highlightthickness=2)
        self.marco_ext.pack(fill="both", expand=True, padx=6, pady=6)
        self.vista = Desplazable(self.marco_ext, bg=BG)
        self.vista.pack(fill="both", expand=True)
        self.marco = tk.Frame(self.vista.interior, bg=BG)
        self.marco.pack(padx=14, pady=(10, 12), fill="both", expand=True)
        m = self.marco
        self.f_grande = tkfont.Font(family="Segoe UI Black", size=26)
        self._resp = None
        self._resp_pend = False
        self._graf_pend = None
        self.res, self.res_t = {}, {}
        self.root.bind("<MouseWheel>", self.vista.rueda, add="+")

        # --- cabecera: título, perfil y luz de estado ---
        cab = tk.Frame(m, bg=BG)
        cab.pack(fill="x", pady=(0, 10))
        self.img_cab = icono_cabecera(30, BG)
        if self.img_cab is not None:
            tk.Label(cab, image=self.img_cab, bg=BG, bd=0).pack(side="left", padx=(0, 8))
        tk.Label(cab, text="CONTADOR DE COFRES", font=("Segoe UI Semibold", 13), fg=ORO, bg=BG).pack(side="left")
        est = tk.Frame(cab, bg=BG)
        est.pack(side="right")
        self.cv_luz = tk.Canvas(est, width=24, height=24, bg=BG, highlightthickness=0, bd=0)
        self.cv_luz.pack(side="left")
        self.luz_aro = self.cv_luz.create_oval(7, 7, 17, 17, outline=BG, width=2)
        self.luz_halo = self.cv_luz.create_oval(5, 5, 19, 19, fill=mezclar(BG, APAGADO, 0.28), outline="")
        self.luz_punto = self.cv_luz.create_oval(8, 8, 16, 16, fill=APAGADO, outline="")
        self.lbl_luz = tk.Label(est, text="esperando", font=("Segoe UI", 9), fg=APAGADO, bg=BG)
        self.lbl_luz.pack(side="left", padx=(2, 0))
        self.lbl_perfil = tk.Label(cab, text="", font=("Segoe UI", 9), fg=APAGADO, bg=BG, cursor="hand2")
        self.lbl_perfil.pack(side="left", expand=True)
        self.lbl_perfil.bind("<Button-1>", self.editar_perfil)

        cuerpo = tk.Frame(m, bg=BG)
        cuerpo.pack(fill="x")
        cuerpo.grid_columnconfigure(0, weight=1, uniform="c")
        cuerpo.grid_columnconfigure(1, weight=1, uniform="c")
        izq = tk.Frame(cuerpo, bg=BG)
        izq.grid(row=0, column=0, sticky="nsew", padx=(0, 6))
        der = tk.Frame(cuerpo, bg=BG)
        der.grid(row=0, column=1, sticky="nsew", padx=(6, 0))

        # --- izquierda: total y última partida ---
        self.t_hero = Tarjeta(izq, pad=14, radio=14)
        self.t_hero.pack(fill="x")
        h = self.panel_num = self.t_hero.cuerpo
        fila = tk.Frame(h, bg=PANEL)
        fila.pack(fill="x")
        c1 = tk.Frame(fila, bg=PANEL)
        c1.pack(side="left", fill="x", expand=True)
        self.lbl_total = tk.Label(c1, text=str(self.total), font=self.f_grande, fg=ORO, bg=PANEL, anchor="w",
                                  cursor="hand2", bd=0, padx=0)
        self.lbl_total.pack(anchor="w")
        tk.Label(c1, text="cofres en total", font=("Segoe UI", 9), fg=APAGADO, bg=PANEL).pack(anchor="w")
        tk.Frame(fila, bg=LINEA, width=1).pack(side="left", fill="y", padx=12, pady=4)
        c2 = tk.Frame(fila, bg=PANEL)
        c2.pack(side="left", fill="x", expand=True)
        self.lbl_sesion = tk.Label(c2, text=str(self.sesion), font=self.f_grande, fg=COLOR_PARTIDA, bg=PANEL,
                                   anchor="w", cursor="hand2", bd=0, padx=0)
        self.lbl_sesion.pack(anchor="w")
        tk.Label(c2, text="última partida", font=("Segoe UI", 9), fg=APAGADO, bg=PANEL).pack(anchor="w")
        self.lbl_total.bind("<Double-Button-1>", self.editar)
        self.lbl_sesion.bind("<Double-Button-1>", self.editar_partida)
        tk.Frame(h, bg=LINEA, height=1).pack(fill="x", pady=(10, 6))
        self.lbl_ses_info = tk.Label(h, text="", font=("Segoe UI Semibold", 9), fg=TEXTO, bg=PANEL, anchor="w")
        self.lbl_ses_info.pack(fill="x")

        t = Tarjeta(izq, pad=10, radio=12)
        t.pack(fill="x", pady=(8, 0))
        f = tk.Frame(t.cuerpo, bg=PANEL)
        f.pack(fill="x")
        tk.Label(f, text="Última partida", font=("Segoe UI", 9), fg=APAGADO, bg=PANEL).pack(side="left")
        self.lbl_ult_info = tk.Label(f, text="", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL)
        self.lbl_ult_info.pack(side="right")
        self.lbl_ult = tk.Label(t.cuerpo, text="–", font=("Segoe UI Semibold", 13), fg=COLOR_PARTIDA, bg=PANEL,
                                anchor="w")
        self.lbl_ult.pack(fill="x")

        t = Tarjeta(izq, pad=10, radio=12)
        t.pack(fill="x", pady=(8, 0))
        tk.Label(t.cuerpo, text="Últimos 7 días", font=("Segoe UI", 9), fg=APAGADO, bg=PANEL, anchor="w").pack(fill="x")
        self.grafica7 = MiniGrafica(t.cuerpo, fondo=PANEL)
        self.grafica7.pack(fill="x", pady=(4, 0))

        # --- derecha: cifras y botones ---
        rej = tk.Frame(der, bg=BG)
        rej.pack(fill="x")
        for c in range(2):
            rej.grid_columnconfigure(c, weight=1, uniform="s")
        for k, (clave, tit, col) in enumerate((("hoy", "Hoy", ORO), ("dia", "Mejor día", ORO),
                                               ("media", "Media por partida", CIAN), ("record", "Mejor partida", VERDE),
                                               ("partidas", "Desde", TEXTO), ("tesoros", "Tesoros", TEXTO))):
            self.stat(rej, clave, tit, col, k // 2, k % 2)
        self.fila_acciones = tk.Frame(der, bg=BG)
        self.fila_acciones.pack(fill="x", pady=(8, 0))
        for c in range(3):
            self.fila_acciones.grid_columnconfigure(c, weight=1, uniform="acc")
        self.btn_overlay = self.boton(self.fila_acciones, "● Overlay", self.alternar_overlay_boton, BTN, 3)
        self.btn_stats = self.boton(self.fila_acciones, "Estadísticas", self.alternar_stats, AZUL, 3)
        self.btn_ajustes = self.boton(self.fila_acciones, "Ajustes", self.alternar_ajustes, MORADO, 3)
        for c, b in enumerate((self.btn_overlay, self.btn_stats, self.btn_ajustes)):
            b.grid(row=0, column=c, sticky="ew", padx=(0 if c == 0 else 3, 0))

        # --- equipo (ocupa todo el ancho) ---
        self.extra = tk.Frame(m, bg=BG)
        self.t_equipo = Tarjeta(self.extra, pad=12, radio=14)
        self.t_equipo.pack(fill="x")
        self.construir_amigos(self.t_equipo.cuerpo)

        self.lbl_estado = tk.Label(m, text="Iniciando...", font=("Segoe UI", 8), fg=APAGADO, bg=BG, justify="center")
        self.lbl_estado.pack(fill="x", pady=(8, 0))
        envolver(self.lbl_estado, m)

        # piezas que otras partes del programa siguen usando (sin enseñarse)
        self.lbl_ritmo = tk.Label(m, text="", bg=BG)
        self.cv_meta = tk.Canvas(m, width=200, height=26, bg=PANEL, highlightthickness=0)
        self._meta_w = 0
        self.lbl_meta = tk.Label(m, text="", bg=BG)
        self.lbl_detalle = tk.Label(m, text="", bg=BG)
        self.lbl_sonido = tk.Label(m, text="", bg=BG)

        self.construir_ventana_ajustes()
        self.var_ov.trace_add("write", lambda *a: self.pintar_btn_overlay())
        self.pintar_btn_overlay()
        self.actualizar_textos_teclas()
        self.pintar_meta()
        self.pintar_resumen()
        self.aplicar_ui()
        self.pintar_amigo(forzar=True)
        self.vista.al_cambiar = self.programar_adaptar
        self.servidor_overlay()
        if self.cfg_ui.get("abrir_informe"):
            self.root.after(1200, self.alternar_stats)

    def pintar_btn_overlay(self):
        b = self.btn_overlay
        b._color = MORADO if self.var_ov.get() else BTN
        b.config(text="● Overlay")

    def actualizar_textos_teclas(self):
        self.btn_stats.config(text="Estadísticas" + self.texto_tecla("stats"))
        if getattr(self, "lbl_atajos_ov", None) is not None:
            f = lambda a: (self.cfg_teclas.get(a) or "Ninguna")
            self.lbl_atajos_ov.config(text="%s mostrar  ·  %s fijar" % (f("overlay"), f("mover")))

    def editar_perfil(self, event=None):
        def ok(texto):
            self.cfg_on["nombre"] = texto.strip()[:20] or nombre_por_defecto()
            self._res_clave = None
            self.pintar_resumen()
            self.guardar()
            return None

        self.dialogo_texto("Perfil", "¿Cómo te llamas?", self.cfg_on.get("nombre", ""),
                           "Así te verán tus amigos en la sala.", ok, ancho=22)

    def pintar_resumen(self):
        st = self.estadisticas()
        tes = self.cfg_ui.get("tesoros", 0)
        clave = (self.hist.version, st["hoy_fecha"], nombre_zona(), self.sesion, self.total, tes,
                 self.cfg_on.get("nombre"))
        if clave == self._res_clave:
            return
        self._res_clave = clave
        juegos = self.hist.todas()
        ult = self.hist.partidas[-1] if self.hist.partidas else None
        por_dia = Counter(fecha_madrid(ts) for p in juegos for ts, _ in p)
        md = max(por_dia.items(), key=lambda kv: (kv[1], kv[0])) if por_dia else None
        ses = [p for p in juegos if p[0][0] >= self.t_inicio - 5]
        ses_c = sum(len(p) for p in ses)
        R, T = self.res, self.res_t
        self.lbl_perfil.config(text="Perfil: %s." % (self.cfg_on.get("nombre") or "").upper())
        self.lbl_sesion.config(text=str(self.sesion if self.sesion else (len(ult) if ult else 0)))
        self.lbl_ses_info.config(text="Sesión: %d cofres  ·  %d partidas  ·  media %d" % (
            ses_c, len(ses), int(round(ses_c / float(len(ses)))) if ses else 0))
        R["hoy"].config(text=str(st["hoy"]))
        R["dia"].config(text=str(st["mejor_dia"]))
        T["dia"].config(text="Mejor día · %s" % md[0].strftime("%d/%m") if md else "Mejor día")
        R["media"].config(text=f1(st["media_total"]) if st["media_total"] is not None else "–")
        R["record"].config(text=str(st["mejor_partida"]))
        R["partidas"].config(text="%d partidas" % st["partidas"])
        T["partidas"].config(text="Desde %s" % a_madrid(juegos[0][0][0]).strftime("%d/%m/%y") if juegos else "Desde")
        R["tesoros"].config(text=str(tes))
        self.grafica7.poner(st["dias14"][-7:])
        if ult:
            ini = a_madrid(ult[0][0])
            dur = max(0, ult[-1][0] - ult[0][0])
            info = "%s %s" % ("hoy" if ini.date() == st["hoy_fecha"] else ini.strftime("%d/%m"), ini.strftime("%H:%M"))
            if dur >= 60:
                info += " · %d min" % (dur // 60)
            rep = self.cfg_ui.get("ult_rep")
            if isinstance(rep, dict) and rep.get("n") == len(self.hist.partidas):
                info += " · 🎞 ✓"
            self.lbl_ult.config(text="%d cofres abiertos" % len(ult))
            self.lbl_ult_info.config(text=info)
        else:
            self.lbl_ult.config(text="Aún sin partidas")
            self.lbl_ult_info.config(text="")
        if getattr(self, "lbl_base", None) is not None:
            base = max(0, self.total - sum(len(p) for p in juegos))
            self.lbl_base.config(text=str(base))
            self.lbl_base_txt.config(text="estimado · se suma al total de %s." % (self.cfg_on.get("nombre") or "").upper())

    def ajustar_base(self, n):
        self.total = max(0, min(MAX_NUMERO, self.total + n))
        self.lbl_total.config(text=str(self.total))
        self.pintar_meta()
        self.refrescar_overlay()
        self.pintar_resumen()

    def pintar_amigo(self, forzar=False):
        antes = self.amigo_render
        _pintar_amigo_orig(self, forzar)
        if self.amigo_render != antes:
            self.root.after(80, self.reajustar_alto)

    def reajustar_alto(self):
        """El ancho es fijo; el alto se ajusta solo al contenido (por ejemplo, al entrar un amigo)."""
        try:
            self.root.update_idletasks()
            h = min(max(463, self.vista.alto_contenido() + 18), self.root.winfo_screenheight() - 60)
            self.root.minsize(617, h)
            self.root.maxsize(617, h)
            self.root.geometry("617x%d" % h)
        except tk.TclError:
            pass

    def ajustar_grafica(self):
        self._graf_pend = None

    # ---------- ventana de ajustes ----------
    def construir_ventana_ajustes(self):
        self.crear_vars()
        w = self.win_aj = tk.Toplevel(self.root)
        w.withdraw()
        w.title("Ajustes")
        w.configure(bg=BG)
        w.resizable(False, False)
        poner_icono_ventana(w)
        w.protocol("WM_DELETE_WINDOW", self.cerrar_ajustes)
        w.bind("<Escape>", lambda e: self.cerrar_ajustes())
        marco_aj = tk.Frame(w, bg=BG, highlightbackground=ORO, highlightcolor=ORO, highlightthickness=2)
        marco_aj.pack(fill="both", expand=True, padx=6, pady=6)
        self.vista_aj = Desplazable(marco_aj, bg=BG)
        self.vista_aj.pack(fill="both", expand=True)
        w.bind("<MouseWheel>", self.vista_aj.rueda, add="+")
        raiz = tk.Frame(self.vista_aj.interior, bg=BG)
        raiz.pack(fill="both", expand=True, padx=14, pady=12)
        raiz.grid_columnconfigure(0, weight=1, uniform="aj")
        raiz.grid_columnconfigure(1, weight=1, uniform="aj")
        izq = tk.Frame(raiz, bg=BG)
        izq.grid(row=0, column=0, sticky="nsew", padx=(0, 6))
        der = tk.Frame(raiz, bg=BG)
        der.grid(row=0, column=1, sticky="nsew", padx=(6, 0))
        tk.Label(izq, text="AJUSTES", font=("Segoe UI Semibold", 10), fg=ORO, bg=BG, anchor="w").pack(fill="x", pady=(0, 8))

        # --- columna izquierda ---
        c = self.caja(izq, "Cómo contar los cofres")
        Segmentado(c, self.var_modo, (("✋ Manual", "manual"), ("🖥 Pantalla", "pantalla"), ("🎞 Replays", "replays")),
                   self.aplicar_modo, fondo=PANEL).pack(fill="x", pady=(8, 4))
        self.lbl_modo = tk.Label(c, text="", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL, anchor="w", justify="left")
        self.lbl_modo.pack(fill="x")
        envolver(self.lbl_modo, c, 4, 120)
        self.aplicar_modo(guardar=False, avisar=False)
        c = self.caja(izq, "Inicio")
        self.fila(c, "Abrir con Windows", self.var_inicio, self.al_cambiar_inicio, "Cuenta tus partidas sin pensar en ello")
        self.fila_ui(c, "Abrir estadísticas al iniciar", "abrir_informe", False)
        c = self.caja(izq, "Equipo y tesoros compartidos")
        self.fila_ui(c, "Mostrar compañeros", "mostrar_comp", True, "En la ventana y en las estadísticas")
        self.fila_ui(c, "Sumar sus cofres a tu total", "sumar_comp", False)
        self.fila_ui(c, "Sumar tesoros del equipo", "sumar_tes", False)
        c = self.caja(izq, "Contar también como cofre")
        self.fila_ui(c, "Cajas de munición", "c_municion", False)
        self.fila_ui(c, "Cajas de comida", "c_comida", False)
        self.fila_ui(c, "Cañones de botín", "c_canon", False)
        c = self.caja(izq, "Overlay")
        self.fila(c, "Abrir overlay", self.var_ov, self.alternar_overlay, "Muestra el número encima del juego")
        self.fila(c, "Mover", self.var_mover, self.cambiar_mover, "Arrástralo donde quieras y apágalo para fijarlo")
        self.subtitulo(c, "TAMAÑO")
        Segmentado(c, self.var_tam, [(n, n) for n in TAMANOS], self.refrescar_overlay, fondo=PANEL).pack(fill="x")
        self.subtitulo(c, "QUÉ ENSEÑAR")
        self.rejilla_chips(c, [("🧰  Cofre", self.var_icono, self.refrescar_overlay),
                               ("🎮  Partida", self.var_partida, self.refrescar_overlay),
                               ("🎯  Meta", self.var_meta, self.refrescar_overlay),
                               ("👥  Amigos", self.var_amigo, self.refrescar_overlay),
                               ("🏆  Grupo", self.var_grupo, self.refrescar_overlay)], columnas=3)
        f = tk.Frame(c, bg=PANEL)
        f.pack(fill="x", pady=(8, 0))
        self.lbl_atajos_ov = tk.Label(f, text="", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL, anchor="w")
        self.lbl_atajos_ov.pack(side="left")
        self.boton_texto(f, "⌨ Atajos", self.dialogo_teclas, fg=ORO).pack(side="right")

        # --- columna derecha ---
        f = tk.Frame(der, bg=BG)
        f.pack(fill="x", pady=(0, 10))
        self.var_idioma = tk.StringVar(value="Sistema (Español)")
        self.menu_opciones(f, self.var_idioma, ["Sistema (Español)"]).pack(side="left", fill="x", expand=True)
        tk.Label(f, text="Versión %s" % VERSION, font=("Segoe UI", 9), fg=APAGADO, bg=BG).pack(side="right", padx=8)
        c = self.caja(der, "Cofres antes del contador")
        f = tk.Frame(c, bg=PANEL)
        f.pack(fill="x", pady=(6, 0))
        self.lbl_base = tk.Label(f, text="0", font=("Segoe UI Black", 28), fg=COLOR_PARTIDA, bg=PANEL)
        self.lbl_base.pack(side="left")
        bf = tk.Frame(f, bg=PANEL)
        bf.pack(side="right")
        self.boton(bf, "+", lambda: self.ajustar_base(1), BTN, 2).pack(pady=(0, 4))
        self.boton(bf, "−", lambda: self.ajustar_base(-1), BTN, 2).pack()
        self.lbl_base_txt = tk.Label(c, text="", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL, anchor="w")
        self.lbl_base_txt.pack(fill="x", pady=(4, 0))
        c = self.caja(der, "Actualizaciones")

        def guarda_upd():
            self.cfg_ui["upd"] = self.var_upd.get()
            self.guardar()

        Segmentado(c, self.var_upd, (("Preguntar", "preguntar"), ("Automáticas", "auto"), ("Nunca", "nunca")),
                   guarda_upd, fondo=PANEL).pack(fill="x", pady=(8, 2))
        f = tk.Frame(c, bg=PANEL)
        f.pack(fill="x", pady=(4, 0))
        self.boton_texto(f, "Buscar ahora", lambda: self.buscar_actualizaciones(True), fg=ORO).pack(side="left")
        self.lbl_upd = tk.Label(f, text="", font=("Segoe UI", 8), fg=APAGADO, bg=PANEL, anchor="w")
        self.lbl_upd.pack(side="left", padx=8)
        c = self.caja(der)
        f = tk.Frame(c, bg=PANEL)
        f.pack(fill="x")
        tk.Label(f, text="Overlay para OBS", font=("Segoe UI", 9), fg=APAGADO, bg=PANEL).pack(side="left")
        self.lbl_obs_est = tk.Label(f, text="", font=("Segoe UI Semibold", 8), bg="#10301f", fg=VERDE, padx=8, pady=2)
        self.lbl_obs_est.pack(side="right")
        f = tk.Frame(c, bg=PANEL)
        f.pack(fill="x", pady=(8, 0))
        self.var_url = tk.StringVar(value="http://localhost:7373/")
        tk.Entry(f, textvariable=self.var_url, state="readonly", font=("Segoe UI", 10), bg=BG, fg=TEXTO,
                 readonlybackground=BG, relief="flat", highlightthickness=1,
                 highlightbackground=LINEA).pack(side="left", fill="x", expand=True, ipady=5)

        def copiar():
            self.root.clipboard_clear()
            self.root.clipboard_append(self.var_url.get())
            self.aviso("Dirección del overlay copiada. En OBS: Fuente → Navegador → pega la dirección.")

        self.boton(f, "Copiar", copiar, BTN, 6).pack(side="left", padx=(6, 0))
        c = self.caja(der, "Carpeta de replays")
        f = tk.Frame(c, bg=PANEL)
        f.pack(fill="x", pady=(6, 0))
        e = tk.Entry(f, textvariable=self.var_replays, state="readonly", font=("Segoe UI", 9), bg=BG, fg=TEXTO,
                     readonlybackground=BG, relief="flat", highlightthickness=1, highlightbackground=LINEA)
        e.pack(side="left", fill="x", expand=True, ipady=4)
        self.boton(f, "Cambiar", self.cambiar_replays, BTN, 6).pack(side="left", padx=(6, 0))
        tk.Label(c, text="Tus datos se guardan en %s" % DATOS, font=("Segoe UI", 8), fg=APAGADO, bg=PANEL, anchor="w",
                 justify="left", wraplength=240).pack(fill="x", pady=(6, 0))
        c = self.caja(der)
        b = self.boton_texto(c, "Restablecer estadísticas...", self.restablecer_stats, bg=PANEL, fg=ROJO)
        b.config(font=("Segoe UI Semibold", 10), pady=6)
        b.pack(fill="x")
        self.boton(der, "Cerrar", self.cerrar_ajustes, MORADO, 9).pack(fill="x", pady=(4, 10))
        f = tk.Frame(der, bg=BG)
        f.pack(fill="x")
        tk.Label(f, text="Web y redes", font=("Segoe UI", 9), fg=APAGADO, bg=BG).pack(side="left")
        lk = tk.Label(f, text="github.com/soyelsol1 ↗", font=("Segoe UI Semibold", 9), fg=ORO, bg=BG, cursor="hand2")
        lk.pack(side="left", padx=8)
        lk.bind("<Button-1>", lambda e: webbrowser.open("https://github.com/soyelsol1/Contador-De-Cofres"))
        w.update_idletasks()
        self.aj_tam = (588, min(max(656, self.vista_aj.alto_contenido() + 18), w.winfo_screenheight() - 80))
        w.minsize(*self.aj_tam)
        w.maxsize(*self.aj_tam)

    def tamano_inicial(self, datos):
        """Ventana principal de tamaño fijo (como la captura: 617 px de ancho)."""
        self.root.resizable(False, False)
        self.root.update_idletasks()
        h = min(max(463, self.vista.alto_contenido() + 18), self.root.winfo_screenheight() - 60)
        geo = "617x%d" % h
        if datos.get("geometria"):
            geo += datos["geometria"]
        try:
            self.root.geometry(geo)
        except tk.TclError:
            self.root.geometry("617x%d" % h)
        self.root.minsize(617, h)
        self.root.maxsize(617, h)

    def alternar_ajustes(self):
        w = self.win_aj
        try:
            if w.winfo_viewable():
                self.cerrar_ajustes()
                return
            ww, wh = self.aj_tam
            rx, ry, rw = self.root.winfo_rootx(), self.root.winfo_rooty(), self.root.winfo_width()
            sw, sh = w.winfo_screenwidth(), w.winfo_screenheight()
        except tk.TclError:
            return
        x = rx + rw + 14
        if x + ww > sw:
            x = max(0, rx - ww - 14)
        y = max(0, min(ry - 30, sh - wh - 60))
        w.geometry("%dx%d+%d+%d" % (ww, wh, x, y))
        w.deiconify()
        self.preparar_ventana(w)
        try:
            w.lift()
            w.focus_force()
        except tk.TclError:
            pass

    TEXTOS_MODO = {
        "manual": "Solo cuentas tú, con el atajo o el botón +1. No se mira la pantalla ni se leen repeticiones.",
        "pantalla": "Se cuentan solos mirando los avisos de la pantalla. No se leen repeticiones.",
        "replays": "No se cuenta en directo: al terminar cada partida (en cuanto Fortnite cierra la repetición, sin esperar al lobby) se lee su "
                   "repetición y se suman los cofres. En Fortnite tiene que estar activado «Grabar repeticiones».",
    }

    def aplicar_modo(self, guardar=True, avisar=True):
        """Un solo modo a la vez: manual, pantalla o replays."""
        m = self.var_modo.get()
        self.cfg_ui["modo_conteo"] = m
        self.var_manual.set(m != "pantalla")     # manual y replays no analizan la pantalla para contar
        self.var_rep.set(m == "replays")         # solo replays lee la repetición al acabar la partida
        self.rec = None
        self.reiniciar_detector()
        self.lbl_modo.config(text=self.TEXTOS_MODO[m])
        if avisar:
            self.aviso(self.TEXTOS_MODO[m], 12)
        if guardar:
            self.guardar()

    def al_cambiar_manual(self):
        """El atajo «conteo automático» alterna entre manual y pantalla."""
        self.var_modo.set("manual" if self.var_manual.get() else "pantalla")
        self.aplicar_modo()

    def programar_recuento(self, contados, guardada):
        if not self.var_rep.get():
            return
        if self.cfg_ui.get("modo_conteo") == "replays":       # en este modo se encarga vigilar_replay, sin esperar al lobby
            return
        if contados == 0 and not self.en_lobby:
            return
        self.rec = {"t": time.time(), "contados": contados, "estado": "esperando", "res": None, "ruta": None,
                    "mtime": 0.0, "visto": 0.0, "indice": (len(self.hist.partidas) - 1) if guardada else None}

    def tick_manual(self):
        _tick_manual_orig(self)
        if self.cfg_ui.get("modo_conteo") == "replays":
            if not self.en_lobby:
                self.poner_luz(COLOR_PARTIDA, "replays")
            self.poner_estado("🎞 Modo replays: los cofres se suman al terminar cada partida, leyendo su repetición.")
            self.lbl_detalle.config(text="Modo replays: no se analiza la pantalla para contar cofres.")

    def cambiar_replays(self):
        r = filedialog.askdirectory(parent=self.win_aj, initialdir=CARPETA_DEMOS or os.path.expanduser("~"))
        if r:
            globals()["CARPETA_DEMOS"] = os.path.normpath(r)
            self.cfg_ui["replays"] = CARPETA_DEMOS
            self.var_replays.set(CARPETA_DEMOS)
            self.guardar()

    def restablecer_stats(self):
        if not messagebox.askyesno("Restablecer estadísticas",
                                   "Se borrará TODO el historial (partidas, días, rachas y récords).\n\n"
                                   "Tu TOTAL de cofres no cambia.\n\n¿Seguro?", parent=self.win_aj, icon="warning"):
            return
        self.hist.borrar_todo()
        self._st = None
        self._res_clave = None
        self.pintar_resumen()

    def buscar_actualizaciones(self, manual=False):
        if not manual and self.var_upd.get() == "nunca":
            return
        return _buscar_orig(self, manual)

    def servidor_overlay(self):
        app = self

        class H(http.server.BaseHTTPRequestHandler):
            def log_message(self, *a):
                pass

            def do_GET(self):
                if self.path.startswith("/datos"):
                    cuerpo, tipo = json.dumps({"total": app.total, "partida": app.sesion}).encode(), "application/json"
                else:
                    cuerpo, tipo = PAGINA_OBS.encode("utf-8"), "text/html; charset=utf-8"
                self.send_response(200)
                self.send_header("Content-Type", tipo)
                self.send_header("Content-Length", str(len(cuerpo)))
                self.end_headers()
                self.wfile.write(cuerpo)

        try:
            srv = http.server.ThreadingHTTPServer(("127.0.0.1", 7373), H)
            threading.Thread(target=srv.serve_forever, daemon=True).start()
            self.lbl_obs_est.config(text="● ACTIVO")
        except OSError:
            self.lbl_obs_est.config(text="● NO DISPONIBLE", fg=ROJO, bg="#2a1620")


_buscar_orig = App.buscar_actualizaciones
_pintar_amigo_orig = App.pintar_amigo
_tick_manual_orig = App.tick_manual
for _n, _f in list(vars(_UI).items()):
    if not _n.startswith("__"):
        setattr(App, _n, _f)

_init_orig = App.__init__


def _init_seguro(self, root):
    """Si algo falla al abrir, lo enseña en una ventana y lo guarda en errores.log (en vez de cerrarse sin más)."""
    try:
        _init_orig(self, root)
    except Exception:
        import traceback
        texto = traceback.format_exc()
        registrar_error("inicio: " + " | ".join(texto.strip().splitlines()[-6:]))
        try:
            messagebox.showerror("Contador de cofres: error al abrir",
                                 "No se ha podido abrir. Copia este texto y mándaselo a quien te ayuda:\n\n"
                                 + "\n".join(texto.strip().splitlines()[-8:]), parent=root)
        except Exception:
            pass
        raise


App.__init__ = _init_seguro

# ---------------------------------------------------------------- recuento con lector_repeticiones.py
# Si lector_repeticiones.py está junto al programa, el recuento al final de cada partida usa ese lector
# (no necesita la DLL de Oodle). Si no está o falla, se usa el sistema anterior (DLL).
# Ojo: ese archivo es GPL v3; si compartes el programa con alguien, también debe compartirse bajo GPL v3
# (el código fuente de verdad sigue público, sin cifrar, en el repositorio de GitHub: la copia local cifrada
# de abajo es solo para que no quede un ".py" suelto y legible en la carpeta de datos de cada quien lo use).
try:
    asegurar_extras()
except Exception:
    pass
try:
    import lector_repeticiones as _lector_rep        # si lo tienes junto al programa (tú, en desarrollo), ese manda
except Exception:
    try:
        _lector_rep = _cargar_modulo_cifrado(os.path.join(CARPETA_CODIGO, "lector_repeticiones.py"),
                                             "lector_repeticiones")
    except Exception as _e_lector:
        _lector_rep = None
        registrar_error("lector_repeticiones no disponible: %s" % (_e_lector or type(_e_lector).__name__))
_analizar_dll = analizar_repeticion
_buscar_oodle_orig = buscar_oodle


def buscar_oodle():
    return _buscar_oodle_orig() or (True if _lector_rep is not None else None)


H_RAF = (20, 25, 28, 36, 69, 240, 260)   # ráfaga de propiedades de tu personaje al golpear/abrir
TOL_RAF = 0.35
H_BUSCAR = 285                    # marca «buscando cofre» del personaje (1 al empezar, 0 al abrir)
H_ANIM = (429, 434, 412)          # animaciones del personaje (golpe de pico)
VENT_ANTES, VENT_DESPUES = 3.0, 0.8   # ventana de la animación respecto a la apertura
TOL_MANO = 0.4                    # tolerancia entre el «0» de la marca y la apertura


def _aperturas_cofre(groups, cache, paquetes):
    """Cofres que aparecen en la repetición: {actor: [segundo en que se ve, ¿ya venía abierto?, clase]}."""
    cls2grp = {}
    for pi, g in groups.items():
        cls2grp.setdefault(g["path"].split(".")[-1], pi)
    res = {}
    for t, x in _lector_rep.bunches(paquetes):
        if not x["open"]:
            continue
        b = x["pkt"]
        b.p = x["start"]
        fin = x["start"] + x["nb"]
        try:
            g, cl = _lector_rep._clasificar_apertura(b, x, cache)
            if not cl or "Chest" not in cl or "Buried" in cl or cl.startswith("BGA_") or g in res:
                continue
            b.p = x["start"]
            grp = cls2grp.get(cl)
            nombres = groups[grp]["props"] if grp is not None else {}
            abierto = False
            if x["mm"]:
                k = b.bits(16)
                for _ in range(k):
                    b.packed()
            b.packed()
            while b.p < fin:
                b.bit()
                if not b.bit():
                    break
                npb = b.packed()
                s0 = b.p
                if s0 + npb > fin:
                    break
                for h, st, nb in _lector_rep._bloque_props(b, s0 + npb):
                    if nombres.get(h) == "SearchingPawn":
                        b.p = st
                        abierto = abierto or b.bits(min(nb, 32)) == 1
                b.p = s0 + npb
            res[g] = [t, abierto, cl]
        except Exception:
            continue
    return res


def _cofres_especiales(groups, cache, paquetes):
    """Cofres de espíritu y raros que aparecen o desaparecen: [(segundo, actor, clase)]."""
    chan, res = {}, []
    for t, x in _lector_rep.bunches(paquetes):
        b = x["pkt"]
        b.p = x["start"]
        ch = x["ch"]
        try:
            if x["open"]:
                g, cl = _lector_rep._clasificar_apertura(b, x, cache)
                chan[ch] = (g, cl)
                if cl and ("Relics" in cl or "RareChest" in cl):
                    res.append((t, g, cl))
            if x["close"]:
                if ch in chan and chan[ch][1] and ("Relics" in chan[ch][1] or "RareChest" in chan[ch][1]):
                    res.append((t, chan[ch][0], chan[ch][1]))
                chan.pop(ch, None)
        except Exception:
            continue
    return res


def _cofres_sin_evento(groups, cache, paquetes, ev, marcas):
    """Búsquedas a mano tuyas (marca 1→0) sin ningún cofre contado, en las que aparece un cofre que no traía
    señal de apertura (aparece justo al abrirlo): se cuentan como cofre tuyo."""
    extra = []
    ap = _aperturas_cofre(groups, cache, paquetes)
    esp = _cofres_especiales(groups, cache, paquetes)
    usados = set()
    ini = None
    for t, v in marcas:
        if v:
            ini = t
            continue
        if ini is None:
            continue
        t1, t0, ini = ini, t, None
        if not 0.5 <= t0 - t1 <= 2.0 or any(t1 - 0.3 <= e["t"] <= t0 + 0.3 for e in ev):
            continue
        for g, (ta, ya, cl) in ap.items():
            if False and g not in usados and not ya and t1 - 0.15 <= ta <= t1 + 0.15:   # el cofre «despierta» al empezar la búsqueda
                usados.add(g)
                extra.append({"t": t0, "actor": g, "clase": cl, "espiritu": False, "sospechoso": False,
                              "mio": True, "via": "mano"})
                break
        else:
            # cofres de espíritu o raros que no mandan señal de apertura: aparecen o se van justo al abrirlos
            for ta, g, cl in esp:
                if g not in usados and t1 - 0.5 <= ta <= t0 + 0.8:
                    usados.add(g)
                    extra.append({"t": t0, "actor": g, "clase": cl, "espiritu": "Relics" in cl, "sospechoso": False,
                                  "mio": True, "via": "mano"})
                    break
    return extra


def _cofres_por_botin(groups, cache, paquetes, ev, marcas):
    """Aperturas a mano tuyas completas (marca 1→0) a las que no corresponde ningún cofre contado, pero tras las
    cuales sale el botín de un cofre que aparece justo al empezar: se cuenta ese cofre."""
    ventanas, ini = [], None
    for t, v in marcas:
        if v:
            ini = t
        elif ini is not None:
            if t - ini >= 0.5:
                ventanas.append((ini, t))
            ini = None
    if not ventanas:
        return []
    tiempos = sorted(e["t"] for e in ev)
    usada = set()
    for e in tiempos:                                  # cada cofre ya contado gasta su apertura
        mejor = None
        for i, (a, b) in enumerate(ventanas):
            if i not in usada and a - 0.3 <= e <= b + 1.0:
                d = abs(e - b)
                if mejor is None or d < mejor[0]:
                    mejor = (d, i)
        if mejor:
            usada.add(mejor[1])
    libres = [w for i, w in enumerate(ventanas) if i not in usada]
    if not libres:
        return []
    botin = []
    for t, x in _lector_rep.bunches(paquetes):
        if x["open"]:
            b = x["pkt"]
            b.p = x["start"]
            try:
                _g, cl = _lector_rep._clasificar_apertura(b, x, cache)
            except Exception:
                continue
            if cl and "Pickup" in cl:
                botin.append(t)
    ap = _aperturas_cofre(groups, cache, paquetes)
    extra = []
    for a, b in libres:
        n = sum(1 for t in botin if b - 0.3 <= t <= b + 1.2)
        if not 2 <= n <= 7 or any(a - 1.5 <= e <= b + 1.5 for e in tiempos):
            continue
        nuevos = [(g, cl) for g, (ta, _ya, cl) in ap.items() if a - 0.7 <= ta <= a + 0.2]
        if len(nuevos) == 1:
            g, cl = nuevos[0]
            extra.append({"t": b, "actor": g, "clase": cl, "espiritu": "Relics" in cl, "sospechoso": False,
                          "mio": True, "via": "mano"})
    return extra


def clasificar_propios(groups, cache, paquetes, ev):
    """Añade a cada evento e["mio"] (True/False) y e["via"] ("mano"/"pico"/"").
    Devuelve False si no encuentra tu personaje (entonces no se puede separar)."""
    cls2grp = {}
    for pi, g in groups.items():
        cls2grp.setdefault(g["path"].split(".")[-1], pi)
    chan, movs = {}, {}
    buscar, anim, raf = {}, {}, {}
    for t, x in _lector_rep.bunches(paquetes):
        b = x["pkt"]
        b.p = x["start"]
        fin = x["start"] + x["nb"]
        ch = x["ch"]
        try:
            if x["open"]:
                g, cl = _lector_rep._clasificar_apertura(b, x, cache)
                chan[ch] = (g, cl)
                b.p = x["start"]
            if x["close"]:
                chan.pop(ch, None)
                continue
            if ch not in chan or "Pawn_Athena" not in (chan[ch][1] or ""):
                continue
            g = chan[ch][0]
            if x["mm"]:
                k = b.bits(16)
                for _ in range(k):
                    b.packed()
            if x["open"]:
                b.packed()
            while b.p < fin:
                b.bit()
                if not b.bit():
                    break
                npb = b.packed()
                s = b.p
                if s + npb > fin:
                    break
                for h, st, nb in _lector_rep._bloque_props(b, s + npb):
                    if h == 12 and nb >= 100:
                        movs[g] = movs.get(g, 0) + 1
                    elif h == H_BUSCAR:
                        b.p = st
                        buscar.setdefault(g, []).append((t, b.bits(min(nb, 8)) != 0))
                    elif h in H_ANIM:
                        anim.setdefault(g, []).append(t)
                    elif h in H_RAF:
                        raf.setdefault(g, []).append(t)
                b.p = s + npb
        except Exception:
            continue
    if not movs:
        return False
    yo = max(movs, key=movs.get)            # tu personaje: el que más se actualiza en tu repetición
    ceros = [t for t, v in buscar.get(yo, []) if not v]
    golpes = anim.get(yo, [])
    rafagas = raf.get(yo, [])
    for e in ev:
        t = e["t"]
        mano = any(abs(t - c) <= TOL_MANO for c in ceros)
        pico = any(t - VENT_ANTES <= a <= t + VENT_DESPUES for a in golpes)
        raga = any(abs(t - a) <= TOL_RAF for a in rafagas)
        pico = pico or raga
        e["mio"] = mano or pico
        e["via"] = "mano" if mano else ("pico" if pico else "")
    try:
        ev.extend(_cofres_sin_evento(groups, cache, paquetes, ev, buscar.get(yo, [])))
    except Exception:
        pass
    try:
        ev.extend(_cofres_por_botin(groups, cache, paquetes, ev, buscar.get(yo, [])))
    except Exception:
        pass
    return True


def _referencias_cofres(groups, cache, paquetes):
    """Quién abrió cada cofre, con el identificador exacto del personaje (SearchingPawn).
    Devuelve (tu personaje, {cofre: [personajes]}, {cofre: clase}, {objeto: clase})."""
    cls2grp = {}
    for pi, g in groups.items():
        cls2grp.setdefault(g["path"].split(".")[-1], pi)
    chan, movs, refs, clase_cofre, clase_obj = {}, {}, {}, {}, {}
    for t, x in _lector_rep.bunches(paquetes):
        b = x["pkt"]
        b.p = x["start"]
        fin = x["start"] + x["nb"]
        ch = x["ch"]
        try:
            if x["open"]:
                g, cl = _lector_rep._clasificar_apertura(b, x, cache)
                chan[ch] = (g, cl, cls2grp.get(cl))
                clase_obj[g] = cl
                b.p = x["start"]
            if x["close"]:
                chan.pop(ch, None)
                continue
            if ch not in chan:
                continue
            g, cl, grp = chan[ch]
            cl = cl or ""
            pers, cofre = "Pawn_Athena" in cl, "Chest" in cl
            if not (pers or cofre):
                continue
            nombres = groups[grp]["props"] if grp is not None else {}
            if x["mm"]:
                k = b.bits(16)
                for _ in range(k):
                    b.packed()
            if x["open"]:
                b.packed()
            while b.p < fin:
                b.bit()
                if not b.bit():
                    break
                npb = b.packed()
                s0 = b.p
                if s0 + npb > fin:
                    break
                for h, st, nb in _lector_rep._bloque_props(b, s0 + npb):
                    if pers:
                        if h == 12 and nb >= 100:
                            movs[g] = movs.get(g, 0) + 1
                    elif nombres.get(h - 1) in ("SearchingPawn", "InteractingPawn"):
                        b.p = st
                        try:
                            pk = b.packed()
                        except Exception:
                            pk = 0
                        if pk:
                            refs.setdefault(g, []).append(pk)
                            clase_cofre[g] = cl
                b.p = s0 + npb
        except Exception:
            continue
    yo = max(movs, key=movs.get) if movs else None
    return yo, refs, clase_cofre, clase_obj


def _disparos_propios(f, h):
    """Segundos en que dispara TU arma: la propiedad LastFireTimeVerified solo llega del jugador que graba."""
    groups, cache = {}, {}
    paquetes = _lector_rep.recorrer_fotogramas(_lector_rep.bloques_de_datos(f, h), groups, cache)
    cls2grp = {}
    for pi, g in groups.items():
        cls2grp.setdefault(g["path"].split(".")[-1], pi)
    chan, tiros = {}, []
    for t, x in _lector_rep.bunches(paquetes):
        b = x["pkt"]
        b.p = x["start"]
        fin = x["start"] + x["nb"]
        ch = x["ch"]
        try:
            if x["open"]:
                g, cl = _lector_rep._clasificar_apertura(b, x, cache)
                chan[ch] = (g, cl, cls2grp.get(cl))
                b.p = x["start"]
            if x["close"]:
                chan.pop(ch, None)
                continue
            if ch not in chan:
                continue
            g, cl, grp = chan[ch]
            if grp is None or not cl or any(k in cl for k in ("Chest", "Pickup", "Pawn", "Pickaxe")):
                continue
            nombres = groups[grp]["props"]
            if "LastFireTimeVerified" not in nombres.values():
                continue
            if x["mm"]:
                k = b.bits(16)
                for _ in range(k):
                    b.packed()
            if x["open"]:
                b.packed()
            while b.p < fin:
                b.bit()
                if not b.bit():
                    break
                npb = b.packed()
                s0 = b.p
                if s0 + npb > fin:
                    break
                for hh, st, nb in _lector_rep._bloque_props(b, s0 + npb):
                    if nombres.get(hh - 1) == "LastFireTimeVerified":
                        tiros.append(t)
                b.p = s0 + npb
        except Exception:
            continue
    return sorted(tiros)


def analizar_repeticion(ruta, parar=None):
    if _lector_rep is not None:
        # Método principal: el analizador de cofres del programa (abiertos + rotos del personaje que graba),
        # con el descompresor sin DLL. Si algo falla, se usa el método de respaldo de más abajo.
        try:
            with open(ruta, "rb") as fh:
                f = fh.read()
            h = _lector_rep.leer_cabecera_replay(f)
            an, n = AnalizadorRepeticion(), 0
            try:
                for blk in _lector_rep.bloques_de_datos(f, h):
                    if parar is not None and parar():
                        raise ErrorRepeticion("cancelado")
                    an.bloque(blk)
                    n += 1
            except ErrorRepeticion:
                raise
            except Exception:
                if n == 0:
                    raise                          # el último bloque a medio escribir: vale lo leído hasta aquí
            if n:
                res = an.resultado()
                res["archivo"] = os.path.basename(ruta)
                # Cofres rotos de lejos: sin ningún jugador asociado, pero rotos mientras TU arma disparaba.
                try:
                    mios = set(g for g, (c, _v) in an.peones.items() if c >= 25)
                    sin_dueno = {}
                    for e in an.eventos:
                        if e[4] and not e[5]:
                            sin_dueno.setdefault(e[1], e[0])
                    if sin_dueno:
                        tiros = _disparos_propios(f, h)
                        lejos = [n_ for n_, t in sin_dueno.items() if any(t - 1.5 <= q <= t + 0.3 for q in tiros)]
                        if lejos:
                            res["rotos"] += len(lejos)
                            res["total"] += len(lejos)
                except Exception:
                    pass
                return res
        except ErrorRepeticion as e:
            if str(e) == "cancelado":
                raise
        except Exception:
            pass
        try:
            with open(ruta, "rb") as fh:
                f = fh.read()
            h = _lector_rep.leer_cabecera_replay(f)
            groups, cache = {}, {}
            paquetes = _lector_rep.recorrer_fotogramas(_lector_rep.bloques_de_datos(f, h), groups, cache)
            ev = _lector_rep.eventos_cofres(groups, cache, paquetes)
            try:
                sepa = clasificar_propios(groups, cache, paquetes, ev)
            except Exception:
                sepa = False
            mios = [e for e in ev if e["mio"]] if sepa else [e for e in ev if not e["sospechoso"]]
            # Atribución exacta: el cofre guarda el identificador del personaje que lo abrió o rompió.
            try:
                yo, refs, clases, clase_obj = _referencias_cofres(groups, cache, paquetes)
            except Exception:
                yo = None
            if yo is not None:
                propios = {a for a, ps in refs.items() if yo in ps}
                conservar = {}
                for e in mios:
                    ps = refs.get(e["actor"], [])
                    otros_reales = ps and yo not in ps and all(clase_obj.get(q) == "PlayerPawn_Athena_C" for q in ps)
                    if not otros_reales:
                        conservar[e["actor"]] = e["clase"]
                for a in propios:
                    conservar.setdefault(a, clases.get(a, ""))
                total = len(conservar)
                esp = sum(1 for c in conservar.values() if "Relics" in (c or ""))
                return {"abiertos": total, "rotos": 0, "total": total, "archivo": os.path.basename(ruta),
                        "espiritu": esp, "dudosos": max(0, len(ev) - len(mios)),
                        "mano": sum(1 for e in mios if e.get("via") == "mano"),
                        "pico": sum(1 for e in mios if e.get("via") == "pico"), "sepa": True}
            return {"abiertos": len(mios), "rotos": 0, "total": len(mios), "archivo": os.path.basename(ruta),
                    "espiritu": sum(1 for e in mios if e["espiritu"]), "dudosos": len(ev) - len(mios),
                    "mano": sum(1 for e in mios if e.get("via") == "mano"),
                    "pico": sum(1 for e in mios if e.get("via") == "pico"), "sepa": sepa}
        except Exception as e:
            if _buscar_oodle_orig() is None:
                raise ErrorRepeticion("lector_repeticiones: %s" % (e or type(e).__name__))
    return _analizar_dll(ruta, parar)


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
        identidad_app()
        root = tk.Tk()
        App(root)
        root.mainloop()

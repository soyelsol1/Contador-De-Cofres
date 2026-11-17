# -*- coding: utf-8 -*-
"""
lector_repeticiones.py — cuenta los cofres de una repetición de Fortnite (.replay) SIN DLL de Oodle.

Uso:   python lector_repeticiones.py            (usa la repetición más reciente de la carpeta Demos)
       python lector_repeticiones.py ruta.replay

Contiene un port a Python del descompresor «ooz» (Kraken Decompressor, Copyright (C) 2016 Powzix),
publicado bajo GNU GPL v3 o posterior (https://github.com/powzix/ooz). Por tanto este archivo
también se distribuye bajo la GPL v3 o posterior.

Solo LEE la repetición; no modifica nada. Si tienes «cryptography» instalada la usa para el
descifrado (más rápido); si no, usa un descifrador propio incluido aquí.
"""
import glob
import os
import re
import struct
import sys
import time

try:
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
except Exception:
    Cipher = None


M32 = 0xFFFFFFFF


class OodleError(Exception):
    pass


# ------------------------------------------------------------------ bit reader (BitReader de ooz)
class BR:
    __slots__ = ("d", "p", "p_end", "bits", "bitpos")

    def __init__(self, d, p, p_end):
        self.d = d
        self.p = p
        self.p_end = p_end
        self.bits = 0
        self.bitpos = 24
        self.refill()

    def refill(self):
        d, p, pe = self.d, self.p, self.p_end
        bits, bp = self.bits, self.bitpos
        while bp > 0:
            b = d[p] if p < pe else 0
            bits |= (b << bp) & M32
            bp -= 8
            p += 1
        self.bits, self.bitpos, self.p = bits, bp, p

    def read_bit_nr(self):
        r = self.bits >> 31
        self.bits = (self.bits << 1) & M32
        self.bitpos += 1
        return r

    def read_bits_nr(self, n):
        r = self.bits >> (32 - n)
        self.bits = (self.bits << n) & M32
        self.bitpos += n
        return r

    def read_bits_nr_zero(self, n):
        r = self.bits >> 1 >> (31 - n)
        self.bits = (self.bits << n) & M32
        self.bitpos += n
        return r


def clz32(x):
    return 32 - x.bit_length()


# ------------------------------------------------------------------ Golomb-Rice (BitReader2)
def rice_lengths(d, p, p_end, bitpos, size):
    """Lee `size` valores unarios (bits MSB primero: ceros hasta un 1). Devuelve (valores, p, bitpos)."""
    out = []
    count = 0
    pos = p * 8 + bitpos
    end_bits = p_end * 8
    while len(out) < size:
        if pos >= end_bits:
            raise OodleError("rice: fin de datos")
        bit = (d[pos >> 3] >> (7 - (pos & 7))) & 1
        pos += 1
        if bit:
            out.append(count)
            count = 0
        else:
            count += 1
    return out, pos >> 3, pos & 7


def rice_bits(vals, size, bitcount, d, p, bitpos, p_end):
    if bitcount == 0:
        return p, bitpos
    bits_required = bitpos + bitcount * size
    if ((bits_required + 7) >> 3) > p_end - p:
        raise OodleError("rice bits: fin de datos")
    pos = p * 8 + bitpos
    for i in range(size):
        v = 0
        for _ in range(bitcount):
            v = (v << 1) | ((d[pos >> 3] >> (7 - (pos & 7))) & 1)
            pos += 1
        vals[i] = (vals[i] << bitcount) + v
    return p + (bits_required >> 3), bits_required & 7


def read_fluff(br, num_symbols):
    if num_symbols == 256:
        return 0
    x = 257 - num_symbols
    if x > num_symbols:
        x = num_symbols
    x *= 2
    y = (x - 1).bit_length()          # BSR(x-1)+1
    v = br.bits >> (32 - y)
    z = (1 << y) - x
    if (v >> 1) >= z:
        br.bits = (br.bits << y) & M32
        br.bitpos += y
        return v - z
    br.bits = (br.bits << (y - 1)) & M32
    br.bitpos += y - 1
    return v >> 1


def huff_convert_to_ranges(num_symbols, P, symlen, br):
    """Devuelve lista de (symbol, num). symlen es una lista (valores rice a partir de num_symbols)."""
    num_ranges = P >> 1
    sym_idx = 0
    si = 0
    ranges = []
    if P & 1:
        br.refill()
        v = symlen[si]
        si += 1
        if v >= 8:
            raise OodleError("ranges")
        sym_idx = br.read_bits_nr(v + 1) + (1 << (v + 1)) - 1
    syms_used = 0
    for i in range(num_ranges):
        br.refill()
        v = symlen[si]
        if v >= 9:
            raise OodleError("ranges")
        num = br.read_bits_nr_zero(v) + (1 << v)
        v = symlen[si + 1]
        if v >= 8:
            raise OodleError("ranges")
        space = br.read_bits_nr(v + 1) + (1 << (v + 1)) - 1
        ranges.append((sym_idx, num))
        syms_used += num
        sym_idx += num + space
        si += 2
    if sym_idx >= 256 or syms_used >= num_symbols or sym_idx + num_symbols - syms_used > 256:
        raise OodleError("ranges")
    ranges.append((sym_idx, num_symbols - syms_used))
    return ranges


# ------------------------------------------------------------------ Huffman
def huff_read_code_lengths_old(br, syms, code_prefix):
    if br.read_bit_nr():
        sym = 0
        num_symbols = 0
        avg_bits_x4 = 32
        forced_bits = br.read_bits_nr(2)
        thres = 1 << (31 - (20 >> forced_bits))
        skip_initial = br.read_bit_refill()
        first = True
        while True:
            if not (first and skip_initial):
                if not (br.bits & 0xff000000):
                    return -1
                sym += br.read_bits_nr(2 * (clz32(br.bits) + 1)) - 2 + 1
                if sym >= 256:
                    break
            first = False
            br.refill()
            if not (br.bits & 0xff000000):
                return -1
            n = br.read_bits_nr(2 * (clz32(br.bits) + 1)) - 2 + 1
            if sym + n > 256:
                return -1
            br.refill()
            num_symbols += n
            while True:
                if br.bits < thres:
                    return -1
                lz = clz32(br.bits)
                v = br.read_bits_nr(lz + forced_bits + 1) + ((lz - 1) << forced_bits)
                codelen = ((-(v & 1)) ^ (v >> 1)) + ((avg_bits_x4 + 2) >> 2)
                if codelen < 1 or codelen > 11:
                    return -1
                avg_bits_x4 = codelen + ((3 * avg_bits_x4 + 2) >> 2)
                br.refill()
                syms[code_prefix[codelen]] = sym
                code_prefix[codelen] += 1
                sym += 1
                n -= 1
                if n == 0:
                    break
            if sym == 256:
                break
        return num_symbols if (sym == 256 and num_symbols >= 2) else -1
    else:
        num_symbols = br.read_bits_nr(8)
        if num_symbols == 0:
            return -1
        if num_symbols == 1:
            syms[0] = br.read_bits_nr(8)
        else:
            codelen_bits = br.read_bits_nr(3)
            if codelen_bits > 4:
                return -1
            for i in range(num_symbols):
                br.refill()
                sym = br.read_bits_nr(8)
                codelen = br.read_bits_nr_zero(codelen_bits) + 1
                if codelen > 11:
                    return -1
                syms[code_prefix[codelen]] = sym
                code_prefix[codelen] += 1
        return num_symbols


def _read_bit_refill(self):
    self.refill()
    return self.read_bit_nr()


BR.read_bit_refill = _read_bit_refill


def huff_read_code_lengths_new(br, syms, code_prefix):
    forced_bits = br.read_bits_nr(2)
    num_symbols = br.read_bits_nr(8) + 1
    fluff = read_fluff(br, num_symbols)
    p = br.p - ((24 - br.bitpos + 7) >> 3)
    bitpos = (br.bitpos - 24) & 7
    code_len, p2, bp2 = rice_lengths(br.d, p, br.p_end, bitpos, num_symbols + fluff)
    code_len = code_len + [0] * 16
    p2, bp2 = rice_bits(code_len, num_symbols, forced_bits, br.d, p2, bp2, br.p_end)
    br.bitpos = 24
    br.p = p2
    br.bits = 0
    br.refill()
    br.bits = (br.bits << bp2) & M32
    br.bitpos += bp2
    running_sum = 0x1e
    for i in range(num_symbols):
        v = code_len[i]
        v = (-(v & 1)) ^ (v >> 1)
        code_len[i] = v + (running_sum >> 2) + 1
        if code_len[i] < 1 or code_len[i] > 11:
            return -1
        running_sum = (running_sum + v) & M32
    ranges = huff_convert_to_ranges(num_symbols, fluff, code_len[num_symbols:], br)
    cp = 0
    for sym, n in ranges:
        for _ in range(n):
            c = code_len[cp]
            cp += 1
            syms[code_prefix[c]] = sym
            code_prefix[c] += 1
            sym += 1
    return num_symbols


_CODE_PREFIX_ORG = (0x0, 0x0, 0x2, 0x6, 0xE, 0x1E, 0x3E, 0x7E, 0xFE, 0x1FE, 0x2FE, 0x3FE)
_REV11 = [int(format(i, "011b")[::-1], 2) for i in range(2048)]


def huff_make_lut(prefix_org, prefix_cur, syms):
    bits2len = bytearray(2048)
    bits2sym = bytearray(2048)
    currslot = 0
    for i in range(1, 11):
        start = prefix_org[i]
        count = prefix_cur[i] - start
        if count:
            stepsize = 1 << (11 - i)
            num_to_set = count << (11 - i)
            if currslot + num_to_set > 2048:
                return None
            bits2len[currslot:currslot + num_to_set] = bytes([i]) * num_to_set
            p = currslot
            for j in range(count):
                bits2sym[p:p + stepsize] = bytes([syms[start + j]]) * stepsize
                p += stepsize
            currslot += num_to_set
    n11 = prefix_cur[11] - prefix_org[11]
    if n11:
        if currslot + n11 > 2048:
            return None
        bits2len[currslot:currslot + n11] = bytes([11]) * n11
        bits2sym[currslot:currslot + n11] = bytes(syms[prefix_org[11]:prefix_org[11] + n11])
        currslot += n11
    if currslot != 2048:
        return None
    # tabla invertida en bits (índice leído LSB primero)
    rl = bytearray(2048)
    rs = bytearray(2048)
    for i in range(2048):
        j = _REV11[i]
        rl[j] = bits2len[i]
        rs[j] = bits2sym[i]
    return rl, rs


def huff_core(rl, rs, A, B, out_size, out):
    """Decodifica out_size símbolos. A: bytes del flujo delantero; B: bytes de los flujos mid(adelante) y end(atrás)."""
    # flujo 0: A hacia delante. flujo 2 (mid): B hacia delante. flujo 1 (end): B hacia atrás.
    posA = 0
    posM = 0
    posE = len(B) - 1
    bitsA = nA = 0
    bitsM = nM = 0
    bitsE = nE = 0
    lenA = len(A)
    lenB = len(B)
    i = 0
    n = out_size
    while i < n:
        # flujo A
        while nA < 16:
            bitsA |= (A[posA] if posA < lenA else 0) << nA
            posA += 1
            nA += 8
        k = bitsA & 0x7FF
        l = rl[k]
        out[i] = rs[k]
        bitsA >>= l
        nA -= l
        i += 1
        if i >= n:
            break
        while nE < 16:
            bitsE |= (B[posE] if 0 <= posE < lenB else 0) << nE
            posE -= 1
            nE += 8
        k = bitsE & 0x7FF
        l = rl[k]
        out[i] = rs[k]
        bitsE >>= l
        nE -= l
        i += 1
        if i >= n:
            break
        while nM < 16:
            bitsM |= (B[posM] if posM < lenB else 0) << nM
            posM += 1
            nM += 8
        k = bitsM & 0x7FF
        l = rl[k]
        out[i] = rs[k]
        bitsM >>= l
        nM -= l
        i += 1


def decode_huff(d, p, src_size, out_size, typ):
    end = p + src_size
    br = BR(d, p, end)
    code_prefix = list(_CODE_PREFIX_ORG)
    syms = [0] * 1280
    if not br.read_bit_nr():
        num_syms = huff_read_code_lengths_old(br, syms, code_prefix)
    elif not br.read_bit_nr():
        num_syms = huff_read_code_lengths_new(br, syms, code_prefix)
    else:
        raise OodleError("huff tipo")
    if num_syms < 1:
        raise OodleError("huff syms")
    src = br.p - ((24 - br.bitpos) // 8)
    if num_syms == 1:
        return bytes([syms[0]]) * out_size
    lut = huff_make_lut(_CODE_PREFIX_ORG, code_prefix, syms)
    if lut is None:
        raise OodleError("huff lut")
    rl, rs = lut
    out = bytearray(out_size)
    if typ == 1:
        if src + 3 > end:
            raise OodleError("huff")
        split_mid = d[src] | (d[src + 1] << 8)
        src += 2
        A = d[src:src + split_mid]
        B = d[src + split_mid:end]
        huff_core(rl, rs, A, B, out_size, out)
    else:
        if src + 6 > end:
            raise OodleError("huff")
        half = (out_size + 1) >> 1
        split_mid = d[src] | (d[src + 1] << 8) | (d[src + 2] << 16)
        src += 3
        if split_mid > end - src:
            raise OodleError("huff")
        src_mid = src + split_mid
        split_left = d[src] | (d[src + 1] << 8)
        src += 2
        if src_mid - src < split_left + 2 or end - src_mid < 3:
            raise OodleError("huff")
        split_right = d[src_mid] | (d[src_mid + 1] << 8)
        if end - (src_mid + 2) < split_right + 2:
            raise OodleError("huff")
        out1 = bytearray(half)
        huff_core(rl, rs, d[src:src + split_left], d[src + split_left:src_mid], half, out1)
        s2 = src_mid + 2
        out2 = bytearray(out_size - half)
        huff_core(rl, rs, d[s2:s2 + split_right], d[s2 + split_right:end], out_size - half, out2)
        out = out1 + out2
    return bytes(out)


# ------------------------------------------------------------------ TANS
def _bsf(x):
    return (x & -x).bit_length() - 1


def tans_decode_table(br, L_bits):
    br.refill()
    if br.read_bit_nr():
        Q = br.read_bits_nr(3)
        num_symbols = br.read_bits_nr(8) + 1
        if num_symbols < 2:
            raise OodleError("tans")
        fluff = read_fluff(br, num_symbols)
        total = fluff + num_symbols
        p = br.p - ((24 - br.bitpos + 7) >> 3)
        bitpos = (br.bitpos - 24) & 7
        rice, p2, bp2 = rice_lengths(br.d, p, br.p_end, bitpos, total)
        rice = rice + [0] * 16
        br.bitpos = 24
        br.p = p2
        br.bits = 0
        br.refill()
        br.bits = (br.bits << bp2) & M32
        br.bitpos += bp2
        ranges = huff_convert_to_ranges(num_symbols, fluff, rice[num_symbols:], br)
        br.refill()
        L = 1 << L_bits
        ci = 0
        average = 6
        somesum = 0
        A = []
        B = []
        for symbol, num in ranges:
            for _ in range(num):
                br.refill()
                nextra = Q + rice[ci]
                ci += 1
                if nextra > 15:
                    raise OodleError("tans")
                v = br.read_bits_nr_zero(nextra) + (1 << nextra) - (1 << Q)
                average_div4 = average >> 2
                limit = 2 * average_div4
                if v <= limit:
                    v = average_div4 + ((-(v & 1)) ^ (v >> 1))
                if limit > v:
                    limit = v
                v += 1
                average += limit - average_div4
                if v == 1:
                    A.append(symbol)
                else:
                    B.append((symbol << 16) + v)
                somesum += v
                symbol += 1
        if somesum != L:
            raise OodleError("tans suma")
        return A, B
    seen = set()
    L = 1 << L_bits
    count = br.read_bits_nr(3) + 1
    bits_per_sym = L_bits.bit_length()
    max_delta_bits = br.read_bits_nr(bits_per_sym)
    if max_delta_bits == 0 or max_delta_bits > L_bits:
        raise OodleError("tans")
    A = []
    B = []
    weight = 0
    total_weights = 0
    while True:
        br.refill()
        sym = br.read_bits_nr(8)
        if sym in seen:
            raise OodleError("tans")
        delta = br.read_bits_nr(max_delta_bits)
        weight += delta
        if weight == 0:
            raise OodleError("tans")
        seen.add(sym)
        if weight == 1:
            A.append(sym)
        else:
            B.append((sym << 16) + weight)
        total_weights += weight
        count -= 1
        if count == 0:
            break
    br.refill()
    sym = br.read_bits_nr(8)
    if sym in seen:
        raise OodleError("tans")
    if L - total_weights < weight or L - total_weights <= 1:
        raise OodleError("tans")
    B.append((sym << 16) + (L - total_weights))
    A.sort()
    B.sort()
    return A, B


def tans_init_lut(A, B, L_bits):
    L = 1 << L_bits
    a_used = len(A)
    lut = [None] * L
    slots = L - a_used
    sa = slots >> 2
    ptr = [0, 0, 0, 0]
    sb = sa + ((slots & 3) > 0)
    ptr[1] = sb
    sb += sa + ((slots & 3) > 1)
    ptr[2] = sb
    sb += sa + ((slots & 3) > 2)
    ptr[3] = sb
    for i in range(a_used):
        lut[slots + i] = ((1 << L_bits) - 1, L_bits, A[i], 0)
    weights_sum = 0
    for ent in B:
        weight = ent & 0xffff
        symbol = ent >> 16
        if weight > 4:
            sym_bits = weight.bit_length() - 1
            Z = L_bits - sym_bits
            bits_x = Z
            x = (1 << Z) - 1
            w = (L - 1) & (weight << Z)
            what_to_add = 1 << Z
            X = (1 << (sym_bits + 1)) - weight
            for j in range(4):
                dst = ptr[j]
                Y = (weight + ((weights_sum - j - 1) & 3)) >> 2
                if X >= Y:
                    for _ in range(Y):
                        lut[dst] = (x, bits_x, symbol, w & 0xFFFF)
                        dst += 1
                        w += what_to_add
                    X -= Y
                else:
                    for _ in range(X):
                        lut[dst] = (x, bits_x, symbol, w & 0xFFFF)
                        dst += 1
                        w += what_to_add
                    Z -= 1
                    what_to_add >>= 1
                    bits_x = Z
                    w = 0
                    x >>= 1
                    for _ in range(Y - X):
                        lut[dst] = (x, bits_x, symbol, w & 0xFFFF)
                        dst += 1
                        w += what_to_add
                    X = weight
                ptr[j] = dst
        else:
            bits = ((1 << weight) - 1) << (weights_sum & 3)
            bits |= bits >> 4
            n = weight
            ww = weight
            while n:
                idx = _bsf(bits)
                bits &= bits - 1
                dst = ptr[idx]
                ptr[idx] += 1
                weight_bits = ww.bit_length() - 1
                bx = L_bits - weight_bits
                lut[dst] = ((1 << bx) - 1, bx, symbol, (L - 1) & (ww << bx))
                ww += 1
                n -= 1
        weights_sum += weight
    return lut


def _u32(d, p):
    q = d[p:p + 4]
    if len(q) < 4:
        q = q + bytes(4 - len(q))
    return struct.unpack("<I", q)[0]


def _u32be_before(d, p):
    """bswap32(*(uint32*)(p-4)) con relleno de ceros fuera de rango."""
    s = p - 4
    if s < 0:
        q = bytes(-s) + d[0:p]
    else:
        q = d[s:p]
    if len(q) < 4:
        q = q + bytes(4 - len(q))
    return struct.unpack(">I", q)[0]


def decode_tans(d, p, src_size, dst_size):
    if src_size < 8 or dst_size < 5:
        raise OodleError("tans")
    src_end = p + src_size
    br = BR(d, p, src_end)
    if br.read_bit_nr():
        raise OodleError("tans")
    L_bits = br.read_bits_nr(2) + 8
    A, B = tans_decode_table(br, L_bits)
    src = br.p - (24 - br.bitpos) // 8
    if src >= src_end:
        raise OodleError("tans")
    lut = tans_init_lut(A, B, L_bits)
    L_mask = (1 << L_bits) - 1
    bits_f = _u32(d, src)
    src += 4
    bits_b = _u32be_before(d, src_end)
    src_end -= 4
    bitpos_f = 32
    bitpos_b = 32
    st0 = bits_f & L_mask
    st1 = bits_b & L_mask
    bits_f >>= L_bits
    bitpos_f -= L_bits
    bits_b >>= L_bits
    bitpos_b -= L_bits
    st2 = bits_f & L_mask
    st3 = bits_b & L_mask
    bits_f >>= L_bits
    bitpos_f -= L_bits
    bits_b >>= L_bits
    bitpos_b -= L_bits
    bits_f |= (_u32(d, src) << bitpos_f) & M32
    src += (31 - bitpos_f) >> 3
    bitpos_f |= 24
    st4 = bits_f & L_mask
    bits_f >>= L_bits
    bitpos_f -= L_bits
    ptr_f = src - (bitpos_f >> 3)
    bitpos_f &= 7
    ptr_b = src_end + (bitpos_b >> 3)
    bitpos_b &= 7
    if ptr_f > ptr_b:
        raise OodleError("tans")
    out = bytearray(dst_size)
    n_end = dst_size - 5
    di = 0
    if di < n_end:
        states = [st0, st1, st2, st3, st4]
        order_f = (0, 1, 2, 3, 4)
        done = False
        while not done:
            # forward
            for grp in ((0, 1), (2, 3), (4,)):
                bits_f |= (_u32(d, ptr_f) << bitpos_f) & M32
                ptr_f += (31 - bitpos_f) >> 3
                bitpos_f |= 24
                for s in grp:
                    e = lut[states[s]]
                    out[di] = e[2]
                    di += 1
                    bitpos_f -= e[1]
                    states[s] = (bits_f & e[0]) + e[3]
                    bits_f >>= e[1]
                    if di >= n_end:
                        done = True
                        break
                if done:
                    break
            if done:
                break
            for grp in ((0, 1), (2, 3), (4,)):
                bits_b |= (_u32be_before(d, ptr_b) << bitpos_b) & M32
                ptr_b -= (31 - bitpos_b) >> 3
                bitpos_b |= 24
                for s in grp:
                    e = lut[states[s]]
                    out[di] = e[2]
                    di += 1
                    bitpos_b -= e[1]
                    states[s] = (bits_b & e[0]) + e[3]
                    bits_b >>= e[1]
                    if di >= n_end:
                        done = True
                        break
                if done:
                    break
        st0, st1, st2, st3, st4 = states
    if ptr_b - ptr_f + (bitpos_f >> 3) + (bitpos_b >> 3) != 0:
        raise OodleError("tans fin")
    if (st0 | st1 | st2 | st3 | st4) & ~0xFF:
        raise OodleError("tans estados")
    out[n_end:n_end + 5] = bytes((st0, st1, st2, st3, st4))
    return bytes(out)


# ------------------------------------------------------------------ RLE / recursivo / multi-array
def decode_rle(d, p, src_size, dst_size):
    src = d[p:p + src_size]
    if src_size <= 1:
        if src_size != 1:
            raise OodleError("rle")
        return bytes([src[0]]) * dst_size
    dst = bytearray()
    cmd_ptr = 1
    cmd_end = src_size
    buf = src
    if src[0]:
        dec, pos = decode_bytes(d, p, p + src_size, 1 << 30)
        n = pos - p
        buf = bytes(dec) + src[n:]
        cmd_ptr = 0
        cmd_end = len(dec) + (src_size - n)
    rle_byte = 0
    while cmd_ptr < cmd_end:
        cmd = buf[cmd_end - 1]
        if cmd - 1 >= 0x2f:
            cmd_end -= 1
            to_copy = (-1 - cmd) & 0xF
            to_rle = cmd >> 4
            if len(dst) + to_copy + to_rle > dst_size or cmd_end - cmd_ptr < to_copy:
                raise OodleError("rle")
            dst += buf[cmd_ptr:cmd_ptr + to_copy]
            cmd_ptr += to_copy
            dst += bytes([rle_byte]) * to_rle
        elif cmd >= 0x10:
            data = (buf[cmd_end - 2] | (buf[cmd_end - 1] << 8)) - 4096
            cmd_end -= 2
            to_copy = data & 0x3F
            to_rle = data >> 6
            if len(dst) + to_copy + to_rle > dst_size or cmd_end - cmd_ptr < to_copy:
                raise OodleError("rle")
            dst += buf[cmd_ptr:cmd_ptr + to_copy]
            cmd_ptr += to_copy
            dst += bytes([rle_byte]) * to_rle
        elif cmd == 1:
            rle_byte = buf[cmd_ptr]
            cmd_ptr += 1
            cmd_end -= 1
        elif cmd >= 9:
            to_rle = ((buf[cmd_end - 2] | (buf[cmd_end - 1] << 8)) - 0x8ff) * 128
            cmd_end -= 2
            if len(dst) + to_rle > dst_size:
                raise OodleError("rle")
            dst += bytes([rle_byte]) * to_rle
        else:
            to_copy = ((buf[cmd_end - 2] | (buf[cmd_end - 1] << 8)) - 511) * 64
            cmd_end -= 2
            if cmd_end - cmd_ptr < to_copy or len(dst) + to_copy > dst_size:
                raise OodleError("rle")
            dst += buf[cmd_ptr:cmd_ptr + to_copy]
            cmd_ptr += to_copy
    if cmd_ptr != cmd_end or len(dst) != dst_size:
        raise OodleError("rle fin")
    return bytes(dst)


def get_block_size(d, p, end, cap):
    if end - p < 2:
        raise OodleError("bloque")
    chunk_type = (d[p] >> 4) & 7
    if chunk_type == 0:
        if d[p] >= 0x80:
            src_size = ((d[p] << 8) | d[p + 1]) & 0xFFF
            p += 2
        else:
            if end - p < 3:
                raise OodleError("bloque")
            src_size = (d[p] << 16) | (d[p + 1] << 8) | d[p + 2]
            if src_size & ~0x3ffff:
                raise OodleError("bloque")
            p += 3
        if src_size > cap or end - p < src_size:
            raise OodleError("bloque")
        return src_size
    if chunk_type >= 6:
        raise OodleError("bloque")
    if d[p] >= 0x80:
        if end - p < 3:
            raise OodleError("bloque")
        bits = (d[p] << 16) | (d[p + 1] << 8) | d[p + 2]
        src_size = bits & 0x3ff
        dst_size = src_size + ((bits >> 10) & 0x3ff) + 1
        p += 3
    else:
        if end - p < 5:
            raise OodleError("bloque")
        bits = (d[p + 1] << 24) | (d[p + 2] << 16) | (d[p + 3] << 8) | d[p + 4]
        src_size = bits & 0x3ffff
        dst_size = (((bits >> 18) | (d[p] << 14)) & 0x3FFFF) + 1
        if src_size >= dst_size:
            raise OodleError("bloque")
        p += 5
    if end - p < src_size or dst_size > cap:
        raise OodleError("bloque")
    return dst_size


def _rotl(x, n):
    n &= 31
    return ((x << n) | (x >> (32 - n))) & M32 if n else x


def decode_multi_array(d, p, end, array_count, cap):
    src_org = p
    if end - p < 4:
        raise OodleError("multi")
    num_arrays = d[p]
    p += 1
    if not (num_arrays & 0x80):
        raise OodleError("multi")
    num_arrays &= 0x3f
    if num_arrays == 0:
        arrays = []
        for _ in range(array_count):
            out, p = decode_bytes(d, p, end, cap)
            arrays.append(out)
        return arrays, p - src_org
    ent = []
    total_size = 0
    for _ in range(num_arrays):
        out, p = decode_bytes(d, p, end, 1 << 30)
        ent.append([out, 0])
        total_size += len(out)
    if end - p < 3:
        raise OodleError("multi")
    Q = d[p] | (d[p + 1] << 8)
    p += 2
    out_size = get_block_size(d, p, end, total_size)
    num_indexes = out_size
    num_lens = num_indexes - array_count
    if num_lens < 1:
        raise OodleError("multi")
    if Q & 0x8000:
        arr, n = decode_bytes(d, p, end, num_indexes)
        if len(arr) != num_indexes:
            raise OodleError("multi")
        p = n
        lenlog2 = [t >> 4 for t in arr]
        indexes = [t & 0xF for t in arr]
        num_lens = num_indexes
    else:
        lenlog2_chunksize = num_indexes - array_count
        indexes, p = decode_bytes(d, p, end, num_indexes)
        if len(indexes) != num_indexes:
            raise OodleError("multi")
        lenlog2, p = decode_bytes(d, p, end, lenlog2_chunksize)
        if len(lenlog2) != lenlog2_chunksize:
            raise OodleError("multi")
        for v in lenlog2:
            if v > 16:
                raise OodleError("multi")
    varbits_complen = Q & 0x3FFF
    if end - p < varbits_complen:
        raise OodleError("multi")
    f = p
    bits_f = 0
    bitpos_f = 24
    src_end_actual = p + varbits_complen
    b = src_end_actual
    bits_b = 0
    bitpos_b = 24
    decoded = [0] * num_lens
    i = 0
    while i + 2 <= num_lens:
        bits_f |= (_u32be_after(d, f) >> (24 - bitpos_f)) & M32
        f += (bitpos_f + 7) >> 3
        bits_b |= (_u32le_before(d, b) >> (24 - bitpos_b)) & M32
        b -= (bitpos_b + 7) >> 3
        nf = lenlog2[i]
        nb = lenlog2[i + 1]
        bits_f = _rotl(bits_f | 1, nf)
        bitpos_f += nf - 8 * ((bitpos_f + 7) >> 3)
        bits_b = _rotl(bits_b | 1, nb)
        bitpos_b += nb - 8 * ((bitpos_b + 7) >> 3)
        mf = (1 << nf) - 1
        mb = (1 << nb) - 1
        decoded[i] = bits_f & mf
        bits_f &= ~mf & M32
        decoded[i + 1] = bits_b & mb
        bits_b &= ~mb & M32
        i += 2
    if i < num_lens:
        bits_f |= (_u32be_after(d, f) >> (24 - bitpos_f)) & M32
        nf = lenlog2[i]
        bits_f = _rotl(bits_f | 1, nf)
        decoded[i] = bits_f & ((1 << nf) - 1)
    if indexes[num_indexes - 1]:
        raise OodleError("multi")
    indi = 0
    leni = 0
    inc = 1 if (Q & 0x8000) else 0
    arrays = []
    for _ in range(array_count):
        if indi >= num_indexes:
            raise OodleError("multi")
        cur = bytearray()
        while True:
            source = indexes[indi]
            indi += 1
            if source == 0:
                break
            if source > num_arrays or leni >= num_lens:
                raise OodleError("multi")
            cur_len = decoded[leni]
            leni += 1
            ea = ent[source - 1]
            if cur_len > len(ea[0]) - ea[1]:
                raise OodleError("multi")
            cur += ea[0][ea[1]:ea[1] + cur_len]
            ea[1] += cur_len
        leni += inc
        arrays.append(bytes(cur))
    if indi != num_indexes or leni != num_lens:
        raise OodleError("multi")
    for ea in ent:
        if ea[1] != len(ea[0]):
            raise OodleError("multi")
    return arrays, src_end_actual - src_org


def _u32be_after(d, p):
    q = d[p:p + 4]
    if len(q) < 4:
        q = q + bytes(4 - len(q))
    return struct.unpack(">I", q)[0]


def _u32le_before(d, p):
    s = p - 4
    q = d[s:p] if s >= 0 else bytes(-s) + d[0:p]
    if len(q) < 4:
        q = q + bytes(4 - len(q))
    return struct.unpack("<I", q)[0]


def decode_recursive(d, p, src_size, out_size):
    src_org = p
    end = p + src_size
    if src_size < 6:
        raise OodleError("rec")
    n = d[p] & 0x7f
    if n < 2:
        raise OodleError("rec")
    if not (d[p] & 0x80):
        p += 1
        out = bytearray()
        while n:
            dec, p = decode_bytes(d, p, end, out_size - len(out))
            out += dec
            n -= 1
        if len(out) != out_size:
            raise OodleError("rec")
        return bytes(out), p - src_org
    arrays, used = decode_multi_array(d, p, end, 1, out_size)
    if len(arrays[0]) != out_size:
        raise OodleError("rec")
    return arrays[0], used


# ------------------------------------------------------------------ DecodeBytes (entropía)
def decode_bytes(d, p, end, cap):
    """Devuelve (bytes decodificados, posición tras el bloque)."""
    if end - p < 2:
        raise OodleError("pocos bytes")
    chunk_type = (d[p] >> 4) & 7
    if chunk_type == 0:
        if d[p] >= 0x80:
            src_size = ((d[p] << 8) | d[p + 1]) & 0xFFF
            p += 2
        else:
            if end - p < 3:
                raise OodleError("pocos bytes")
            src_size = (d[p] << 16) | (d[p + 1] << 8) | d[p + 2]
            if src_size & ~0x3ffff:
                raise OodleError("reservado")
            p += 3
        if src_size > cap or end - p < src_size:
            raise OodleError("tamano")
        return d[p:p + src_size], p + src_size
    if d[p] >= 0x80:
        if end - p < 3:
            raise OodleError("pocos bytes")
        bits = (d[p] << 16) | (d[p + 1] << 8) | d[p + 2]
        src_size = bits & 0x3ff
        dst_size = src_size + ((bits >> 10) & 0x3ff) + 1
        p += 3
    else:
        if end - p < 5:
            raise OodleError("pocos bytes")
        bits = (d[p + 1] << 24) | (d[p + 2] << 16) | (d[p + 3] << 8) | d[p + 4]
        src_size = bits & 0x3ffff
        dst_size = (((bits >> 18) | (d[p] << 14)) & 0x3FFFF) + 1
        if src_size >= dst_size:
            raise OodleError("tamano")
        p += 5
    if end - p < src_size or dst_size > cap:
        raise OodleError("tamano")
    if chunk_type in (2, 4):
        out = decode_huff(d, p, src_size, dst_size, chunk_type >> 1)
    elif chunk_type == 5:
        out, used = decode_recursive(d, p, src_size, dst_size)
        if used != src_size:
            raise OodleError("rec tam")
    elif chunk_type == 3:
        out = decode_rle(d, p, src_size, dst_size)
    elif chunk_type == 1:
        out = decode_tans(d, p, src_size, dst_size)
    else:
        raise OodleError("tipo")
    return out, p + src_size


# ------------------------------------------------------------------ Mermaid (decoder tipo 10)
def _decode_far_offsets(d, p, end, count, offset):
    out = []
    cur = p
    if offset < (0xC00000 - 1):
        for _ in range(count):
            if end - cur < 3:
                raise OodleError("far")
            off = d[cur] | (d[cur + 1] << 8) | (d[cur + 2] << 16)
            cur += 3
            out.append(off)
            if off > offset:
                raise OodleError("far")
        return out, cur
    for _ in range(count):
        if end - cur < 3:
            raise OodleError("far")
        off = d[cur] | (d[cur + 1] << 8) | (d[cur + 2] << 16)
        cur += 3
        if off >= 0xc00000:
            if cur == end:
                raise OodleError("far")
            off += d[cur] << 22
            cur += 1
        out.append(off)
        if off > offset:
            raise OodleError("far")
    return out, cur


class _Lz:
    pass


def mermaid_read_lz_table(mode, d, p, end, out, dst_pos, dst_size, offset):
    """Lee las tablas del quantum. Devuelve (lz, dst_pos_actual)."""
    if mode > 1:
        raise OodleError("modo")
    if end - p < 10:
        raise OodleError("corto")
    lz = _Lz()
    lz.first8 = False
    if offset == 0:
        out[dst_pos:dst_pos + 8] = d[p:p + 8]
        p += 8
    lz.lit, p = decode_bytes(d, p, end, dst_size)
    lz.cmd, p = decode_bytes(d, p, end, dst_size)
    lz.cmd_2_offs_end = len(lz.cmd)
    if dst_size <= 0x10000:
        lz.cmd_2_offs = len(lz.cmd)
    else:
        if end - p < 2:
            raise OodleError("corto")
        lz.cmd_2_offs = d[p] | (d[p + 1] << 8)
        p += 2
        if lz.cmd_2_offs > lz.cmd_2_offs_end:
            raise OodleError("cmd2")
    if end - p < 2:
        raise OodleError("corto")
    off16_count = d[p] | (d[p + 1] << 8)
    if off16_count == 0xffff:
        p += 2
        hi, p = decode_bytes(d, p, end, dst_size >> 1)
        lo, p = decode_bytes(d, p, end, dst_size >> 1)
        if len(lo) != len(hi):
            raise OodleError("off16")
        lz.off16 = [lo[i] + hi[i] * 256 for i in range(len(lo))]
    else:
        lz.off16 = list(struct.unpack_from("<%dH" % off16_count, d, p + 2))
        p += 2 + off16_count * 2
    if end - p < 3:
        raise OodleError("corto")
    tmp = d[p] | (d[p + 1] << 8) | (d[p + 2] << 16)
    p += 3
    lz.off32_1 = []
    lz.off32_2 = []
    if tmp != 0:
        s1 = tmp >> 12
        s2 = tmp & 0xFFF
        if s1 == 4095:
            if end - p < 2:
                raise OodleError("corto")
            s1 = d[p] | (d[p + 1] << 8)
            p += 2
        if s2 == 4095:
            if end - p < 2:
                raise OodleError("corto")
            s2 = d[p] | (d[p + 1] << 8)
            p += 2
        lz.off32_1, p = _decode_far_offsets(d, p, end, s1, offset)
        lz.off32_2, p = _decode_far_offsets(d, p, end, s2, offset + 0x10000)
    lz.length_pos = p
    lz.lit_pos = 0
    lz.off16_pos = 0
    return lz


def _mermaid_run(mode, out, dst_begin, dst_size, startoff, dst_end_all, d, src_end, lz,
                 cmd, cmd_a, cmd_b, off32, saved):
    """Ejecuta un tramo de 64 KB. Devuelve True si bien. `saved` = [recent_offs]."""
    dst_end = dst_begin + dst_size
    dst = dst_begin + startoff
    lit = lz.lit
    lp = lz.lit_pos
    lit_end = len(lit)
    o16 = lz.off16
    o16p = lz.off16_pos
    o16n = len(o16)
    o32p = 0
    o32n = len(off32)
    lens_pos = lz.length_pos
    recent = saved[0]
    delta = (mode == 0)
    ci = cmd_a
    while ci < cmd_b:
        c = cmd[ci]
        ci += 1
        if c >= 24:
            litlen = c & 7
            if litlen:
                if delta:
                    base = dst + recent
                    for k in range(litlen):
                        out[dst + k] = (lit[lp + k] + out[base + k]) & 0xFF
                else:
                    out[dst:dst + litlen] = lit[lp:lp + litlen]
                dst += litlen
                lp += litlen
            if not (c >> 7):
                recent = -o16[o16p]
                o16p += 1
            ml = (c >> 3) & 0xF
            if ml:
                m = dst + recent
                if -recent >= ml:
                    out[dst:dst + ml] = out[m:m + ml]
                else:
                    for k in range(ml):
                        out[dst + k] = out[m + k]
                dst += ml
        elif c > 2:
            length = c + 5
            if o32p == o32n:
                return False
            m = dst_begin - off32[o32p]
            o32p += 1
            recent = m - dst
            if dst_end - dst < length:
                return False
            if -recent >= length:
                out[dst:dst + length] = out[m:m + length]
            else:
                for k in range(length):
                    out[dst + k] = out[m + k]
            dst += length
        else:
            if src_end - lens_pos == 0:
                return False
            length = d[lens_pos]
            if length > 251:
                if src_end - lens_pos < 3:
                    return False
                length += (d[lens_pos + 1] | (d[lens_pos + 2] << 8)) * 4
                lens_pos += 2
            lens_pos += 1
            if c == 0:
                length += 64
                if dst_end - dst < length or lit_end - lp < length:
                    return False
                if delta:
                    base = dst + recent
                    for k in range(length):
                        out[dst + k] = (lit[lp + k] + out[base + k]) & 0xFF
                else:
                    out[dst:dst + length] = lit[lp:lp + length]
                dst += length
                lp += length
            elif c == 1:
                length += 91
                if o16p == o16n:
                    return False
                m = dst - o16[o16p]
                o16p += 1
                recent = m - dst
                if -recent >= length:
                    out[dst:dst + length] = out[m:m + length]
                else:
                    for k in range(length):
                        out[dst + k] = out[m + k]
                dst += length
            else:
                length += 29
                if o32p == o32n:
                    return False
                m = dst_begin - off32[o32p]
                o32p += 1
                recent = m - dst
                if -recent >= length:
                    out[dst:dst + length] = out[m:m + length]
                else:
                    for k in range(length):
                        out[dst + k] = out[m + k]
                dst += length
    length = dst_end - dst
    if length > 0:
        if lit_end - lp < length:
            return False
        if delta:
            base = dst + recent
            for k in range(length):
                out[dst + k] = (lit[lp + k] + out[base + k]) & 0xFF
        else:
            out[dst:dst + length] = lit[lp:lp + length]
        lp += length
    saved[0] = recent
    lz.length_pos = lens_pos
    lz.off16_pos = o16p
    lz.lit_pos = lp
    return True


def mermaid_process(mode, d, src_end, out, dst_pos, dst_size, offset, lz):
    saved = [-8]
    cmd = lz.cmd
    cmd_pos = 0
    for iteration in range(2):
        cur = min(dst_size, 0x10000)
        if iteration == 0:
            off32 = lz.off32_1
            cmd_a, cmd_b = 0, lz.cmd_2_offs
        else:
            off32 = lz.off32_2
            cmd_a, cmd_b = lz.cmd_2_offs, lz.cmd_2_offs_end
        startoff = 8 if (offset == 0 and iteration == 0) else 0
        if not _mermaid_run(mode, out, dst_pos, cur, startoff, None, d, src_end, lz, cmd, cmd_a, cmd_b, off32, saved):
            raise OodleError("mermaid run")
        dst_pos += cur
        dst_size -= cur
        if dst_size == 0:
            break
    if lz.length_pos != src_end:
        raise OodleError("mermaid: sobran/faltan bytes (%d != %d)" % (lz.length_pos, src_end))


def mermaid_decode_quantum(out, dst, dst_end, d, p, src_end):
    src_in = p
    while dst_end - dst != 0:
        dst_count = min(dst_end - dst, 0x20000)
        if src_end - p < 4:
            raise OodleError("quantum corto")
        chunkhdr = d[p + 2] | (d[p + 1] << 8) | (d[p] << 16)
        if not (chunkhdr & 0x800000):
            dec, np = decode_bytes(d, p, src_end, dst_count)
            if len(dec) != dst_count:
                raise OodleError("entropia sola")
            out[dst:dst + dst_count] = dec
            src_used = np - p
        else:
            p += 3
            src_used = chunkhdr & 0x7FFFF
            mode = (chunkhdr >> 19) & 0xF
            if src_end - p < src_used:
                raise OodleError("quantum")
            if src_used < dst_count:
                lz = mermaid_read_lz_table(mode, d, p, p + src_used, out, dst, dst_count, dst)
                mermaid_process(mode, d, p + src_used, out, dst, dst_count, dst, lz)
            elif src_used > dst_count or mode != 0:
                raise OodleError("quantum")
            else:
                out[dst:dst + dst_count] = d[p:p + dst_count]
        p += src_used
        dst += dst_count
    return p - src_in


# ------------------------------------------------------------------ cabeceras y bucle principal
def decompress(src, dst_len):
    """Descomprime un bloque Oodle (Mermaid/Kraken-like tipo 10) de `src` a `dst_len` bytes."""
    out = bytearray(dst_len)
    d = bytes(src)
    p = 0
    src_end = len(d)
    offset = 0
    hdr = None
    while offset < dst_len:
        if (offset & 0x3FFFF) == 0:
            b = d[p]
            if (b & 0xF) != 0xC or ((b >> 4) & 3) != 0:
                raise OodleError("cabecera")
            restart = (b >> 7) & 1
            uncompressed = (b >> 6) & 1
            b2 = d[p + 1]
            dtype = b2 & 0x7F
            use_checksums = b2 >> 7
            if dtype != 10:
                raise OodleError("decoder tipo %d no soportado" % dtype)
            hdr = (uncompressed, use_checksums)
            p += 2
        uncompressed, use_checksums = hdr
        left = min(0x40000, dst_len - offset)
        if uncompressed:
            out[offset:offset + left] = d[p:p + left]
            p += left
            offset += left
            continue
        v = (d[p] << 16) | (d[p + 1] << 8) | d[p + 2]
        size = v & 0x3FFFF
        if size != 0x3ffff:
            csize = size + 1
            p += 6 if use_checksums else 3
            whole = 0
            checksum = 0
        else:
            v >>= 18
            if v == 1:
                checksum = d[p + 3]
                csize = 0
                whole = 0
                p += 4
            else:
                raise OodleError("quantum especial")
        if src_end - p < csize:
            raise OodleError("quantum corto")
        if csize == 0:
            out[offset:offset + left] = bytes([checksum]) * left
        elif csize == left:
            out[offset:offset + left] = d[p:p + left]
            p += csize
        else:
            n = mermaid_decode_quantum(out, offset, offset + left, d, p, p + csize)
            if n != csize:
                raise OodleError("quantum tam")
            p += csize
        offset += left
    return bytes(out)


# ---------------------------------------------------------------- AES-256 (ECB) sin librerías
def _crear_tablas():
    sbox = [0] * 256
    p = q = 1
    while True:
        p = p ^ ((p << 1) & 0xFF) ^ (0x1B if p & 0x80 else 0)
        q ^= q << 1
        q ^= q << 2
        q ^= q << 4
        q &= 0xFF
        if q & 0x80:
            q ^= 0x09
        x = q ^ ((q << 1) | (q >> 7)) & 0xFF ^ ((q << 2) | (q >> 6)) & 0xFF ^ \
            ((q << 3) | (q >> 5)) & 0xFF ^ ((q << 4) | (q >> 4)) & 0xFF
        sbox[p] = (x ^ 0x63) & 0xFF
        if p == 1:
            break
    sbox[0] = 0x63
    inv = [0] * 256
    for i, v in enumerate(sbox):
        inv[v] = i
    return sbox, inv


_SBOX, _INV = _crear_tablas()


def _mul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a = ((a << 1) ^ 0x11B) if a & 0x80 else (a << 1)
        b >>= 1
    return r & 0xFF


_M9 = [_mul(i, 9) for i in range(256)]
_M11 = [_mul(i, 11) for i in range(256)]
_M13 = [_mul(i, 13) for i in range(256)]
_M14 = [_mul(i, 14) for i in range(256)]


def _expandir(key):
    w = [list(key[i:i + 4]) for i in range(0, 32, 4)]
    rcon = 1
    for i in range(8, 60):
        t = list(w[i - 1])
        if i % 8 == 0:
            t = t[1:] + t[:1]
            t = [_SBOX[b] for b in t]
            t[0] ^= rcon
            rcon = _mul(rcon, 2)
        elif i % 8 == 4:
            t = [_SBOX[b] for b in t]
        w.append([a ^ b for a, b in zip(w[i - 8], t)])
    return [sum((w[4 * r + c] for c in range(4)), []) for r in range(15)]


def _descifrar_bloque(rk, b):
    s = [x ^ y for x, y in zip(b, rk[14])]
    for r in range(13, -1, -1):
        # InvShiftRows
        s = [s[0], s[13], s[10], s[7], s[4], s[1], s[14], s[11],
             s[8], s[5], s[2], s[15], s[12], s[9], s[6], s[3]]
        s = [_INV[x] for x in s]
        s = [x ^ y for x, y in zip(s, rk[r])]
        if r:
            n = []
            for c in range(0, 16, 4):
                a0, a1, a2, a3 = s[c:c + 4]
                n += [_M14[a0] ^ _M11[a1] ^ _M13[a2] ^ _M9[a3],
                      _M9[a0] ^ _M14[a1] ^ _M11[a2] ^ _M13[a3],
                      _M13[a0] ^ _M9[a1] ^ _M14[a2] ^ _M11[a3],
                      _M11[a0] ^ _M13[a1] ^ _M9[a2] ^ _M14[a3]]
            s = n
    return s


def _aes_propio(key, datos):
    rk = _expandir(key)
    out = bytearray()
    for i in range(0, len(datos) // 16 * 16, 16):
        out += bytes(_descifrar_bloque(rk, datos[i:i + 16]))
    return bytes(out)



def descifrar(key, datos):
    n = len(datos) // 16 * 16
    if Cipher is not None:
        d = Cipher(algorithms.AES(key), modes.ECB()).decryptor()
        return d.update(datos[:n]) + d.finalize()
    return _aes_propio(key, datos[:n])

class R:
    def __init__(s,b,p=0): s.b=b; s.p=p
    def u8(s): v=s.b[s.p]; s.p+=1; return v
    def u32(s): v=struct.unpack_from('<I',s.b,s.p)[0]; s.p+=4; return v
    def i32(s): v=struct.unpack_from('<i',s.b,s.p)[0]; s.p+=4; return v
    def f32(s): v=struct.unpack_from('<f',s.b,s.p)[0]; s.p+=4; return v
    def packed(s):
        v=0; sh=0
        while True:
            b=s.u8(); v|=(b>>1)<<sh; sh+=7
            if not b&1: return v
    def fstr(s):
        n=s.i32()
        if n==0: return ''
        if n<0:
            t=s.b[s.p:s.p+(-n)*2-2].decode('utf-16le','replace'); s.p+=-n*2; return t
        t=s.b[s.p:s.p+n-1].decode('latin1'); s.p+=n; return t
    def fname(s):
        h=s.u8()
        if h: return 'HC%d'%s.packed()
        t=s.fstr(); s.i32(); return t


class B:
    def __init__(s,b,nbits=None):
        s.b=b; s.p=0
        if nbits is None:
            v=b[-1]
            if v==0: nbits=len(b)*8
            else: nbits=(len(b)-1)*8+(v.bit_length()-1)
        s.n=nbits
    def eof(s): return s.p>=s.n
    def bit(s):
        if s.p>=s.n: raise EOFError
        v=(s.b[s.p>>3]>>(s.p&7))&1; s.p+=1; return v
    def bits(s,k):
        if s.p+k>s.n: raise EOFError
        v=0
        for i in range(k):
            v|=((s.b[(s.p+i)>>3]>>((s.p+i)&7))&1)<<i
        s.p+=k; return v
    def sint(s,mx):
        # UE SerializeInt(value, ValueMax)
        v=0; mask=1; 
        while (v+mask)<mx and mask:
            if s.bit(): v|=mask
            mask<<=1
        return v
    def packed(s):
        v=0; sh=0
        while True:
            b=s.bits(8); v|=(b>>1)<<sh; sh+=7
            if not b&1: return v
    def bytes(s,k): return bytes(s.bits(8) for _ in range(k))
    def fstr(s):
        n=s.bits(32)
        if n>=2**31: n-=2**32
        if n==0: return ''
        if n<0:
            return bytes(s.bits(8) for _ in range(-n*2)).decode('utf-16le','replace').rstrip('\0')
        return s.bytes(n).decode('latin1').rstrip('\0')


# ================================================================ lectura de la repetición
def _load_obj(rr):
    g = rr.packed()
    if g == 0:
        return None
    fl = rr.u8()
    outer = None
    path = None
    if fl & 1:
        outer = _load_obj(rr)
        path = rr.fstr()
        if fl & 4:
            rr.u32()
    return (g, path, outer)


def parse_exports(r, groups):
    n = r.packed()
    for _ in range(n):
        pi = r.packed()
        ex = r.packed()
        if ex == 1:
            path = r.fstr()
            ne = r.packed()
            groups[pi] = {"path": path, "n": ne, "props": {}}
        fl = r.u8()
        if fl == 1:
            h = r.packed()
            r.u32()
            nm = r.fname()
            if pi in groups:
                groups[pi]["props"][h] = nm
    return n


def parse_guids(r, cache):
    n = r.packed()

    def reg(o):
        if o is None:
            return
        g, path, outer = o
        cache[g] = (path, outer[0] if outer else 0)
        reg(outer)

    for _ in range(n):
        sz = r.i32()
        sub = R(r.b[r.p:r.p + sz])
        reg(_load_obj(sub))
        r.p += sz
    return n


def leer_cabecera_replay(f):
    p = 0

    def u32():
        nonlocal p
        v = struct.unpack_from("<I", f, p)[0]
        p += 4
        return v

    u32()
    ver = u32()
    if ver >= 7:
        n = u32()
        p += 20 * n
    ms = u32()
    u32()
    u32()
    n = struct.unpack_from("<i", f, p)[0]
    p += 4
    p += (-n * 2) if n < 0 else n
    p += 12
    comp, enc, kl = u32(), u32(), u32()
    key = f[p:p + kl]
    p += kl
    chunks = []
    while p + 8 <= len(f):
        t = u32()
        s = struct.unpack_from("<i", f, p)[0]
        p += 4
        if s < 0 or p + s > len(f):
            break                      # bloque sin terminar (partida en curso)
        chunks.append((t, p, s))
        p += s
    return {"ver": ver, "ms": ms, "comp": comp, "enc": enc, "key": key, "chunks": chunks}


def bloques_de_datos(f, h):
    """Genera los bloques de datos de la partida ya descifrados y descomprimidos."""
    for t, p, s in h["chunks"]:
        if t != 1:
            continue
        raw = f[p + 16:p + s]
        d = descifrar(h["key"], raw) if h["enc"] else raw
        a, b = struct.unpack_from("<ii", d, 0)
        yield decompress(d[8:8 + b], a)


def recorrer_fotogramas(bloques, groups, cache):
    paquetes = []
    for d in bloques:
        r = R(d, 0)
        while r.p < len(d):
            r.u32()
            t = r.f32()
            parse_exports(r, groups)
            parse_guids(r, cache)
            nl = r.packed()
            for _ in range(nl):
                r.fstr()
            ext = struct.unpack_from("<Q", d, r.p)[0]
            r.p += 8 + ext + 12
            while True:
                r.packed()
                sz = r.i32()
                if sz == 0:
                    break
                paquetes.append((t, d[r.p:r.p + sz]))
                r.p += sz
    return paquetes


def _payload_int(b, start, nb):
    b0 = start >> 3
    b1 = (start + nb + 7) >> 3
    v = int.from_bytes(b.b[b0:b1], "little") >> (start & 7)
    return v & ((1 << nb) - 1)


def _bunches_paquete(p):
    b = B(p)
    out = []
    while not b.eof():
        ctrl = b.bit()
        opn = b.bit() if ctrl else 0
        cls = b.bit() if ctrl else 0
        if cls:
            b.sint(15)
        b.bit()
        rel = b.bit()
        ch = b.packed()
        b.bit()
        mm = b.bit()
        part = b.bit()
        pi = pf = 0
        if part:
            pi = b.bit()
            b.bit()
            pf = b.bit()
        if rel or opn:
            if b.bit():
                b.packed()
            else:
                b.fstr()
                b.bits(32)
        nb = b.sint(16384)
        if b.p + nb > b.n:
            raise EOFError
        out.append({"open": opn, "close": cls, "ch": ch, "mm": mm, "part": part, "pi": pi, "pf": pf,
                    "nb": nb, "start": b.p, "pkt": b})
        b.p += nb
    return out


def bunches(paquetes):
    """Genera (tiempo, bunch) completos, juntando los bunches parciales de cada canal."""
    parcial = {}
    for t, p in paquetes:
        try:
            bs = _bunches_paquete(p)
        except Exception:
            continue
        for x in bs:
            if not x["part"]:
                yield t, x
                continue
            ch = x["ch"]
            val = _payload_int(x["pkt"], x["start"], x["nb"])
            if x["pi"]:
                parcial[ch] = {"x0": x, "val": val, "n": x["nb"]}
            else:
                cur = parcial.get(ch)
                if cur is None:
                    continue
                cur["val"] |= val << cur["n"]
                cur["n"] += x["nb"]
            if x["pf"]:
                cur = parcial.pop(ch, None)
                if cur is None:
                    continue
                raw = cur["val"].to_bytes((cur["n"] + 7) // 8 + 1, "little")
                m = dict(cur["x0"])
                m.update(pkt=B(raw, cur["n"]), start=0, nb=cur["n"], part=0)
                yield t, m


def _clasificar_apertura(b, x, cache):
    gs = []
    if x["mm"]:
        k = b.bits(16)
        gs = [b.packed() for _ in range(k)]
    g = b.packed()
    cl = None
    ac = cache.get(g)
    if ac and ac[0]:
        m = re.match(r"(.+?_C)_UAID", ac[0]) or re.match(r"(.+?_C)_\d+$", ac[0])
        cl = m.group(1) if m else ac[0]
    if cl is None:
        nombres = [cache.get(q, (None,))[0] for q in gs]
        dn = [n[len("Default__"):] for n in nombres if n and n.startswith("Default__")]
        if dn:
            cl = dn[0]
    if cl is None and g % 2 == 0 and g > 0:
        try:
            a = cache.get(b.packed(), (None,))[0]
            if a and a.startswith("Default__"):
                cl = a[len("Default__"):]
        except Exception:
            pass
    return g, cl


def _bloque_props(b, fin):
    props = []
    b.bit()
    while b.p < fin:
        h = b.packed()
        if h == 0:
            break
        nb = b.packed()
        props.append((h, b.p, nb))
        b.p += nb
    return props


TIPO_ESPIRITU = ("B_TieredChest_Relics_C",)
SEPARACION_MIN_S = 0.5     # dos cofres tuyos no se abren con menos de ~0,5 s de diferencia (en la prueba llegan a ~0,9 s)


def eventos_cofres(groups, cache, paquetes):
    """Cada vez que un cofre pasa a «buscado» (y no estaba ya abierto cuando lo vimos por primera vez)."""
    cls2grp = {}
    for pi, g in groups.items():
        cls2grp.setdefault(g["path"].split(".")[-1], pi)
    chan = {}
    eventos = []
    for t, x in bunches(paquetes):
        b = x["pkt"]
        b.p = x["start"]
        fin = x["start"] + x["nb"]
        ch = x["ch"]
        try:
            if x["open"]:
                g, cl = _clasificar_apertura(b, x, cache)
                chan[ch] = (g, cl, cls2grp.get(cl))
                b.p = x["start"]
            if x["close"]:
                chan.pop(ch, None)
                continue
            if ch not in chan:
                continue
            g, cl, grp = chan[ch]
            if grp is None:
                continue
            nombres = groups[grp]["props"]
            if "SearchingPawn" not in nombres.values():
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
                s = b.p
                if s + npb > fin:
                    break
                for h, st, nb in _bloque_props(b, s + npb):
                    if nombres.get(h) == "SearchingPawn":
                        b.p = st
                        eventos.append((t, g, cl, b.bits(min(nb, 32)), bool(x["open"])))
                b.p = s + npb
        except Exception:
            continue
    por_actor = {}
    for e in eventos:
        por_actor.setdefault(e[1], []).append(e)
    nuevos = []
    for g, es in por_actor.items():
        es.sort()
        if any(e[4] and e[3] == 1 for e in es):
            continue                      # ya estaba abierto al verlo: no cuenta
        vivos = [e for e in es if not e[4] and e[3] == 1]
        if vivos:
            nuevos.append(vivos[0])
    nuevos.sort()
    res = []
    prev = None
    for t, g, cl, _v, _o in nuevos:
        sospechoso = prev is not None and (t - prev) < SEPARACION_MIN_S
        res.append({"t": t, "actor": g, "clase": cl, "espiritu": cl in TIPO_ESPIRITU, "sospechoso": sospechoso})
        prev = t
    return res


def analizar(ruta):
    f = open(ruta, "rb").read()
    h = leer_cabecera_replay(f)
    groups = {}
    cache = {}
    paquetes = recorrer_fotogramas(bloques_de_datos(f, h), groups, cache)
    ev = eventos_cofres(groups, cache, paquetes)
    return {
        "duracion_s": h["ms"] / 1000.0,
        "eventos": ev,
        "total": len(ev),
        "espiritu": sum(1 for e in ev if e["espiritu"]),
        "normales": sum(1 for e in ev if not e["espiritu"]),
        "sospechosos": sum(1 for e in ev if e["sospechoso"]),
    }


def _mmss(s):
    return "%d:%02d" % (int(s) // 60, int(s) % 60)


if __name__ == "__main__":
    if len(sys.argv) > 1:
        ruta = sys.argv[1]
    else:
        demos = os.path.join(os.environ.get("LOCALAPPDATA", ""), "FortniteGame", "Saved", "Demos")
        lista = [x for x in glob.glob(os.path.join(demos, "*.replay")) if os.path.getsize(x) > 100000]
        ruta = max(lista, key=os.path.getmtime) if lista else None
    if not ruta:
        print("No encuentro ninguna repetición con datos.")
        sys.exit(1)
    t0 = time.time()
    r = analizar(ruta)
    print("Repetición: %s  (%s de partida, analizada en %.1f s)" % (os.path.basename(ruta), _mmss(r["duracion_s"]),
                                                                    time.time() - t0))
    for i, e in enumerate(r["eventos"], 1):
        print("%3d  %s  %-28s%s%s" % (i, _mmss(e["t"]), e["clase"], "  [ESPÍRITU]" if e["espiritu"] else "",
                                       "  (¿de otro jugador? casi a la vez)" if e["sospechoso"] else ""))
    print("\nTOTAL cofres abiertos: %d  (normales %d, de espíritu %d; %d dudosos por abrirse casi a la vez)" % (
        r["total"], r["normales"], r["espiritu"], r["sospechosos"]))

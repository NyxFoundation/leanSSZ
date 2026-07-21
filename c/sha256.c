/*
 * SHA-256 for leanSSZ merkleization.
 *
 * Compact, allocation-free implementation of FIPS 180-4 SHA-256 plus the
 * Lean FFI entry point `lssz_sha256_combine` (hash of the 64-byte
 * concatenation of two 32-byte inputs -> 32 bytes), which is the only
 * primitive SSZ merkleization needs.
 *
 * Trust note: this file is OUTSIDE the proof boundary. Its behavioural
 * contract is recorded as named axioms in LeanSSZ/Hasher/Sha256FFI.lean
 * and checked against NIST CAVP vectors by the test suite.
 */

#include <stdint.h>
#include <string.h>
#include <lean/lean.h>

static const uint32_t K[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

#define ROTR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))

static void sha256_compress(uint32_t state[8], const uint8_t block[64]) {
    uint32_t w[64];
    for (int i = 0; i < 16; i++) {
        w[i] = ((uint32_t)block[4 * i] << 24) | ((uint32_t)block[4 * i + 1] << 16)
             | ((uint32_t)block[4 * i + 2] << 8) | (uint32_t)block[4 * i + 3];
    }
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = ROTR(w[i - 15], 7) ^ ROTR(w[i - 15], 18) ^ (w[i - 15] >> 3);
        uint32_t s1 = ROTR(w[i - 2], 17) ^ ROTR(w[i - 2], 19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16] + s0 + w[i - 7] + s1;
    }
    uint32_t a = state[0], b = state[1], c = state[2], d = state[3];
    uint32_t e = state[4], f = state[5], g = state[6], h = state[7];
    for (int i = 0; i < 64; i++) {
        uint32_t S1 = ROTR(e, 6) ^ ROTR(e, 11) ^ ROTR(e, 25);
        uint32_t ch = (e & f) ^ (~e & g);
        uint32_t t1 = h + S1 + ch + K[i] + w[i];
        uint32_t S0 = ROTR(a, 2) ^ ROTR(a, 13) ^ ROTR(a, 22);
        uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
        uint32_t t2 = S0 + maj;
        h = g; g = f; f = e; e = d + t1;
        d = c; c = b; b = a; a = t1 + t2;
    }
    state[0] += a; state[1] += b; state[2] += c; state[3] += d;
    state[4] += e; state[5] += f; state[6] += g; state[7] += h;
}

static void sha256(const uint8_t *data, size_t len, uint8_t out[32]) {
    uint32_t state[8] = {
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
    };
    size_t i = 0;
    for (; i + 64 <= len; i += 64) {
        sha256_compress(state, data + i);
    }
    uint8_t block[64];
    size_t rem = len - i;
    memcpy(block, data + i, rem);
    block[rem] = 0x80;
    if (rem >= 56) {
        memset(block + rem + 1, 0, 64 - rem - 1);
        sha256_compress(state, block);
        memset(block, 0, 56);
    } else {
        memset(block + rem + 1, 0, 56 - rem - 1);
    }
    uint64_t bitlen = (uint64_t)len * 8;
    for (int j = 0; j < 8; j++) {
        block[56 + j] = (uint8_t)(bitlen >> (56 - 8 * j));
    }
    sha256_compress(state, block);
    for (int j = 0; j < 8; j++) {
        out[4 * j]     = (uint8_t)(state[j] >> 24);
        out[4 * j + 1] = (uint8_t)(state[j] >> 16);
        out[4 * j + 2] = (uint8_t)(state[j] >> 8);
        out[4 * j + 3] = (uint8_t)(state[j]);
    }
}

/* hash(a ++ b) for two 32-byte inputs; the sole merkleization primitive. */
LEAN_EXPORT lean_obj_res lssz_sha256_combine(b_lean_obj_arg a, b_lean_obj_arg b) {
    uint8_t buf[64];
    size_t la = lean_sarray_size(a);
    size_t lb = lean_sarray_size(b);
    /* Contract: both inputs are 32 bytes (enforced by Bytes32 on the Lean
       side). Defensive clamp keeps memory safety if ever violated. */
    if (la > 32) la = 32;
    if (lb > 32) lb = 32;
    memset(buf, 0, sizeof(buf));
    memcpy(buf, lean_sarray_cptr(a), la);
    memcpy(buf + 32, lean_sarray_cptr(b), lb);
    lean_obj_res r = lean_alloc_sarray(1, 32, 32);
    sha256(buf, 64, lean_sarray_cptr(r));
    return r;
}

/* General-purpose hash for tests (NIST CAVP validation). */
LEAN_EXPORT lean_obj_res lssz_sha256(b_lean_obj_arg data) {
    lean_obj_res r = lean_alloc_sarray(1, 32, 32);
    sha256(lean_sarray_cptr(data), lean_sarray_size(data), lean_sarray_cptr(r));
    return r;
}

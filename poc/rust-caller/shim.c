/*
 * Rust-facing C shim over the leanSSZ exported functions.
 *
 * Keeps every Lean runtime detail (object allocation, refcounts, IO world
 * initialization) on this side, so the Rust caller sees plain
 * byte-pointer + length functions -- the Verity C-8 seam shape.
 */

#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <lean/lean.h>

extern void lean_initialize_runtime_module(void);
extern lean_object *initialize_LeanSSZ_LeanSSZ(uint8_t builtin, lean_object *w);

extern uint16_t lssz_block_validate(lean_object *bs);
extern lean_object *lssz_block_reencode(lean_object *bs);
extern lean_object *lssz_block_htr(lean_object *bs);

static lean_object *mk_bytes(const uint8_t *p, size_t n) {
    lean_object *a = lean_alloc_sarray(1, n, n);
    memcpy(lean_sarray_cptr(a), p, n);
    return a;
}

int lssz_poc_init(void) {
    lean_initialize_runtime_module();
    lean_object *res = initialize_LeanSSZ_LeanSSZ(1, lean_io_mk_world());
    if (lean_io_result_is_ok(res)) {
        lean_dec_ref(res);
    } else {
        lean_io_result_show_error(res);
        lean_dec(res);
        return 1;
    }
    lean_io_mark_end_initialization();
    return 0;
}

uint16_t lssz_poc_validate(const uint8_t *in, size_t n) {
    return lssz_block_validate(mk_bytes(in, n));
}

/* Returns the re-encoded length (0 = decode error); writes at most cap bytes. */
size_t lssz_poc_reencode(const uint8_t *in, size_t n, uint8_t *out, size_t cap) {
    lean_object *r = lssz_block_reencode(mk_bytes(in, n));
    size_t m = lean_sarray_size(r);
    if (m > cap) m = cap;
    memcpy(out, lean_sarray_cptr(r), m);
    lean_dec(r);
    return m;
}

/* Returns 0 on success and fills out[32]; 1 = decode error. */
int lssz_poc_htr(const uint8_t *in, size_t n, uint8_t out[32]) {
    lean_object *r = lssz_block_htr(mk_bytes(in, n));
    if (lean_sarray_size(r) != 32) {
        lean_dec(r);
        return 1;
    }
    memcpy(out, lean_sarray_cptr(r), 32);
    lean_dec(r);
    return 0;
}

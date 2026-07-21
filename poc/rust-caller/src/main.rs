//! Rust caller PoC: consume the proven leanSSZ codec over the C ABI.
//!
//! End-to-end validation of the Verity architecture slice:
//! Lean-proven pure functions -> Lean C backend -> static lib -> C ABI ->
//! Rust runtime. The Rust side re-verifies nothing.

use std::os::raw::c_int;

extern "C" {
    fn lssz_poc_init() -> c_int;
    fn lssz_poc_validate(input: *const u8, len: usize) -> u16;
    fn lssz_poc_reencode(input: *const u8, len: usize, out: *mut u8, cap: usize) -> usize;
    fn lssz_poc_htr(input: *const u8, len: usize, out: *mut u8) -> c_int;
}

/// leanSpec devnet fixture `test_block_empty_body`: SSZ `Block` with an
/// empty body (80 zero bytes of fixed fields, offset 84, body offset 4).
fn block_empty_body() -> Vec<u8> {
    let mut v = vec![0u8; 80];
    v.extend_from_slice(&[0x54, 0, 0, 0]);
    v.extend_from_slice(&[0x04, 0, 0, 0]);
    v
}

/// Expected hash_tree_root, computed by the Lean side (`lake exe htrblock`).
const EXPECTED_HTR: &str = "ed01b1825c7b112c8b9c6e0f41c4d49e400fc120425582e533c332a6ac46082e";

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn main() {
    unsafe {
        assert_eq!(lssz_poc_init(), 0, "lean runtime init failed");

        let block = block_empty_body();

        // 1. The proven strict decoder accepts the canonical encoding.
        let status = lssz_poc_validate(block.as_ptr(), block.len());
        assert_eq!(status, 0, "validate: expected ok, got {status}");
        println!("ok   validate(canonical block) = 0");

        // 2. Decode -> re-encode is byte-identical (roundtrip, proven in Lean).
        let mut out = vec![0u8; 1024];
        let n = lssz_poc_reencode(block.as_ptr(), block.len(), out.as_mut_ptr(), out.len());
        assert_eq!(&out[..n], &block[..], "re-encode mismatch");
        println!("ok   reencode roundtrip ({n} bytes, byte-identical)");

        // 3. hash_tree_root matches the Lean-side computation.
        let mut root = [0u8; 32];
        assert_eq!(lssz_poc_htr(block.as_ptr(), block.len(), root.as_mut_ptr()), 0);
        assert_eq!(hex(&root), EXPECTED_HTR, "hash_tree_root mismatch");
        println!("ok   hash_tree_root = {}", hex(&root));

        // 4. The strict decoder rejects malformed input (truncated).
        let status = lssz_poc_validate(block.as_ptr(), block.len() - 1);
        assert_ne!(status, 0, "truncated block must be rejected");
        println!("ok   validate(truncated) = {status} (rejected)");

        // 5. Bad offset rejected.
        let mut bad = block.clone();
        bad[80] = 0x55; // first offset != fixed-part end
        let status = lssz_poc_validate(bad.as_ptr(), bad.len());
        assert_ne!(status, 0, "bad offset must be rejected");
        println!("ok   validate(bad offset) = {status} (rejected)");

        println!("all Rust-side checks passed");
    }
}

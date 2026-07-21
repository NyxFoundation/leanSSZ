use std::process::Command;

fn lean_print(arg: &str) -> String {
    let out = Command::new("lean").arg(arg).output().expect("lean not on PATH");
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

fn main() {
    let sysroot = lean_print("--print-prefix");
    let libdir = lean_print("--print-libdir");
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap();
    let lake_lib = repo.join(".lake/build/lib");

    cc::Build::new()
        .file("shim.c")
        .include(format!("{sysroot}/include"))
        .compile("lssz_shim");

    println!("cargo:rustc-link-search=native={}", lake_lib.display());
    println!("cargo:rustc-link-lib=static=LeanSSZ_LeanSSZ");
    println!("cargo:rustc-link-lib=static=leanssz_sha256");
    println!("cargo:rustc-link-search=native={libdir}");
    println!("cargo:rustc-link-lib=dylib=leanshared");
    println!("cargo:rustc-link-arg=-Wl,-rpath,{libdir}");
    println!("cargo:rerun-if-changed=shim.c");
}

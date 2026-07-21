import Lake
open Lake DSL

package LeanSSZ

@[default_target]
lean_lib LeanSSZ

lean_exe sanity where
  root := `Tests.Sanity

target sha256.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "sha256.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "sha256.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-O2", "-fPIC"] "cc" getLeanTrace

extern_lib libleanssz_sha256 pkg := do
  let libFile := pkg.staticLibDir / (nameToStaticLib "leanssz_sha256")
  let oJob ← fetch <| pkg.target ``sha256.o
  buildStaticLib libFile #[oJob]

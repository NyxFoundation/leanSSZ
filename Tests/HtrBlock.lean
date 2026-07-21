import LeanSSZ
open LeanSSZ LeanSSZ.Export

def hex (bs : ByteArray) : String :=
  String.join (bs.data.toList.map fun b =>
    let h := "0123456789abcdef".toList
    String.mk [h[(b.toNat / 16) % 16]!, h[b.toNat % 16]!])

def main : IO Unit := do
  let bytes := (List.replicate 80 (0 : UInt8)) ++ [0x54, 0, 0, 0] ++ [0x04, 0, 0, 0]
  let ba := ByteArray.mk bytes.toArray
  IO.println s!"validate: {blockValidate ba}"
  IO.println s!"htr: {hex (blockHtr ba)}"

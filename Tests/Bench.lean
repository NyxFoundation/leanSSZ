/-
Performance measurement: serialize / deserialize / hash_tree_root for
representative devnet values.

Reference context (Verity consensus-ffi-poc, measured on the same class
of machine): decode State 4.6 ms, STF+HTR 27.5 ms @ V = 4096.
-/

import LeanSSZ

open LeanSSZ LeanSSZ.Devnet

def timeIt (label : String) (iters : Nat) (act : IO Nat) : IO Unit := do
  let _ ← act  -- warmup
  let t0 ← IO.monoNanosNow
  let mut sink := 0
  for _ in [0:iters] do
    sink := sink + (← act)
  let t1 ← IO.monoNanosNow
  let per := (t1 - t0) / iters
  let shown :=
    if per ≥ 1000000 then s!"{per / 1000000}.{per / 1000 % 1000} ms"
    else if per ≥ 1000 then s!"{per / 1000}.{per % 1000 / 100} µs"
    else s!"{per} ns"
  IO.println s!"   {label}: {shown}/op  ({iters} iters, sink {sink % 2})"

def mkCheckpoint : Checkpoint := ⟨BytesN.zero 32, 12345⟩

def mkAttData : AttestationData :=
  ⟨777, mkCheckpoint, mkCheckpoint, mkCheckpoint⟩

def mkAggAtt (bits : Nat) : AggregatedAttestation :=
  ⟨⟨List.replicate (min bits 4096) true, by
      simp [List.length_replicate]; omega⟩,
   mkAttData⟩

def mkBody (atts bits : Nat) (h : atts ≤ 4096) : BlockBody :=
  ⟨⟨List.replicate atts (mkAggAtt bits), by
      simpa [List.length_replicate] using h⟩⟩

def mkBlock (atts bits : Nat) (h : atts ≤ 4096) : Block :=
  ⟨42, 7, BytesN.zero 32, BytesN.zero 32, mkBody atts bits h⟩

def mkValidator : Validator := ⟨BytesN.zero 52, BytesN.zero 52, 0⟩

def mkState (v hist : Nat) (hv : v ≤ 4096) (hh : hist ≤ 262144) : State :=
  ⟨⟨1700000000⟩, 999,
   ⟨999, 3, BytesN.zero 32, BytesN.zero 32, BytesN.zero 32⟩,
   mkCheckpoint, mkCheckpoint,
   ⟨List.replicate hist (BytesN.zero 32), by simpa [List.length_replicate] using hh⟩,
   ⟨List.replicate hist true, by
      simp [List.length_replicate]
      omega⟩,
   ⟨List.replicate v mkValidator, by simpa [List.length_replicate] using hv⟩,
   ⟨List.replicate hist (BytesN.zero 32), by simpa [List.length_replicate] using hh⟩,
   ⟨List.replicate (hist * 8) true, by
      simp [List.length_replicate]
      omega⟩⟩

def bench {T : Type} [SSZCodec T] [HasHTR T]
    (label : String) (iters : Nat) (v : T) : IO Unit := do
  let vr ← IO.mkRef v
  let br ← IO.mkRef (serialize v)
  let bytes := serialize v
  IO.println s!"-- {label} ({bytes.size} bytes serialized)"
  timeIt "serialize" iters do
    let v ← vr.get
    pure (serialize v).size
  timeIt "deserialize" iters do
    let b ← br.get
    pure (match deserialize (T := T) b with
      | .ok _ => 1
      | .error _ => 0)
  timeIt "hash_tree_root" iters do
    let v ← vr.get
    pure (htr v).val.size

def main : IO Unit := do
  IO.println "leanSSZ performance (list-based v1, uncached merkleization)"
  bench "Checkpoint" 10000 mkCheckpoint
  bench "AttestationData" 5000 mkAttData
  bench "Block (empty body)" 2000 (mkBlock 0 0 (by omega))
  bench "AggregatedAttestation (256 bits)" 2000 (mkAggAtt 256)
  bench "Block (64 atts × 256 bits)" 100 (mkBlock 64 256 (by omega))
  bench "Block (512 atts × 4096 bits)" 5 (mkBlock 512 4096 (by omega))
  bench "State (V=256, hist=256)" 50 (mkState 256 256 (by omega) (by omega))
  bench "State (V=4096, hist=1024)" 5 (mkState 4096 1024 (by omega) (by omega))

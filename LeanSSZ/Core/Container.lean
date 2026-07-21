/-
SSZ container byte-level machinery: the fixed part / offset table / tail
layout, proven once.

Mirrors `src/lean_spec/spec/ssz/container.py` in leanSpec:
  - the fixed part holds, per field in declaration order, either the
    field's bytes (fixed-size field) or a 4-byte little-endian offset
    (variable-size field);
  - variable payloads land after the fixed part, in field order;
  - decode checks: first offset equals the fixed-part length, offsets are
    monotone, the final payload is closed by the scope.

Design: a container encoder turns the value into `List Part`, where a
`Part` is `(some width, bytes)` for a fixed field or `(none, bytes)` for a
variable one. `assemble` lays parts out per the SSZ rules; `disassemble`
recovers the per-field byte slices from a schema (`List (Option Nat)`).
The central theorem `disassemble_assemble` is proven once, so each
concrete container's roundtrip reduces to chaining its field roundtrips.

Offsets are 4-byte, so `disassemble_assemble` carries the (real-world SSZ)
hypothesis that the encoding fits below `2 ^ 32` bytes; concrete
containers discharge it from their schema bounds.
-/

import LeanSSZ.Core.Uint

namespace LeanSSZ
namespace Container

/-- One encoded field: `(some w, bytes)` fixed of width `w` (with
`bytes.length = w`), `(none, bytes)` variable. -/
abbrev Part := Option Nat × List UInt8

/-- Width a field occupies in the fixed part: its own width, or 4 for an
offset slot. -/
def slotLen : Option Nat → Nat
  | some w => w
  | none => 4

/-- Total width of the fixed part. -/
def fixedLen (schema : List (Option Nat)) : Nat :=
  (schema.map slotLen).sum

/-- Total length of the variable payloads. -/
def varTotal : List Part → Nat
  | [] => 0
  | (some _, _) :: rest => varTotal rest
  | (none, b) :: rest => b.length + varTotal rest

/-! ## Encoding -/

/-- The fixed part: field bytes or 4-byte offsets; `off` is the running
offset of the next variable payload. -/
def encFixed : List Part → Nat → List UInt8
  | [], _ => []
  | (some _, bytes) :: rest, off => bytes ++ encFixed rest off
  | (none, bytes) :: rest, off =>
    LE.encodeNat off 4 ++ encFixed rest (off + bytes.length)

/-- The concatenated variable payloads, in field order. -/
def encTails : List Part → List UInt8
  | [] => []
  | (some _, _) :: rest => encTails rest
  | (none, bytes) :: rest => bytes ++ encTails rest

/-- Full container layout. -/
def assemble (parts : List Part) : List UInt8 :=
  encFixed parts (fixedLen (parts.map Prod.fst)) ++ encTails parts

/-- Well-formed parts: declared fixed widths match the byte lengths. -/
def WFParts (parts : List Part) : Prop :=
  ∀ p ∈ parts, ∀ w, p.1 = some w → p.2.length = w

theorem wfparts_cons {p : Part} {rest : List Part} (h : WFParts (p :: rest)) :
    WFParts rest :=
  fun q hq => h q (List.mem_cons_of_mem _ hq)

/-! ## Length lemmas -/

private theorem take_len_append (as bs : List UInt8) :
    (as ++ bs).take as.length = as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

private theorem drop_len_append (as bs : List UInt8) :
    (as ++ bs).drop as.length = bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

private theorem take_append_of_len {as bs : List UInt8} {n : Nat}
    (h : as.length = n) : (as ++ bs).take n = as := by
  subst h; exact take_len_append ..

private theorem drop_append_of_len {as bs : List UInt8} {n : Nat}
    (h : as.length = n) : (as ++ bs).drop n = bs := by
  subst h; exact drop_len_append ..

theorem encTails_length (parts : List Part) :
    (encTails parts).length = varTotal parts := by
  induction parts with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨o, bytes⟩ := p
    cases o with
    | some w =>
      show (encTails rest).length = varTotal rest
      exact ih
    | none =>
      show (bytes ++ encTails rest).length = bytes.length + varTotal rest
      rw [List.length_append, ih]

theorem encFixed_length (parts : List Part) (off : Nat) (hwf : WFParts parts) :
    (encFixed parts off).length = fixedLen (parts.map Prod.fst) := by
  induction parts generalizing off with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨o, bytes⟩ := p
    cases o with
    | some w =>
      have hb : bytes.length = w := hwf (some w, bytes) (List.mem_cons_self ..) w rfl
      show (bytes ++ encFixed rest off).length = fixedLen (some w :: rest.map Prod.fst)
      rw [List.length_append, ih off (wfparts_cons hwf), hb]
      simp [fixedLen, slotLen]
    | none =>
      show (LE.encodeNat off 4 ++ encFixed rest (off + bytes.length)).length
          = fixedLen (none :: rest.map Prod.fst)
      rw [List.length_append, LE.encodeNat_length,
          ih (off + bytes.length) (wfparts_cons hwf)]
      simp [fixedLen, slotLen]

theorem assemble_length (parts : List Part) (hwf : WFParts parts) :
    (assemble parts).length
      = fixedLen (parts.map Prod.fst) + varTotal parts := by
  rw [assemble, List.length_append, encFixed_length parts _ hwf, encTails_length]

/-! ## Decoding -/

/-- Phase 1: walk the schema over the fixed part, returning field bytes
(`inl`) or read offsets (`inr`), plus the unconsumed remainder. -/
def phase1 : List (Option Nat) → List UInt8 →
    Except SSZError (List (List UInt8 ⊕ Nat) × List UInt8)
  | [], bs => .ok ([], bs)
  | some w :: sch, bs =>
    if w ≤ bs.length then
      match phase1 sch (bs.drop w) with
      | .ok (items, rest) => .ok (.inl (bs.take w) :: items, rest)
      | .error e => .error e
    else .error (.invalidLength w bs.length)
  | none :: sch, bs =>
    if 4 ≤ bs.length then
      match phase1 sch (bs.drop 4) with
      | .ok (items, rest) => .ok (.inr (LE.decodeNat (bs.take 4)) :: items, rest)
      | .error e => .error e
    else .error (.invalidLength 4 bs.length)

def offsetsOf : List (List UInt8 ⊕ Nat) → List Nat
  | [] => []
  | .inl _ :: rest => offsetsOf rest
  | .inr o :: rest => o :: offsetsOf rest

/-- Slice the variable payloads out of the full input by consecutive
offset windows; the scope closes the final window. -/
def sliceVars : List Nat → Nat → List UInt8 → Except SSZError (List (List UInt8))
  | [], _, _ => .ok []
  | [o], scope, bs =>
    if o ≤ scope then .ok [(bs.drop o).take (scope - o)]
    else .error (.invalidOffset "final offset exceeds scope")
  | o₁ :: o₂ :: rest, scope, bs =>
    if o₁ ≤ o₂ then
      match sliceVars (o₂ :: rest) scope bs with
      | .ok ss => .ok ((bs.drop o₁).take (o₂ - o₁) :: ss)
      | .error e => .error e
    else .error (.invalidOffset "offsets not monotonically increasing")

/-- Put fixed-field bytes and sliced variable payloads back in field order. -/
def mergeSlices : List (List UInt8 ⊕ Nat) → List (List UInt8) →
    Option (List (List UInt8))
  | [], [] => some []
  | [], _ :: _ => none
  | .inl b :: items, ss => (mergeSlices items ss).map (b :: ·)
  | .inr _ :: items, s :: ss => (mergeSlices items ss).map (s :: ·)
  | .inr _ :: _, [] => none

/-- Recover the per-field byte slices of a container encoding. -/
def disassemble (schema : List (Option Nat)) (bs : List UInt8) :
    Except SSZError (List (List UInt8)) :=
  match phase1 schema bs with
  | .error e => .error e
  | .ok (items, _) =>
    match offsetsOf items with
    | [] =>
      if bs.length = fixedLen schema then
        match mergeSlices items [] with
        | some fields => .ok fields
        | none => .error (.invalidValue "container: internal merge failure")
      else .error (.invalidLength (fixedLen schema) bs.length)
    | o :: offs =>
      if o = fixedLen schema then
        match sliceVars (o :: offs) bs.length bs with
        | .error e => .error e
        | .ok ss =>
          match mergeSlices items ss with
          | some fields => .ok fields
          | none => .error (.invalidValue "container: internal merge failure")
      else .error (.invalidOffset "first offset must equal fixed-part length")

/-! ## Roundtrip: specification functions -/

/-- What phase 1 recovers from a well-formed encoding. -/
def itemsOf : List Part → Nat → List (List UInt8 ⊕ Nat)
  | [], _ => []
  | (some _, b) :: rest, off => .inl b :: itemsOf rest off
  | (none, b) :: rest, off => .inr off :: itemsOf rest (off + b.length)

/-- The offset table an encoding carries. -/
def cumOffs : List Part → Nat → List Nat
  | [], _ => []
  | (some _, _) :: rest, off => cumOffs rest off
  | (none, b) :: rest, off => off :: cumOffs rest (off + b.length)

/-- The variable payloads, in order. -/
def varBytes : List Part → List (List UInt8)
  | [] => []
  | (some _, _) :: rest => varBytes rest
  | (none, b) :: rest => b :: varBytes rest

/-! ## Roundtrip: lemmas -/

theorem phase1_encFixed (parts : List Part) (off : Nat) (suffix : List UInt8)
    (hwf : WFParts parts) (hoff : off + varTotal parts < 2 ^ 32) :
    phase1 (parts.map Prod.fst) (encFixed parts off ++ suffix)
      = .ok (itemsOf parts off, suffix) := by
  induction parts generalizing off suffix with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨o, bytes⟩ := p
    cases o with
    | some w =>
      have hb : bytes.length = w := hwf (some w, bytes) (List.mem_cons_self ..) w rfl
      show phase1 (some w :: rest.map Prod.fst)
          ((bytes ++ encFixed rest off) ++ suffix)
          = .ok (.inl bytes :: itemsOf rest off, suffix)
      rw [List.append_assoc]
      simp only [phase1]
      rw [if_pos (by rw [List.length_append]; omega)]
      rw [take_append_of_len hb, drop_append_of_len hb]
      rw [ih off suffix (wfparts_cons hwf) (by simpa [varTotal] using hoff)]
    | none =>
      have hvt : off + (bytes.length + varTotal rest) < 2 ^ 32 := by
        simpa [varTotal] using hoff
      show phase1 (none :: rest.map Prod.fst)
          ((LE.encodeNat off 4 ++ encFixed rest (off + bytes.length)) ++ suffix)
          = .ok (.inr off :: itemsOf rest (off + bytes.length), suffix)
      rw [List.append_assoc]
      simp only [phase1]
      rw [if_pos (by rw [List.length_append, LE.encodeNat_length]; omega)]
      rw [take_append_of_len (LE.encodeNat_length ..),
          drop_append_of_len (LE.encodeNat_length ..)]
      rw [ih (off + bytes.length) suffix (wfparts_cons hwf) (by omega)]
      have hdec : LE.decodeNat (LE.encodeNat off 4) = off := by
        rw [LE.decodeNat_encodeNat]
        have h32 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
        exact Nat.mod_eq_of_lt (by omega)
      rw [hdec]

theorem offsetsOf_itemsOf (parts : List Part) (off : Nat) :
    offsetsOf (itemsOf parts off) = cumOffs parts off := by
  induction parts generalizing off with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨o, b⟩ := p
    cases o with
    | some w =>
      show offsetsOf (itemsOf rest off) = cumOffs rest off
      exact ih off
    | none =>
      show off :: offsetsOf (itemsOf rest (off + b.length))
          = off :: cumOffs rest (off + b.length)
      rw [ih]

theorem cumOffs_head (parts : List Part) (off o : Nat) (t : List Nat)
    (h : cumOffs parts off = o :: t) : o = off := by
  induction parts generalizing off with
  | nil => simp [cumOffs] at h
  | cons p rest ih =>
    obtain ⟨oo, b⟩ := p
    cases oo with
    | some w => exact ih off (by simpa [cumOffs] using h)
    | none =>
      have h' : off :: cumOffs rest (off + b.length) = o :: t := by
        simpa [cumOffs] using h
      injection h' with h1 _
      exact h1.symm

theorem cumOffs_nil_encTails (parts : List Part) (off : Nat)
    (h : cumOffs parts off = []) : encTails parts = [] := by
  induction parts generalizing off with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨o, b⟩ := p
    cases o with
    | some w =>
      show encTails rest = []
      exact ih off (by simpa [cumOffs] using h)
    | none => simp [cumOffs] at h

theorem cumOffs_nil_varBytes (parts : List Part) (off : Nat)
    (h : cumOffs parts off = []) : varBytes parts = [] := by
  induction parts generalizing off with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨o, b⟩ := p
    cases o with
    | some w =>
      show varBytes rest = []
      exact ih off (by simpa [cumOffs] using h)
    | none => simp [cumOffs] at h

theorem sliceVars_encTails (parts : List Part) (P : List UInt8) :
    sliceVars (cumOffs parts P.length) (P ++ encTails parts).length
      (P ++ encTails parts) = .ok (varBytes parts) := by
  induction parts generalizing P with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨o, b⟩ := p
    cases o with
    | some w =>
      show sliceVars (cumOffs rest P.length) (P ++ encTails rest).length
          (P ++ encTails rest) = .ok (varBytes rest)
      exact ih P
    | none =>
      show sliceVars (P.length :: cumOffs rest (P.length + b.length))
          (P ++ (b ++ encTails rest)).length (P ++ (b ++ encTails rest))
          = .ok (b :: varBytes rest)
      cases hc : cumOffs rest (P.length + b.length) with
      | nil =>
        have htails : encTails rest = [] := cumOffs_nil_encTails rest _ hc
        have hvb : varBytes rest = [] := cumOffs_nil_varBytes rest _ hc
        rw [htails, hvb]
        simp only [sliceVars]
        have hlen : (P ++ (b ++ [])).length = P.length + b.length := by simp
        rw [if_pos (by rw [hlen]; omega)]
        rw [hlen]
        have hdrop : (P ++ (b ++ [])).drop P.length = b := by
          rw [drop_len_append]; simp
        rw [hdrop]
        have harith : P.length + b.length - P.length = b.length := by omega
        rw [harith, List.take_length]
      | cons o₂ t =>
        have ho₂ : o₂ = P.length + b.length := cumOffs_head rest _ o₂ t hc
        subst ho₂
        have hnext : sliceVars ((P.length + b.length) :: t)
            (P ++ (b ++ encTails rest)).length (P ++ (b ++ encTails rest))
            = .ok (varBytes rest) := by
          have hc' : cumOffs rest ((P ++ b).length) = (P.length + b.length) :: t := by
            rw [List.length_append]; exact hc
          have h := ih (P ++ b)
          rw [hc'] at h
          rw [List.append_assoc] at h
          exact h
        simp only [sliceVars]
        rw [if_pos (by omega)]
        rw [hnext]
        have hdrop : (P ++ (b ++ encTails rest)).drop P.length = b ++ encTails rest :=
          drop_len_append ..
        rw [hdrop]
        have harith : P.length + b.length - P.length = b.length := by omega
        rw [harith, take_len_append]

theorem mergeSlices_itemsOf (parts : List Part) (off : Nat) :
    mergeSlices (itemsOf parts off) (varBytes parts)
      = some (parts.map Prod.snd) := by
  induction parts generalizing off with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨o, b⟩ := p
    cases o with
    | some w =>
      show (mergeSlices (itemsOf rest off) (varBytes rest)).map (b :: ·)
          = some (b :: rest.map Prod.snd)
      rw [ih off]
      rfl
    | none =>
      show (mergeSlices (itemsOf rest (off + b.length)) (varBytes rest)).map (b :: ·)
          = some (b :: rest.map Prod.snd)
      rw [ih (off + b.length)]
      rfl

/-! ## The central theorem -/

/-- Disassembling a well-formed assembly recovers every field's bytes.
The `2 ^ 32` bound is the SSZ offset-width constraint; concrete containers
discharge it from their schema bounds. -/
theorem disassemble_assemble (parts : List Part) (hwf : WFParts parts)
    (hsize : fixedLen (parts.map Prod.fst) + varTotal parts < 2 ^ 32) :
    disassemble (parts.map Prod.fst) (assemble parts)
      = .ok (parts.map Prod.snd) := by
  have hp1 := phase1_encFixed parts (fixedLen (parts.map Prod.fst))
    (encTails parts) hwf hsize
  show disassemble (parts.map Prod.fst)
      (encFixed parts (fixedLen (parts.map Prod.fst)) ++ encTails parts)
      = .ok (parts.map Prod.snd)
  simp only [disassemble, hp1]
  rw [offsetsOf_itemsOf]
  cases hc : cumOffs parts (fixedLen (parts.map Prod.fst)) with
  | nil =>
    have htails : encTails parts = [] := cumOffs_nil_encTails parts _ hc
    have hvb : varBytes parts = [] := cumOffs_nil_varBytes parts _ hc
    rw [if_pos (by
      rw [List.length_append, encFixed_length parts _ hwf, htails]
      simp)]
    have hm := mergeSlices_itemsOf parts (fixedLen (parts.map Prod.fst))
    rw [hvb] at hm
    rw [hm]
  | cons o offs =>
    have ho : o = fixedLen (parts.map Prod.fst) := cumOffs_head parts _ o offs hc
    subst ho
    have hs := sliceVars_encTails parts
      (encFixed parts (fixedLen (parts.map Prod.fst)))
    rw [encFixed_length parts _ hwf] at hs
    rw [hc] at hs
    simp only [hs, mergeSlices_itemsOf parts]
    simp

end Container
end LeanSSZ

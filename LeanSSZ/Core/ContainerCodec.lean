/-
Typed helpers for defining concrete SSZ containers on top of the proven
byte-level machinery (`Core/Container.lean`), plus the SSZList codec for
VARIABLE-size elements (an offset-table list is a container whose fields
are all variable).

A concrete container instance provides:
  - `enc  := Container.assemble [part f₁, …, part fₙ]` using `fixedPart` /
    `varPart` per field;
  - `dec` via `Container.disassemble schema bs` followed by field decodes;
  - a roundtrip proof that is a mechanical chain: `disassemble_assemble`
    (with `WFParts` from the lemmas below and the `2 ^ 32` bound from the
    schema arithmetic) then `dec_enc` per field.
-/

import LeanSSZ.Core.Container
import LeanSSZ.Core.List

namespace LeanSSZ
namespace Container

/-- A fixed-size field's part: declared width is the type's width. -/
def fixedPart {T : Type} [SSZCodec T] [SSZFixed T] (x : T) : Part :=
  (some (SSZFixed.size T), enc x)

/-- A variable-size field's part. -/
def varPart {T : Type} [SSZCodec T] (x : T) : Part :=
  (none, enc x)

theorem wfparts_nil : WFParts [] := fun _ hp => absurd hp (List.not_mem_nil)

theorem wfparts_cons_fixed {T : Type} [SSZCodec T] [SSZFixed T] (x : T)
    {rest : List Part} (h : WFParts rest) : WFParts (fixedPart x :: rest) := by
  intro p hp w hw
  rcases List.mem_cons.mp hp with rfl | hmem
  · have hww : SSZFixed.size T = w := Option.some.inj hw
    show (enc x).length = w
    rw [SSZFixed.enc_size x, hww]
  · exact h p hmem w hw

theorem wfparts_cons_var {T : Type} [SSZCodec T] (x : T)
    {rest : List Part} (h : WFParts rest) : WFParts (varPart x :: rest) := by
  intro p hp w hw
  rcases List.mem_cons.mp hp with rfl | hmem
  · exact absurd hw (by simp [varPart])
  · exact h p hmem w hw

@[simp] theorem fixedPart_fst {T : Type} [SSZCodec T] [SSZFixed T] (x : T) :
    (fixedPart x).1 = some (SSZFixed.size T) := rfl

@[simp] theorem fixedPart_snd {T : Type} [SSZCodec T] [SSZFixed T] (x : T) :
    (fixedPart x).2 = enc x := rfl

@[simp] theorem varPart_fst {T : Type} [SSZCodec T] (x : T) :
    (varPart x).1 = none := rfl

@[simp] theorem varPart_snd {T : Type} [SSZCodec T] (x : T) :
    (varPart x).2 = enc x := rfl

end Container

/-- Offset arithmetic sanity for a variable-element list: the worst-case
encoding stays below the 4-byte offset horizon. Concrete instantiations
discharge it by `decide` / `omega` on their literals. -/
class SSZOffsetsFit (T : Type) [SSZCodec T] (limit : Nat) : Prop where
  fits : limit * (4 + SSZCodec.maxSize (T := T)) < 2 ^ 32

/-! ## SSZList of variable-size elements -/

namespace SSZList

variable {T : Type} {limit : Nat} [SSZCodec T]

/-- Decode every slice with the element decoder. -/
def decEach : List (List UInt8) → Except SSZError (List T)
  | [] => .ok []
  | s :: ss =>
    match dec (T := T) s, decEach ss with
    | .ok x, .ok xs => .ok (x :: xs)
    | .error e, _ => .error e
    | _, .error e => .error e

theorem decEach_map_enc [LawfulSSZ T] (xs : List T) :
    decEach (T := T) (xs.map enc) = .ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, decEach, dec_enc x, ih]

/-- Variable-size-element list encoding: offset table + bodies. -/
def encVL (l : SSZList T limit) : List UInt8 :=
  Container.assemble (l.data.map Container.varPart)

/-- Variable-size-element list decoding: element count from the first
offset, then container disassembly. The empty list is zero bytes. -/
def decVL (bs : List UInt8) : Except SSZError (SSZList T limit) :=
  if bs.length = 0 then
    .ok ⟨[], Nat.zero_le _⟩
  else if 4 ≤ bs.length then
    if LE.decodeNat (bs.take 4) % 4 = 0 then
      if LE.decodeNat (bs.take 4) / 4 ≤ limit then
        match Container.disassemble
            (List.replicate (LE.decodeNat (bs.take 4) / 4) none) bs with
        | .error e => .error e
        | .ok slices =>
          match decEach (T := T) slices with
          | .error e => .error e
          | .ok xs =>
            if hx : xs.length ≤ limit then .ok ⟨xs, hx⟩
            else .error (.invalidValue "list element count over limit")
      else .error (.invalidValue "list element count over limit")
    else .error (.invalidOffset "first offset not a multiple of 4")
  else .error (.invalidLength 4 bs.length)

theorem map_varPart_fst (xs : List T) :
    (xs.map Container.varPart).map Prod.fst = List.replicate xs.length none := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp [ih, List.replicate_succ]

theorem map_varPart_snd (xs : List T) :
    (xs.map Container.varPart).map Prod.snd = xs.map enc := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp [ih]

theorem wfparts_map_varPart (xs : List T) :
    Container.WFParts (xs.map Container.varPart) := by
  intro p hp w hw
  rcases List.mem_map.mp hp with ⟨x, _, rfl⟩
  exact absurd hw (by simp [Container.varPart])

theorem fixedLen_replicate_none (n : Nat) :
    Container.fixedLen (List.replicate n none) = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Container.fixedLen (none :: List.replicate n none) = 4 * (n + 1)
    show (List.map Container.slotLen (none :: List.replicate n none)).sum = _
    rw [List.map_cons, List.sum_cons]
    have h : (List.map Container.slotLen (List.replicate n none)).sum = 4 * n := ih
    rw [h]
    show 4 + 4 * n = 4 * (n + 1)
    omega

theorem varTotal_le [LawfulSSZ T] (xs : List T) :
    Container.varTotal (xs.map Container.varPart)
      ≤ xs.length * SSZCodec.maxSize (T := T) := by
  induction xs with
  | nil => simp [Container.varTotal]
  | cons x rest ih =>
    show (enc x).length + Container.varTotal (rest.map Container.varPart)
        ≤ (rest.length + 1) * SSZCodec.maxSize (T := T)
    have hx := enc_size_le x
    rw [Nat.succ_mul]
    omega

theorem encVL_length_le [LawfulSSZ T] (l : SSZList T limit) :
    (encVL l).length ≤ limit * (4 + SSZCodec.maxSize (T := T)) := by
  rw [encVL, Container.assemble_length _ (wfparts_map_varPart _),
      map_varPart_fst, fixedLen_replicate_none]
  have h1 := varTotal_le (T := T) l.data
  have h2 : l.data.length ≤ limit := l.le_limit
  have h3 : l.data.length * SSZCodec.maxSize (T := T)
      ≤ limit * SSZCodec.maxSize (T := T) := Nat.mul_le_mul_right _ h2
  have h4 : limit * (4 + SSZCodec.maxSize (T := T))
      = limit * 4 + limit * SSZCodec.maxSize (T := T) := Nat.mul_add ..
  omega

theorem decVL_encVL [LawfulSSZ T] [fits : SSZOffsetsFit T limit]
    (l : SSZList T limit) : decVL (encVL l) = .ok l := by
  obtain ⟨xs, hle⟩ := l
  cases xs with
  | nil => rfl
  | cons x rest =>
    -- abbreviations
    have hwf := wfparts_map_varPart (x :: rest)
    have hF : Container.fixedLen (((x :: rest).map Container.varPart).map Prod.fst)
        = 4 * (x :: rest).length := by
      rw [map_varPart_fst, fixedLen_replicate_none]
    -- global size bound
    have hmax : (encVL (limit := limit) ⟨x :: rest, hle⟩).length
        ≤ limit * (4 + SSZCodec.maxSize (T := T)) := encVL_length_le _
    have hlen : (encVL (limit := limit) ⟨x :: rest, hle⟩).length
        = 4 * (x :: rest).length
          + Container.varTotal ((x :: rest).map Container.varPart) := by
      rw [encVL, Container.assemble_length _ hwf, hF]
    have hbound : Container.fixedLen (((x :: rest).map Container.varPart).map Prod.fst)
        + Container.varTotal ((x :: rest).map Container.varPart) < 2 ^ 32 := by
      rw [hF]
      have := fits.fits
      omega
    have hasm := Container.disassemble_assemble
      ((x :: rest).map Container.varPart) hwf hbound
    -- the first four bytes are the offset 4 * n
    have htake4 : (encVL (limit := limit) ⟨x :: rest, hle⟩).take 4
        = LE.encodeNat (4 * (x :: rest).length) 4 := by
      show ((LE.encodeNat
            (Container.fixedLen (((x :: rest).map Container.varPart).map Prod.fst)) 4
          ++ Container.encFixed (rest.map Container.varPart) _)
          ++ Container.encTails ((x :: rest).map Container.varPart)).take 4 = _
      rw [List.append_assoc, Container.take_append_of_len (LE.encodeNat_length ..), hF]
    have hoff : LE.decodeNat ((encVL (limit := limit) ⟨x :: rest, hle⟩).take 4)
        = 4 * (x :: rest).length := by
      rw [htake4, LE.decodeNat_encodeNat]
      have h32 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
      have := fits.fits
      have hn4 : 4 * (x :: rest).length
          ≤ limit * (4 + SSZCodec.maxSize (T := T)) := by omega
      exact Nat.mod_eq_of_lt (by omega)
    -- walk the decoder
    unfold decVL
    rw [if_neg (by rw [hlen]; simp only [List.length_cons]; omega)]
    rw [if_pos (by rw [hlen]; simp only [List.length_cons]; omega)]
    simp only [hoff]
    rw [if_pos (by omega)]
    rw [if_pos (by
      have : 4 * (x :: rest).length / 4 = (x :: rest).length := by omega
      rw [this]; exact hle)]
    have hdiv : 4 * (x :: rest).length / 4 = (x :: rest).length := by omega
    rw [hdiv]
    rw [show (List.replicate (x :: rest).length (none : Option Nat))
        = ((x :: rest).map Container.varPart).map Prod.fst
        from (map_varPart_fst _).symm]
    rw [show encVL (limit := limit) ⟨x :: rest, hle⟩
        = Container.assemble ((x :: rest).map Container.varPart) from rfl]
    simp only [hasm, map_varPart_snd, decEach_map_enc]
    rw [dif_pos hle]

end SSZList

/-- Codec for lists of VARIABLE-size elements (offset-table layout).
Lower priority than the packed fixed-element codec, so fixed-size element
types keep the packed layout. -/
instance (priority := 500) instSSZCodecListVar {T : Type} {limit : Nat}
    [SSZCodec T] : SSZCodec (SSZList T limit) where
  enc := SSZList.encVL
  dec := SSZList.decVL
  isFixedSize := false
  maxSize := limit * (4 + SSZCodec.maxSize (T := T))

instance (priority := 500) instLawfulSSZListVar {T : Type} {limit : Nat}
    [SSZCodec T] [LawfulSSZ T] [SSZOffsetsFit T limit] :
    LawfulSSZ (SSZList T limit) where
  dec_enc := SSZList.decVL_encVL
  enc_size_le := SSZList.encVL_length_le

end LeanSSZ

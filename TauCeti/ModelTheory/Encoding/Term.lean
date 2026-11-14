/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Primrec.List
public import Mathlib.ModelTheory.Encoding
public import TauCeti.ModelTheory.Encoding.Symbols

/-!
# Mathlib's encoding of first-order terms is primitive recursive

Mathlib spells a term as its list of variables and function symbols in Polish notation
(`FirstOrder.Language.Term.listEncode`), reads lists back with
`FirstOrder.Language.Term.listDecode`, and encodes terms by the codes of their spellings. This
file shows that this encoding is primitive recursive when the variables and the function symbols
are primitively encoded and the arity of a function symbol is primitive recursive
(`FirstOrder.Language.PrimrecFunctionArity`).

## Main results

* `FirstOrder.Language.Term.instPrimcodable`: the `Primcodable` structure on `L.Term α`. Its
  encoding and decoding functions are those of Mathlib's `Encodable (L.Term α)` instance; only
  the proof that they are primitive recursive is new.
* `FirstOrder.Language.Term.primrec_listEncode`, `FirstOrder.Language.Term.primrec_listDecode`:
  spelling a term, and reading a list of symbols as a list of terms with `listDecode`, are
  primitive recursive.
* `FirstOrder.Language.Term.primrec_var`, `FirstOrder.Language.Term.primrec_func`: forming a
  variable term and applying a function symbol to a tuple of terms are primitive recursive.
* `FirstOrder.Language.Term.primrecPred_exists_listEncode_eq`: the lists that spell a term form
  a primitive recursive set. The decoder of terms (`Encodable.decode`) returns the first term
  that `listDecode` reads off the coded list, so it also accepts lists that spell no term, such
  as the spelling of a term followed by further symbols. A list spells a term exactly when
  `listDecode` reads it as a single term whose spelling is the list,
  `FirstOrder.Language.Term.exists_listEncode_eq_iff`. For natural-number codes, the set of
  codes of terms is primitive recursive by Mathlib's `Primcodable.mem_range_encode`.

The decoder is shown primitive recursive by running it on spellings: a variable pushes its
one-letter spelling on a stack, and a function symbol of arity `n` replaces the top `n` spellings
by the symbol followed by their concatenation.
-/

public section

universe u v w

namespace FirstOrder.Language.Term

open Encodable

variable {L : Language.{u, v}} {α : Type w}

/-- The spelling of a term is not empty. -/
@[simp]
theorem listEncode_ne_nil (t : L.Term α) : t.listEncode ≠ [] := by
  cases t <;> simp [listEncode]

/-- Decoding the spelling of a term gives back that term and nothing else. -/
@[simp]
theorem listDecode_listEncode (t : L.Term α) : listDecode t.listEncode = [t] := by
  simpa using listDecode_encode_list [t]

/-- A list spells a term exactly when `listDecode` reads it as a single term whose spelling is
the list. -/
theorem exists_listEncode_eq_iff {l : List (α ⊕ Σ i, L.Functions i)} :
    (∃ t : L.Term α, t.listEncode = l) ↔ (listDecode l).map listEncode = [l] := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨t, rfl⟩
    simp
  · obtain ⟨t, -, ht⟩ := List.map_eq_singleton_iff.1 h
    exact ⟨t, ht⟩

/-- A function symbol of positive arity without arguments decodes to no term. -/
@[simp]
theorem listDecode_singleton_inr_add_one {n : ℕ} (f : L.Functions (n + 1)) :
    listDecode [Sum.inr ⟨n + 1, f⟩] = ([] : List (L.Term α)) := by
  simp [listDecode]

/-- A function symbol of positive arity without arguments does not spell a term. -/
@[simp]
theorem listEncode_ne_singleton_inr_add_one {n : ℕ} (f : L.Functions (n + 1)) (t : L.Term α) :
    t.listEncode ≠ [Sum.inr ⟨n + 1, f⟩] := fun h => by
  simpa [h] using listDecode_listEncode t

/-- Spelling the terms `l[0], …, l[n - 1]` of a list one after the other. -/
private theorem flatMap_finRange_listEncode_getElem (l : List (L.Term α)) {n : ℕ}
    (h : n ≤ l.length) :
    ((List.finRange n).flatMap fun i => (l[i.1]'(i.2.trans_le h)).listEncode) =
      ((l.map listEncode).take n).flatten := by
  have : (List.finRange n).map (fun i => l[i.1]'(i.2.trans_le h)) = l.take n :=
    List.ext_getElem (by simp [h]) (by simp)
  rw [← List.map_take, ← this, List.map_map, List.flatMap_def]
  rfl

/-- One step of decoding on spellings: a variable pushes its spelling, and a function symbol of
arity `n` replaces the first `n` spellings by the spelling of its application to them. The whole
stack is discarded when there are fewer than `n` spellings. -/
private def decodeStep (x : α ⊕ Σ i, L.Functions i)
    (st : List (List (α ⊕ Σ i, L.Functions i))) : List (List (α ⊕ Σ i, L.Functions i)) :=
  x.elim (fun a => [Sum.inl a] :: st) fun F =>
    if F.1 ≤ st.length then (Sum.inr F :: (st.take F.1).flatten) :: st.drop F.1 else []

/-- The spellings of the terms decoded from a list are computed by `decodeStep`. -/
private theorem map_listEncode_listDecode (l : List (α ⊕ Σ i, L.Functions i)) :
    (listDecode l).map listEncode = l.foldr decodeStep [] := by
  induction l with
  | nil => simp [listDecode]
  | cons x l ih =>
    rcases x with a | ⟨n, f⟩
    · simp [listDecode, listEncode, decodeStep, ← ih]
    · by_cases h : n ≤ (listDecode l).length
      · simpa [listDecode, listEncode, decodeStep, ← ih, h, List.map_drop] using
          flatMap_finRange_listEncode_getElem _ h
      · simp [listDecode, decodeStep, ← ih, h]

section Encodable

variable [Encodable α] [Encodable (Σ i, L.Functions i)]

/-- The code of a term is the code of its spelling. -/
theorem encode_eq_encode_listEncode (t : L.Term α) : encode t = encode t.listEncode :=
  -- Mathlib's instance is `Encodable.ofLeftInjection listEncode _ _`, which encodes by spelling.
  (rfl)

/-- The code of a variable term is the code of the one-letter list. -/
theorem encode_var (a : α) :
    encode (var a : L.Term α) = encode ([Sum.inl a] : List (α ⊕ Σ i, L.Functions i)) :=
  encode_eq_encode_listEncode _

/-- Mathlib's decoder of terms reads the first term of the list coded by a number. -/
theorem decode_eq_decode_bind_listDecode (n : ℕ) :
    decode (α := L.Term α) n = (decode n).bind fun l => (listDecode l).head? := by
  have key (l : List (α ⊕ Σ i, L.Functions i)) :
      ((listDecode l).head?.join : Option (L.Term α)) = (listDecode l).head? := by
    cases (listDecode l).head? <;> rfl
  -- Mathlib's instance decodes `n` as `(decode n).bind fun l => (listDecode l).head?.join`.
  exact congrArg (Option.bind (decode n)) (funext key)

/-- Mathlib's decoder of terms reads the first term of a list from the code of the list. -/
theorem decode_encode_list (l : List (α ⊕ Σ i, L.Functions i)) :
    decode (α := L.Term α) (encode l) = (listDecode l).head? := by
  simp [decode_eq_decode_bind_listDecode]

/-- The code of a function symbol of positive arity without arguments decodes to no term. -/
theorem decode_encode_singleton_inr_add_one {n : ℕ} (f : L.Functions (n + 1)) :
    decode (α := L.Term α) (encode ([Sum.inr ⟨n + 1, f⟩] : List (α ⊕ Σ i, L.Functions i))) =
      none := by
  rw [decode_encode_list, listDecode_singleton_inr_add_one, List.head?_nil]

/-- A list of terms and the list of their spellings have the same code. -/
theorem encode_map_listEncode (l : List (L.Term α)) : encode (l.map listEncode) = encode l := by
  induction l with
  | nil => rfl
  | cons t l ih => simp [encode_list_cons, ih, encode_eq_encode_listEncode]

end Encodable

variable [Primcodable α] [Primcodable (Σ i, L.Functions i)] [L.PrimrecFunctionArity]

private theorem primrec₂_decodeStep :
    Primrec₂ (decodeStep :
      (α ⊕ Σ i, L.Functions i) → _ → List (List (α ⊕ Σ i, L.Functions i))) := by
  have harity := PrimrecFunctionArity.primrec_fst (L := L)
  have hvar : Primrec₂ fun (p : (α ⊕ Σ i, L.Functions i) × List (List (α ⊕ Σ i, L.Functions i)))
      (a : α) => [Sum.inl a] :: p.2 :=
    Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.sumInl.comp .snd) (.const []))
      (Primrec.snd.comp .fst)
  have hfunc : Primrec₂ fun (p : (α ⊕ Σ i, L.Functions i) × List (List (α ⊕ Σ i, L.Functions i)))
      (F : Σ i, L.Functions i) =>
        if F.1 ≤ p.2.length then (Sum.inr F :: (p.2.take F.1).flatten) :: p.2.drop F.1 else [] :=
    Primrec.ite (Primrec.nat_le.comp (harity.comp .snd)
        (Primrec.list_length.comp (Primrec.snd.comp .fst)))
      (Primrec.list_cons.comp
        (Primrec.list_cons.comp (Primrec.sumInr.comp .snd)
          (Primrec.list_flatten.comp
            (Primrec.list_take.comp (harity.comp .snd) (Primrec.snd.comp .fst))))
        (Primrec.list_drop.comp (harity.comp .snd) (Primrec.snd.comp .fst)))
      (.const [])
  exact (Primrec.sumCasesOn .fst hvar hfunc).of_eq fun p => by rcases p with ⟨_ | _, _⟩ <;> rfl

private theorem primrec_foldr_decodeStep :
    Primrec fun l : List (α ⊕ Σ i, L.Functions i) => l.foldr decodeStep [] :=
  Primrec.list_foldr .id (.const []) (primrec₂_decodeStep.comp (Primrec.fst.comp .snd)
    (Primrec.snd.comp .snd)).to₂

private theorem primrec_encode_decode :
    Primrec fun n : ℕ => encode (decode (α := L.Term α) n) := by
  have h : Primrec fun n : ℕ => encode ((decode (α := List (α ⊕ Σ i, L.Functions i)) n).bind
      fun l => (l.foldr decodeStep []).head?) :=
    Primrec.encode.comp (Primrec.option_bind .decode
      (Primrec.list_head?.comp (primrec_foldr_decodeStep.comp .snd)).to₂)
  refine h.of_eq fun n => ?_
  rw [decode_eq_decode_bind_listDecode]
  cases decode (α := List (α ⊕ Σ i, L.Functions i)) n with
  | none => rfl
  | some l =>
    rw [Option.bind_some, Option.bind_some, ← map_listEncode_listDecode, List.head?_map]
    cases (listDecode l).head? <;> rfl

/-- Mathlib's encoding of terms is primitive recursive: for primitively encoded variables and
function symbols with primitive recursive arity, the encoding and decoding functions of Mathlib's
`Encodable (L.Term α)` instance form a `Primcodable` structure. -/
instance instPrimcodable : Primcodable (L.Term α) :=
  { (inferInstance : Encodable (L.Term α)) with
    prim := by exact Primrec.nat_iff.1 primrec_encode_decode }

/-- The primitive encoding of terms is Mathlib's encoding of terms. -/
theorem toEncodable_instPrimcodable :
    (Primcodable.toEncodable : Encodable (L.Term α)) = instEncodableOfSigmaNatFunctions :=
  (rfl)

/-- A function into terms is primitive recursive exactly when its spelling is. -/
theorem primrec_listEncode_iff {β : Type*} [Primcodable β] {f : β → L.Term α} :
    (Primrec fun b => (f b).listEncode) ↔ Primrec f :=
  ⟨fun h => Primrec.encode_iff.1 <|
      (Primrec.encode.comp h).of_eq fun b => (encode_eq_encode_listEncode (f b)).symm,
    fun h => Primrec.encode_iff.1 <|
      (Primrec.encode.comp h).of_eq fun b => encode_eq_encode_listEncode (f b)⟩

/-- Spelling a term as a list of variables and function symbols is primitive recursive. -/
theorem primrec_listEncode :
    Primrec (listEncode : L.Term α → List (α ⊕ Σ i, L.Functions i)) :=
  primrec_listEncode_iff.2 .id

/-- Reading a list of variables and function symbols as a list of terms is primitive recursive. -/
theorem primrec_listDecode :
    Primrec (listDecode : List (α ⊕ Σ i, L.Functions i) → List (L.Term α)) :=
  Primrec.encode_iff.1 <| (Primrec.encode.comp primrec_foldr_decodeStep).of_eq fun l => by
    rw [← map_listEncode_listDecode, encode_map_listEncode]

/-- The lists of variables and function symbols that spell a term form a primitive recursive
set. -/
theorem primrecPred_exists_listEncode_eq :
    PrimrecPred fun l : List (α ⊕ Σ i, L.Functions i) => ∃ t : L.Term α, t.listEncode = l :=
  (Primrec.eq.comp (Primrec.list_map primrec_listDecode (primrec_listEncode.comp .snd).to₂)
    (Primrec.list_cons.comp .id (.const []))).of_eq fun _ => exists_listEncode_eq_iff.symm

/-- Forming a variable term is primitive recursive. -/
theorem primrec_var : Primrec (var : α → L.Term α) :=
  primrec_listEncode_iff.1 <| Primrec.list_cons.comp Primrec.sumInl (.const [])

/-- Applying a function symbol to a tuple of terms is primitive recursive. -/
theorem primrec_func {n : ℕ} (f : L.Functions n) :
    Primrec (func f : (Fin n → L.Term α) → L.Term α) := by
  refine primrec_listEncode_iff.1 <| (Primrec.list_cons.comp (.const (Sum.inr ⟨n, f⟩))
    (Primrec.list_flatten.comp <| Primrec.list_ofFn fun i =>
      primrec_listEncode.comp (Primrec.fin_app.comp .id (.const i)))).of_eq fun ts => ?_
  simp [listEncode, List.ofFn_eq_map, List.flatMap_def]

end FirstOrder.Language.Term

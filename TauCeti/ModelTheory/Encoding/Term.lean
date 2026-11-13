/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Encoding
public import TauCeti.Computability.Partrec.List
public import TauCeti.ModelTheory.Encoding.Symbols
public import TauCeti.ModelTheory.Term.Substitution

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
* `FirstOrder.Language.Term.primrec_listEncode_iff`,
  `FirstOrder.Language.Term.computable_listEncode_iff`: a function into terms is primitive
  recursive, respectively computable, exactly when its spelling is.
* `FirstOrder.Language.Term.primrec_var`, `FirstOrder.Language.Term.primrec_func`: forming a
  variable term and applying a function symbol to a tuple of terms are primitive recursive.
* `FirstOrder.Language.Term.primrecPred_exists_listEncode_eq`: the lists that spell a term form
  a primitive recursive set. The decoder of terms (`Encodable.decode`) returns the first term
  that `listDecode` reads off the coded list, so it also accepts lists that spell no term, such
  as the spelling of a term followed by further symbols. A list spells a term exactly when
  `listDecode` reads it as a single term whose spelling is the list,
  `FirstOrder.Language.Term.exists_listEncode_eq_iff`. For natural-number codes, the set of
  codes of terms is primitive recursive by Mathlib's `Primcodable.mem_range_encode`.

On spellings, relabelling the variables of a term along `g` replaces each variable letter `a` by
`g a` (`FirstOrder.Language.Term.listEncode_relabel`), and substituting terms for the variables
replaces each variable letter by the spelling of the substituted term
(`FirstOrder.Language.Term.listEncode_subst`). Consequently, as relabelling is the substitution of
variables (`FirstOrder.Language.Term.relabel_eq_subst`):

* `FirstOrder.Language.Term.primrec₂_subst`, `FirstOrder.Language.Term.computable₂_subst`:
  substitution is primitive recursive, respectively computable, uniformly in a parameter on which
  the substituted terms depend primitive recursively, respectively computably;
* `FirstOrder.Language.Term.primrec₂_subst_fin`: substitution of a finite table of terms for the
  variables `Fin n` is primitive recursive, jointly in the term and the table;
* `FirstOrder.Language.Term.primrec₂_relabel`, `FirstOrder.Language.Term.primrec_relabel`,
  `FirstOrder.Language.Term.computable₂_relabel`, `FirstOrder.Language.Term.computable_relabel`:
  relabelling along a primitive recursive, respectively computable, map is primitive recursive,
  respectively computable.

Functions on terms defined by structural recursion are primitive recursive when the data of the
recursion are (`FirstOrder.Language.Term.primrec₂_of_rec`): the value on a variable is given by a
primitive recursive function, and the value on `func F ts` by a primitive recursive step applied to
the function symbol and the list of the values on the arguments, in order.

## Implementation notes

The decoder is shown primitive recursive by running it on spellings: a variable pushes its
one-letter spelling on a stack, and a function symbol of arity `n` replaces the top `n` spellings
by the symbol followed by their concatenation. The recursion principle runs a recursion on
spellings in the same way, with a stack of values in place of spellings.
-/

public section

universe u v w w'

namespace FirstOrder.Language.Term

open Encodable

variable {L : Language.{u, v}} {α : Type w} {β : Type w'}

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

/-- Relabelling the variables of a term relabels the variable letters of its spelling. -/
@[simp]
theorem listEncode_relabel (g : α → β) (t : L.Term α) :
    (t.relabel g).listEncode = t.listEncode.map (Sum.map g id) := by
  induction t <;> simp_all [listEncode, List.map_flatMap]

/-- Substituting terms for the variables of a term replaces each variable letter of its spelling
by the spelling of the substituted term. -/
@[simp]
theorem listEncode_subst (t : L.Term α) (tf : α → L.Term β) :
    (t.subst tf).listEncode =
      t.listEncode.flatMap (Sum.elim (fun a => (tf a).listEncode) fun F => [Sum.inr F]) := by
  induction t <;> simp_all [listEncode, List.flatMap_assoc]

/-- One step of a recursion on terms run on spellings from right to left: a variable pushes its
value on the stack, and a function symbol of arity `n` replaces the top `n` values by the value of
the step `h`. -/
private def recStep {σ : Type*} (g : α → σ) (h : (Σ i, L.Functions i) × List σ → σ)
    (x : α ⊕ Σ i, L.Functions i) (st : List σ) : List σ :=
  x.elim (fun a => g a :: st) fun F => h (F, st.take F.1) :: st.drop F.1

/-- Running `recStep` over the spelling of a term pushes the value of the term on the stack. -/
private theorem foldr_recStep {σ : Type*} {f : L.Term α → σ} {g : α → σ}
    {h : (Σ i, L.Functions i) × List σ → σ} (hvar : ∀ a, f (var a) = g a)
    (hfunc : ∀ {l} (F : L.Functions l) (ts : Fin l → L.Term α),
      f (func F ts) = h (⟨l, F⟩, List.ofFn fun i => f (ts i))) (t : L.Term α)
    (r : List (α ⊕ Σ i, L.Functions i)) (st : List σ) :
    (t.listEncode ++ r).foldr (recStep g h) st = f t :: r.foldr (recStep g h) st := by
  induction t generalizing r with
  | var a => simp [listEncode, recStep, hvar]
  | @func l F ts ih =>
    -- the spellings of the arguments leave their values, in order, on top of the stack
    have key (k : List (Fin l)) (r : List (α ⊕ Σ i, L.Functions i)) :
        ((k.flatMap fun i => (ts i).listEncode) ++ r).foldr (recStep g h) st =
          k.map (fun i => f (ts i)) ++ r.foldr (recStep g h) st := by
      induction k with
      | nil => simp
      | cons i k ihk => simp [ih, ihk]
    simp [listEncode, recStep, key, hfunc, List.ofFn_eq_map]

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

/-- A function into terms is computable exactly when its spelling is. -/
theorem computable_listEncode_iff {β : Type*} [Primcodable β] {f : β → L.Term α} :
    (Computable fun b => (f b).listEncode) ↔ Computable f :=
  ⟨fun h => Computable.encode_iff.1 <|
      (Computable.encode.comp h).of_eq fun b => (encode_eq_encode_listEncode (f b)).symm,
    fun h => primrec_listEncode.to_comp.comp h⟩

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

private theorem primrec₂_recStep {γ σ : Type*} [Primcodable γ] [Primcodable σ] {g : γ → α → σ}
    {h : γ → (Σ i, L.Functions i) × List σ → σ} (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec₂ fun c (p : (α ⊕ Σ i, L.Functions i) × List σ) => recStep (g c) (h c) p.1 p.2 := by
  have harity := PrimrecFunctionArity.primrec_fst (L := L)
  refine (Primrec.sumCasesOn (Primrec.fst.comp .snd)
    (Primrec.list_cons.comp (hg.comp (Primrec.fst.comp .fst) .snd)
      (Primrec.snd.comp (Primrec.snd.comp .fst))).to₂
    (Primrec.list_cons.comp (hh.comp (Primrec.fst.comp .fst) (Primrec.pair .snd
        (Primrec.list_take.comp (harity.comp .snd) (Primrec.snd.comp (Primrec.snd.comp .fst)))))
      (Primrec.list_drop.comp (harity.comp .snd)
        (Primrec.snd.comp (Primrec.snd.comp .fst)))).to₂).of_eq fun p => ?_
  rcases p with ⟨c, x | F, st⟩ <;> rfl

/-- Primitive recursion on terms: a function on terms, depending on a parameter, given by
structural recursion with primitive recursive values on variables and a primitive recursive step
at function symbols, is primitive recursive. The step receives the function symbol and the list of
the values on its arguments, in order. -/
theorem primrec₂_of_rec {γ σ : Type*} [Primcodable γ] [Primcodable σ] {f : γ → L.Term α → σ}
    {g : γ → α → σ} {h : γ → (Σ i, L.Functions i) × List σ → σ} (hg : Primrec₂ g) (hh : Primrec₂ h)
    (hvar : ∀ c a, f c (var a) = g c a)
    (hfunc : ∀ c {l} (F : L.Functions l) (ts : Fin l → L.Term α),
      f c (func F ts) = h c (⟨l, F⟩, List.ofFn fun i => f c (ts i))) : Primrec₂ f := by
  refine Primrec₂.option_some_iff.1 <| (Primrec.list_head?.comp <| Primrec.list_foldr
    (primrec_listEncode.comp .snd) (.const [])
    ((primrec₂_recStep hg hh).comp (Primrec.fst.comp .fst) .snd).to₂).of_eq fun p => ?_
  simpa using congrArg List.head? (foldr_recStep (hvar p.1) (hfunc p.1) p.2 [] [])

variable [Primcodable β]

/-- Substituting terms for variables is primitive recursive, uniformly in a parameter on which the
substituted terms depend primitive recursively. -/
theorem primrec₂_subst {γ : Type*} [Primcodable γ] {tf : γ → α → L.Term β} (htf : Primrec₂ tf) :
    Primrec₂ fun c (t : L.Term α) => t.subst (tf c) := by
  have hletter : Primrec₂ fun c (x : α ⊕ Σ i, L.Functions i) =>
      Sum.elim (fun a => (tf c a).listEncode) (fun F => [Sum.inr F]) x :=
    (Primrec.sumCasesOn .snd
      (primrec_listEncode.comp (htf.comp (Primrec.fst.comp .fst) .snd)).to₂
      (Primrec.list_cons.comp (Primrec.sumInr.comp .snd) (.const [])).to₂).of_eq
      fun p => by rcases p with ⟨_, _ | _⟩ <;> rfl
  exact primrec_listEncode_iff.1 <| (Primrec.list_flatMap (primrec_listEncode.comp .snd)
    (hletter.comp (Primrec.fst.comp .fst) .snd).to₂).of_eq fun _ => by rw [listEncode_subst]

/-- Substituting terms for variables is computable, uniformly in a parameter on which the
substituted terms depend computably. -/
theorem computable₂_subst {γ : Type*} [Primcodable γ] {tf : γ → α → L.Term β}
    (htf : Computable₂ tf) : Computable₂ fun c (t : L.Term α) => t.subst (tf c) := by
  have hletter : Computable₂ fun c (x : α ⊕ Σ i, L.Functions i) =>
      Sum.elim (fun a => (tf c a).listEncode) (fun F => [Sum.inr F]) x :=
    (Computable.sumCasesOn .snd
      (primrec_listEncode.to_comp.comp (htf.comp (Computable.fst.comp .fst) .snd)).to₂
      (Computable.list_cons.comp (Computable.sumInr.comp .snd) (.const [])).to₂).of_eq
      fun p => by rcases p with ⟨_, _ | _⟩ <;> rfl
  exact computable_listEncode_iff.1 <| (Computable.list_flatMap
    (primrec_listEncode.to_comp.comp .snd) (hletter.comp (Computable.fst.comp .fst) .snd).to₂).of_eq
    fun _ => by rw [listEncode_subst]

/-- Relabelling the variables of terms along a map depending primitive recursively on a parameter
is primitive recursive. -/
theorem primrec₂_relabel {γ : Type*} [Primcodable γ] {g : γ → α → β} (hg : Primrec₂ g) :
    Primrec₂ fun c (t : L.Term α) => t.relabel (g c) :=
  (primrec₂_subst (tf := fun c => var ∘ g c) (primrec_var.comp hg).to₂).of_eq fun c t =>
    (relabel_eq_subst t (g c)).symm

/-- Relabelling the variables of terms along a primitive recursive map is primitive recursive. -/
theorem primrec_relabel {g : α → β} (hg : Primrec g) : Primrec (relabel g : L.Term α → L.Term β) :=
  (primrec₂_relabel (hg.comp .snd).to₂).comp (.const ()) .id

/-- Relabelling the variables of terms along a map depending computably on a parameter is
computable. -/
theorem computable₂_relabel {γ : Type*} [Primcodable γ] {g : γ → α → β} (hg : Computable₂ g) :
    Computable₂ fun c (t : L.Term α) => t.relabel (g c) :=
  (computable₂_subst (tf := fun c => var ∘ g c) (primrec_var.to_comp.comp hg).to₂).of_eq fun p =>
    (relabel_eq_subst p.2 (g p.1)).symm

/-- Relabelling the variables of terms along a computable map is computable. -/
theorem computable_relabel {g : α → β} (hg : Computable g) :
    Computable (relabel g : L.Term α → L.Term β) :=
  (computable₂_relabel (hg.comp .snd).to₂).comp (.const ()) .id

/-- Substituting a finite table of terms for the variables `Fin n` is primitive recursive, jointly
in the term and the table. -/
theorem primrec₂_subst_fin {n : ℕ} :
    Primrec₂ (subst : L.Term (Fin n) → (Fin n → L.Term β) → L.Term β) :=
  (primrec₂_subst (tf := fun tf : Fin n → L.Term β => tf) Primrec.fin_app).swap

end FirstOrder.Language.Term

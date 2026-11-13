/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Primrec.Basic
public import TauCeti.Logic.Encodable.Basic
public import TauCeti.ModelTheory.Encoding.Term
public import TauCeti.ModelTheory.Term.Substitution

/-!
# Primitive-recursive codes of terms with bound-variable slots

Mathlib's list encoding of bounded formulas (`FirstOrder.Language.BoundedFormula.listEncode`)
spells the terms of a formula as letters `⟨k, t⟩` of the dependent-pair type
`Σ k, L.Term (α ⊕ Fin k)`: a number `k` of bound-variable slots together with a term over the
free variables `α` and the slots `Fin k`. These letters are coded by Mathlib's `Encodable`
instances for dependent pairs and for terms. This file shows that this encoding is primitive
recursive, uniformly in the number of slots, and that the operations which substitution,
relabelling and shifting of bound variables perform on the terms of a formula are primitive
recursive on these letters.

## Main results

* `FirstOrder.Language.Term.encode_sigma`: the code of `⟨k, t⟩` is the code of the pair of `k`
  and the term `t` with its slots read as natural numbers.
* `FirstOrder.Language.Term.instPrimcodableSigma`: the `Primcodable` structure on
  `Σ k, L.Term (α ⊕ Fin k)`; its encoding and decoding functions are those of Mathlib's
  `Encodable` instance for dependent pairs, only the proof that they are primitive recursive is
  new.
* `FirstOrder.Language.Term.primrec_sigma_iff`: a function into terms with slots is primitive
  recursive exactly when its number of slots and its term with slots read as numbers are.
* `FirstOrder.Language.Term.primrec₂_liftAt_sigma`,
  `FirstOrder.Language.Term.primrec₂_relabel_castLE_sigma`,
  `FirstOrder.Language.Term.primrec₂_relabel_relabelAux_sigma`,
  `FirstOrder.Language.Term.primrec₂_subst_sigma`: shifting slots (`Term.liftAt`), enlarging the
  number of slots (as in `BoundedFormula.castLE`), relabelling free variables into free variables
  and new slots (as in `BoundedFormula.relabel`) and substituting terms for free variables (as in
  `BoundedFormula.subst`) are primitive recursive.

## Implementation notes

A slot `i : Fin k` has the same code as the number `i`, so reading slots as numbers
(`Term.relabel (Sum.map id Fin.val)`) embeds `Σ k, L.Term (α ⊕ Fin k)` into
`ℕ × L.Term (α ⊕ ℕ)` without changing codes; its image consists of the pairs `(k, s)` all of
whose slot letters are below `k`. Primitive recursiveness is reduced along this embedding to
`FirstOrder.Language.Term.instPrimcodable` with variables `α ⊕ ℕ`.

## References

The encoding of terms and formulas is that of `Mathlib.ModelTheory.Encoding`; the operations on
bounded formulas are those of `Mathlib.ModelTheory.Syntax`. The language of groups with
coefficients, whose formulas these letters are meant to code, is that of Kharlampovich and
Myasnikov, *Implicit function theorem over free groups*, §2.3.
-/

public section

universe u v w

namespace FirstOrder.Language.Term

open Encodable

variable {L : Language.{u, v}} {α : Type w}

/-! ### Spellings and slots read as numbers -/

/-- Reading slots as numbers after `Term.liftAt n' m` raises the numbers `≥ m` by `n'`. -/
private theorem relabel_val_liftAt {k : ℕ} (n' m : ℕ) (t : L.Term (α ⊕ Fin k)) :
    (t.liftAt n' m).relabel (Sum.map id Fin.val) =
      (t.relabel (Sum.map id Fin.val)).relabel
        (Sum.map id fun i => if i < m then i else i + n') := by
  rw [liftAt, relabel_relabel, relabel_relabel]
  congr 1
  funext x
  rcases x with a | i
  · rfl
  · simp only [Function.comp_apply, Sum.map_inr]
    split_ifs <;> simp

/-- Reading slots as numbers after `BoundedFormula.relabelAux g k` sends a free variable to the
number of the slot that `g` assigns to it, and the slot `j` to `n + j`. -/
private theorem relabel_val_relabelAux {β : Type*} {n k : ℕ} (g : α → β ⊕ Fin n)
    (t : L.Term (α ⊕ Fin k)) :
    (t.relabel (BoundedFormula.relabelAux g k)).relabel (Sum.map id Fin.val) =
      (t.relabel (Sum.map id Fin.val)).relabel
        (Sum.elim (Sum.map id Fin.val ∘ g) fun j => Sum.inr (n + j)) := by
  rw [relabel_relabel, relabel_relabel]
  congr 1
  funext x
  rcases x with a | i
  · rcases h : g a with b | j <;> simp [BoundedFormula.relabelAux, h]
  · simp [BoundedFormula.relabelAux]

/-- Reading slots as numbers commutes with the substitution of `BoundedFormula.subst`. -/
private theorem relabel_val_subst {β : Type*} {k : ℕ} (f : α → L.Term β)
    (t : L.Term (α ⊕ Fin k)) :
    (t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr))).relabel
        (Sum.map id Fin.val) =
      (t.relabel (Sum.map id Fin.val)).subst
        (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr)) := by
  rw [relabel_subst, subst_relabel]
  congr 1
  funext x
  rcases x with a | i <;> simp [Function.comp_def]

section Encodable

variable [Encodable α] [Encodable (Σ i, L.Functions i)]

/-- The code of a term with bound-variable slots is the code of the pair of its number of slots
and of the term with its slots read as natural numbers. -/
theorem encode_sigma (t : Σ k, L.Term (α ⊕ Fin k)) :
    encode t = encode (t.1, t.2.relabel (Sum.map id Fin.val)) := by
  obtain ⟨k, t⟩ := t
  -- A slot `i : Fin k` is coded by its value, so reading slots as numbers keeps all codes.
  rw [encode_sigma_val, encode_prod_val, encode_relabel fun x => by rcases x with a | i <;> rfl]

/-- The test that every slot letter of a letter of a term over `α ⊕ ℕ` is below `k`. -/
private def slotLT (k : ℕ) : (α ⊕ ℕ) ⊕ (Σ i, L.Functions i) → Bool :=
  Sum.elim (Sum.elim (fun _ => true) fun i => decide (i < k)) fun _ => true

/-- Decoding a list of letters of terms with `k` slots and reading the slots as numbers is
decoding a list of letters of terms over `α ⊕ ℕ` and keeping it when its slot letters are below
`k`. -/
private theorem map_decode_list_letters (k n : ℕ) :
    (decode (α := List ((α ⊕ Fin k) ⊕ Σ i, L.Functions i)) n).map
        (List.map (Sum.map (Sum.map id Fin.val) id)) =
      (decode (α := List ((α ⊕ ℕ) ⊕ Σ i, L.Functions i)) n).filter
        fun l => l.all (slotLT k) :=
  map_listMap_decode (map_sumMap_decode (map_sumMap_decode
    (fun n => by cases decode (α := α) n <;> rfl) (map_val_decode_fin k))
    (fun n => by cases decode (α := Σ i, L.Functions i) n <;> rfl)) n

/-- Decoding a term with `k` slots and reading its slots as numbers is reading the first term
from the decoded list of letters over `α ⊕ ℕ`, when its slot letters are below `k`. -/
private theorem map_relabel_decode (k n : ℕ) :
    (decode (α := L.Term (α ⊕ Fin k)) n).map (relabel (Sum.map id Fin.val)) =
      ((decode (α := List ((α ⊕ ℕ) ⊕ Σ i, L.Functions i)) n).filter
        fun l => l.all (slotLT k)).bind fun l => (listDecode l).head? := by
  rw [decode_eq_decode_bind_listDecode, Option.map_bind, ← map_decode_list_letters,
    Option.bind_map]
  congr 1
  funext l
  simp only [Function.comp_apply, listDecode_map_sumMap, List.head?_map]

/-- The code of the decoded term with bound-variable slots, computed from terms over
`α ⊕ ℕ`. -/
private theorem encode_decode_sigma (c : ℕ) :
    encode (decode (α := Σ k, L.Term (α ⊕ Fin k)) c) =
      encode ((((decode (α := List ((α ⊕ ℕ) ⊕ Σ i, L.Functions i)) c.unpair.2).filter
        fun l => l.all (slotLT c.unpair.1)).bind fun l => (listDecode l).head?).map
          (Prod.mk c.unpair.1)) := by
  rw [← map_relabel_decode, decode_sigma_val, decode_nat, Option.bind_some]
  cases decode (α := L.Term (α ⊕ Fin c.unpair.1)) c.unpair.2 with
  | none => rfl
  | some t => exact congrArg Nat.succ (encode_sigma ⟨_, t⟩)

end Encodable

section Primcodable

variable [Primcodable α] [Primcodable (Σ i, L.Functions i)]

private theorem primrec₂_slotLT :
    Primrec₂ (slotLT : ℕ → (α ⊕ ℕ) ⊕ (Σ i, L.Functions i) → Bool) :=
  (Primrec.sumCasesOn .snd
    (Primrec.sumCasesOn .snd (.const true)
      (Primrec.nat_lt.decide.comp .snd (Primrec.fst.comp (Primrec.fst.comp .fst))).to₂).to₂
    (.const true)).of_eq fun p => by rcases p with ⟨k, (a | i) | F⟩ <;> rfl

variable [L.PrimrecFunctionArity]

private theorem primrec_encode_decode_sigma :
    Primrec fun c : ℕ => encode (decode (α := Σ k, L.Term (α ⊕ Fin k)) c) := by
  have hR : PrimrecRel fun (x : (α ⊕ ℕ) ⊕ Σ i, L.Functions i) (k : ℕ) => slotLT k x = true :=
    Primrec.eq.comp (primrec₂_slotLT.comp .snd .fst) (.const true)
  have hall : Primrec₂ fun (k : ℕ) (l : List ((α ⊕ ℕ) ⊕ Σ i, L.Functions i)) =>
      l.all (slotLT k) :=
    (hR.forall_mem_list.decide.comp .snd .fst).of_eq fun _ => List.all_eq.symm
  have hfilter : Primrec fun c : ℕ =>
      (decode (α := List ((α ⊕ ℕ) ⊕ Σ i, L.Functions i)) c.unpair.2).filter
        fun l => l.all (slotLT c.unpair.1) :=
    (Primrec.option_bind (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.cond (hall.comp (Primrec.fst.comp (Primrec.unpair.comp .fst)) .snd)
        (Primrec.option_some.comp .snd) (.const none)).to₂).of_eq fun c => by
      cases decode (α := List ((α ⊕ ℕ) ⊕ Σ i, L.Functions i)) c.unpair.2 with
      | none => rfl
      | some l => simp only [Option.bind_some, Option.filter, Bool.cond_eq_ite]
  exact (Primrec.encode.comp (Primrec.option_map (Primrec.option_bind hfilter
    (Primrec.list_head?.comp (primrec_listDecode.comp .snd)).to₂)
    (Primrec.pair (Primrec.fst.comp (Primrec.unpair.comp .fst)) .snd).to₂)).of_eq
    fun c => (encode_decode_sigma c).symm

/-- Mathlib's encoding of terms with a varying number of bound-variable slots is primitive
recursive: the encoding and decoding functions of Mathlib's `Encodable` instance for dependent
pairs of terms form a `Primcodable` structure. -/
instance instPrimcodableSigma : Primcodable (Σ k, L.Term (α ⊕ Fin k)) :=
  { (inferInstance : Encodable (Σ k, L.Term (α ⊕ Fin k))) with
    prim := by exact Primrec.nat_iff.1 primrec_encode_decode_sigma }

/-- The primitive encoding of terms with bound-variable slots is Mathlib's encoding of dependent
pairs of terms. -/
theorem toEncodable_instPrimcodableSigma :
    (Primcodable.toEncodable : Encodable (Σ k, L.Term (α ⊕ Fin k))) = Sigma.encodable :=
  (rfl)

/-- A function into terms with bound-variable slots is primitive recursive exactly when its
number of slots and its term with slots read as natural numbers are. -/
theorem primrec_sigma_iff {β : Type*} [Primcodable β] {f : β → Σ k, L.Term (α ⊕ Fin k)} :
    Primrec f ↔ Primrec fun b => ((f b).1, (f b).2.relabel (Sum.map id Fin.val)) :=
  ⟨fun h => Primrec.encode_iff.1 <| (Primrec.encode.comp h).of_eq fun b => encode_sigma (f b),
    fun h => Primrec.encode_iff.1 <|
      (Primrec.encode.comp h).of_eq fun b => (encode_sigma (f b)).symm⟩

/-- The number of bound-variable slots is primitive recursive. -/
theorem primrec_sigma_fst : Primrec (Sigma.fst : (Σ k, L.Term (α ⊕ Fin k)) → ℕ) :=
  Primrec.fst.comp (primrec_sigma_iff.1 .id)

/-- Reading the bound-variable slots of a term as natural numbers is primitive recursive. -/
theorem primrec_relabel_sigma_val :
    Primrec fun t : Σ k, L.Term (α ⊕ Fin k) => t.2.relabel (Sum.map id Fin.val) :=
  Primrec.snd.comp (primrec_sigma_iff.1 .id)

/-- Substitution along a primitive recursive family of assignments is primitive recursive: the
spelling of a substituted term replaces each variable letter by the spelling of the term
substituted for it. -/
private theorem primrec₂_subst_term {γ β : Type*} [Primcodable γ] [Primcodable β]
    {f : γ → α → L.Term β} (hf : Primrec₂ f) :
    Primrec₂ fun c (t : L.Term α) => t.subst (f c) := by
  have hspell (c : γ) (t : L.Term α) : (t.subst (f c)).listEncode =
      t.listEncode.flatMap (Sum.elim (fun a => (f c a).listEncode) fun F => [Sum.inr F]) := by
    induction t with
    | var => simp [listEncode]
    | func F ts ih => simp [listEncode, ih, List.flatMap_assoc]
  have h : Primrec₂ fun (p : γ × L.Term α) (x : α ⊕ Σ i, L.Functions i) =>
      Sum.elim (fun a => (f p.1 a).listEncode) (fun F => [Sum.inr F]) x :=
    (Primrec.sumCasesOn .snd
      (primrec_listEncode.comp (hf.comp (Primrec.fst.comp (Primrec.fst.comp .fst)) .snd)).to₂
      (Primrec.list_cons.comp (Primrec.sumInr.comp .snd) (.const [])).to₂).to₂.of_eq
      fun _ x => by rcases x with a | F <;> rfl
  exact primrec_listEncode_iff.1 <| (Primrec.list_flatMap (primrec_listEncode.comp .snd) h).of_eq
    fun p => (hspell p.1 p.2).symm

/-- Relabelling along a primitive recursive family of maps of variables is primitive
recursive. -/
private theorem primrec₂_relabel_term {γ β : Type*} [Primcodable γ] [Primcodable β]
    {g : γ → α → β} (hg : Primrec₂ g) : Primrec₂ fun c (t : L.Term α) => t.relabel (g c) :=
  (primrec₂_subst_term (primrec_var.comp hg).to₂).of_eq fun c t => (relabel_eq_subst t (g c)).symm

/-- Raising the bound-variable slots `≥ m` by `n'` (`Term.liftAt n' m`) is primitive recursive,
jointly in `(n', m)` and the term. -/
theorem primrec₂_liftAt_sigma :
    Primrec₂ fun (p : ℕ × ℕ) (t : Σ k, L.Term (α ⊕ Fin k)) =>
      (⟨t.1 + p.1, t.2.liftAt p.1 p.2⟩ : Σ k, L.Term (α ⊕ Fin k)) := by
  have hlift : Primrec₂ fun (p : ℕ × ℕ) (x : α ⊕ ℕ) =>
      Sum.map id (fun i => if i < p.2 then i else i + p.1) x :=
    (Primrec.sumCasesOn .snd (Primrec.sumInl.comp .snd).to₂
      (Primrec.sumInr.comp (Primrec.ite
        (Primrec.nat_lt.comp .snd (Primrec.snd.comp (Primrec.fst.comp .fst))) .snd
        (Primrec.nat_add.comp .snd (Primrec.fst.comp (Primrec.fst.comp .fst))))).to₂).to₂.of_eq
      fun _ x => by rcases x with a | i <;> rfl
  refine primrec_sigma_iff.2 <| (Primrec.pair
    (Primrec.nat_add.comp (primrec_sigma_fst.comp .snd) (Primrec.fst.comp .fst))
    ((primrec₂_relabel_term hlift).comp .fst (primrec_relabel_sigma_val.comp .snd))).of_eq
    fun p => ?_
  rw [relabel_val_liftAt]

/-- Enlarging the number of bound-variable slots to `n`, as `BoundedFormula.castLE` does on the
terms of a formula, is primitive recursive; terms with more than `n` slots are left unchanged. -/
theorem primrec₂_relabel_castLE_sigma :
    Primrec₂ fun (n : ℕ) (t : Σ k, L.Term (α ⊕ Fin k)) =>
      (if h : t.1 ≤ n then ⟨n, t.2.relabel (Sum.map id (Fin.castLE h))⟩ else t :
        Σ k, L.Term (α ⊕ Fin k)) := by
  -- Enlarging the number of slots keeps the term with slots read as numbers.
  refine primrec_sigma_iff.2 <| (Primrec.pair
    (Primrec.nat_max.comp .fst (primrec_sigma_fst.comp .snd))
    (primrec_relabel_sigma_val.comp .snd)).of_eq fun p => ?_
  obtain ⟨n, k, t⟩ := p
  dsimp only
  by_cases h : k ≤ n
  · rw [dite_eq_left_of_eq_true (eq_true h), relabel_relabel, Sum.map_comp_map]
    simp only [Prod.mk.injEq, max_eq_left h, true_and]
    rfl
  · rw [dite_eq_right_of_eq_false (eq_false h), max_eq_right (Nat.le_of_not_le h)]

/-- Relabelling the free variables of a term into free variables and `n` new bound-variable
slots, as `BoundedFormula.relabel` does on the terms of a formula, is primitive recursive,
uniformly in a parameter on which the relabelling depends primitive recursively. -/
theorem primrec₂_relabel_relabelAux_sigma {γ β : Type*} [Primcodable γ] [Primcodable β] {n : ℕ}
    {g : γ → α → β ⊕ Fin n} (hg : Primrec₂ g) :
    Primrec₂ fun c (t : Σ k, L.Term (α ⊕ Fin k)) =>
      (⟨n + t.1, t.2.relabel (BoundedFormula.relabelAux (g c) t.1)⟩ :
        Σ k, L.Term (β ⊕ Fin k)) := by
  have hval : Primrec (Sum.map id Fin.val : β ⊕ Fin n → β ⊕ ℕ) := .sumMap .id .fin_val
  have hmap : Primrec₂ fun (c : γ) (x : α ⊕ ℕ) =>
      Sum.elim (Sum.map id Fin.val ∘ g c) (fun j => Sum.inr (n + j)) x :=
    (Primrec.sumCasesOn .snd (hval.comp (hg.comp (Primrec.fst.comp .fst) .snd)).to₂
      (Primrec.sumInr.comp (Primrec.nat_add.comp (.const n) .snd)).to₂).to₂.of_eq fun _ x => by
      rcases x with a | j <;> rfl
  refine primrec_sigma_iff.2 <| (Primrec.pair
    (Primrec.nat_add.comp (.const n) (primrec_sigma_fst.comp .snd))
    ((primrec₂_relabel_term hmap).comp .fst (primrec_relabel_sigma_val.comp .snd))).of_eq
    fun p => ?_
  rw [relabel_val_relabelAux]

/-- Substituting terms for the free variables of a term with bound-variable slots, as
`BoundedFormula.subst` does on the terms of a formula, is primitive recursive, uniformly in a
parameter on which the substituted terms depend primitive recursively. -/
theorem primrec₂_subst_sigma {γ β : Type*} [Primcodable γ] [Primcodable β]
    {f : γ → α → L.Term β} (hf : Primrec₂ f) :
    Primrec₂ fun c (t : Σ k, L.Term (α ⊕ Fin k)) =>
      (⟨t.1, t.2.subst (Sum.elim (Term.relabel Sum.inl ∘ f c) (var ∘ Sum.inr))⟩ :
        Σ k, L.Term (β ⊕ Fin k)) := by
  have hinl : Primrec₂ fun (c : γ) (a : α) => (f c a).relabel (Sum.inl : β → β ⊕ ℕ) :=
    (primrec₂_relabel_term (g := fun (_ : Unit) => (Sum.inl : β → β ⊕ ℕ))
      (Primrec.sumInl.comp .snd)).comp (.const ()) hf
  have hσ : Primrec₂ fun (c : γ) (x : α ⊕ ℕ) =>
      Sum.elim (Term.relabel Sum.inl ∘ f c) (var ∘ Sum.inr) x :=
    (Primrec.sumCasesOn .snd (hinl.comp (Primrec.fst.comp .fst) .snd).to₂
      (primrec_var.comp (Primrec.sumInr.comp .snd)).to₂).to₂.of_eq fun _ x => by
      rcases x with a | j <;> rfl
  refine primrec_sigma_iff.2 <| (Primrec.pair (primrec_sigma_fst.comp .snd)
    ((primrec₂_subst_term hσ).comp .fst (primrec_relabel_sigma_val.comp .snd))).of_eq fun p => ?_
  rw [relabel_val_subst]

end Primcodable

end FirstOrder.Language.Term

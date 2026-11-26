/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.EM.Indiscernible

import Mathlib.Data.Finset.Sort
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Ehrenfeucht–Mostowski templates and the Morley seed

An *Ehrenfeucht–Mostowski template* records, for each arity `n`, a set of `L_{ω₁ω}` formulas in
`n` bound positions, declared true of increasing `n`-tuples. A sequence indexed by an order
*realizes* a template on a set `Δ` of formulas when each formula of `Δ` holds at an increasing
tuple exactly if the template declares it true. The template of a sequence consists of the formulas
true at all of its increasing tuples. Templates are the data from which Ehrenfeucht–Mostowski
models are stretched over arbitrary linear orders: they let the indiscernibles of one model be
transferred to sequences, and models, indexed by other orders.

Indiscernibility is realization of the sequence's own template, and a sequence realizing any
template is indiscernible. A template is *coherent* when membership does not change under
relabelling the bound positions of a formula along an order embedding `Fin n ↪o Fin m`; the
template of an indiscernible sequence over an infinite linear order is coherent.

The *Morley seed* of a sentence `φ` is the set `{φ, x₀ ≠ x₁}`. Every injective sequence is
indiscernible for it, and a sequence over a linear order realizing the template of an injective
sequence in a model of `φ` on the seed is again injective with values in a model of `φ`; so its
index order is no larger than the structure it lands in.

Realizability of templates is not of finite character in `L_{ω₁ω}`: a template every finite part of
which is realized need not be realized, as unary predicates `Pᵢ` with `Pᵢ x ↔ i ≤ x` on `ℕ` show,
where each `Pᵢ x` and `¬⋀ᵢ Pᵢ x` are eventually true along the identity sequence.

## Main definitions

* `FirstOrder.Language.EMTemplate L`: a template, a set of formulas in `n` bound positions for each
  arity `n`.
* `FirstOrder.Language.templateOf L a`: the formulas true at every increasing tuple of `a`.
* `FirstOrder.Language.EMTemplate.RealizesOn Φ a Δ`: `a` realizes `Φ` on `Δ`.
* `FirstOrder.Language.EMTemplate.IsCoherentOn Φ Δ`: membership in `Φ` of members of `Δ` is
  invariant under order-preserving relabelling of bound positions.
* `FirstOrder.Language.disEq`: the formula `x₀ ≠ x₁`.
* `FirstOrder.Language.morleySeed φ`: the set `{φ, x₀ ≠ x₁}`.

## Main results

* `FirstOrder.Language.isIndiscernibleOn_iff_realizesOn_templateOf`: a sequence is indiscernible
  for `Δ` exactly when it realizes its own template on `Δ`.
* `FirstOrder.Language.EMTemplate.RealizesOn.isIndiscernibleOn`: a sequence realizing a template
  on `Δ` is indiscernible for `Δ`.
* `FirstOrder.Language.IsIndiscernibleOn.isCoherentOn_templateOf`: over an infinite index order,
  the template of a sequence indiscernible for `Δ` is coherent on `Δ`.
* `FirstOrder.Language.IsIndiscernibleOn.mem_templateOf_comp_iff`: over an infinite index order, a
  subsequence of a sequence indiscernible for `Δ` has the same template on `Δ`.
* `FirstOrder.Language.isIndiscernibleOn_morleySeed`: an injective sequence is indiscernible for
  the Morley seed.
* `FirstOrder.Language.realize_and_injective_of_realizesOn_templateOf_morleySeed`: a sequence
  realizing on the Morley seed of `φ` the template of an injective sequence in a model of `φ` is
  injective, and its target is a model of `φ`.
* `FirstOrder.Language.lift_mk_le_of_realizesOn_templateOf_morleySeed`: if `b : I → N` realizes on
  the Morley seed of a sentence the template of an injective sequence, then `#I ≤ #N`.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46 (2016), §5.1: the
  proof of Theorem 5.2, whose starting theory contains `φ` and the disequalities `dᵢ ≠ dⱼ`, and
  whose indiscernibility conditions `Γ` are recorded here by templates.
* C. Freer, `cameronfreer/infinitary-logic` (Apache-2.0) at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`: `InfinitaryLogic/Methods/EM/Template.lean`
  (`Lomega1omegaTemplate`, `templateOfSeq`), `InfinitaryLogic/Methods/EM/Realization.lean` and
  `InfinitaryLogic/Methods/EM/FragmentAdapter.lean` (`disEqFormula`, `morleySeed`) formalize the
  same layer. Divergences: index types are preorders rather than linear orders, a template is a
  set of bounded formulas for each arity rather than a truth assignment turned into template
  sentences over `L[[J]]`, realization is relative to a set `Δ` of formulas, and the Morley seed
  is the set `{φ, x₀ ≠ x₁}` rather than a sequence of formulas.
-/

public section

universe u v w w' u₁ u₂ u₃

open Cardinal

namespace FirstOrder

namespace Language

/-- An *Ehrenfeucht–Mostowski template* for a language `L`: for each arity `n`, the set of formulas
in `n` bound positions that it declares true of increasing `n`-tuples. -/
@[ext]
structure EMTemplate (L : Language.{u, v}) where
  /-- The formulas in `n` bound positions declared true. -/
  formulas : (n : ℕ) → Set (L.BoundedFormulaω Empty n)

variable {L : Language.{u, v}} {J : Type u₁} {K : Type u₂} [Preorder J] [Preorder K]
  {I : Type u₃} [LinearOrder I] {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
  {a : J → M} {c : I → M} {Δ Δ' : Set (Σ n, L.BoundedFormulaω Empty n)} {Φ : L.EMTemplate}
  {n m : ℕ}

variable (L) in
/-- The *template* of a sequence: the formulas true at every increasing tuple of it. -/
def templateOf (a : J → M) : L.EMTemplate where
  formulas n := {φ | ∀ t : Fin n ↪o J, φ.Realize (Empty.elim : Empty → M) (a ∘ t)}

@[simp]
theorem mem_templateOf_formulas {φ : L.BoundedFormulaω Empty n} :
    φ ∈ (L.templateOf a).formulas n ↔
      ∀ t : Fin n ↪o J, φ.Realize (Empty.elim : Empty → M) (a ∘ t) :=
  Iff.rfl

/-- A sentence lies in the template of a sequence exactly when it holds in the structure. -/
theorem mem_templateOf_formulas_zero_iff {φ : L.Sentenceω} :
    φ ∈ (L.templateOf a).formulas 0 ↔ SentenceInf.Realize φ M := by
  simp only [mem_templateOf_formulas, Subsingleton.elim (a ∘ _) default, SentenceInf.realize_def,
    FormulaInf.realize_def]
  exact ⟨fun h ↦ h OrderEmbedding.ofIsEmpty, fun h _ ↦ h⟩

namespace EMTemplate

/-- A sequence *realizes* a template `Φ` on a set `Δ` of formulas when each formula of `Δ` holds at
an increasing tuple of the sequence exactly if `Φ` declares it true. -/
def RealizesOn (Φ : L.EMTemplate) (a : J → M) (Δ : Set (Σ n, L.BoundedFormulaω Empty n)) : Prop :=
  ∀ p ∈ Δ, ∀ t : Fin p.1 ↪o J, p.2.Realize (Empty.elim : Empty → M) (a ∘ t) ↔ p.2 ∈ Φ.formulas p.1

theorem realizesOn_def :
    Φ.RealizesOn a Δ ↔
      ∀ p ∈ Δ, ∀ t : Fin p.1 ↪o J,
        p.2.Realize (Empty.elim : Empty → M) (a ∘ t) ↔ p.2 ∈ Φ.formulas p.1 :=
  Iff.rfl

/-- A formula of `Δ` holds at an increasing tuple of a sequence realizing `Φ` on `Δ` exactly when
`Φ` declares it true. -/
theorem RealizesOn.realize_iff (h : Φ.RealizesOn a Δ) {φ : L.BoundedFormulaω Empty n}
    (hφ : ⟨n, φ⟩ ∈ Δ) (t : Fin n ↪o J) :
    φ.Realize (Empty.elim : Empty → M) (a ∘ t) ↔ φ ∈ Φ.formulas n :=
  h _ hφ t

/-- A sentence of `Δ` holds in the target of a sequence realizing `Φ` on `Δ` exactly when `Φ`
declares it true. -/
theorem RealizesOn.realize_sentence_iff (h : Φ.RealizesOn a Δ) {φ : L.Sentenceω}
    (hφ : ⟨0, φ⟩ ∈ Δ) : SentenceInf.Realize φ M ↔ φ ∈ Φ.formulas 0 := by
  rw [← h.realize_iff hφ OrderEmbedding.ofIsEmpty, Subsingleton.elim (a ∘ _) default,
    SentenceInf.realize_def, FormulaInf.realize_def]

theorem RealizesOn.mono (hΔ : Δ' ⊆ Δ) (h : Φ.RealizesOn a Δ) : Φ.RealizesOn a Δ' :=
  fun p hp ↦ h p (hΔ hp)

/-- Realization on one formula: it holds at an increasing tuple exactly if `Φ` declares it
true. -/
@[simp]
theorem realizesOn_singleton {φ : L.BoundedFormulaω Empty n} :
    Φ.RealizesOn a {⟨n, φ⟩} ↔
      ∀ t : Fin n ↪o J, φ.Realize (Empty.elim : Empty → M) (a ∘ t) ↔ φ ∈ Φ.formulas n :=
  ⟨fun h ↦ h.realize_iff rfl, fun h ↦ by rintro _ rfl; exact h⟩

@[simp]
theorem realizesOn_empty : Φ.RealizesOn a (∅ : Set (Σ n, L.BoundedFormulaω Empty n)) :=
  fun _ hp ↦ hp.elim

@[simp]
theorem realizesOn_union :
    Φ.RealizesOn a (Δ ∪ Δ') ↔ Φ.RealizesOn a Δ ∧ Φ.RealizesOn a Δ' :=
  ⟨fun h ↦ ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩,
    fun h p hp ↦ hp.elim (h.1 p) (h.2 p)⟩

@[simp]
theorem realizesOn_iUnion {ι : Sort*} {Δs : ι → Set (Σ n, L.BoundedFormulaω Empty n)} :
    Φ.RealizesOn a (⋃ i, Δs i) ↔ ∀ i, Φ.RealizesOn a (Δs i) :=
  ⟨fun h i ↦ h.mono (Set.subset_iUnion Δs i), fun h p hp ↦ by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
    exact h i p hi⟩

@[simp]
theorem realizesOn_insert {p : Σ n, L.BoundedFormulaω Empty n} :
    Φ.RealizesOn a (insert p Δ) ↔ Φ.RealizesOn a {p} ∧ Φ.RealizesOn a Δ := by
  rw [Set.insert_eq, realizesOn_union]

/-- A subsequence of a sequence realizing `Φ` on `Δ` realizes `Φ` on `Δ`. -/
theorem RealizesOn.comp_orderEmbedding (h : Φ.RealizesOn a Δ) (e : K ↪o J) :
    Φ.RealizesOn (a ∘ e) Δ := fun p hp t ↦ by
  simpa only [RelEmbedding.coe_trans, Function.comp_assoc] using h p hp (t.trans e)

/-- A sequence realizing a template on `Δ` is indiscernible for `Δ`. -/
theorem RealizesOn.isIndiscernibleOn (h : Φ.RealizesOn a Δ) : IsIndiscernibleOn a Δ :=
  isIndiscernibleOn_def.2 fun p hp s t ↦ (h p hp s).trans (h p hp t).symm

/-- A template is *coherent* on `Δ` when, for each member of `Δ`, its relabellings along order
embeddings `Fin n ↪o Fin m` of bound positions are declared true exactly when the member is. -/
def IsCoherentOn (Φ : L.EMTemplate) (Δ : Set (Σ n, L.BoundedFormulaω Empty n)) : Prop :=
  ∀ p ∈ Δ, ∀ {m : ℕ} (r : Fin p.1 ↪o Fin m), p.2.mapBound r ∈ Φ.formulas m ↔ p.2 ∈ Φ.formulas p.1

theorem isCoherentOn_def :
    Φ.IsCoherentOn Δ ↔
      ∀ p ∈ Δ, ∀ {m : ℕ} (r : Fin p.1 ↪o Fin m),
        p.2.mapBound r ∈ Φ.formulas m ↔ p.2 ∈ Φ.formulas p.1 :=
  Iff.rfl

/-- In a coherent template, a member of `Δ` and its relabelling along an order embedding of bound
positions are declared true together. -/
theorem IsCoherentOn.mapBound_mem_iff (h : Φ.IsCoherentOn Δ) {φ : L.BoundedFormulaω Empty n}
    (hφ : ⟨n, φ⟩ ∈ Δ) (r : Fin n ↪o Fin m) : φ.mapBound r ∈ Φ.formulas m ↔ φ ∈ Φ.formulas n :=
  h _ hφ r

theorem IsCoherentOn.mono (hΔ : Δ' ⊆ Δ) (h : Φ.IsCoherentOn Δ) : Φ.IsCoherentOn Δ' :=
  fun p hp ↦ h p (hΔ hp)

/-- Over an infinite index order, a template realized on `Δ` declares a member of `Δ` and a
relabelling of it lying in `Δ` true together: both have the truth value of the member at one
increasing tuple. -/
theorem RealizesOn.mapBound_mem_iff [Infinite I] (h : Φ.RealizesOn c Δ)
    {φ : L.BoundedFormulaω Empty n} (hφ : ⟨n, φ⟩ ∈ Δ) {r : Fin n ↪o Fin m}
    (hr : ⟨m, φ.mapBound r⟩ ∈ Δ) : φ.mapBound r ∈ Φ.formulas m ↔ φ ∈ Φ.formulas n := by
  obtain ⟨t⟩ := nonempty_orderEmbedding_of_finite_infinite (Fin m) I
  rw [← h.realize_iff hr t, ← h.realize_iff hφ (r.trans t), BoundedFormulaInf.realize_mapBound,
    RelEmbedding.coe_trans, Function.comp_assoc]

/-- Over an infinite index order, a template realized on a set `Δ` closed under order-preserving
relabelling of bound positions is coherent on `Δ`. -/
theorem RealizesOn.isCoherentOn [Infinite I] (h : Φ.RealizesOn c Δ)
    (hΔ : ∀ p ∈ Δ, ∀ {m : ℕ} (r : Fin p.1 ↪o Fin m), ⟨m, p.2.mapBound r⟩ ∈ Δ) :
    Φ.IsCoherentOn Δ :=
  fun p hp _ r ↦ h.mapBound_mem_iff hp (hΔ p hp r)

end EMTemplate

open EMTemplate

/-- **Indiscernibility is realization of the own template.** A sequence is indiscernible for `Δ`
exactly when it realizes its own template on `Δ`. -/
theorem isIndiscernibleOn_iff_realizesOn_templateOf :
    IsIndiscernibleOn a Δ ↔ (L.templateOf a).RealizesOn a Δ :=
  ⟨fun h _ hp t ↦ ⟨fun ht s ↦ (h.realize_iff hp s t).2 ht, fun ht ↦ ht t⟩,
    RealizesOn.isIndiscernibleOn⟩

/-- For a sequence indiscernible for `Δ`, a member of `Δ` lies in the template of the sequence
exactly when it holds at one given increasing tuple. -/
theorem IsIndiscernibleOn.mem_templateOf_iff (h : IsIndiscernibleOn a Δ)
    {φ : L.BoundedFormulaω Empty n} (hφ : ⟨n, φ⟩ ∈ Δ) (t : Fin n ↪o J) :
    φ ∈ (L.templateOf a).formulas n ↔ φ.Realize (Empty.elim : Empty → M) (a ∘ t) :=
  ((isIndiscernibleOn_iff_realizesOn_templateOf.1 h).realize_iff hφ t).symm

/-- **Coherence of the template of an indiscernible sequence.** Over an infinite index order, the
template of a sequence indiscernible for `Δ` is coherent on `Δ`. -/
theorem IsIndiscernibleOn.isCoherentOn_templateOf [Infinite I] (h : IsIndiscernibleOn c Δ) :
    (L.templateOf c).IsCoherentOn Δ := by
  intro p hp m r
  obtain ⟨t⟩ := nonempty_orderEmbedding_of_finite_infinite (Fin m) I
  simp only [mem_templateOf_formulas, BoundedFormulaInf.realize_mapBound]
  refine ⟨fun hr u ↦ (h.realize_iff hp (r.trans t) u).1 ?_, fun hp' u ↦ ?_⟩
  · simpa only [RelEmbedding.coe_trans, Function.comp_assoc] using hr t
  · simpa only [RelEmbedding.coe_trans, Function.comp_assoc] using hp' (r.trans u)

/-- **Subsequences of an indiscernible sequence have the same template.** Over an infinite index
order `I`, if `a` is indiscernible for `Δ` then its composite with an order embedding `I ↪o J`
has the same template on `Δ`. -/
theorem IsIndiscernibleOn.mem_templateOf_comp_iff [Infinite I] (h : IsIndiscernibleOn a Δ)
    (e : I ↪o J) {φ : L.BoundedFormulaω Empty n} (hφ : ⟨n, φ⟩ ∈ Δ) :
    φ ∈ (L.templateOf (a ∘ e)).formulas n ↔ φ ∈ (L.templateOf a).formulas n := by
  obtain ⟨t⟩ := nonempty_orderEmbedding_of_finite_infinite (Fin n) I
  rw [(h.comp_orderEmbedding e).mem_templateOf_iff hφ t, h.mem_templateOf_iff hφ (t.trans e),
    RelEmbedding.coe_trans, Function.comp_assoc]

section MorleySeed

variable (L) in
/-- The formula `x₀ ≠ x₁` in two bound positions. -/
def disEq : L.BoundedFormulaω Empty 2 :=
  (BoundedFormulaInf.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))).not

@[simp]
theorem realize_disEq {v : Empty → M} {xs : Fin 2 → M} : (L.disEq).Realize v xs ↔ xs 0 ≠ xs 1 := by
  simp [disEq]

/-- The *Morley seed* of a sentence `φ`: the set consisting of `φ` and the formula `x₀ ≠ x₁`. -/
def morleySeed (φ : L.Sentenceω) : Set (Σ n, L.BoundedFormulaω Empty n) :=
  {⟨0, φ⟩, ⟨2, L.disEq⟩}

theorem morleySeed_def (φ : L.Sentenceω) : morleySeed φ = {⟨0, φ⟩, ⟨2, L.disEq⟩} :=
  (rfl)

@[simp]
theorem mem_morleySeed_iff {φ : L.Sentenceω} {p : Σ n, L.BoundedFormulaω Empty n} :
    p ∈ morleySeed φ ↔ p = ⟨0, φ⟩ ∨ p = ⟨2, L.disEq⟩ :=
  Iff.rfl

/-- **Injective sequences are indiscernible for the Morley seed**: the sentence has no variables,
and `x₀ ≠ x₁` holds at every increasing pair. -/
theorem isIndiscernibleOn_morleySeed (φ : L.Sentenceω) (ha : Function.Injective a) :
    IsIndiscernibleOn a (morleySeed φ) := by
  refine isIndiscernibleOn_insert.2 ⟨isIndiscernibleOn_of_forall_fst_eq_zero a (by simp), ?_⟩
  exact ((isIndiscernibleOn_equal_var (n := 2) ha 0 1).insert_not rfl).mono
    (Set.singleton_subset_iff.2 (Set.mem_insert _ _))

/-- The template of an injective sequence contains `x₀ ≠ x₁`. -/
theorem disEq_mem_templateOf (ha : Function.Injective a) : L.disEq ∈ (L.templateOf a).formulas 2 :=
  fun t ↦ (realize_disEq).2 fun h ↦ absurd (t.injective (ha h)) (by decide)

/-- A sequence realizing on a set containing `x₀ ≠ x₁` a template that declares `x₀ ≠ x₁` true is
injective. -/
theorem EMTemplate.RealizesOn.injective (h : Φ.RealizesOn c Δ) (hΔ : ⟨2, L.disEq⟩ ∈ Δ)
    (hΦ : L.disEq ∈ Φ.formulas 2) : Function.Injective c := by
  intro x y hxy
  by_contra hne
  -- Order the two indices to obtain an increasing pair on which `c` takes equal values.
  wlog hlt : x < y generalizing x y
  · exact this hxy.symm (Ne.symm hne) ((le_of_not_gt hlt).lt_of_ne' hne)
  let t : Fin 2 ↪o I := .ofStrictMono ![x, y] <| Fin.strictMono_iff_lt_succ.2 fun i ↦ by
    simpa [Fin.fin_one_eq_zero i] using hlt
  have := (h.realize_iff hΔ t).2 hΦ
  simp [t, hxy] at this

/-- **Realizing the template of an injective sequence on the Morley seed.** Let `a` be an
injective sequence in a model of `φ`. A sequence `b : I → N` realizing the template of `a` on the
Morley seed of `φ` is injective, and `N` is a model of `φ`. -/
theorem realize_and_injective_of_realizesOn_templateOf_morleySeed {φ : L.Sentenceω}
    (hM : SentenceInf.Realize φ M) (ha : Function.Injective a) {b : I → N}
    (hb : (L.templateOf a).RealizesOn b (morleySeed φ)) :
    SentenceInf.Realize φ N ∧ Function.Injective b :=
  ⟨(hb.realize_sentence_iff (by simp)).2 (mem_templateOf_formulas_zero_iff.2 hM),
    hb.injective (by simp) (disEq_mem_templateOf ha)⟩

/-- **The cardinality bound of the Morley seed.** Let `a` be an injective sequence. If `b : I → N`
realizes the template of `a` on the Morley seed of a sentence, then `#I ≤ #N`. -/
theorem lift_mk_le_of_realizesOn_templateOf_morleySeed {φ : L.Sentenceω}
    (ha : Function.Injective a) {b : I → N} (hb : (L.templateOf a).RealizesOn b (morleySeed φ)) :
    Cardinal.lift.{w'} #I ≤ Cardinal.lift.{u₃} #N :=
  lift_mk_le'.2 ⟨⟨b, hb.injective (by simp) (disEq_mem_templateOf ha)⟩⟩

end MorleySeed

end Language

end FirstOrder

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Equiv
public import Mathlib.Order.Hom.Basic

/-!
# Indiscernible sequences for `Lω₁ω`

A sequence `a : J → M` in a structure `M`, indexed by an ordered type `J`, is indiscernible for a
set `Δ` of `Lω₁ω` formulas when each formula of `Δ`, read as a property of tuples, takes the same
truth value at any two increasing tuples of the sequence. An increasing `n`-tuple from `J` is an
order embedding `Fin n ↪o J`. A formula of arity `n` is an `L.BoundedFormulaω Empty n` with the
tuple in its `n` bound positions, and `Δ` collects formulas of varying arity as a
`Set (Σ n, L.BoundedFormulaω Empty n)`.

Indiscernibility for `Δ` passes to smaller sets of formulas, and to subsequences: precomposing with
an order embedding `K ↪o J` keeps it, and precomposing with an order isomorphism neither gains nor
loses it. Moving the values of the sequence along an isomorphism of structures `M ≃[L] N` neither
gains nor loses it either.

## Main definitions

* `FirstOrder.Language.IsIndiscernibleOn a Δ`: each formula of `Δ` takes the same truth value at
  any two increasing tuples of `a`.
* `FirstOrder.Language.IsIndiscernible L a`: indiscernibility for every formula of every arity.

## Main results

* `FirstOrder.Language.IsIndiscernibleOn.mono`: indiscernibility for `Δ` gives it for every subset
  of `Δ`.
* `FirstOrder.Language.IsIndiscernibleOn.comp_orderEmbedding` and
  `FirstOrder.Language.isIndiscernibleOn_comp_orderIso_iff`: restriction along an order embedding
  and transport along an order isomorphism of index types.
* `FirstOrder.Language.isIndiscernibleOn_equiv_comp_iff`: transport along an isomorphism of
  structures.
-/

public section

universe u v w w' z z'

namespace FirstOrder.Language

variable {L : Language.{u, v}} {J : Type z} {K : Type z'} [LE J] [LE K] {M : Type w}
  [L.Structure M]

/-- A sequence `a : J → M` is **indiscernible** for a set `Δ` of `Lω₁ω` formulas when each formula
of `Δ`, of arity `n`, takes the same truth value at the tuples `a ∘ s` and `a ∘ t` for any two
increasing `n`-tuples `s t : Fin n ↪o J` of indices. -/
def IsIndiscernibleOn (a : J → M) (Δ : Set (Σ n, L.BoundedFormulaω Empty n)) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃ψ : L.BoundedFormulaω Empty n⦄, ⟨n, ψ⟩ ∈ Δ → ∀ s t : Fin n ↪o J,
    ψ.Realize Empty.elim (a ∘ s) ↔ ψ.Realize Empty.elim (a ∘ t)

variable (L) in
/-- A sequence `a : J → M` is **indiscernible** when it is indiscernible for every `Lω₁ω` formula
of every arity. -/
def IsIndiscernible (a : J → M) : Prop :=
  IsIndiscernibleOn a (Set.univ : Set (Σ n, L.BoundedFormulaω Empty n))

/-- Unfolding lemma for `IsIndiscernibleOn`. -/
theorem isIndiscernibleOn_iff {a : J → M} {Δ : Set (Σ n, L.BoundedFormulaω Empty n)} :
    IsIndiscernibleOn a Δ ↔ ∀ ⦃n : ℕ⦄ ⦃ψ : L.BoundedFormulaω Empty n⦄, ⟨n, ψ⟩ ∈ Δ →
      ∀ s t : Fin n ↪o J, ψ.Realize Empty.elim (a ∘ s) ↔ ψ.Realize Empty.elim (a ∘ t) :=
  Iff.rfl

/-- Indiscernibility is indiscernibility for the set of all formulas. -/
theorem isIndiscernible_iff_isIndiscernibleOn_univ {a : J → M} :
    L.IsIndiscernible a ↔
      IsIndiscernibleOn a (Set.univ : Set (Σ n, L.BoundedFormulaω Empty n)) :=
  Iff.rfl

/-- **Monotonicity.** A sequence indiscernible for `Δ` is indiscernible for every subset of `Δ`. -/
theorem IsIndiscernibleOn.mono {a : J → M} {Δ Δ' : Set (Σ n, L.BoundedFormulaω Empty n)}
    (h : IsIndiscernibleOn a Δ) (hΔ : Δ' ⊆ Δ) : IsIndiscernibleOn a Δ' :=
  fun _ _ hψ => h (hΔ hψ)

/-- An indiscernible sequence is indiscernible for every set of formulas. -/
theorem IsIndiscernible.isIndiscernibleOn {a : J → M} (h : L.IsIndiscernible a)
    (Δ : Set (Σ n, L.BoundedFormulaω Empty n)) : IsIndiscernibleOn a Δ :=
  IsIndiscernibleOn.mono h (Set.subset_univ Δ)

/-- **Restriction.** Precomposing a sequence indiscernible for `Δ` with an order embedding of index
types gives a sequence indiscernible for `Δ`. -/
theorem IsIndiscernibleOn.comp_orderEmbedding {a : J → M}
    {Δ : Set (Σ n, L.BoundedFormulaω Empty n)} (h : IsIndiscernibleOn a Δ) (e : K ↪o J) :
    IsIndiscernibleOn (a ∘ e) Δ :=
  fun _ _ hψ s t => h hψ (s.trans e) (t.trans e)

/-- **Transport along an order isomorphism.** Precomposing with an order isomorphism of index
types neither gains nor loses indiscernibility for `Δ`. -/
theorem isIndiscernibleOn_comp_orderIso_iff {a : J → M}
    {Δ : Set (Σ n, L.BoundedFormulaω Empty n)} (e : K ≃o J) :
    IsIndiscernibleOn (a ∘ e) Δ ↔ IsIndiscernibleOn a Δ := by
  refine ⟨fun h => ?_, fun h => h.comp_orderEmbedding e.toOrderEmbedding⟩
  have he : (a ∘ e) ∘ e.symm.toOrderEmbedding = a := funext fun x => by simp
  simpa only [he] using h.comp_orderEmbedding e.symm.toOrderEmbedding

/-- **Transport along an isomorphism of structures.** Moving the values of a sequence along an
isomorphism `M ≃[L] N` neither gains nor loses indiscernibility for `Δ`: the same increasing tuples
of indices are compared on both sides. -/
theorem isIndiscernibleOn_equiv_comp_iff {N : Type w'} [L.Structure N] (e : M ≃[L] N)
    {a : J → M} {Δ : Set (Σ n, L.BoundedFormulaω Empty n)} :
    IsIndiscernibleOn (e ∘ a) Δ ↔ IsIndiscernibleOn a Δ := by
  have hv : (Empty.elim : Empty → N) = e ∘ Empty.elim := funext fun x => x.elim
  simp only [isIndiscernibleOn_iff, hv, Function.comp_assoc,
    StrongHomClass.realize_boundedFormulaInf]

end FirstOrder.Language

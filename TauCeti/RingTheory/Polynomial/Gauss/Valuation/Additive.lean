/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Gauss.Valuation.Splits
public import Mathlib.Algebra.Order.Monoid.WithTop
import TauCeti.RingTheory.Valuation.AddValuation
import Mathlib.Order.MinMax

/-!
# Additive reading of the Gauss valuation

`Polynomial.addGaussValuation` reads the existing multiplicative Gauss valuation through
`AddValuation.toValuation`: products become sums and the order is reversed. Its weighted
coefficients are `v (g.coeff i) + i • ρ`. The lemmas here perform that translation once,
so applications can use coefficient bounds, evaluation and root formulas additively.
The split-polynomial identity `Polynomial.addValuation_eval_add_card_tied_roots` isolates the
correction contributed by roots whose valuation equals that of the evaluation point.

## Main results

* `Polynomial.addGaussValuation`: the additive Gauss valuation, with simp formulas for zero,
  constants, one, the variable, monomials and linear factors.
* `Polynomial.le_addGaussValuation_iff`, `Polynomial.addGaussValuation_le_iff`: weighted
  coefficient bounds and attainment of finite upper bounds.
* `Polynomial.addGaussValuation_mul`, `Polynomial.addGaussValuation_prod`: products become sums.
* `Polynomial.addGaussValuation_le_valuation_eval`: the Gauss bound for evaluation.
* `Polynomial.addGaussValuation_eq_add_sum_roots`,
  `Polynomial.addValuation_eval_eq_add_sum_roots`: split-polynomial root formulas.
* `Polynomial.addValuation_eval_add_card_tied_roots`: the correction from roots tied in valuation.

## Provenance

`Polynomial.addValuation_eval_add_card_tied_roots` adapts `New.Selmer.ellVal_eval_add_card_mul`
in `src/New/Congruences/Selmer/RootsOfUnity.lean` in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC), generalized to split polynomials over arbitrary valued
integral domains and arbitrary linearly ordered additive value monoids with infinity.
-/

public section

namespace Polynomial

section Ring

variable {R Γ : Type*} [Ring R] [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  (v : AddValuation R (WithTop Γ)) (ρ : Γ)

/-- The additive reading of the Gauss valuation at finite radius `ρ`. -/
noncomputable def addGaussValuation (g : R[X]) : WithTop Γ :=
  (g.gaussValuation v.toValuation (.ofAdd (.toDual (ρ : WithTop Γ)))).toAdd.ofDual

/-- Translation to the multiplicative Gauss valuation. -/
theorem addGaussValuation_def (g : R[X]) :
    g.addGaussValuation v ρ =
      (g.gaussValuation v.toValuation (.ofAdd (.toDual (ρ : WithTop Γ)))).toAdd.ofDual := (rfl)

/-- A lower bound for the additive Gauss valuation bounds every weighted coefficient. -/
theorem le_addGaussValuation_iff {g : R[X]} {a : WithTop Γ} :
    a ≤ g.addGaussValuation v ρ ↔ ∀ i, a ≤ v (g.coeff i) + i • (ρ : WithTop Γ) := by
  rw [addGaussValuation_def, ← OrderDual.le_toDual, ← Multiplicative.ofAdd_le,
    ofAdd_toAdd, gaussValuation_le_iff]
  simp only [AddValuation.toValuation_apply, ← ofAdd_nsmul, ← ofAdd_add,
    Multiplicative.ofAdd_le]
  refine forall_congr' fun i ↦ ?_
  rw [← OrderDual.ofDual_le_ofDual, ofDual_add, OrderDual.ofDual_toDual,
    OrderDual.ofDual_toDual]
  -- The order dual inherits natural scalar multiplication from the same additive monoid.
  rfl

/-- The additive Gauss valuation is at most every weighted coefficient. -/
theorem addGaussValuation_le_coeff (g : R[X]) (i : ℕ) :
    g.addGaussValuation v ρ ≤ v (g.coeff i) + i • (ρ : WithTop Γ) :=
  (le_addGaussValuation_iff v ρ).1 le_rfl i

/-- The zero polynomial has infinite additive Gauss valuation. -/
@[simp]
theorem addGaussValuation_zero : (0 : R[X]).addGaussValuation v ρ = ⊤ := by
  rw [addGaussValuation_def, gaussValuation_zero, ofDual_toAdd_zero]

/-- A constant polynomial has the valuation of its coefficient. -/
@[simp]
theorem addGaussValuation_C (a : R) : (C a).addGaussValuation v ρ = v a := by
  rw [addGaussValuation_def, gaussValuation_C, AddValuation.toValuation_apply,
    toAdd_ofAdd, OrderDual.ofDual_toDual]

/-- The polynomial one has additive Gauss valuation zero. -/
@[simp]
theorem addGaussValuation_one : (1 : R[X]).addGaussValuation v ρ = 0 := by
  rw [← C_1, addGaussValuation_C, v.map_one]

/-- A monomial has its weighted coefficient valuation. -/
@[simp]
theorem addGaussValuation_monomial (n : ℕ) (a : R) :
    (monomial n a).addGaussValuation v ρ = v a + n • (ρ : WithTop Γ) := by
  rw [addGaussValuation_def, gaussValuation_monomial, AddValuation.toValuation_apply,
    toAdd_mul, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, ofDual_add,
    OrderDual.ofDual_toDual]
  -- The order dual inherits natural scalar multiplication from the same additive monoid.
  rfl

/-- The variable has additive Gauss valuation equal to the radius. -/
@[simp]
theorem addGaussValuation_X : (X : R[X]).addGaussValuation v ρ = ρ := by
  rw [addGaussValuation_def, gaussValuation_X, toAdd_ofAdd, OrderDual.ofDual_toDual]

/-- A finite upper bound for the additive Gauss valuation is attained by a weighted coefficient. -/
theorem addGaussValuation_le_iff {g : R[X]} {b : Γ} :
    g.addGaussValuation v ρ ≤ b ↔ ∃ i, v (g.coeff i) + i • (ρ : WithTop Γ) ≤ b := by
  refine ⟨fun hb ↦ ?_, fun ⟨i, hi⟩ ↦ (addGaussValuation_le_coeff v ρ g i).trans hi⟩
  have hne : g.gaussValuation v.toValuation (.ofAdd (.toDual (ρ : WithTop Γ))) ≠ 0 := by
    intro hz
    rw [addGaussValuation_def, hz, ofDual_toAdd_zero] at hb
    exact WithTop.not_top_le_coe _ hb
  obtain ⟨i, _, hi⟩ := exists_eq_gaussValuation (v := v.toValuation)
    (r := .ofAdd (.toDual (ρ : WithTop Γ))) (show g ≠ 0 by rintro rfl; simp at hne)
  have hi' := congrArg (fun t : Multiplicative (WithTop Γ)ᵒᵈ ↦ t.toAdd.ofDual) hi
  simp only [AddValuation.toValuation_apply, toAdd_mul, toAdd_pow, toAdd_ofAdd,
    ofDual_add, OrderDual.ofDual_toDual, ← addGaussValuation_def] at hi'
  -- The remaining natural scalar multiplication is inherited unchanged by the order dual.
  exact ⟨i, hi'.symm ▸ hb⟩

/-- The additive Gauss valuation increases with the radius. -/
theorem addGaussValuation_mono {ρ σ : Γ} (h : ρ ≤ σ) (g : R[X]) :
    g.addGaussValuation v ρ ≤ g.addGaussValuation v σ := by
  refine (le_addGaussValuation_iff v σ).2 fun i ↦ ?_
  exact (addGaussValuation_le_coeff v ρ g i).trans
    (add_le_add_right (nsmul_le_nsmul_right (WithTop.coe_le_coe.2 h) i) _)

/-- The additive Gauss valuation turns products into sums. -/
theorem addGaussValuation_mul (g q : R[X]) :
    (g * q).addGaussValuation v ρ = g.addGaussValuation v ρ + q.addGaussValuation v ρ := by
  simp only [addGaussValuation_def, gaussValuation_mul, toAdd_mul, ofDual_add]

/-- A linear factor has additive Gauss valuation `min ρ (v a)`. -/
@[simp]
theorem addGaussValuation_X_sub_C (a : R) :
    (X - C a).addGaussValuation v ρ = min (ρ : WithTop Γ) (v a) := by
  rw [addGaussValuation_def, gaussValuation_X_sub_C,
    Monotone.map_max (f := Multiplicative.toAdd (α := (WithTop Γ)ᵒᵈ))
      (fun _ _ h ↦ Multiplicative.toAdd_mono h), ofDual_max,
    AddValuation.toValuation_apply, toAdd_ofAdd, toAdd_ofAdd,
    OrderDual.ofDual_toDual, OrderDual.ofDual_toDual]

/-- Evaluation at a point of valuation at least `ρ` bounds the additive Gauss valuation. -/
theorem addGaussValuation_le_valuation_eval (g : R[X]) {x : R}
    (hx : (ρ : WithTop Γ) ≤ v x) : g.addGaussValuation v ρ ≤ v (g.eval x) := by
  rw [addGaussValuation_def, ← OrderDual.toDual_le, ← Multiplicative.ofAdd_le,
    ofAdd_toAdd, ← AddValuation.toValuation_apply]
  apply valuation_eval_le_gaussValuation
  simpa only [AddValuation.toValuation_apply, Multiplicative.ofAdd_le,
    OrderDual.toDual_le_toDual] using hx

end Ring

section CommRing

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  (v : AddValuation R (WithTop Γ)) (ρ : Γ)

/-- The additive Gauss valuation of a multiset product is the sum of the valuations. -/
theorem addGaussValuation_multiset_prod (s : Multiset R[X]) :
    s.prod.addGaussValuation v ρ = (s.map fun g ↦ g.addGaussValuation v ρ).sum := by
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.prod_zero, addGaussValuation_one, Multiset.map_zero,
      Multiset.sum_zero]
  | cons g s ih => simp [addGaussValuation_mul, ih]

/-- The additive Gauss valuation of a finite product is the sum of the valuations. -/
theorem addGaussValuation_prod {ι : Type*} (s : Finset ι) (g : ι → R[X]) :
    (∏ i ∈ s, g i).addGaussValuation v ρ = ∑ i ∈ s, (g i).addGaussValuation v ρ := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, addGaussValuation_one, Finset.sum_empty]
  | cons i s hi ih => rw [Finset.prod_cons, Finset.sum_cons, addGaussValuation_mul, ih]

variable [IsDomain R]

/-- For a split polynomial, the additive Gauss valuation is the leading coefficient valuation
plus the sum of the root valuations truncated above at `ρ`. -/
theorem addGaussValuation_eq_add_sum_roots (g : R[X]) (hg : g.Splits) :
    g.addGaussValuation v ρ =
      v g.leadingCoeff + (g.roots.map fun a ↦ min (ρ : WithTop Γ) (v a)).sum := by
  conv_lhs => rw [hg.eq_prod_roots]
  rw [addGaussValuation_mul, addGaussValuation_C, addGaussValuation_multiset_prod,
    Multiset.map_map]
  simp only [Function.comp_def, addGaussValuation_X_sub_C]

end CommRing

section Split

variable {R Γ₀ : Type*} [CommRing R] [IsDomain R]
  [LinearOrderedAddCommMonoidWithTop Γ₀] (v : AddValuation R Γ₀)

/-- Evaluation of a split polynomial is the leading coefficient valuation plus the sum of
the valuations of the distances to its roots, counted with multiplicity. -/
theorem addValuation_eval_eq_add_sum_roots (g : R[X]) (hg : g.Splits) (x : R) :
    v (g.eval x) = v g.leadingCoeff + (g.roots.map fun a ↦ v (x - a)).sum := by
  conv_lhs => rw [hg.eq_prod_roots]
  simp only [eval_mul, eval_C, eval_multiset_prod, v.map_mul, v.map_multiset_prod,
    Multiset.map_map, Function.comp_def, eval_sub, eval_X]

/-- For a split polynomial evaluated at a point of valuation `r`, the correction to
the sum of root valuations truncated at `r` comes from roots of valuation exactly `r`. -/
theorem addValuation_eval_add_card_tied_roots (g : R[X]) (hg : g.Splits) {r : Γ₀} {y : R}
    (hy : v y = r) :
    v (g.eval y) + (g.roots.filter fun a ↦ v a = r).card • r =
      v g.leadingCoeff + (g.roots.map fun a ↦ min r (v a)).sum +
        ((g.roots.filter fun a ↦ v a = r).map fun a ↦ v (y - a)).sum := by
  classical
  let R := g.roots.filter fun a ↦ v a = r
  let R' := g.roots.filter fun a ↦ ¬v a = r
  have hsplit : g.roots = R + R' := (Multiset.filter_add_not _ _).symm
  have hother : ∀ a ∈ R', v (y - a) = min r (v a) := by
    intro a ha
    rw [sub_eq_add_neg, v.map_add_of_distinct_val (by
      rw [hy, v.map_neg]
      exact Ne.symm (Multiset.mem_filter.1 ha).2), hy, v.map_neg]
  have hsame : ∀ a ∈ R, min r (v a) = r := by
    intro a ha
    rw [(Multiset.mem_filter.1 ha).2, min_self]
  have heval : v (g.eval y) =
      v g.leadingCoeff + (g.roots.map fun a ↦ v (y - a)).sum :=
    g.addValuation_eval_eq_add_sum_roots v hg y
  have heval' : v (g.eval y) = v g.leadingCoeff +
      ((R.map fun a ↦ v (y - a)).sum + (R'.map fun a ↦ min r (v a)).sum) := by
    conv_lhs => rw [heval, hsplit]
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_congr rfl hother]
  have hgauss : (g.roots.map fun a ↦ min r (v a)).sum =
      R.card • r + (R'.map fun a ↦ min r (v a)).sum := by
    conv_lhs => rw [hsplit]
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_congr rfl hsame,
      Multiset.map_const', Multiset.sum_replicate]
  rw [heval', hgauss]
  ac_rfl

end Split

end Polynomial

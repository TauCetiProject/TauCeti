/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.GaussValuation
public import Mathlib.Algebra.Order.Monoid.WithTop
import TauCeti.RingTheory.Valuation.Polynomial

/-!
# Additive reading of the Gauss valuation

`Polynomial.addGaussValuation` reads the existing multiplicative Gauss valuation through
`AddValuation.toValuation`: products become sums and the order is reversed. Its weighted
coefficients are `v (g.coeff i) + i • ρ`. The lemmas here perform that translation once,
so applications can use coefficient bounds, evaluation and root formulas additively.
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
  -- The equivalence reverses order and reads multiplication and powers as addition and nsmul.
  exact gaussValuation_le_iff v.toValuation (.ofAdd (.toDual (ρ : WithTop Γ)))

/-- The additive Gauss valuation is at most every weighted coefficient. -/
theorem addGaussValuation_le_coeff (g : R[X]) (i : ℕ) :
    g.addGaussValuation v ρ ≤ v (g.coeff i) + i • (ρ : WithTop Γ) :=
  (le_addGaussValuation_iff v ρ).1 le_rfl i

/-- The zero polynomial has infinite additive Gauss valuation. -/
@[simp]
theorem addGaussValuation_zero : (0 : R[X]).addGaussValuation v ρ = ⊤ := by
  rw [addGaussValuation_def, gaussValuation_zero]
  rfl

/-- A finite upper bound for the additive Gauss valuation is attained by a weighted coefficient. -/
theorem addGaussValuation_le_iff {g : R[X]} {b : Γ} :
    g.addGaussValuation v ρ ≤ b ↔ ∃ i, v (g.coeff i) + i • (ρ : WithTop Γ) ≤ b := by
  refine ⟨fun hb ↦ ?_, fun ⟨i, hi⟩ ↦ (addGaussValuation_le_coeff v ρ g i).trans hi⟩
  have hne : g.gaussValuation v.toValuation (.ofAdd (.toDual (ρ : WithTop Γ))) ≠ 0 := by
    intro hz
    rw [addGaussValuation_def, hz] at hb
    exact WithTop.not_top_le_coe _ hb
  obtain ⟨i, _, hi⟩ := exists_eq_gaussValuation _ _ hne
  -- Apply the inverse type tags to the attaining weighted coefficient.
  have hi' := congrArg (fun t : Multiplicative (WithTop Γ)ᵒᵈ ↦ t.toAdd.ofDual) hi
  have hi'' : v (g.coeff i) + i • (ρ : WithTop Γ) = g.addGaussValuation v ρ := hi'
  exact ⟨i, hi''.symm ▸ hb⟩

/-- The additive Gauss valuation increases with the radius. -/
theorem addGaussValuation_mono {ρ σ : Γ} (h : ρ ≤ σ) (g : R[X]) :
    g.addGaussValuation v ρ ≤ g.addGaussValuation v σ := by
  refine (le_addGaussValuation_iff v σ).2 fun i ↦ ?_
  exact (addGaussValuation_le_coeff v ρ g i).trans
    (add_le_add_right (nsmul_le_nsmul_right (WithTop.coe_le_coe.2 h) i) _)

/-- The additive Gauss valuation turns products into sums. -/
theorem addGaussValuation_mul (g q : R[X]) :
    (g * q).addGaussValuation v ρ = g.addGaussValuation v ρ + q.addGaussValuation v ρ := by
  simp only [addGaussValuation_def, gaussValuation_mul]
  rfl

/-- A linear factor has additive Gauss valuation `min ρ (v a)`. -/
@[simp]
theorem addGaussValuation_X_sub_C (a : R) :
    (X - C a).addGaussValuation v ρ = min (ρ : WithTop Γ) (v a) := by
  rw [addGaussValuation_def, gaussValuation_X_sub_C]
  rfl

/-- Evaluation at a point of valuation at least `ρ` bounds the additive Gauss valuation. -/
theorem addGaussValuation_le_valuation_eval (g : R[X]) {x : R}
    (hx : (ρ : WithTop Γ) ≤ v x) : g.addGaussValuation v ρ ≤ v (g.eval x) := by
  -- Order reversal turns the multiplicative evaluation bound into this lower bound.
  exact valuation_eval_le_gaussValuation v.toValuation
    (.ofAdd (.toDual (ρ : WithTop Γ))) g hx

end Ring

section CommRing

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  (v : AddValuation R (WithTop Γ)) (ρ : Γ)

/-- The additive Gauss valuation of a multiset product is the sum of the valuations. -/
theorem addGaussValuation_multiset_prod (s : Multiset R[X]) :
    s.prod.addGaussValuation v ρ = (s.map fun g ↦ g.addGaussValuation v ρ).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [addGaussValuation_def]
  | cons g s ih => simp [addGaussValuation_mul, ih]

/-- The additive Gauss valuation of a finite product is the sum of the valuations. -/
theorem addGaussValuation_prod {ι : Type*} (s : Finset ι) (g : ι → R[X]) :
    (∏ i ∈ s, g i).addGaussValuation v ρ = ∑ i ∈ s, (g i).addGaussValuation v ρ := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [addGaussValuation_def]
  | cons i s hi ih => rw [Finset.prod_cons, Finset.sum_cons, addGaussValuation_mul, ih]

variable [IsDomain R]

/-- For a split polynomial, the additive Gauss valuation is the leading coefficient valuation
plus the sum of the root valuations truncated above at `ρ`. -/
theorem addGaussValuation_eq_add_sum_roots (g : R[X]) (hg : g.Splits) :
    g.addGaussValuation v ρ =
      v g.leadingCoeff + (g.roots.map fun a ↦ min (ρ : WithTop Γ) (v a)).sum := by
  rw [addGaussValuation_def, gaussValuation_eq_mul_prod_roots _ _ hg]
  -- The inverse type tags turn the root product into an additive sum.
  rfl

/-- Evaluation of a split polynomial is the leading coefficient valuation plus the sum of
the valuations of the distances to its roots, counted with multiplicity. -/
theorem addValuation_eval_eq_add_sum_roots (g : R[X]) (hg : g.Splits) (x : R) :
    v (g.eval x) = v g.leadingCoeff + (g.roots.map fun a ↦ v (x - a)).sum := by
  -- Translate the existing root-product formula through the valuation equivalence.
  exact valuation_eval_eq_mul_prod_roots v.toValuation g hg x

end CommRing

end Polynomial

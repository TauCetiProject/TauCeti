/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Polynomial evaluation into ideal powers

A lower bound on the degree in selected variables gives a lower bound on the ideal power
containing the value of the polynomial when those variables take values in the ideal.

## Main results

* `MvPolynomial.aeval_monomial_mem_pow`: substituting elements of an ideal `I` into a unit monomial
  of total degree at least `d` produces an element of `I ^ d`.
* `MvPolynomial.aeval_mem_pow_of_le_weight`: each monomial need only have degree at least `d`
  in the selected variables; the values at the other variables are arbitrary.

## References

* L. Alpöge and L. Sernau, grh-lean (<https://github.com/lsernau/grh-lean>, Apache 2.0,
  Copyright 2026 Anthropic, PBC), `src/Lib/General/Algebra/MultivariatePolynomials.lean`
  (`New.exists_le_weight_of_mem_vanishingIdeal_pow`).
-/

public section

namespace MvPolynomial

/-- If `φ u ∈ I` for every variable `u`, then `aeval φ (monomial γ 1)` lies in `I ^ d` for every
`d ≤ γ.degree`. -/
theorem aeval_monomial_mem_pow {R A σ : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    {I : Ideal A} {φ : σ → A} (hφ : ∀ u, φ u ∈ I) {d : ℕ} {γ : σ →₀ ℕ} (hγ : d ≤ γ.degree) :
    aeval φ (monomial γ (1 : R)) ∈ I ^ d := by
  rcases subsingleton_or_nontrivial R with _ | _
  · simp [Subsingleton.elim (1 : R) 0]
  have h_vars : idealOfVars σ R ≤ I.comap (aeval φ) := by
    rw [← Ideal.map_le_iff_le_comap, map_aeval_idealOfVars, Ideal.span_le]
    rintro _ ⟨u, rfl⟩
    exact hφ u
  exact Ideal.le_comap_pow (aeval φ) d
    (Ideal.pow_right_mono h_vars d ((monomial_mem_pow_idealOfVars_iff d γ one_ne_zero).2 hγ))

/-- If each monomial of `p` has degree at least `d` in the variables selected by `D`, and
those variables take values in `I`, then `aeval φ p` lies in `I ^ d`. -/
theorem aeval_mem_pow_of_le_weight {R A σ : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    {p : MvPolynomial σ R} {φ : σ → A} {I : Ideal A} (D : σ → Prop) [DecidablePred D]
    (hφ : ∀ u, D u → φ u ∈ I) {d : ℕ}
    (hp : ∀ β ∈ p.support, d ≤ Finsupp.weight (fun u ↦ if D u then 1 else 0) β) :
    aeval φ p ∈ I ^ d := by
  rw [p.as_sum, aeval_sum]
  refine Ideal.sum_mem _ fun β hβ ↦ ?_
  rw [aeval_monomial]
  apply Ideal.mul_mem_left
  have h := Ideal.prod_mem_prod (s := β.support) (I := fun u ↦ I ^ (if D u then β u else 0))
    (x := fun u ↦ φ u ^ β u) (fun u _ ↦ by
      by_cases hu : D u
      · simpa only [ite_eq_left hu] using Ideal.pow_mem_pow (hφ u hu) (β u)
      · simp [hu])
  rw [Finset.prod_pow_eq_pow_sum] at h
  have hd : d ≤ ∑ u ∈ β.support, if D u then β u else 0 := by
    simpa [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, mul_ite] using hp β hβ
  exact Ideal.pow_le_pow_right hd h

end MvPolynomial

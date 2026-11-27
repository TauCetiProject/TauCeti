/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal
import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Evaluation of monomials into ideal powers

If a family `φ : σ → A` of elements of an `R`-algebra `A` takes values in an ideal `I : Ideal A`,
then evaluating any monomial of total degree at least `d` at `φ` lands in `I ^ d`.

## Main results

* `MvPolynomial.aeval_monomial_mem_pow`: substituting elements of an ideal `I` into a unit monomial
  of total degree at least `d` produces an element of `I ^ d`.

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

end MvPolynomial

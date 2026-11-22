/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Coordinate expansion of Kähler differentials for multivariate polynomials

Mathlib's `KaehlerDifferential.mvPolynomialBasis` identifies `Ω[MvPolynomial σ R⁄R]` with the free
module on `{D (X i) | i : σ}` with coordinates given by `MvPolynomial.pderiv`. This file records the
resulting coordinate expansion of `KaehlerDifferential.D R (MvPolynomial σ R) p` as a finite sum
over `p.vars` (valid for arbitrary, possibly infinite variable sets `σ`), together with its
specialization to a `[Fintype σ]` sum, mirroring `KaehlerDifferential.polynomial_D_apply`.
Through the universal property of `Ω[MvPolynomial σ R⁄R]`, the same expansion holds for every
`R`-linear derivation on `MvPolynomial σ R`.

## Main results

* `KaehlerDifferential.mvPolynomial_D_apply_eq_sum_vars`:
  `D R (MvPolynomial σ R) p = ∑ i ∈ p.vars, MvPolynomial.pderiv i p • D R (MvPolynomial σ R) (X i)`.
* `KaehlerDifferential.mvPolynomial_D_apply`: the corresponding sum over `i : σ` when `[Fintype σ]`.
* `MvPolynomial.derivation_apply_eq_sum_vars`: every derivation `D` on `MvPolynomial σ R` satisfies
  `D p = ∑ i ∈ p.vars, MvPolynomial.pderiv i p • D (X i)`.
-/

public section

namespace KaehlerDifferential

variable {R σ : Type*} [CommRing R]

/-- Over a multivariate polynomial ring `MvPolynomial σ R` (with `σ` possibly infinite), the
universal Kähler differential of `p` is the finite sum over `p.vars` of its formal partial
derivatives times `D (X i)`. -/
theorem mvPolynomial_D_apply_eq_sum_vars (p : MvPolynomial σ R) :
    KaehlerDifferential.D R (MvPolynomial σ R) p =
      ∑ i ∈ p.vars,
        MvPolynomial.pderiv i p •
          KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i) := by
  classical
  conv_lhs =>
    rw [← (KaehlerDifferential.mvPolynomialBasis R σ).linearCombination_repr
      (KaehlerDifferential.D R (MvPolynomial σ R) p)]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have hsub : ((KaehlerDifferential.mvPolynomialBasis R σ).repr
      (KaehlerDifferential.D R (MvPolynomial σ R) p)).support ⊆ p.vars := by
    intro i hi
    rw [Finsupp.mem_support_iff, KaehlerDifferential.mvPolynomialBasis_repr_apply] at hi
    by_contra hni
    exact hi (MvPolynomial.pderiv_eq_zero_of_notMem_vars hni)
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [KaehlerDifferential.mvPolynomialBasis_repr_apply,
      KaehlerDifferential.mvPolynomialBasis_apply]
  · intro i _ hni
    rw [Finsupp.notMem_support_iff.mp hni, zero_smul]

/-- Over a multivariate polynomial ring on a finite variable set `σ`, the universal Kähler
differential of `p` is `∑ i : σ, MvPolynomial.pderiv i p • D (X i)`. -/
theorem mvPolynomial_D_apply [Fintype σ] (p : MvPolynomial σ R) :
    KaehlerDifferential.D R (MvPolynomial σ R) p =
      ∑ i : σ,
        MvPolynomial.pderiv i p •
          KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i) := by
  classical
  rw [mvPolynomial_D_apply_eq_sum_vars]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ ?_
  rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hi, zero_smul]

end KaehlerDifferential

namespace MvPolynomial

variable {R σ M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

/-- Every `R`-linear derivation `D` on `MvPolynomial σ R` (with `σ` possibly infinite) is
determined by its values on the variables of `p`:
`D p = ∑ i ∈ p.vars, pderiv i p • D (X i)`. -/
theorem derivation_apply_eq_sum_vars (D : Derivation R (MvPolynomial σ R) M)
    (p : MvPolynomial σ R) : D p = ∑ i ∈ p.vars, pderiv i p • D (X i) := by
  rw [← D.liftKaehlerDifferential_comp_D, KaehlerDifferential.mvPolynomial_D_apply_eq_sum_vars]
  simp

end MvPolynomial

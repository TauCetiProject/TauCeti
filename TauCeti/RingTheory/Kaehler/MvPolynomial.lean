/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Kaehler.Basic
import TauCeti.Algebra.MvPolynomial.PDeriv

/-!
# Coordinate expansion of Kähler differentials for multivariate polynomials

This file records the coordinate expansion of `KaehlerDifferential.D R (MvPolynomial σ R) p` as a
finite sum over `p.vars` (valid for arbitrary, possibly infinite variable sets `σ`), the special
case `D = KaehlerDifferential.D` of `MvPolynomial.derivation_apply_eq_sum_vars`, together with its
specialization to a `[Fintype σ]` sum, mirroring `KaehlerDifferential.polynomial_D_apply`.

## Main results

* `KaehlerDifferential.mvPolynomial_D_apply_eq_sum_vars`:
  `D R (MvPolynomial σ R) p = ∑ i ∈ p.vars, MvPolynomial.pderiv i p • D R (MvPolynomial σ R) (X i)`.
* `KaehlerDifferential.mvPolynomial_D_apply`: the corresponding sum over `i : σ` when `[Fintype σ]`.
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
          KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i) :=
  MvPolynomial.derivation_apply_eq_sum_vars _ p

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

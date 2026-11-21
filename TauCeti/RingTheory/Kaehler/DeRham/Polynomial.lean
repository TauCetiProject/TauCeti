/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import TauCeti.RingTheory.Kaehler.DeRham.Basic
import TauCeti.RingTheory.Kaehler.MvPolynomial

/-!
# Algebraic de Rham coordinate formulas over multivariate polynomial algebras

Over a multivariate polynomial ring `MvPolynomial σ R` (for an arbitrary, possibly infinite
variable set `σ`), the universal Kähler differential `D R (MvPolynomial σ R) p` expands in terms
of formal partial derivatives (`KaehlerDifferential.mvPolynomial_D_apply_eq_sum_vars`). This file
transfers those coordinate formulas to the algebraic exterior derivative
`TauCeti.KaehlerDeRham.extDeriv` on `ExteriorAlgebra (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R]`.

## Main results

* `TauCeti.KaehlerDeRham.extDeriv_algebraMap_mvPolynomial_eq_sum_vars`:
  `d p = ∑ i ∈ p.vars, MvPolynomial.pderiv i p • ι (D (X i))` for arbitrary `σ`.
* `TauCeti.KaehlerDeRham.extDeriv_algebraMap_mvPolynomial`:
  `d p = ∑ i : σ, MvPolynomial.pderiv i p • ι (D (X i))` when `[Fintype σ]`.
* `TauCeti.KaehlerDeRham.extDeriv_smul_eq_sum_vars_of_extDeriv_eq_zero`:
  for any closed form `x` (`extDeriv R (MvPolynomial σ R) x = 0`),
  `d (p • x) = ∑ j ∈ p.vars, MvPolynomial.pderiv j p • (ι (D (X j)) * x)`.
-/

public section

namespace TauCeti.KaehlerDeRham

variable {R σ : Type*} [CommRing R]

/-- Over a multivariate polynomial ring `MvPolynomial σ R` (with `σ` possibly infinite), the
algebraic exterior derivative of a polynomial `p` is the finite sum over `p.vars` of its formal
partial derivatives wedged with the coordinate differentials `D (X i)`. -/
theorem extDeriv_algebraMap_mvPolynomial_eq_sum_vars (p : MvPolynomial σ R) :
    extDeriv R (MvPolynomial σ R)
        (algebraMap (MvPolynomial σ R) (ExteriorAlgebra (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R])
          p) =
      ∑ i ∈ p.vars,
        MvPolynomial.pderiv i p •
          ExteriorAlgebra.ι (MvPolynomial σ R)
            (KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i)) := by
  rw [extDeriv_algebraMap, KaehlerDifferential.mvPolynomial_D_apply_eq_sum_vars, map_sum]
  simp only [LinearMap.map_smul]

/-- Over a multivariate polynomial ring on a finite variable set `σ`, the exterior derivative of `p`
is `∑ i : σ, MvPolynomial.pderiv i p • ι (D (X i))`. -/
theorem extDeriv_algebraMap_mvPolynomial [Fintype σ] (p : MvPolynomial σ R) :
    extDeriv R (MvPolynomial σ R)
        (algebraMap (MvPolynomial σ R) (ExteriorAlgebra (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R])
          p) =
      ∑ i : σ,
        MvPolynomial.pderiv i p •
          ExteriorAlgebra.ι (MvPolynomial σ R)
            (KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i)) := by
  rw [extDeriv_algebraMap, KaehlerDifferential.mvPolynomial_D_apply, map_sum]
  simp only [LinearMap.map_smul]

/-- Coordinate formula for `extDeriv` on `p • x` for any closed form `x`
(`extDeriv R (MvPolynomial σ R) x = 0`) over `MvPolynomial σ R`, valid without finiteness
hypotheses on `σ`. -/
theorem extDeriv_smul_eq_sum_vars_of_extDeriv_eq_zero (p : MvPolynomial σ R)
    {x : ExteriorAlgebra (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R]}
    (hx : extDeriv R (MvPolynomial σ R) x = 0) :
    extDeriv R (MvPolynomial σ R) (p • x) =
      ∑ j ∈ p.vars,
        MvPolynomial.pderiv j p •
          (ExteriorAlgebra.ι (MvPolynomial σ R)
              (KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X j)) * x) := by
  rw [extDeriv_smul, hx, smul_zero, add_zero, ← extDeriv_algebraMap,
    extDeriv_algebraMap_mvPolynomial_eq_sum_vars, Finset.sum_mul]
  simp only [smul_mul_assoc]

end TauCeti.KaehlerDeRham

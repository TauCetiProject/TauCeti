/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Coleman
import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Spectrum
import TauCeti.Analysis.Polynomial.Coleman.Coprime

/-!
# Coprime polynomial factors of the Fredholm series and invertibility

Let `u` be a row-compact endomorphism of a Banach module with property (Pr) over a complete
ultrametric normed ring `R` with `‖1‖ = 1` and Tate scalars, and let `Q` be a polynomial whose
leading coefficient is a unit. Write `Q* = Q.reverse` for its reversal. Then `Q*(u)` is invertible
exactly when `Q` and the Fredholm series `det (1 - T u)` are coprime in the ring of entire series
(`ContinuousLinearMap.IsPrCompact.isUnit_aeval_reverse_iff`).

If `c` inverts the leading coefficient of `Q`, the polynomial `B = 1 - c Q*` vanishes at `0`, and
`1 - B(u) = c Q*(u)`. Since `B(u)` is row compact, `1 - B(u)` is invertible exactly when its
Fredholm determinant `det (1 - B(u))` is a unit. By polynomial spectral mapping that determinant is
the value at `T = 1` of Coleman's transform of `det (1 - T u)` along `B`, which is a unit exactly
when `Q` and `det (1 - T u)` are coprime
(`Polynomial.isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff`).

For `Q = X - a` this recovers the invertibility of `1 - a u` exactly when `det (1 - T u)` takes a
unit value at `a`. The criterion concerns coprimality with the whole Fredholm series, and hence
invertibility on all of `M`: if `Q` divides `det (1 - T u)` and is not a unit of the ring of entire
series, then `Q*(u)` is not invertible.

## Main results

* `ContinuousLinearMap.IsPrCompact.isUnit_aeval_reverse_iff`: `Q*(u)` is invertible exactly when
  `Q` and `det (1 - T u)` are coprime entire series.
* `ContinuousLinearMap.IsRowCompact.isUnit_aeval_reverse_iff`: the same criterion on a model space
  `C₀(I, R)`, for the principal-minor series of the matrix of `u`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A4.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.2.
-/

public section

open Polynomial
open scoped ZeroAtInfty

open PowerSeries (IsEntire)

namespace ContinuousLinearMap

variable {R M : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [ContinuousConstSMul R M]

/-- **Coprime polynomial factors and invertibility.** Let `u` be a row-compact endomorphism of a
module with property (Pr) and `Q` a polynomial with invertible leading coefficient. Then `Q*(u)`,
for the reversal `Q* = Q.reverse`, is invertible exactly when `Q` and the Fredholm series
`det (1 - T u)` are coprime in the ring of entire series. -/
theorem IsPrCompact.isUnit_aeval_reverse_iff {u : M →L[R] M} (hu : u.IsPrCompact) {Q : R[X]}
    (hQ : IsUnit Q.leadingCoeff) :
    IsUnit (Polynomial.aeval u Q.reverse) ↔
      IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
        ⟨u.charPowerSeries, IsEntire.mem_subring.mpr hu.isEntire_charPowerSeries⟩ := by
  obtain ⟨c, hc⟩ := hQ.exists_left_inv
  have hB0 := coeff_zero_one_sub_C_mul_reverse hc
  -- `1 - B(u) = c • Q*(u)` for `B = 1 - c Q*`, and scaling by the unit `c` preserves invertibility
  have hBu : IsUnit (1 - Polynomial.aeval u (1 - C c * Q.reverse)) ↔
      IsUnit (Polynomial.aeval u Q.reverse) := by
    have h : 1 - Polynomial.aeval u (1 - C c * Q.reverse) =
        (IsUnit.of_mul_eq_one _ hc).unit • Polynomial.aeval u Q.reverse := by
      simp [Units.smul_def, Algebra.smul_def]
    rw [h, isUnit_smul_iff]
  calc IsUnit (Polynomial.aeval u Q.reverse)
      ↔ IsUnit (1 - Polynomial.aeval u (1 - C c * Q.reverse)) := hBu.symm
    _ ↔ IsUnit ((Polynomial.aeval u (1 - C c * Q.reverse)).charPowerSeries.evalAt (1 : R)) := by
      simpa only [one_smul] using (hu.aeval hB0).isUnit_one_sub_smul_iff (a := 1)
    _ ↔ IsUnit (((1 - C c * Q.reverse).colemanDSeries u.charPowerSeries).evalAt (1 : R)) := by
      rw [hu.charPowerSeries_aeval hB0]
    _ ↔ _ := isUnit_evalAt_one_colemanDSeries_one_sub_C_mul_reverse_iff hc
      hu.isEntire_charPowerSeries u.constantCoeff_charPowerSeries

/-- **Coprime polynomial factors and invertibility on model spaces.** For a row-compact
endomorphism `u` of `C₀(I, R)` and a polynomial `Q` with invertible leading coefficient, `Q*(u)` is
invertible exactly when `Q` and the principal-minor series `det (1 - T u)` are coprime in the ring
of entire series. -/
theorem IsRowCompact.isUnit_aeval_reverse_iff {I : Type*} [TopologicalSpace I] [DiscreteTopology I]
    [DecidableEq I] {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) {Q : R[X]}
    (hQ : IsUnit Q.leadingCoeff) :
    IsUnit (Polynomial.aeval u Q.reverse) ↔
      IsCoprime (⟨Q, IsEntire.mem_subring.mpr (PowerSeries.isEntire_coe Q)⟩ : IsEntire.subring R)
        ⟨u.matrixCoeff.charPowerSeries, IsEntire.mem_subring.mpr hu.isEntire_charPowerSeries⟩ := by
  have hu' := isPrCompact_iff_isRowCompact.2 hu
  convert hu'.isUnit_aeval_reverse_iff hQ using 3
  exact hu.charPowerSeries_eq_charPowerSeries_matrixCoeff.symm

end ContinuousLinearMap

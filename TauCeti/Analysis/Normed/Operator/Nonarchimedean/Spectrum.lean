/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.FredholmDet
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Resolvent

/-!
# Invertibility and the nonzero spectrum of a row-compact operator

Let `R` be a complete ultrametric normed commutative ring with Tate scalars, `I` a discrete
index type, and `u` a row-compact endomorphism of the model space `C₀(I, R)` with Fredholm
series `H_u(T) = det (1 - T u)`, the principal-minor series `u.matrixCoeff.charPowerSeries`.
The Fredholm series detects exactly which operators `1 - a • u` are invertible in the algebra
of continuous endomorphisms:

`IsUnit (1 - a • u) ↔ IsUnit (H_u(a))`
(`ContinuousLinearMap.IsRowCompact.isUnit_one_sub_smul_iff`).

The resolvent `V(a)` supplies the inverse when `H_u(a)` is a unit, and multiplicativity of the
Fredholm determinant gives the converse. In terms of the spectrum of `u` over `R`, the inverse
`r⁻¹` of a unit `r` lies in the spectrum exactly when `H_u(r)` is not a unit
(`ContinuousLinearMap.IsRowCompact.inv_mem_spectrum_iff`). Over coefficient rings with
nilpotents this is a condition on units, not on vanishing.

Over a complete nontrivially normed ultrametric field `K` it becomes Serre's description of the
nonzero spectrum: for `μ ≠ 0`,

`μ ∈ spectrum K u ↔ H_u(μ⁻¹) = 0`
(`ContinuousLinearMap.IsRowCompact.mem_spectrum_iff_evalAt_inv_eq_zero`).

Since `H_u(0) = 1`, every zero `a` of `H_u` is nonzero, and the zeros of `H_u` are exactly the
inverses of the nonzero spectral values
(`ContinuousLinearMap.IsRowCompact.evalAt_charPowerSeries_eq_zero_iff`). Nothing is asserted
about `0 ∈ spectrum K u`, which the Fredholm series does not see.

## Main results

* `ContinuousLinearMap.IsRowCompact.isUnit_one_sub_smul_iff`: `1 - a • u` is invertible if and
  only if `H_u(a)` is a unit.
* `ContinuousLinearMap.IsRowCompact.isUnit_one_sub_iff`: `1 - u` is invertible if and only if
  the Fredholm determinant `det (1 - u)` is a unit.
* `ContinuousLinearMap.IsRowCompact.mem_spectrum_iff_evalAt_inv_eq_zero`: over a field, a
  nonzero `μ` lies in the spectrum of `u` if and only if `H_u(μ⁻¹) = 0`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§5–6.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A.
-/

public section

open scoped ZeroAtInfty

variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I] [DecidableEq I]

namespace ContinuousLinearMap

section Ring

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  [TauCeti.NormedRing.IsTate R]

/-- **Invertibility and the Fredholm series.** For a row-compact endomorphism `u` of `C₀(I, R)`,
the operator `1 - a • u` is invertible if and only if the value `H_u(a)` of the Fredholm series
`det (1 - T u)` is a unit of `R`. -/
theorem IsRowCompact.isUnit_one_sub_smul_iff {u : C₀(I, R) →L[R] C₀(I, R)}
    (hu : u.IsRowCompact) {a : R} :
    IsUnit (1 - a • u) ↔ IsUnit (u.matrixCoeff.charPowerSeries.evalAt a) :=
  ⟨hu.isUnit_evalAt_charPowerSeries_of_isUnit_one_sub_smul, hu.isUnit_one_sub_smul⟩

/-- **Invertibility and the Fredholm determinant.** For a row-compact endomorphism `u` of
`C₀(I, R)`, the operator `1 - u` is invertible if and only if the Fredholm determinant
`det (1 - u)` is a unit of `R`. -/
theorem IsRowCompact.isUnit_one_sub_iff {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact) :
    IsUnit (1 - u) ↔ IsUnit u.fredholmDet := by
  simpa [fredholmDet_def] using hu.isUnit_one_sub_smul_iff (a := 1)

/-- **Unit spectral values.** For a row-compact endomorphism `u` of `C₀(I, R)` and a unit `r` of
`R`, the inverse `r⁻¹` lies in the spectrum of `u` if and only if the value `H_u(r)` of the
Fredholm series is not a unit of `R`. -/
theorem IsRowCompact.inv_mem_spectrum_iff {u : C₀(I, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    {r : Rˣ} :
    ((r⁻¹ : Rˣ) : R) ∈ spectrum R u ↔ ¬IsUnit (u.matrixCoeff.charPowerSeries.evalAt (r : R)) := by
  rw [← spectrum.smul_mem_smul_iff (r := r)]
  simp only [Units.smul_def, smul_eq_mul, Units.mul_inv]
  rw [spectrum.mem_iff, map_one, hu.isUnit_one_sub_smul_iff]

end Ring

section Field

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The nonzero spectrum of a row-compact operator.** For a row-compact endomorphism `u` of
`C₀(I, K)` over a complete ultrametric field and `μ ≠ 0`, `μ` lies in the spectrum of `u` if and
only if `μ⁻¹` is a zero of the Fredholm series `det (1 - T u)`. -/
theorem IsRowCompact.mem_spectrum_iff_evalAt_inv_eq_zero {u : C₀(I, K) →L[K] C₀(I, K)}
    (hu : u.IsRowCompact) {μ : K} (hμ : μ ≠ 0) :
    μ ∈ spectrum K u ↔ u.matrixCoeff.charPowerSeries.evalAt μ⁻¹ = 0 := by
  simpa [Units.val_inv_eq_inv_val] using
    hu.inv_mem_spectrum_iff (r := Units.mk0 μ⁻¹ (inv_ne_zero hμ))

/-- **The zeros of the Fredholm series.** For a row-compact endomorphism `u` of `C₀(I, K)`, the
zeros of the Fredholm series `det (1 - T u)` are exactly the inverses of the nonzero elements of
the spectrum of `u`. Since `det (1 - 0 u) = 1`, no zero is `0`. -/
theorem IsRowCompact.evalAt_charPowerSeries_eq_zero_iff {u : C₀(I, K) →L[K] C₀(I, K)}
    (hu : u.IsRowCompact) {a : K} :
    u.matrixCoeff.charPowerSeries.evalAt a = 0 ↔ a ≠ 0 ∧ a⁻¹ ∈ spectrum K u := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [PowerSeries.evalAt_at_zero, Matrix.constantCoeff_charPowerSeries]
  · rw [hu.mem_spectrum_iff_evalAt_inv_eq_zero (inv_ne_zero ha), inv_inv]
    exact ⟨fun h ↦ ⟨ha, h⟩, And.right⟩

end Field

end ContinuousLinearMap

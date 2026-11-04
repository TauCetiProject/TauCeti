/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.FredholmDet
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Fredholm invertibility on modules with property (Pr)

The Fredholm series of a row-compact endomorphism of a module with property (Pr) detects
invertibility: `1 - a u` is a unit exactly when `H_u(a)` is a unit. This transports the
model-space criterion along an arbitrary continuous linear retract, without assuming a finite
free complement. The rectangular Jacobson identity compares `1 - a u` with `1 - a i u r`.

Over a complete ultrametric field, the nonzero spectrum is therefore the set of inverses of
Fredholm zeros. Over coefficient rings, the criterion is about units, not vanishing; it applies
also to nonreduced rings and finite projective modules of nonconstant rank. No assertion about
the spectral value zero is made.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§5–7.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §§2.1–2.2.
-/

public section

open scoped ZeroAtInfty

namespace ContinuousLinearMap

section Ring

variable {R M : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [ContinuousConstSMul R M]
  {u : M →L[R] M}

/-- For a row-compact endomorphism of a module with property (Pr), `1 - a u` is invertible
exactly when its Fredholm series evaluated at `a` is a unit. -/
theorem IsPrCompact.isUnit_one_sub_smul_iff (hu : u.IsPrCompact) {a : R} :
    IsUnit (1 - a • u) ↔ IsUnit (u.charPowerSeries.evalAt a) := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (TauCeti.hasPr_def R M).mp hu.hasPr_source
  rw [hu.charPowerSeries_eq hri]
  have hv := hu.isRowCompact_comp i r
  have hmodel : IsUnit (1 - a • i.comp (u.comp r)) ↔
      IsUnit ((i.comp (u.comp r)).matrixCoeff.charPowerSeries.evalAt a) :=
    ⟨hv.isUnit_evalAt_charPowerSeries_of_isUnit_one_sub_smul, hv.isUnit_one_sub_smul⟩
  rw [← hmodel]
  have hscale : a • i.comp (u.comp r) = i.comp ((a • u).comp r) := by
    simp only [smul_comp, comp_smul]
  rw [hscale, isUnit_one_sub_comp_comm, comp_assoc, hri, comp_id]

/-- For a unit `a` in the coefficient ring, `a⁻¹` is in the spectrum of a row-compact
endomorphism of a (Pr) module exactly when `H_u(a)` is not a unit. -/
theorem IsPrCompact.inv_mem_spectrum_iff (hu : u.IsPrCompact) {a : Rˣ} :
    ((a⁻¹ : Rˣ) : R) ∈ spectrum R u ↔ ¬IsUnit (u.charPowerSeries.evalAt (a : R)) := by
  rw [← spectrum.smul_mem_smul_iff (r := a)]
  simp only [Units.smul_def, smul_eq_mul, Units.mul_inv]
  rw [spectrum.mem_iff, map_one, hu.isUnit_one_sub_smul_iff]

end Ring

section Field

variable {K M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [SeminormedAddCommGroup M] [Module K M] [ContinuousConstSMul K M]
  {u : M →L[K] M}

/-- The nonzero spectrum of a row-compact endomorphism of a (Pr) module over a complete
ultrametric field is detected by the zeros of its Fredholm series. -/
theorem IsPrCompact.mem_spectrum_iff_evalAt_inv_eq_zero (hu : u.IsPrCompact)
    {μ : K} (hμ : μ ≠ 0) :
    μ ∈ spectrum K u ↔ u.charPowerSeries.evalAt μ⁻¹ = 0 := by
  simpa [Units.val_inv_eq_inv_val] using
    hu.inv_mem_spectrum_iff (a := Units.mk0 μ⁻¹ (inv_ne_zero hμ))

/-- Fredholm zeros on a (Pr) module are exactly the inverses of its nonzero spectral values.
In particular zero is never a Fredholm zero. -/
theorem IsPrCompact.evalAt_charPowerSeries_eq_zero_iff (hu : u.IsPrCompact) {a : K} :
    u.charPowerSeries.evalAt a = 0 ↔ a ≠ 0 ∧ a⁻¹ ∈ spectrum K u := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [PowerSeries.evalAt_at_zero]
  · rw [hu.mem_spectrum_iff_evalAt_inv_eq_zero (inv_ne_zero ha), inv_inv]
    exact ⟨fun h ↦ ⟨ha, h⟩, And.right⟩

end Field

end ContinuousLinearMap

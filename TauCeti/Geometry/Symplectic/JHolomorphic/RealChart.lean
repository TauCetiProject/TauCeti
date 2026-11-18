/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
public import TauCeti.Analysis.Complex.RealChart

/-!
# Holomorphic maps of the plane in real coordinates

A map `f : ℂ → ℂ` with a complex derivative becomes, read in the real coordinates `ℝ × ℝ` through
`TauCeti.Complex.realChart`, a map of the standard complex line whose real derivative is complex
linear for `AlmostComplexStructure.product ℝ`. This is the source-side holomorphicity used when a
holomorphic change of domain coordinates is applied to a `J`-holomorphic map or to its energy.

## Main results

* `TauCeti.isComplexLinearMap_fderiv_realChart`: a map of the plane with a complex derivative has
  complex-linear derivative in the real coordinates.
-/

public section

open TauCeti.Complex (realChart fderiv_realChart_apply)

namespace TauCeti

/-- A map of the plane with a complex derivative is holomorphic in real coordinates: the derivative
of its real chart is complex linear. -/
theorem isComplexLinearMap_fderiv_realChart {f : ℂ → ℂ} {f' : ℂ} {z : ℝ × ℝ}
    (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm z)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (AlmostComplexStructure.product ℝ)
      (fderiv ℝ (realChart f) z : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
  rw [isComplexLinearMap_iff_apply]
  intro v
  simp only [ContinuousLinearMap.coe_coe, fderiv_realChart_apply hf,
    AlmostComplexStructure.product_apply]
  apply Prod.ext <;>
    simp [Complex.equivRealProdCLM_symm_apply, Complex.mul_re, Complex.mul_im] <;> ring

end TauCeti

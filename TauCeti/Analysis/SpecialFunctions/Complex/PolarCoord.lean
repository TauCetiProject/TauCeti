/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

import TauCeti.MeasureTheory.Integral.PolarCoord

/-!
# The differential of the complex polar parametrization

The Cartesian polar map has differential `polarCoordSymmDeriv` at every real radius and angle.
Its differential is injective at nonzero radius, where the map is a `C^n` local diffeomorphism
for every regularity `n ≥ 1`, including analytic regularity. The derivative and smoothness
proofs reuse the translated polar-coordinate results from
`TauCeti.MeasureTheory.Integral.PolarCoord`.
-/

public noncomputable section

namespace TauCeti

open scoped Manifold ContDiff

/-- The differential of the Cartesian polar parametrization in radius and angle coordinates. -/
def polarCoordSymmDeriv (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp (fderivPolarCoordSymm x)

/-- The Cartesian polar parametrization has derivative `polarCoordSymmDeriv` at every point. -/
theorem hasFDerivAt_polarCoord_symm_polarCoordSymmDeriv (x : ℝ × ℝ) :
    HasFDerivAt Complex.polarCoord.symm (polarCoordSymmDeriv x) x := by
  simpa only [zero_add, polarCoordSymmDeriv] using TauCeti.hasFDerivAt_add_polarCoord_symm x 0

/-- The Fréchet derivative of the Cartesian polar parametrization is `polarCoordSymmDeriv`. -/
@[simp] theorem fderiv_polarCoord_symm (x : ℝ × ℝ) :
    fderiv ℝ Complex.polarCoord.symm x = polarCoordSymmDeriv x :=
  (hasFDerivAt_polarCoord_symm_polarCoordSymmDeriv x).fderiv

/-- The polar differential applied to a radial and angular tangent vector. -/
@[simp] theorem polarCoordSymmDeriv_apply (x v : ℝ × ℝ) :
    polarCoordSymmDeriv x v =
      ⟨Real.cos x.2 * v.1 - x.1 * Real.sin x.2 * v.2,
        Real.sin x.2 * v.1 + x.1 * Real.cos x.2 * v.2⟩ := by
  apply Complex.ext <;>
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin, polarCoordSymmDeriv, fderivPolarCoordSymm,
      Matrix.toLin_finTwoProd_toContinuousLinearMap, Complex.equivRealProdCLM_symm_apply,
      sub_eq_add_neg]

/-- The polar parametrization has injective differential at every nonzero radius. -/
theorem polarCoordSymmDeriv_injective (x : ℝ × ℝ) (hx : x.1 ≠ 0) :
    Function.Injective (polarCoordSymmDeriv x) := by
  have hunit : IsUnit (fderivPolarCoordSymm x : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
    rw [LinearMap.isUnit_iff_isUnit_det, ← ContinuousLinearMap.det, det_fderivPolarCoordSymm]
    exact hx.isUnit
  exact Complex.equivRealProdCLM.symm.injective.comp ((Module.End.isUnit_iff _).mp hunit).injective

/-- The Cartesian polar parametrization is a `C^n` local diffeomorphism at every nonzero
radius, for every regularity `n ≥ 1`, including analytic regularity. -/
theorem isLocalDiffeomorphAt_polarCoord_symm (x : ℝ × ℝ) (hx : x.1 ≠ 0)
    {n : WithTop ℕ∞} (hn : 1 ≤ n) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) n Complex.polarCoord.symm x := by
  have hs : ContDiff ℝ n Complex.polarCoord.symm := by
    simpa only [zero_add] using TauCeti.contDiff_add_polarCoord_symm (n := n) 0
  let e := ((polarCoordSymmDeriv x).toLinearMap.linearEquivOfInjective
    (polarCoordSymmDeriv_injective x hx) Complex.equivRealProdCLM.symm.toLinearEquiv.finrank_eq
    ).toContinuousLinearEquiv
  have he : (e : ℝ × ℝ →L[ℝ] ℂ) = polarCoordSymmDeriv x :=
    ContinuousLinearMap.ext fun v ↦ by simp [e]
  exact TauCeti.isLocalDiffeomorphAt_of_fderiv_eq hs.contDiffOn isOpen_univ (Set.mem_univ x)
    hn (e := e) (he.trans (fderiv_polarCoord_symm x).symm)

end TauCeti

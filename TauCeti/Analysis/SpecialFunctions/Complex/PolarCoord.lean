/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The differential of the complex polar parametrization

The Cartesian polar map has differential `polarCoordSymmDeriv` at every real radius and angle.
Its differential is injective at nonzero radius, where the map is a `C^n` local diffeomorphism
for every regularity `n ≥ 1`, including analytic regularity. The translated polar map is smooth
even at zero radius. Its radial and angular derivative vectors give the pullback Euclidean metric
`dr² + r² dθ²`, which is invariant under angular translations.
-/

public noncomputable section

namespace TauCeti

open scoped Manifold ContDiff RealInnerProductSpace

open Complex

/-- The translated inverse complex polar map is smooth, including at zero radius. -/
theorem contDiff_add_polarCoord_symm (z₀ : ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p ↦ z₀ + Complex.polarCoord.symm p) := by
  simp only [Complex.polarCoord_symm_apply, ← Complex.ofRealCLM_apply]
  fun_prop

/-- The derivative of the translated inverse complex polar-coordinate map at any `(r, θ)`.
No restriction to the positive-radius chart is needed for this derivative formula. -/
theorem hasFDerivAt_add_polarCoord_symm (p : ℝ × ℝ) (z₀ : ℂ) :
    HasFDerivAt (fun p ↦ z₀ + Complex.polarCoord.symm p)
      (Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp (fderivPolarCoordSymm p)) p :=
  (Complex.equivRealProdCLM.symm.hasFDerivAt.comp p (hasFDerivAt_polarCoord_symm p)).const_add z₀

/-- The radial derivative of the inverse polar-coordinate map, expressed as a complex number,
is the unit vector at the given angle. -/
theorem equivRealProd_symm_fderivPolarCoordSymm_apply_one_zero (p : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (fderivPolarCoordSymm p (1, 0)) =
      Complex.exp (p.2 * I) := by
  simp [fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap,
    Complex.equivRealProdCLM_symm_apply, Complex.exp_mul_I]

/-- The angular derivative of the inverse polar-coordinate map, expressed as a complex number,
is the tangent vector to the circle with the given radius and angle. -/
theorem equivRealProd_symm_fderivPolarCoordSymm_apply_zero_one (p : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (fderivPolarCoordSymm p (0, 1)) =
      circleMap 0 p.1 p.2 * I := by
  apply Complex.ext <;>
  simp [fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap,
    Complex.equivRealProdCLM_symm_apply, Complex.exp_mul_I, circleMap]

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

/-- Pullback of the Euclidean metric in radius and angle coordinates, at any real radius. -/
theorem inner_polarCoordSymmDeriv (x v w : ℝ × ℝ) :
    ⟪polarCoordSymmDeriv x v, polarCoordSymmDeriv x w⟫ =
      v.1 * w.1 + x.1 ^ 2 * v.2 * w.2 := by
  simp only [polarCoordSymmDeriv_apply, Complex.inner, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  linear_combination
    (v.1 * w.1 + x.1 ^ 2 * v.2 * w.2) * Real.sin_sq_add_cos_sq x.2

/-- Every real angular translation preserves the pullback inner product at any real radius. -/
theorem inner_polarCoordSymmDeriv_add_angle (x v w : ℝ × ℝ) (t : ℝ) :
    ⟪polarCoordSymmDeriv (x + (0, t)) v, polarCoordSymmDeriv (x + (0, t)) w⟫ =
      ⟪polarCoordSymmDeriv x v, polarCoordSymmDeriv x w⟫ := by
  simp only [inner_polarCoordSymmDeriv]
  simp

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
  refine TauCeti.isLocalDiffeomorphAt_of_injective_mfderiv hs.contMDiff.contMDiffOn
    isOpen_univ (Set.mem_univ x) BoundarylessManifold.isInteriorPoint hn ?_
    Complex.equivRealProdCLM.symm.toLinearEquiv.finrank_eq
  rw [mfderiv_eq_fderiv, fderiv_polarCoord_symm]
  exact polarCoordSymmDeriv_injective x hx

end TauCeti

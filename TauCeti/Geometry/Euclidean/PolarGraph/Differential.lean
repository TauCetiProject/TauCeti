/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import TauCeti.Geometry.Euclidean.PolarGraph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

import TauCeti.MeasureTheory.Integral.PolarCoord

/-!
# The differential and metric of the polar projection

In the global coordinates of the polar cover, the pullback of the real Euclidean inner product
on the complex plane is `dr² + r² dθ²`. Each integral deck translation preserves this metric.
The Cartesian parametrization is a smooth local diffeomorphism at every nonzero radius
(`isLocalDiffeomorphAt_polarCoord_symm`), since its differential `projectionDeriv` is injective.
-/

public noncomputable section

namespace TauCeti.PolarGraph

open scoped RealInnerProductSpace Manifold ContDiff

/-- Mathlib's Cartesian parametrization agrees with the polar covering map on positive radii. -/
theorem polarCoord_symm_eq_projection (p : PolarPoint) :
    Complex.polarCoord.symm p.val = projection p := by
  apply Complex.ext <;> simp [-Complex.ofReal_cos, -Complex.ofReal_sin, radius_def, angle_def]

/-- The differential of the Cartesian polar parametrization in radius and angle coordinates. -/
def projectionDeriv (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp (fderivPolarCoordSymm x)

/-- The Cartesian polar parametrization has derivative `projectionDeriv` at every point. -/
theorem hasFDerivAt_polarCoord_symm_projectionDeriv (x : ℝ × ℝ) :
    HasFDerivAt Complex.polarCoord.symm (projectionDeriv x) x := by
  simpa only [zero_add, projectionDeriv] using TauCeti.hasFDerivAt_add_polarCoord_symm x 0

/-- The Fréchet derivative of the Cartesian polar parametrization is `projectionDeriv`. -/
@[simp] theorem fderiv_polarCoord_symm (x : ℝ × ℝ) :
    fderiv ℝ Complex.polarCoord.symm x = projectionDeriv x :=
  (hasFDerivAt_polarCoord_symm_projectionDeriv x).fderiv

@[simp] theorem projectionDeriv_apply (x v : ℝ × ℝ) :
    projectionDeriv x v =
      ⟨Real.cos x.2 * v.1 - x.1 * Real.sin x.2 * v.2,
        Real.sin x.2 * v.1 + x.1 * Real.cos x.2 * v.2⟩ := by
  apply Complex.ext <;>
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin, projectionDeriv, fderivPolarCoordSymm,
      Matrix.toLin_finTwoProd_toContinuousLinearMap, Complex.equivRealProdCLM_symm_apply,
      sub_eq_add_neg]

/-- Pullback of the Euclidean metric in radius and angle coordinates, at any real radius. -/
theorem inner_projectionDeriv (x v w : ℝ × ℝ) :
    ⟪projectionDeriv x v, projectionDeriv x w⟫ =
      v.1 * w.1 + x.1 ^ 2 * v.2 * w.2 := by
  simp only [projectionDeriv_apply, Complex.inner, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  linear_combination
    (v.1 * w.1 + x.1 ^ 2 * v.2 * w.2) * Real.sin_sq_add_cos_sq x.2

/-- The polar parametrization has injective differential at every nonzero radius. -/
theorem projectionDeriv_injective (x : ℝ × ℝ) (hx : x.1 ≠ 0) :
    Function.Injective (projectionDeriv x) := by
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
  let e := ((projectionDeriv x).toLinearMap.linearEquivOfInjective
    (projectionDeriv_injective x hx) Complex.equivRealProdCLM.symm.toLinearEquiv.finrank_eq
    ).toContinuousLinearEquiv
  have he : (e : ℝ × ℝ →L[ℝ] ℂ) = projectionDeriv x :=
    ContinuousLinearMap.ext fun v ↦ by simp [e]
  exact TauCeti.isLocalDiffeomorphAt_of_fderiv_eq hs.contDiffOn isOpen_univ (Set.mem_univ x)
    hn (e := e) (he.trans (fderiv_polarCoord_symm x).symm)

/-- Every real angular translation preserves the pullback inner product at any real radius. -/
theorem inner_projectionDeriv_add_angle (x v w : ℝ × ℝ) (t : ℝ) :
    ⟪projectionDeriv (x + (0, t)) v, projectionDeriv (x + (0, t)) w⟫ =
      ⟪projectionDeriv x v, projectionDeriv x w⟫ := by
  simp only [inner_projectionDeriv]
  simp

/-- All deck translations preserve the pullback inner product. -/
theorem inner_projectionDeriv_deckShift (k : ℤ) (p : PolarPoint) (v w : ℝ × ℝ) :
    ⟪projectionDeriv (deckShift k p).val v, projectionDeriv (deckShift k p).val w⟫ =
      ⟪projectionDeriv p.val v, projectionDeriv p.val w⟫ := by
  simpa only [deckShift_val] using
    inner_projectionDeriv_add_angle p.val v w ((k : ℝ) * (2 * Real.pi))

end TauCeti.PolarGraph

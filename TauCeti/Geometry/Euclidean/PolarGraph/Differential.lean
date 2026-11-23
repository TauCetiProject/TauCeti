/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import TauCeti.Geometry.Euclidean.PolarGraph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The differential and metric of the polar projection

In the global coordinates of the polar cover, the pullback of the real Euclidean inner product
on the complex plane is `dr² + r² dθ²`. Each integral deck translation preserves this metric.
-/

public noncomputable section

namespace TauCeti.PolarGraph

open scoped RealInnerProductSpace Manifold ContDiff

/-- Mathlib's Cartesian parametrization agrees with the polar covering map on positive radii. -/
theorem polarCoord_symm_eq_projection (p : PolarPoint) :
    Complex.polarCoord.symm p.val = projection p := by
  apply Complex.ext <;> simp [-Complex.ofReal_cos, -Complex.ofReal_sin, radius_def, angle_def]

/-- The differential of the polar projection in radius and angle coordinates. -/
def projectionDeriv (p : PolarPoint) : ℝ × ℝ →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp (fderivPolarCoordSymm p.val)

/-- The Cartesian parametrization differentiates to `projectionDeriv` on the positive half-plane. -/
theorem hasFDerivAt_projection (p : PolarPoint) :
    HasFDerivAt Complex.polarCoord.symm (projectionDeriv p) p.val :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.hasFDerivAt.comp p.val
    (hasFDerivAt_polarCoord_symm p.val)

/-- Pullback of the Euclidean metric in radius and angle coordinates. -/
theorem inner_projectionDeriv (p : PolarPoint) (v w : ℝ × ℝ) :
    ⟪projectionDeriv p v, projectionDeriv p w⟫ =
      v.1 * w.1 + radius p ^ 2 * v.2 * w.2 := by
  simp [-Complex.ofReal_cos, -Complex.ofReal_sin, Complex.inner, projectionDeriv,
    fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap,
    Complex.equivRealProdCLM_symm_apply, radius_def]
  linear_combination
    (v.1 * w.1 + p.val.1 ^ 2 * v.2 * w.2) * Real.sin_sq_add_cos_sq p.val.2

/-- The polar projection has injective differential at each positive radius. -/
theorem projectionDeriv_injective (p : PolarPoint) : Function.Injective (projectionDeriv p) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have h := inner_projectionDeriv p v v
  rw [hv, inner_zero_left] at h
  have hr := radius_pos p
  have ha : v.2 = 0 := by
    by_contra hn
    have ht := mul_pos (sq_pos_of_pos hr) (sq_pos_of_ne_zero hn)
    nlinarith [sq_nonneg v.1]
  rw [ha] at h
  exact Prod.ext (show v.1 = 0 by nlinarith) ha

/-- The Cartesian parametrization is a smooth local diffeomorphism at every positive radius. -/
theorem isLocalDiffeomorphAt_polarCoord_symm (p : PolarPoint) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) ∞ Complex.polarCoord.symm p.val := by
  have hs : ContDiff ℝ ∞ Complex.polarCoord.symm := by
    rw [show (⇑Complex.polarCoord.symm) = _ from funext Complex.polarCoord_symm_apply]
    have h : ContDiff ℝ ∞ Complex.ofReal := Complex.ofRealCLM.contDiff
    fun_prop
  let e := ((projectionDeriv p).toLinearMap.linearEquivOfInjective
    (projectionDeriv_injective p) Complex.equivRealProdCLM.symm.toLinearEquiv.finrank_eq
    ).toContinuousLinearEquiv
  exact TauCeti.isLocalDiffeomorphAt_of_fderiv_eq hs.contDiffOn isOpen_univ (Set.mem_univ p.val)
    (by simp) (e := e) (hasFDerivAt_projection p).fderiv.symm

/-- A deck shift is translation by a constant vector in the coordinates of the cover. -/
theorem deckShift_val (k : ℤ) (p : PolarPoint) :
    (deckShift k p).val = p.val + (0, (k : ℝ) * (2 * Real.pi)) := by
  apply Prod.ext
  · change (deckShift k p).val.1 = p.val.1 + 0
    simp only [← radius_def, radius_deckShift, add_zero]
  · change (deckShift k p).val.2 = p.val.2 + _
    simp only [← angle_def, angle_deckShift]

/-- The derivative of a deck translation is the identity in radius and angle coordinates. -/
theorem hasFDerivAt_deckShift (k : ℤ) (p : PolarPoint) :
    HasFDerivAt (fun x : ℝ × ℝ ↦ x + (0, (k : ℝ) * (2 * Real.pi)))
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)) p.val :=
  (hasFDerivAt_id p.val).add_const _

/-- All deck translations preserve the pullback inner product. -/
theorem inner_projectionDeriv_deckShift (k : ℤ) (p : PolarPoint) (v w : ℝ × ℝ) :
    ⟪projectionDeriv (deckShift k p) v, projectionDeriv (deckShift k p) w⟫ =
      ⟪projectionDeriv p v, projectionDeriv p w⟫ := by
  simp only [inner_projectionDeriv, radius_deckShift]

end TauCeti.PolarGraph

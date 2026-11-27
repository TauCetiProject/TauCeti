/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Complex.PolarCoord
public import TauCeti.Geometry.Euclidean.PolarGraph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The differential and metric of the polar projection

In the global coordinates of the polar cover, the pullback of the real Euclidean inner product
on the complex plane is `dr² + r² dθ²`. Each integral deck translation preserves this metric.
The Cartesian parametrization is a smooth local diffeomorphism at every nonzero radius
(`TauCeti.isLocalDiffeomorphAt_polarCoord_symm`), since its differential
`polarCoordSymmDeriv` is injective.
-/

public noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

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

namespace TauCeti.PolarGraph

/-- Mathlib's Cartesian parametrization agrees with the polar covering map on positive radii. -/
theorem polarCoord_symm_eq_projection (p : PolarPoint) :
    Complex.polarCoord.symm p.val = projection p := by
  apply Complex.ext <;> simp [-Complex.ofReal_cos, -Complex.ofReal_sin, radius_def, angle_def]

/-- All deck translations preserve the pullback inner product. -/
theorem inner_polarCoordSymmDeriv_deckShift (k : ℤ) (p : PolarPoint) (v w : ℝ × ℝ) :
    ⟪polarCoordSymmDeriv (deckShift k p).val v, polarCoordSymmDeriv (deckShift k p).val w⟫ =
      ⟪polarCoordSymmDeriv p.val v, polarCoordSymmDeriv p.val w⟫ := by
  simpa only [deckShift_val] using
    inner_polarCoordSymmDeriv_add_angle p.val v w ((k : ℝ) * (2 * Real.pi))

end TauCeti.PolarGraph

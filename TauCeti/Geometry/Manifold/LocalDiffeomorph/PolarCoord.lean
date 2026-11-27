/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Complex.PolarCoord
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Local diffeomorphisms in polar coordinates

The Cartesian polar parametrization is a `C^n` local diffeomorphism at every nonzero radius,
for every regularity `n ≥ 1`, including analytic regularity. This follows from the injectivity
of its differential `TauCeti.polarCoordSymmDeriv` and the inverse function theorem.
-/

public noncomputable section

open scoped Manifold ContDiff

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

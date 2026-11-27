/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Complex.PolarCoord
public import TauCeti.Geometry.Euclidean.PolarGraph.Basic

/-!
# The polar parametrization and deck invariance

The Cartesian polar parametrization agrees with the covering projection on positive radii.
Integral deck translations preserve the pullback Euclidean inner product. The formula
`dr² + r² dθ²` for that inner product is `TauCeti.inner_fderivComplexPolarCoordSymm`.
-/

public noncomputable section

open scoped RealInnerProductSpace

namespace TauCeti.PolarGraph

/-- Mathlib's Cartesian parametrization agrees with the polar covering map on positive radii. -/
theorem complexPolarCoord_symm_eq_projection (p : PolarPoint) :
    Complex.polarCoord.symm p.val = projection p := by
  apply Complex.ext <;> simp [-Complex.ofReal_cos, -Complex.ofReal_sin, radius_def, angle_def]

/-- All deck translations preserve the pullback inner product. -/
theorem inner_fderivComplexPolarCoordSymm_deckShift (k : ℤ) (p : PolarPoint) (v w : ℝ × ℝ) :
    ⟪fderivComplexPolarCoordSymm (deckShift k p).val v,
      fderivComplexPolarCoordSymm (deckShift k p).val w⟫ =
      ⟪fderivComplexPolarCoordSymm p.val v, fderivComplexPolarCoordSymm p.val w⟫ := by
  simpa only [val_deckShift] using
    inner_fderivComplexPolarCoordSymm_add_angle p.val v w ((k : ℝ) * (2 * Real.pi))

end TauCeti.PolarGraph

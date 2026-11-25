/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sphere.Hersch.Basic
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.SphereBoost
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Smoothness of Hersch's sphere homeomorphism

Hersch's sphere homeomorphism is analytic. For a nonzero parameter `a` in the open unit ball,
it is the final slice of the sphere-boost diffeotopy toward `normalize a` with rapidity
`Real.artanh ‖a‖`. This identification supplies both its regularity and a smooth deformation
from the identity, as used to compute its mapping degree.
-/

public section

noncomputable section

open Metric
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] {m : ℕ∞ω}

/-- For a nonzero parameter in the open unit ball, the sphere-boost diffeotopy ends at Hersch's
homeomorphism. -/
theorem sphereBoostDiffeotopy_final_eq_herschHomeomorph {a : E} (ha : ‖a‖ < 1) (ha0 : a ≠ 0) :
    ((sphereBoostDiffeotopy (n := n) (m := m) (NormedSpace.norm_normalize ha0)
      (Real.artanh ‖a‖)).final : sphere (0 : E) 1 → sphere (0 : E) 1) = herschHomeomorph ha := by
  funext x
  apply Subtype.ext
  rw [coe_sphereBoostDiffeotopy_final_apply, coe_herschHomeomorph,
    ← herschMap_tanh_smul (NormedSpace.norm_normalize ha0),
    Real.tanh_artanh ⟨by linarith [norm_nonneg a], ha⟩, NormedSpace.norm_smul_normalize]

/-- Hersch's transformation is analytic, and hence `C^m`, on the unit sphere. -/
theorem contMDiff_herschHomeomorph {a : E} (ha : ‖a‖ < 1) :
    ContMDiff (𝓡 n) (𝓡 n) m (herschHomeomorph ha) := by
  by_cases ha0 : a = 0
  · have hid : (herschHomeomorph ha : sphere (0 : E) 1 → sphere (0 : E) 1) = id := by
      funext x
      exact Subtype.ext (by simp [ha0])
    rw [hid]
    exact contMDiff_id
  · rw [← sphereBoostDiffeotopy_final_eq_herschHomeomorph (n := n) ha ha0 (m := m)]
    exact (sphereBoostDiffeotopy (n := n) (m := m) (NormedSpace.norm_normalize ha0)
      (Real.artanh ‖a‖)).final.contMDiff

end TauCeti

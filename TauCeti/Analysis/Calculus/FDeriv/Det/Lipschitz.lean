/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The determinant is Lipschitz on bounded sets

Over `ℝ`, the determinant of a continuous linear endomorphism of a normed space is Lipschitz on
every bounded set of endomorphisms. In finite dimension it is smooth
(`ContinuousLinearMap.contDiff_det`), hence Lipschitz on every closed ball, which is compact and
convex; in infinite dimension it is the constant `1`. This bounds the change of the Jacobian
determinant `det DΦ` of a map with Lipschitz derivative, as needed for coefficients transformed by
a change of variables.

## Main results

* `ContinuousLinearMap.exists_lipschitzOnWith_det_of_isBounded`: the determinant is Lipschitz on
  every bounded set of continuous linear endomorphisms of a real normed space.
-/

public section

namespace ContinuousLinearMap

/-- The determinant of a continuous linear endomorphism of a real normed space is Lipschitz on
every bounded set of endomorphisms. -/
theorem exists_lipschitzOnWith_det_of_isBounded {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set (E →L[ℝ] E)} (hs : Bornology.IsBounded s) :
    ∃ K, LipschitzOnWith K (fun f : E →L[ℝ] E ↦ f.det) s := by
  by_cases hE : FiniteDimensional ℝ E
  · obtain ⟨r, hr⟩ := hs.subset_closedBall 0
    obtain ⟨K, hK⟩ := (contDiff_det (𝕜 := ℝ) (E := E) (r := 1)).contDiffOn.exists_lipschitzOnWith
      one_ne_zero (convex_closedBall 0 r) (isCompact_closedBall 0 r)
    exact ⟨K, hK.mono hr⟩
  · -- In infinite dimension the determinant is the constant `1`.
    refine ⟨0, LipschitzOnWith.of_dist_le_mul fun f _ g _ ↦ ?_⟩
    rw [ContinuousLinearMap.det, ContinuousLinearMap.det,
      LinearMap.det_eq_one_of_not_module_finite hE, LinearMap.det_eq_one_of_not_module_finite hE,
      dist_self, NNReal.coe_zero, zero_mul]

end ContinuousLinearMap

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Topology.PathSpace.Moore
import Mathlib.Topology.MetricSpace.Lipschitz
import TauCeti.Topology.MetricSpace.Pseudo.Constructions

/-!
# Lipschitz Moore paths

A Moore path `γ` in a pseudometric space is a function `[0, ∞) → X`, so it makes sense to ask that
it be Lipschitz. Constant paths are Lipschitz, and concatenation preserves this
(`TauCeti.MoorePath.lipschitzWith_trans`): the two halves meet at the junction time, where the
triangle inequality splits the distance between points on either side.

## Main results

* `TauCeti.MoorePath.lipschitzWith_refl`, `TauCeti.MoorePath.lipschitzWith_trans`: constant paths
  are Lipschitz, and concatenation preserves the Lipschitz property.
-/

public section

open scoped NNReal

namespace TauCeti

namespace MoorePath

variable {X : Type*} [PseudoMetricSpace X]

/-- The constant Moore path of length zero is Lipschitz with every constant. -/
theorem lipschitzWith_refl (x : X) (K : ℝ≥0) : LipschitzWith K (refl x) := by
  have h : ⇑(refl x) = fun _ ↦ x := funext (refl_apply x)
  rw [h]
  exact LipschitzWith.const' x

/-- **Concatenation preserves the Lipschitz property.** If two Moore paths are `K`-Lipschitz, so is
their concatenation. -/
theorem lipschitzWith_trans {γ δ : MoorePath X} (h : γ.target = δ.source) {K : ℝ≥0}
    (hγ : LipschitzWith K γ) (hδ : LipschitzWith K δ) : LipschitzWith K (γ.trans δ h) := by
  refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm, dist_comm s]
    exact this t s (le_of_not_ge hst)
  rcases le_total t γ.length with ht | ht
  · rw [trans_apply_of_le _ _ _ (hst.trans ht), trans_apply_of_le _ _ _ ht]
    exact hγ.dist_le_mul s t
  rcases le_total γ.length s with hs | hs
  · -- Both times lie in the second path.
    rw [trans_apply_of_length_le _ _ _ hs, trans_apply_of_length_le _ _ _ ht]
    have hsub : dist (s - γ.length) (t - γ.length) = dist s t := by
      rw [NNReal.dist_eq_sub_of_le (tsub_le_tsub_right hst _), NNReal.dist_eq_sub_of_le hst,
        NNReal.coe_sub hs, NNReal.coe_sub ht]
      ring
    simpa only [hsub] using hδ.dist_le_mul (s - γ.length) (t - γ.length)
  · -- The times lie on either side of the junction, where the paths meet.
    rw [trans_apply_of_le _ _ _ hs, trans_apply_of_length_le _ _ _ ht]
    have hjoin : γ γ.length = δ 0 := by rw [← target_def, h, source_def]
    calc dist (γ s) (δ (t - γ.length))
        ≤ dist (γ s) (γ γ.length) + dist (δ 0) (δ (t - γ.length)) := by
          rw [← hjoin]
          exact dist_triangle _ _ _
      _ ≤ K * dist s γ.length + K * dist 0 (t - γ.length) :=
          add_le_add (hγ.dist_le_mul _ _) (hδ.dist_le_mul _ _)
      _ = K * dist s t := by
          rw [NNReal.dist_eq_sub_of_le hs, NNReal.dist_eq_sub_of_le zero_le,
            NNReal.dist_eq_sub_of_le hst, NNReal.coe_sub ht, NNReal.coe_zero]
          ring

end MoorePath

end TauCeti

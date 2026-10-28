/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Bornology.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Inversion of a set in a normed division ring

For a closed bounded set `K` and a centre `q` in a normed division ring, the inversion
`z ↦ (z - q)⁻¹` maps `K \ {q}` onto the closed set `{w | w ≠ 0 ∧ q + w⁻¹ ∈ K}`: the image stays
away from `0`, and away from `0` it is the preimage of `K` under the continuous map
`w ↦ q + w⁻¹`. Conversely, inverting a set about a point of its closure that it does not contain
gives an unbounded set.

## Main results

* `TauCeti.isClosed_setOf_ne_zero_and_add_inv_mem`: the inversion of a closed bounded set about
  any centre, with the centre removed, is closed.
* `TauCeti.not_isBounded_image_sub_inv_of_mem_closure`: the inversion of a set about a point of
  its closure outside the set is unbounded.
-/

public section

namespace TauCeti

open Bornology Metric Set

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] {K : Set 𝕜}

/-- **The inversion of a closed bounded set is closed.** For closed bounded `K` and any `q`, the
image `{w | w ≠ 0 ∧ q + w⁻¹ ∈ K}` of `K \ {q}` under `z ↦ (z - q)⁻¹` is closed: it stays away
from `0`, and away from `0` it is the preimage of `K` under `w ↦ q + w⁻¹`. -/
theorem isClosed_setOf_ne_zero_and_add_inv_mem (hK : IsClosed K) (hKb : IsBounded K) (q : 𝕜) :
    IsClosed {w : 𝕜 | w ≠ 0 ∧ q + w⁻¹ ∈ K} := by
  obtain ⟨R, hR⟩ := hKb.subset_closedBall q
  set R' := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hne : ∀ w : 𝕜, R'⁻¹ ≤ ‖w‖ → w ≠ 0 := fun w hw h0 => by
    rw [h0, norm_zero] at hw
    exact absurd hw (not_le.mpr (inv_pos.mpr hR'))
  have heq : {w : 𝕜 | w ≠ 0 ∧ q + w⁻¹ ∈ K} =
      {w : 𝕜 | R'⁻¹ ≤ ‖w‖} ∩ (fun w : 𝕜 => q + w⁻¹) ⁻¹' K := by
    ext w
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hw, hwK⟩
      refine ⟨?_, hwK⟩
      have hle : ‖w⁻¹‖ ≤ R' := by
        have := mem_closedBall.mp (hR hwK)
        rw [dist_eq_norm, add_sub_cancel_left] at this
        exact this.trans (le_max_left _ _)
      rw [norm_inv] at hle
      have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
      calc R'⁻¹ ≤ (‖w‖⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hpos) hle
        _ = ‖w‖ := inv_inv _
    · rintro ⟨hw, hwK⟩
      exact ⟨hne w hw, hwK⟩
  rw [heq]
  exact ContinuousOn.preimage_isClosed_of_isClosed
    (continuousOn_const.add (continuousOn_inv₀.mono hne))
    (isClosed_le continuous_const continuous_norm) hK

/-- **Inverting about a missing point of the closure gives an unbounded set.** If `q` lies in the
closure of `s` but not in `s`, then the image of `s` under `z ↦ (z - q)⁻¹` is unbounded. -/
theorem not_isBounded_image_sub_inv_of_mem_closure {s : Set 𝕜} {q : 𝕜} (hq : q ∈ closure s)
    (hq' : q ∉ s) : ¬ IsBounded ((fun z => (z - q)⁻¹) '' s) := by
  rw [isBounded_iff_forall_norm_le]
  rintro ⟨M, hM⟩
  obtain ⟨z, hzs, hzq⟩ := Metric.mem_closure_iff.mp hq (max M 1 + 1)⁻¹ (by positivity)
  have hz0 : 0 < ‖z - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hq' (h ▸ hzs))
  have hlt : ‖z - q‖ < (max M 1 + 1)⁻¹ := by rwa [dist_comm, dist_eq_norm] at hzq
  have hle : ‖(z - q)⁻¹‖ ≤ M := hM _ ⟨z, hzs, rfl⟩
  rw [norm_inv] at hle
  have : max M 1 + 1 < ‖z - q‖⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) hz0]
    exact hlt
  linarith [le_max_left M 1]

end TauCeti

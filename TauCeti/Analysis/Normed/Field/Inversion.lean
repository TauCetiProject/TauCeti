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
# Inversion of a closed bounded set in a normed division ring

For a closed bounded set `K` and a centre `q` in a normed division ring, the inversion
`z ↦ (z - q)⁻¹` maps `K \ {q}` onto the closed set `{w | w ≠ 0 ∧ q + w⁻¹ ∈ K}`: the image stays
away from `0`, and away from `0` it is the preimage of `K` under the continuous map
`w ↦ q + w⁻¹`.

## Main results

* `TauCeti.isClosed_setOf_ne_zero_and_add_inv_mem`: the inversion of a closed bounded set about
  any centre, with the centre removed, is closed.
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
      refine ⟨fun h0 => ?_, hwK⟩
      rw [h0, norm_zero] at hw
      exact absurd hw (not_le.mpr (inv_pos.mpr hR'))
  rw [heq]
  refine ContinuousOn.preimage_isClosed_of_isClosed ?_
    (isClosed_le continuous_const continuous_norm) hK
  refine continuousOn_const.add (continuousOn_inv₀.mono fun w hw h0 => ?_)
  rw [mem_ofPred_eq, h0, norm_zero] at hw
  exact absurd hw (not_le.mpr (inv_pos.mpr hR'))

end TauCeti

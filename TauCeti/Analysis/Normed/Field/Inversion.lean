/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Bornology.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Bornology.BoundedOperation
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Inversion of a set in a normed division ring

In any division ring, `w ↦ q + w⁻¹` inverts the inversion `z ↦ (z - q)⁻¹` about `q`.

For a closed bounded set `K` and a centre `q` in a normed division ring, the inversion
`z ↦ (z - q)⁻¹` maps `K \ {q}` onto the closed set `{w | w ≠ 0 ∧ q + w⁻¹ ∈ K}`: the image stays
away from `0`, and away from `0` it is the preimage of `K` under the continuous map
`w ↦ q + w⁻¹`. Inverting a set about a point outside its closure gives a bounded set; conversely,
inverting a set about a point of its closure that it does not contain gives an unbounded set, and
inverting an unbounded set adds `0`, the image of infinity, to the closure. Completing the
inversion of a set by `0` commutes with closures, and turns an open set with bounded complement
into an open set.

## Main results

* `TauCeti.bijOn_add_inv_image_inv_sub`: `w ↦ q + w⁻¹` inverts the inversion about `q`.
* `TauCeti.image_inv_sub_eq_preimage_add_inv`: the inversion about `q` maps a set onto its
  preimage under `w ↦ q + w⁻¹`.
* `TauCeti.isClosed_setOf_ne_zero_and_add_inv_mem`: the inversion of a closed bounded set about
  any centre, with the centre removed, is closed.
* `TauCeti.isBounded_image_inv_sub`: the inversion of a set about a point outside its closure is
  bounded.
* `TauCeti.not_isBounded_image_sub_inv_of_mem_closure`: the inversion of a set about a point of
  its closure outside the set is unbounded.
* `TauCeti.closure_image_inv_sub`: the closure of the inversion of an unbounded set is the
  inverted closure together with `0`.
* `TauCeti.isOpen_insert_zero_image_inv_sub`, `TauCeti.closure_insert_zero_image_inv_sub` and
  `TauCeti.frontier_insert_zero_image_inv_sub`: an open set with bounded complement, inverted about
  any point and completed by `0`, is open; the completed inversion of any set has the completed
  inverted closure as closure; and for a centre outside the closure of such an open set, the
  inverted frontier as frontier.
-/

public section

namespace TauCeti

open Bornology Filter Metric Set Topology

section DivisionRing

variable {𝕜 : Type*} [DivisionRing 𝕜] {q : 𝕜}

/-- The map `w ↦ q + w⁻¹` inverts the inversion `z ↦ (z - q)⁻¹`: it is a bijection from the
inverted image of any set `S` back onto `S`. -/
theorem bijOn_add_inv_image_inv_sub (S : Set 𝕜) :
    BijOn (fun w : 𝕜 => q + w⁻¹) ((fun z : 𝕜 => (z - q)⁻¹) '' S) S :=
  BijOn.symm ⟨fun _ _ => by simp, fun _ _ => by simp⟩
    (inv_injective.comp (sub_left_injective (b := q))).injOn.bijOn_image

/-- The inversion `z ↦ (z - q)⁻¹` is a bijection of `𝕜` (sending `q` to `0⁻¹ = 0`) with inverse
`w ↦ q + w⁻¹`, so it maps any set onto the preimage of that set under `w ↦ q + w⁻¹`. -/
theorem image_inv_sub_eq_preimage_add_inv (S : Set 𝕜) :
    (fun z : 𝕜 => (z - q)⁻¹) '' S = (fun w : 𝕜 => q + w⁻¹) ⁻¹' S :=
  congrFun (image_eq_preimage_of_inverse (f := fun z : 𝕜 => (z - q)⁻¹)
    (g := fun w : 𝕜 => q + w⁻¹) (fun _ => by simp) fun _ => by simp) S

end DivisionRing

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

section Completion

variable {q : 𝕜} {U : Set 𝕜}

/-- Inverting a set `U` about a point `q` outside its closure gives a bounded set. -/
theorem isBounded_image_inv_sub (hq : q ∉ closure U) :
    IsBounded ((fun z : 𝕜 => (z - q)⁻¹) '' U) := by
  -- a ball about `q` misses `U`, so the inversion is bounded by the inverse of its radius
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl q hq
  refine isBounded_iff_forall_norm_le.mpr ⟨r⁻¹, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hrz : r ≤ ‖z - q‖ := by
    rw [← dist_eq_norm, dist_comm]
    exact not_lt.mp fun h => hrU (mem_ball'.mpr h) (subset_closure hz)
  rw [norm_inv]
  exact inv_anti₀ hr hrz

/-- Inverting an open set `U` with bounded complement about any point `q`, and adding `0`, the
image of infinity, gives an open set: `U` contains a neighbourhood of infinity, which the inversion
carries onto a punctured neighbourhood of `0`. -/
theorem isOpen_insert_zero_image_inv_sub (hUo : IsOpen U) (hUc : IsBounded Uᶜ) :
    IsOpen (insert 0 ((fun z : 𝕜 => (z - q)⁻¹) '' U)) := by
  obtain ⟨R, hR, hRU⟩ := hUc.subset_ball_lt 0 q
  rw [image_inv_sub_eq_preimage_add_inv, isOpen_iff_mem_nhds]
  intro w hw
  rcases eq_or_ne w 0 with rfl | hw0
  · -- a point `w ≠ 0` with `‖w‖ < R⁻¹` is sent by `w ↦ q + w⁻¹` outside `ball q R`
    refine Filter.mem_of_superset (ball_mem_nhds 0 (inv_pos.mpr hR)) fun w hw => ?_
    rcases eq_or_ne w 0 with rfl | hw0
    · exact mem_insert _ _
    refine mem_insert_of_mem _ (mem_preimage.mpr (not_not.mp fun h => ?_))
    have hRw : R < ‖w‖⁻¹ :=
      (lt_inv_comm₀ hR (norm_pos_iff.mpr hw0)).mpr (by simpa using hw)
    have hin := hRU h
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_inv] at hin
    exact lt_asymm hin hRw
  · exact Filter.mem_of_superset
      ((continuousAt_const.add (continuousAt_inv₀ hw0)).preimage_mem_nhds
        (hUo.mem_nhds ((mem_insert_iff.mp hw).resolve_left hw0)))
      (subset_insert _ _)

/-- Inverting any set `U` about any point `q` and adding `0`, the image of infinity, commutes with
taking closures. -/
theorem closure_insert_zero_image_inv_sub :
    closure (insert 0 ((fun z : 𝕜 => (z - q)⁻¹) '' U)) =
      insert 0 ((fun z : 𝕜 => (z - q)⁻¹) '' closure U) := by
  rw [insert_eq, closure_union, closure_singleton, ← insert_eq]
  refine Subset.antisymm (insert_subset (mem_insert _ _) fun w hw => ?_)
    (insert_subset (mem_insert _ _) ?_)
  · -- away from `0`, the inverse map `w ↦ q + w⁻¹` is continuous
    rcases eq_or_ne w 0 with rfl | hw0
    · exact mem_insert _ _
    have hg : ContinuousAt (fun w : 𝕜 => q + w⁻¹) w :=
      continuousAt_const.add (continuousAt_inv₀ hw0)
    rw [image_inv_sub_eq_preimage_add_inv] at hw ⊢
    have hgw := mem_closure_image hg hw
    exact mem_insert_of_mem _ (closure_mono (image_preimage_subset _ _) hgw)
  · -- away from `q`, the inversion is continuous; it sends `q` itself to `0`
    rintro _ ⟨z, hz, rfl⟩
    rcases eq_or_ne z q with rfl | hzq
    · simp
    exact mem_insert_of_mem _ (mem_closure_image
      ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hzq)) hz)

/-- Inverting an unbounded set `U` about any point `q`, the closure of the image is the image of the
closure together with `0`, the image of infinity. -/
theorem closure_image_inv_sub (hUb : ¬IsBounded U) :
    closure ((fun z : 𝕜 => (z - q)⁻¹) '' U) = insert 0 ((fun z : 𝕜 => (z - q)⁻¹) '' closure U) := by
  -- `U` reaches infinity, where the inversion tends to `0`
  have h0 : (0 : 𝕜) ∈ closure ((fun z : 𝕜 => (z - q)⁻¹) '' U) := by
    have : NeBot (cobounded 𝕜 ⊓ 𝓟 U) := by
      rw [neBot_iff, Ne, inf_principal_eq_bot, ← isBounded_def]
      exact hUb
    exact mem_closure_of_tendsto
      ((tendsto_inv₀_cobounded.comp (tendsto_sub_const_cobounded q)).mono_left inf_le_left)
      (mem_inf_of_right (mem_principal.mpr fun z hz => mem_image_of_mem _ hz))
  rw [← closure_insert_zero_image_inv_sub, insert_eq, closure_union, closure_singleton,
    ← insert_eq, insert_eq_of_mem h0]

/-- Inverting an open set `U` with bounded complement about a point `q` outside its closure, and
adding `0`, the image of infinity, the frontier of the resulting open set is the inverted frontier
of `U`. -/
theorem frontier_insert_zero_image_inv_sub (hUo : IsOpen U) (hq : q ∉ closure U)
    (hUc : IsBounded Uᶜ) :
    frontier (insert 0 ((fun z : 𝕜 => (z - q)⁻¹) '' U)) =
      (fun z : 𝕜 => (z - q)⁻¹) '' frontier U := by
  have h0 : (0 : 𝕜) ∉ (fun z : 𝕜 => (z - q)⁻¹) '' closure U := by
    rintro ⟨z, hz, hz0⟩
    rw [inv_eq_zero, sub_eq_zero] at hz0
    exact hq (hz0 ▸ hz)
  rw [(isOpen_insert_zero_image_inv_sub hUo hUc).frontier_eq,
    closure_insert_zero_image_inv_sub, insert_sdiff_of_mem _ (mem_insert _ _),
    sdiff_insert_of_notMem h0,
    ← image_sdiff (f := fun z : 𝕜 => (z - q)⁻¹) (inv_injective.comp (sub_left_injective (b := q))),
    ← hUo.frontier_eq]

end Completion

end TauCeti

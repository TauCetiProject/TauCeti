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

On a closed ball `closedBall c r` not containing `w`, the inversion `z ↦ (w - z)⁻¹` about `w` is
bounded by `(‖w - c‖ - r)⁻¹`, so its `n`-th power is bounded by `((‖w - c‖ - r) ^ n)⁻¹`, and
it stays within `r / ((‖w - c‖ - r) ‖w - c‖)` of its value at the centre. These are the kernel
estimates that describe a Cauchy-type integral far from its data.

## Main results

* `TauCeti.bijOn_add_inv_image_inv_sub`: `w ↦ q + w⁻¹` inverts the inversion about `q`.
* `TauCeti.image_inv_sub_eq_preimage_add_inv`: the inversion about `q` maps a set onto its
  preimage under `w ↦ q + w⁻¹`.
* `TauCeti.bijOn_inv_compl_ball_one`, `TauCeti.bijOn_inv_compl_closedBall_one` and
  `TauCeti.bijOn_inv_sphere_one`: inversion exchanges the exterior of the unit ball, of the closed
  unit ball, and the unit sphere with the punctured closed ball, the punctured ball and the sphere.
* `TauCeti.isClosed_setOf_ne_zero_and_add_inv_mem`: the inversion of a closed bounded set about
  any centre, with the centre removed, is closed.
* `TauCeti.isBounded_image_inv_sub`: the inversion of a set about a point outside its closure is
  bounded.
* `TauCeti.isBounded_image_inv_sub_iff`: the inversion of a set about a point outside it is
  bounded exactly when the point is outside its closure.
* `TauCeti.closure_image_inv_sub`: the closure of the inversion of an unbounded set is the
  inverted closure together with `0`.
* `TauCeti.isOpen_image_inv_sub`, `TauCeti.interior_image_inv_sub` and
  `TauCeti.frontier_image_inv_sub`: the inversion of an open set about a point outside it is open,
  the interior of the inversion of a set is the inversion of its interior, and inverting an
  unbounded set about a point outside it adds `0` to the inverted frontier.
* `TauCeti.isOpen_insert_zero_image_inv_sub`, `TauCeti.closure_insert_zero_image_inv_sub` and
  `TauCeti.frontier_insert_zero_image_inv_sub`: an open set with bounded complement, inverted about
  any point and completed by `0`, is open; the completed inversion of any set has the completed
  inverted closure as closure; and for a set with bounded complement and a centre outside its
  closure, the inverted frontier as frontier.
* `TauCeti.mapsTo_inv_ball_diff_singleton_compl_closedBall`: the inversion maps the punctured ball
  of radius `R⁻¹` about `0` outside the closed ball of radius `R`.
* `TauCeti.norm_inv_sub_le_of_mem_closedBall`, `TauCeti.norm_inv_sub_pow_le_of_mem_closedBall`
  and `TauCeti.norm_inv_sub_sub_inv_sub_le_of_mem_closedBall`: on a closed ball `closedBall c r`
  not containing `w`, `‖(w - z)⁻¹‖ ≤ (‖w - c‖ - r)⁻¹`,
  `‖((w - z) ^ n)⁻¹‖ ≤ ((‖w - c‖ - r) ^ n)⁻¹` and
  `‖(w - z)⁻¹ - (w - c)⁻¹‖ ≤ r / ((‖w - c‖ - r) ‖w - c‖)`.
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

section UnitBall

/-- Inversion is a bijection from the closed exterior `(ball 0 1)ᶜ` of the unit ball onto the
punctured closed unit ball. -/
theorem bijOn_inv_compl_ball_one :
    BijOn (fun w : 𝕜 => w⁻¹) (ball 0 1)ᶜ (closedBall 0 1 \ {0}) :=
  (Equiv.inv 𝕜).bijOn fun w => Iff.symm <| by
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · simp [hw, inv_le_one₀ (norm_pos_iff.mpr hw)]

/-- Inversion is a bijection from the exterior `(closedBall 0 1)ᶜ` of the closed unit ball onto
the punctured open unit ball. -/
theorem bijOn_inv_compl_closedBall_one :
    BijOn (fun w : 𝕜 => w⁻¹) (closedBall 0 1)ᶜ (ball 0 1 \ {0}) :=
  (Equiv.inv 𝕜).bijOn fun w => Iff.symm <| by
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · simp [hw, inv_lt_one₀ (norm_pos_iff.mpr hw)]

/-- Inversion is a bijection of the unit sphere. -/
theorem bijOn_inv_sphere_one : BijOn (fun w : 𝕜 => w⁻¹) (sphere 0 1) (sphere 0 1) :=
  (Equiv.inv 𝕜).bijOn fun w => Iff.symm <| by simp

end UnitBall

/-- **The inversion of a closed bounded set is closed.** For closed bounded `K` and any `q`, the
image `{w | w ≠ 0 ∧ q + w⁻¹ ∈ K}` of `K \ {q}` under `z ↦ (z - q)⁻¹` is closed: it stays away
from `0`, and away from `0` it is the preimage of `K` under `w ↦ q + w⁻¹`. -/
theorem isClosed_setOf_ne_zero_and_add_inv_mem (hK : IsClosed K) (hKb : IsBounded K) (q : 𝕜) :
    IsClosed {w : 𝕜 | w ≠ 0 ∧ q + w⁻¹ ∈ K} := by
  -- `K` lies in a closed ball of some radius `R > 0` about `q`, so the set lies outside the open
  -- ball of radius `R⁻¹` about `0`
  obtain ⟨R, hR, hKR⟩ := hKb.subset_closedBall_lt 0 q
  have hne : ∀ w : 𝕜, R⁻¹ ≤ ‖w‖ → w ≠ 0 := fun w hw =>
    norm_pos_iff.mp ((inv_pos.mpr hR).trans_le hw)
  have heq : {w : 𝕜 | w ≠ 0 ∧ q + w⁻¹ ∈ K} =
      {w : 𝕜 | R⁻¹ ≤ ‖w‖} ∩ (fun w : 𝕜 => q + w⁻¹) ⁻¹' K := by
    ext w
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    refine ⟨fun ⟨hw, hwK⟩ => ⟨?_, hwK⟩, fun ⟨hw, hwK⟩ => ⟨hne w hw, hwK⟩⟩
    have hle := mem_closedBall_iff_norm.mp (hKR hwK)
    rw [add_sub_cancel_left, norm_inv] at hle
    exact inv_le_of_inv_le₀ (norm_pos_iff.mpr hw) hle
  rw [heq]
  exact ContinuousOn.preimage_isClosed_of_isClosed
    (continuousOn_const.add (continuousOn_inv₀.mono hne))
    (isClosed_le continuous_const continuous_norm) hK

/-- The inversion maps the punctured ball of radius `R⁻¹` about `0` into the exterior of the
closed ball of radius `R`. -/
theorem mapsTo_inv_ball_diff_singleton_compl_closedBall (R : ℝ) :
    MapsTo (·⁻¹) (ball (0 : 𝕜) R⁻¹ \ {0}) (closedBall 0 R)ᶜ := by
  rintro w ⟨hw, hw0⟩
  simp only [mem_ball_zero_iff, mem_singleton_iff] at hw hw0
  have hR : 0 < R := inv_pos.1 ((norm_nonneg w).trans_lt hw)
  simpa [norm_inv] using (lt_inv_comm₀ (norm_pos_iff.2 hw0) hR).1 hw

/-- On a closed ball `closedBall c r` not containing `w`, the inversion about `w` is bounded:
`‖(w - z)⁻¹‖ ≤ (‖w - c‖ - r)⁻¹`. -/
theorem norm_inv_sub_le_of_mem_closedBall {c w z : 𝕜} {r : ℝ} (hz : z ∈ closedBall c r)
    (hw : r < ‖w - c‖) : ‖(w - z)⁻¹‖ ≤ (‖w - c‖ - r)⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ (sub_pos.mpr hw)
    (by linarith [norm_sub_le_norm_sub_add_norm_sub w z c, mem_closedBall_iff_norm.mp hz])

/-- On a closed ball `closedBall c r` not containing `w`, the powers of the inversion about `w`
are bounded: `‖((w - z) ^ n)⁻¹‖ ≤ ((‖w - c‖ - r) ^ n)⁻¹`. -/
theorem norm_inv_sub_pow_le_of_mem_closedBall {c w z : 𝕜} {r : ℝ} (hz : z ∈ closedBall c r)
    (hw : r < ‖w - c‖) (n : ℕ) : ‖((w - z) ^ n)⁻¹‖ ≤ ((‖w - c‖ - r) ^ n)⁻¹ := by
  rw [← inv_pow, norm_pow, ← inv_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inv_sub_le_of_mem_closedBall hz hw) n

/-- On a closed ball `closedBall c r` not containing `w`, the inversion about `w` differs from its
value at the centre by at most `r / ((‖w - c‖ - r) ‖w - c‖)`. -/
theorem norm_inv_sub_sub_inv_sub_le_of_mem_closedBall {c w z : 𝕜} {r : ℝ}
    (hz : z ∈ closedBall c r) (hw : r < ‖w - c‖) :
    ‖(w - z)⁻¹ - (w - c)⁻¹‖ ≤ r / ((‖w - c‖ - r) * ‖w - c‖) := by
  have hzc := mem_closedBall_iff_norm.mp hz
  have hρ : 0 < ‖w - c‖ := ((norm_nonneg _).trans hzc).trans_lt hw
  have hwz : 0 < ‖w - z‖ := by linarith [norm_sub_le_norm_sub_add_norm_sub w z c]
  rw [inv_sub_inv' (norm_pos_iff.mp hwz) (norm_pos_iff.mp hρ), sub_sub_sub_cancel_left,
    norm_mul, norm_mul, norm_inv (w - c)]
  calc ‖(w - z)⁻¹‖ * ‖z - c‖ * ‖w - c‖⁻¹ ≤ (‖w - c‖ - r)⁻¹ * r * ‖w - c‖⁻¹ := by
        gcongr
        exact norm_inv_sub_le_of_mem_closedBall hz hw
    _ = r / ((‖w - c‖ - r) * ‖w - c‖) := by field_simp

section Completion

variable {q : 𝕜} {U : Set 𝕜}

/-- Inverting a set `U` about a point `q` outside its closure gives a bounded set. -/
theorem isBounded_image_inv_sub (hq : q ∉ closure U) :
    IsBounded ((fun z : 𝕜 => (z - q)⁻¹) '' U) := by
  -- the points of `U` keep a distance `r > 0` from `q`, so the inversion is bounded by `r⁻¹`
  obtain ⟨r, hr, hrU⟩ : ∃ r > 0, ∀ z ∈ U, r ≤ dist q z := by
    simpa [Metric.mem_closure_iff] using hq
  refine isBounded_iff_forall_norm_le.mpr ⟨r⁻¹, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  rw [norm_inv, ← dist_eq_norm, dist_comm]
  exact inv_anti₀ hr (hrU z hz)

/-- **Inverting about a point outside a set gives a bounded set exactly when the point is outside
the closure.** For `q ∉ U`, the image of `U` under `z ↦ (z - q)⁻¹` is bounded if and only if
`q ∉ closure U`. -/
theorem isBounded_image_inv_sub_iff (hqU : q ∉ U) :
    IsBounded ((fun z : 𝕜 => (z - q)⁻¹) '' U) ↔ q ∉ closure U := by
  refine ⟨fun hb hq => ?_, isBounded_image_inv_sub⟩
  -- as `z` tends to `q` within `U`, the inversion `(z - q)⁻¹` tends to infinity
  have := mem_closure_iff_nhdsWithin_neBot.mp hq
  have hlim : Tendsto (fun z : 𝕜 => (z - q)⁻¹) (𝓝[U] q) (cobounded 𝕜) :=
    tendsto_inv₀_nhdsNE_zero.comp <| tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_sub_nhds_zero_iff.mpr tendsto_id).mono_left nhdsWithin_le_nhds)
      (eventually_mem_nhdsWithin.mono fun z hz => sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hqU))
  obtain ⟨z, hzb, hzU⟩ := ((hlim.eventually (isBounded_def.mp hb)).and self_mem_nhdsWithin).exists
  exact hzb (mem_image_of_mem _ hzU)

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

/-- Inverting an open set `U` about a point `q` outside it, the image is open. -/
theorem isOpen_image_inv_sub (hUo : IsOpen U) (hqU : q ∉ U) :
    IsOpen ((fun z : 𝕜 => (z - q)⁻¹) '' U) := by
  -- the image is the preimage of `U` under `w ↦ q + w⁻¹`, which is continuous away from `0`
  have : (fun z : 𝕜 => (z - q)⁻¹) '' U = {0}ᶜ ∩ (fun w : 𝕜 => q + w⁻¹) ⁻¹' U := by
    rw [image_inv_sub_eq_preimage_add_inv]
    exact (inter_eq_right (s := {0}ᶜ).mpr fun w hw => mem_compl_singleton_iff.mpr fun hw0 =>
      hqU (by simpa [hw0] using hw)).symm
  rw [this]
  exact (continuousOn_const.add continuousOn_inv₀).isOpen_inter_preimage isOpen_compl_singleton hUo

/-- Inverting a set `U` about a point `q` outside it, the interior of the image is the image of the
interior. -/
theorem interior_image_inv_sub (hq : q ∉ U) :
    interior ((fun z : 𝕜 => (z - q)⁻¹) '' U) = (fun z : 𝕜 => (z - q)⁻¹) '' interior U := by
  refine Subset.antisymm (fun w hw => ?_) (interior_maximal (image_mono interior_subset)
    (isOpen_image_inv_sub isOpen_interior fun h => hq (interior_subset h)))
  obtain ⟨u, hu, rfl⟩ := interior_subset hw
  -- the points off `q` inverted into the interior of the image form an open subset of `U`
  have hN : IsOpen ({q}ᶜ ∩ (fun z : 𝕜 => (z - q)⁻¹) ⁻¹' interior ((fun z : 𝕜 => (z - q)⁻¹) '' U)) :=
    (continuousOn_inv₀.comp (continuousOn_id.sub continuousOn_const) fun z hz => by
      simpa [sub_ne_zero] using hz).isOpen_inter_preimage isOpen_compl_singleton isOpen_interior
  have hNU : {q}ᶜ ∩ (fun z : 𝕜 => (z - q)⁻¹) ⁻¹' interior ((fun z : 𝕜 => (z - q)⁻¹) '' U) ⊆ U :=
    fun z hz => by
      obtain ⟨v, hv, hvz⟩ := interior_subset hz.2
      exact (inv_injective.comp (sub_left_injective (b := q)) hvz) ▸ hv
  exact ⟨u, hN.subset_interior_iff.mpr hNU ⟨fun h => hq (h ▸ hu), hw⟩, rfl⟩

/-- Inverting an unbounded set `U` about a point `q` outside it, the frontier of the image is the
image of the frontier together with `0`, the image of infinity. -/
theorem frontier_image_inv_sub (hq : q ∉ U) (hUb : ¬IsBounded U) :
    frontier ((fun z : 𝕜 => (z - q)⁻¹) '' U) =
      insert 0 ((fun z : 𝕜 => (z - q)⁻¹) '' frontier U) := by
  have hU0 : (0 : 𝕜) ∉ (fun z : 𝕜 => (z - q)⁻¹) '' interior U := by
    simpa [sub_eq_zero] using fun h => hq (interior_subset h)
  rw [frontier, closure_image_inv_sub hUb, interior_image_inv_sub hq,
    insert_sdiff_of_notMem _ hU0, frontier, image_sdiff (f := fun z : 𝕜 => (z - q)⁻¹)
      (inv_injective.comp (sub_left_injective (b := q)))]

/-- Inverting a set `U` with bounded complement about a point `q` outside its closure, and adding
`0`, the image of infinity, the frontier of the resulting set is the inverted frontier of `U`. -/
theorem frontier_insert_zero_image_inv_sub (hq : q ∉ closure U) (hUc : IsBounded Uᶜ) :
    frontier (insert 0 ((fun z : 𝕜 => (z - q)⁻¹) '' U)) =
      (fun z : 𝕜 => (z - q)⁻¹) '' frontier U := by
  have h0 : (0 : 𝕜) ∉ (fun z : 𝕜 => (z - q)⁻¹) '' closure U := by simpa [sub_eq_zero] using hq
  -- the interior of the completed image is the completed image of the interior: the completed
  -- image of the interior is open, and away from `0` this is `interior_image_inv_sub`
  have hint : interior (insert 0 ((fun z : 𝕜 => (z - q)⁻¹) '' U)) =
      insert 0 ((fun z : 𝕜 => (z - q)⁻¹) '' interior U) := by
    refine Subset.antisymm (fun w hw => ?_) (interior_maximal
      (insert_subset_insert (image_mono interior_subset))
      (isOpen_insert_zero_image_inv_sub isOpen_interior (closure_compl (s := U) ▸ hUc.closure)))
    rcases eq_or_ne w 0 with rfl | hw0
    · exact mem_insert _ _
    have hw' : w ∈ interior (insert 0 ((fun z : 𝕜 => (z - q)⁻¹) '' U) ∩ {0}ᶜ) := by
      rw [interior_inter, isOpen_compl_singleton.interior_eq]
      exact ⟨hw, hw0⟩
    rw [← interior_image_inv_sub fun h => hq (subset_closure h)]
    refine mem_insert_of_mem _ (interior_mono ?_ hw')
    exact fun x hx => (mem_insert_iff.mp hx.1).resolve_left hx.2
  rw [frontier, closure_insert_zero_image_inv_sub, hint, insert_sdiff_of_mem _ (mem_insert _ _),
    sdiff_insert_of_notMem h0, frontier, image_sdiff (f := fun z : 𝕜 => (z - q)⁻¹)
      (inv_injective.comp (sub_left_injective (b := q)))]

end Completion

end TauCeti

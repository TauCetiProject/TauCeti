/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Round subdiscs of the open unit disc

A round disc `B(c, r)` with `‖c‖ + r ≤ 1` lies in `𝔻`, and the affine map `z ↦ c + r z` parametrizes
it by `𝔻` (`TauCeti.Complex.UnitDisc.subdisc`), with inverse `w ↦ (w - c) / r`
(`TauCeti.Complex.UnitDisc.coe_subdisc_sub_div`); read in `ℂ` it is the restriction of the affine
homeomorphism `affineHomeomorph` of `ℂ` (`TauCeti.Complex.UnitDisc.coe_comp_subdisc`), hence an
open embedding (`TauCeti.Complex.UnitDisc.isOpenEmbedding_coe_comp_subdisc`). These maps compose
like affine maps (`TauCeti.Complex.UnitDisc.subdisc_comp_subdisc`). If a compact subset `K` of
`𝔻` meets no point of the circle `‖z - c‖ = r`, then the points of `𝔻` that `subdisc c r` sends
into `K` form a compact set (`TauCeti.Complex.UnitDisc.isCompact_subdisc_preimage`): they are the
rescaled points of `K` inside the disc, and the points of `K` in `B(c, r)` are its points at
distance at most `r` from `c`, a compact set. This is what makes the restriction of a disc map to a
round subdisc again a map with compact preimage of a closed set, as in the theory of positive
cohomology assignments.

Points of a finite subset of `𝔻` can be isolated in pairwise disjoint round discs inside `𝔻`, on
which a function continuous at these points varies arbitrarily little
(`Complex.UnitDisc.exists_isolating_radius`).
-/

public section

noncomputable section

open Metric Set Topology
open scoped Complex.UnitDisc

namespace Complex.UnitDisc

/-- If `‖c‖ + r ≤ 1` and `r > 0`, then `c + r z` lies in the open unit disc for every `z ∈ 𝔻`. -/
theorem norm_add_mul_lt_one {c : ℂ} {r : ℝ} (hc : ‖c‖ + r ≤ 1) (hr : 0 < r) (z : 𝔻) :
    ‖c + r * (z : ℂ)‖ < 1 := by
  calc ‖c + r * (z : ℂ)‖ ≤ ‖c‖ + r * ‖(z : ℂ)‖ := by
        simpa [norm_mul, Complex.norm_real, abs_of_pos hr] using norm_add_le c (r * (z : ℂ))
    _ < ‖c‖ + r * 1 := by gcongr; exact z.norm_lt_one
    _ ≤ 1 := by linarith

/-- Every point `z` of the unit disc is the centre of round discs `B(z, r) ⊆ 𝔻` of every small
enough radius: for `ε > 0` there is such a radius `0 < r < ε`. -/
theorem exists_pos_lt_and_norm_add_le_one (z : 𝔻) {ε : ℝ} (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r < ε ∧ ‖(z : ℂ)‖ + r ≤ 1 := by
  have hz := z.norm_lt_one
  refine ⟨min (ε / 2) (1 - ‖(z : ℂ)‖), lt_min (by positivity) (by linarith),
    (min_le_left _ _).trans_lt (by linarith), ?_⟩
  linarith [min_le_right (ε / 2) (1 - ‖(z : ℂ)‖)]

/-- A function continuous at a point `z` of the disc is uniformly close to its value at `z` on a
round disc about `z`. -/
theorem exists_pos_forall_dist_lt {F : Type*} [PseudoMetricSpace F] {g : 𝔻 → F} {z : 𝔻}
    (hg : ContinuousAt g z) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ > 0, ∀ x : 𝔻, (x : ℂ) ∈ ball (z : ℂ) ρ → dist (g x) (g z) < δ := by
  have hmem := hg (ball_mem_nhds (g z) hδ)
  rw [isEmbedding_coe.isInducing.nhds_eq_comap, Filter.mem_map, Filter.mem_comap] at hmem
  obtain ⟨t, ht, hts⟩ := hmem
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 ht
  exact ⟨ρ, hρ, fun x hx ↦ hts (hball hx)⟩

/-- **Isolating radii.** Around the points of a finite set `s₀ ⊆ 𝔻` there are round discs
`B(z, r z) ⊆ 𝔻`, pairwise disjoint and isolating each point of `s₀` even at twice the radius, on
which a function continuous at the points of `s₀` varies by less than a given `δ > 0`. -/
theorem exists_isolating_radius {F : Type*} [PseudoMetricSpace F] (s₀ : Finset 𝔻)
    {g : 𝔻 → F} (hg : ∀ z ∈ s₀, ContinuousAt g z) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : 𝔻 → ℝ, (∀ z, 0 < r z) ∧ (∀ z : 𝔻, ‖(z : ℂ)‖ + r z ≤ 1) ∧
      (∀ z w : 𝔻, w ∈ s₀ → (w : ℂ) ∈ ball (z : ℂ) (2 * r z) → w = z) ∧
      (∀ z ∈ s₀, ∀ x : 𝔻, (x : ℂ) ∈ ball (z : ℂ) (r z) → dist (g x) (g z) < δ) ∧
      ∀ x : 𝔻, ∀ z ∈ s₀, ∀ z' ∈ s₀, (x : ℂ) ∈ ball (z : ℂ) (r z) →
        (x : ℂ) ∈ ball (z' : ℂ) (r z') → z = z' := by
  have hrad : ∀ z : 𝔻, ∃ r > 0, ‖(z : ℂ)‖ + r ≤ 1 ∧
      (∀ w ∈ s₀, (w : ℂ) ∈ ball (z : ℂ) (2 * r) → w = z) ∧
      (z ∈ s₀ → ∀ x : 𝔻, (x : ℂ) ∈ ball (z : ℂ) r → dist (g x) (g z) < δ) := by
    intro z
    obtain ⟨R, hR, hisoR⟩ := z.exists_pos_forall_mem_ball_eq s₀
    obtain ⟨ρ, hρ, hgρ⟩ : ∃ ρ > 0, z ∈ s₀ →
        ∀ x : 𝔻, (x : ℂ) ∈ ball (z : ℂ) ρ → dist (g x) (g z) < δ := by
      by_cases hz : z ∈ s₀
      · obtain ⟨ρ, hρ, h⟩ := exists_pos_forall_dist_lt (hg z hz) hδ
        exact ⟨ρ, hρ, fun _ ↦ h⟩
      · exact ⟨1, one_pos, fun h ↦ (hz h).elim⟩
    obtain ⟨r, hr, hrlt, hc⟩ := exists_pos_lt_and_norm_add_le_one z (lt_min (half_pos hR) hρ)
    refine ⟨r, hr, hc, fun w hw hwb ↦ hisoR w hw (ball_subset_ball ?_ hwb), fun hz x hx ↦
      hgρ hz x (ball_subset_ball ?_ hx)⟩
    · linarith [min_le_left (R / 2) ρ]
    · linarith [min_le_right (R / 2) ρ]
  choose r hr hc hiso hgr using hrad
  refine ⟨r, hr, hc, fun z ↦ hiso z, hgr, fun x z hz z' hz' hxz hxz' ↦ ?_⟩
  -- Two points of `s₀` are at least twice either radius apart, so their discs are disjoint.
  by_contra hne
  have h1 : 2 * r z ≤ dist (z' : ℂ) z := not_lt.1 fun h ↦ hne (hiso z z' hz' h).symm
  have h2 : 2 * r z' ≤ dist (z : ℂ) z' := not_lt.1 fun h ↦ hne (hiso z' z hz h)
  have := dist_triangle (z : ℂ) x z'
  rw [mem_ball] at hxz hxz'
  rw [dist_comm] at hxz
  linarith [dist_comm (z : ℂ) z']

end Complex.UnitDisc

open Complex.UnitDisc

namespace TauCeti.Complex.UnitDisc

/-- The **round subdisc map** `z ↦ c + r z`, parametrizing the disc `B(c, r)` of `ℂ` by the open
unit disc. It is defined when `B(c, r)` lies in the unit disc, that is when `‖c‖ + r ≤ 1`, and
`r > 0`. -/
def subdisc (c : ℂ) (r : ℝ) (hc : ‖c‖ + r ≤ 1) (hr : 0 < r) : C(𝔻, 𝔻) where
  toFun z := mk (c + r * z) (norm_add_mul_lt_one hc hr z)
  continuous_toFun := by
    refine (isEmbedding_coe.continuous_iff).2 ?_
    exact continuous_const.add (continuous_const.mul continuous_coe)

variable {c c' : ℂ} {r r' : ℝ} {hc : ‖c‖ + r ≤ 1} {hr : 0 < r}

@[simp]
theorem coe_subdisc_apply (z : 𝔻) : (subdisc c r hc hr z : ℂ) = c + r * z :=
  (rfl)

/-- The round subdisc map `subdisc c r`, read in `ℂ`, is the restriction to `𝔻` of the affine
homeomorphism `w ↦ r w + c` of `ℂ` (`affineHomeomorph`). -/
theorem coe_comp_subdisc :
    ((↑) : 𝔻 → ℂ) ∘ subdisc c r hc hr =
      affineHomeomorph (r : ℂ) c (Complex.ofReal_ne_zero.2 hr.ne') ∘ (↑) := by
  ext z
  simp [add_comm]

/-- The round subdisc map `subdisc c r`, read in `ℂ`, is an open embedding: it is the restriction
to `𝔻` of the affine homeomorphism `w ↦ c + r w` of `ℂ`. -/
theorem isOpenEmbedding_coe_comp_subdisc :
    IsOpenEmbedding (((↑) : 𝔻 → ℂ) ∘ subdisc c r hc hr) := by
  rw [coe_comp_subdisc]
  exact (affineHomeomorph _ _ _).isOpenEmbedding.comp isOpenEmbedding_coe

/-- A point of the unit disc lies in the image of `subdisc c r` exactly when it lies in the disc
`B(c, r)`. -/
theorem mem_range_subdisc {w : 𝔻} : w ∈ range (subdisc c r hc hr) ↔ (w : ℂ) ∈ ball c r := by
  constructor
  · rintro ⟨z, rfl⟩
    simpa [dist_eq_norm, abs_of_pos hr] using mul_lt_mul_of_pos_left z.norm_lt_one hr
  · intro hw
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    have hz : ‖((w : ℂ) - c) / r‖ < 1 := by
      simpa [abs_of_pos hr, div_lt_one hr, ← dist_eq_norm] using hw
    refine ⟨mk _ hz, coe_injective ?_⟩
    simp [mul_div_cancel₀ _ hr0]

/-- The round subdisc map `subdisc c r` is inverted by `w ↦ (w - c) / r`. -/
theorem coe_subdisc_sub_div (z : 𝔻) : ((subdisc c r hc hr z : ℂ) - c) / r = z := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  simp [mul_div_cancel_left₀ _ hr0]

/-- The round subdisc map `subdisc c r` is injective. -/
theorem subdisc_injective : Function.Injective (subdisc c r hc hr) :=
  isOpenEmbedding_coe_comp_subdisc.injective.of_comp

/-- Round subdisc maps compose like the affine maps they are:
`subdisc c r ∘ subdisc c' r' = subdisc (c + r c') (r r')`. -/
theorem subdisc_comp_subdisc {hc' : ‖c'‖ + r' ≤ 1} {hr' : 0 < r'}
    (h : ‖c + r * c'‖ + r * r' ≤ 1) :
    (subdisc c r hc hr).comp (subdisc c' r' hc' hr') =
      subdisc (c + r * c') (r * r') h (mul_pos hr hr') := by
  ext z
  simp only [ContinuousMap.comp_apply, coe_subdisc_apply, Complex.ofReal_mul]
  ring

/-- The image in `ℂ` of the points of `𝔻` sent by `subdisc c r` into a set `K ⊆ 𝔻` is the rescaled
part of `K` inside `B(c, r)`. -/
theorem image_coe_subdisc_preimage (K : Set 𝔻) :
    (↑) '' (subdisc c r hc hr ⁻¹' K) =
      (fun w : ℂ ↦ (w - c) / r) '' ((↑) '' K ∩ ball c r) := by
  ext z
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨subdisc c r hc hr z, ⟨⟨_, hz, rfl⟩, mem_range_subdisc.1 ⟨z, rfl⟩⟩,
      coe_subdisc_sub_div z⟩
  · rintro ⟨w, ⟨⟨w, hw, rfl⟩, hwb⟩, rfl⟩
    obtain ⟨z, rfl⟩ := (mem_range_subdisc (hc := hc) (hr := hr)).2 hwb
    exact ⟨z, hw, (coe_subdisc_sub_div z).symm⟩

/-- If a compact set `K` of the unit disc has no point on the circle `‖z - c‖ = r`, then the
points of `𝔻` that `subdisc c r` sends into `K` form a compact set. -/
theorem isCompact_subdisc_preimage {K : Set 𝔻} (hK : IsCompact K)
    (hKs : ∀ z ∈ K, ‖(z : ℂ) - c‖ ≠ r) : IsCompact (subdisc c r hc hr ⁻¹' K) := by
  rw [isEmbedding_coe.isCompact_iff, image_coe_subdisc_preimage]
  have hKb : (↑) '' K ∩ ball c r = (↑) '' K ∩ closedBall c r := by
    refine Subset.antisymm (inter_subset_inter_right _ ball_subset_closedBall) ?_
    rintro _ ⟨⟨z, hz, rfl⟩, hzb⟩
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rw [mem_closedBall, dist_eq_norm] at hzb
    exact mem_ball_iff_norm.2 (lt_of_le_of_ne hzb (hKs z hz))
  rw [hKb]
  exact ((hK.image continuous_coe).inter_right isClosed_closedBall).image
    ((continuous_id.sub continuous_const).div_const _)

end TauCeti.Complex.UnitDisc

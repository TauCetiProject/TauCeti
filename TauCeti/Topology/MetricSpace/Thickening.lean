/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening

import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Thickenings

Compact pairwise disjoint sets in a finite family in an extended metric space admit pairwise
disjoint thickenings of one common positive radius. This supplies uniformly separated
neighborhoods, all of the same metric size. A locally finite family of pairwise disjoint compact
sets still admits pairwise disjoint closed thickenings, with radii depending on the member
(`LocallyFinite.exists_cthickenings_pairwiseDisjoint`). In a proper space, closed thickenings of
the members of a locally finite family by bounded radii again form a locally finite family
(`LocallyFinite.cthickening`).

In a pseudometric space, the closed `δ`-thickening of a nonempty set, for `δ ≥ 0`, consists of the
points at distance at most `δ` from it (`TauCeti.mem_cthickening_iff_infDist_le`). This is the
closed counterpart of Mathlib's `Metric.mem_thickening_iff_infDist_lt`, and describes closed
thickenings as sublevel sets of the distance function, and their complements as strict
superlevel sets (`TauCeti.compl_cthickening_eq_setOf_lt_infDist`).

On the real line, the terms of an injective two-sided sequence tending to `-∞` and `+∞` at its two
ends have pairwise disjoint closed intervals around them forming a locally finite family
(`TauCeti.exists_closedBall_pairwiseDisjoint_locallyFinite`). An open subset of `X × ℝ` containing
a vertical line contains a tube around it, whose radius is locally bounded below by positive
constants (`IsOpen.exists_tube_subset`).

Under a `K`-Lipschitz map, the `R / K`-thickening of a preimage lies in the preimage of the
`R`-thickening (`TauCeti.thickening_preimage_subset_preimage_thickening`), and likewise for closed
thickenings when `K > 0` (`TauCeti.cthickening_preimage_subset_preimage_cthickening`).
-/

public section

open Set Metric Function
open scoped Topology NNReal ENNReal

namespace TauCeti

/-- A finite family of pairwise disjoint compact sets in an extended metric space admits pairwise
disjoint thickenings of one common positive radius. This extends Mathlib's two-set result
`Disjoint.exists_thickenings`. -/
theorem exists_thickenings_pairwiseDisjoint
    {X ι : Type*} [EMetricSpace X] [Finite ι]
    (K : ι → Set X) (hK : ∀ i, IsCompact (K i))
    (hdisj : Pairwise (Disjoint on K)) :
    ∃ δ : ℝ, 0 < δ ∧ Pairwise (Disjoint on fun i => thickening δ (K i)) := by
  have h : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Pairwise (Disjoint on fun i => thickening δ (K i)) := by
    simp only [Pairwise, Filter.eventually_all]
    intro i j hij
    obtain ⟨δ, hδ, hd⟩ := (hdisj hij).exists_thickenings (hK i) (hK j).isClosed
    filter_upwards [eventually_lt_nhds hδ |>.filter_mono nhdsWithin_le_nhds] with ε hε
    exact hd.mono (thickening_mono hε.le _) (thickening_mono hε.le _)
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  exact (hpos.and h).exists

/-- For `δ ≥ 0`, a point lies in the closed `δ`-thickening of a nonempty set exactly when its
distance to the set is at most `δ`. -/
theorem mem_cthickening_iff_infDist_le {X : Type*} [PseudoMetricSpace X] {s : Set X}
    (hs : s.Nonempty) {δ : ℝ} (hδ : 0 ≤ δ) {x : X} : x ∈ cthickening δ s ↔ infDist x s ≤ δ := by
  rw [mem_cthickening_iff, ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hs) hδ, infDist]

/-- For `δ ≥ 0`, the complement of the closed `δ`-thickening of a nonempty set consists of the
points at distance more than `δ` from it. -/
theorem compl_cthickening_eq_setOf_lt_infDist {X : Type*} [PseudoMetricSpace X] {s : Set X}
    (hs : s.Nonempty) {δ : ℝ} (hδ : 0 ≤ δ) : (cthickening δ s)ᶜ = {x | δ < infDist x s} := by
  ext x
  simp [mem_cthickening_iff_infDist_le hs hδ]

/-- Under a `K`-Lipschitz map, the `R / K`-thickening of a preimage lies in the preimage of the
`R`-thickening. -/
theorem thickening_preimage_subset_preimage_thickening {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {f : X → Y} {K : ℝ≥0} {R : ℝ} (hf : LipschitzWith K f)
    (S : Set Y) : thickening (R / K) (f ⁻¹' S) ⊆ f ⁻¹' thickening R S := by
  rcases eq_or_ne K 0 with rfl | hK
  · simp [thickening_of_nonpos]
  intro y hy
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.1 hy
  refine mem_thickening_iff.2 ⟨f z, mem_preimage.1 hz, (hf.dist_le_mul y z).trans_lt ?_⟩
  have hK' : (0 : ℝ) < K := by positivity
  calc (K : ℝ) * dist y z < K * (R / K) := by gcongr
    _ = R := by field_simp

/-- Under a `K`-Lipschitz map, with `K > 0`, the closed `R / K`-thickening of a preimage lies in
the preimage of the closed `R`-thickening. -/
theorem cthickening_preimage_subset_preimage_cthickening {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {f : X → Y} {K : ℝ≥0} {R : ℝ} (hf : LipschitzWith K f) (hK : 0 < K)
    (S : Set Y) : cthickening (R / K) (f ⁻¹' S) ⊆ f ⁻¹' cthickening R S := by
  intro x hx
  rw [mem_cthickening_iff] at hx
  rw [mem_preimage, mem_cthickening_iff]
  have hK0 : (K : ℝ≥0∞) ≠ 0 := by simpa using hK.ne'
  have hle : infEDist (f x) S ≤ K * infEDist x (f ⁻¹' S) := by
    simp only [infEDist, ENNReal.mul_iInf_of_ne hK0 ENNReal.coe_ne_top]
    refine le_iInf₂ fun y hy ↦ ?_
    exact (infEDist_le_edist_of_mem (mem_preimage.1 hy)).trans (hf.edist_le_mul x y)
  refine hle.trans ((mul_le_mul' le_rfl hx).trans ?_)
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg,
    mul_div_cancel₀ _ (by simpa using hK.ne')]

end TauCeti

namespace LocallyFinite

variable {ι X : Type*}

/-- A locally finite family of pairwise disjoint compact sets in an extended metric space admits
pairwise disjoint closed thickenings, of positive radii depending on the member. This extends
Mathlib's two-set result `Disjoint.exists_cthickenings`. -/
theorem exists_cthickenings_pairwiseDisjoint [EMetricSpace X] {K : ι → Set X}
    (hK : ∀ i, IsCompact (K i)) (hdisj : Pairwise (Disjoint on K)) (hlf : LocallyFinite K) :
    ∃ δ : ι → ℝ, (∀ i, 0 < δ i) ∧ Pairwise (Disjoint on fun i ↦ cthickening (δ i) (K i)) := by
  -- Separate each member from the closed union of all the others.
  have hsep (i : ι) : ∃ δ, 0 < δ ∧
      Disjoint (cthickening δ (K i)) (cthickening δ (⋃ j : {j // j ≠ i}, K j)) :=
    (disjoint_iUnion_right.2 fun j ↦ hdisj j.2.symm).exists_cthickenings (hK i)
      ((hlf.comp_injective Subtype.val_injective).isClosed_iUnion fun j ↦ (hK j).isClosed)
  choose δ hδ hsep using hsep
  -- The member with the larger radius is separated from the thickening of the other one.
  have key {i j : ι} (hij : i ≠ j) (hle : δ j ≤ δ i) :
      Disjoint (cthickening (δ i) (K i)) (cthickening (δ j) (K j)) :=
    (hsep i).mono_right <| (cthickening_mono hle _).trans <|
      cthickening_subset_of_subset _ <| subset_iUnion_of_subset ⟨j, hij.symm⟩ subset_rfl
  refine ⟨δ, hδ, fun i j hij ↦ ?_⟩
  rcases le_total (δ j) (δ i) with hle | hle
  · exact key hij hle
  · exact (key hij.symm hle).symm

/-- In a proper space, the closed thickenings of the members of a locally finite family by
radii bounded above form a locally finite family. -/
protected theorem cthickening [PseudoMetricSpace X] [ProperSpace X] {f : ι → Set X}
    (hf : LocallyFinite f) {δ : ι → ℝ} {R : ℝ} (hδ : ∀ i, δ i ≤ R) :
    LocallyFinite fun i ↦ cthickening (δ i) (f i) := by
  intro x
  refine ⟨ball x 1, ball_mem_nhds x one_pos,
    (hf.finite_nonempty_inter_compact (isCompact_closedBall x (max R 0 + 2))).subset ?_⟩
  rintro i ⟨y, hy, hyx⟩
  have hR : 0 < max R 0 + 1 := by positivity
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.1 <|
    cthickening_subset_thickening' hR ((hδ i).trans_lt (by linarith [le_max_left R 0])) _ hy
  refine ⟨z, hz, mem_closedBall.2 ?_⟩
  linarith [dist_triangle z y x, dist_comm z y, mem_ball.1 hyx]

end LocallyFinite

section

open Filter

namespace TauCeti

/-- Around the terms of an injective two-sided sequence of reals tending to `-∞` and to `+∞` at
its two ends, there are closed intervals of positive radii at most `1` which are pairwise disjoint
and form a locally finite family. -/
theorem exists_closedBall_pairwiseDisjoint_locallyFinite (x : ℤ → ℝ) (hx : Injective x)
    (htop : Tendsto x atTop atTop) (hbot : Tendsto x atBot atBot) :
    ∃ ε : ℤ → ℝ, (∀ ν, 0 < ε ν ∧ ε ν ≤ 1) ∧
      Pairwise (Disjoint on fun ν ↦ closedBall (x ν) (ε ν)) ∧
      LocallyFinite fun ν ↦ closedBall (x ν) (ε ν) := by
  have hlf : LocallyFinite fun ν ↦ ({x ν} : Set ℝ) := by
    simpa only [Icc_self] using locallyFinite_Icc_of_tendsto htop hbot
  obtain ⟨δ, hδ, hdisj⟩ := hlf.exists_cthickenings_pairwiseDisjoint (fun _ ↦ isCompact_singleton)
    fun ν μ h ↦ disjoint_singleton.2 (hx.ne h)
  refine ⟨fun ν ↦ min (δ ν) 1, fun ν ↦ ⟨lt_min (hδ ν) one_pos, min_le_right _ _⟩,
    fun ν μ h ↦ Disjoint.mono ?_ ?_ (hdisj h), ?_⟩
  · exact (closedBall_subset_closedBall (min_le_left _ _)).trans
      (cthickening_singleton _ (hδ ν).le).ge
  · exact (closedBall_subset_closedBall (min_le_left _ _)).trans
      (cthickening_singleton _ (hδ μ).le).ge
  · have := hlf.cthickening (δ := fun ν ↦ min (δ ν) 1) (R := 1) fun ν ↦ min_le_right _ _
    simpa only [cthickening_singleton _ (lt_min (hδ _) one_pos).le] using this

end TauCeti

/-- **Tubes around a vertical line.** An open subset `W` of `X × ℝ` containing the vertical line
through `c` contains a tube `{(u, t) | dist u c ≤ γ t}` around that line, whose radius `γ` is
locally bounded below by positive constants. -/
theorem IsOpen.exists_tube_subset {X : Type*} [PseudoMetricSpace X] {c : X}
    {W : Set (X × ℝ)} (hW : IsOpen W) (hcW : ∀ t, (c, t) ∈ W) :
    ∃ γ : ℝ → ℝ, (∀ x, ∃ r > 0, ∀ᶠ y in 𝓝 x, r ≤ γ y) ∧
      ∀ u t, dist u c ≤ γ t → (u, t) ∈ W := by
  -- Over each interval `[n, n + 1]`, the compact segment of the line has a thickening in `W`.
  have hK (n : ℤ) : IsCompact ({c} ×ˢ Icc (n : ℝ) (n + 1)) := isCompact_singleton.prod isCompact_Icc
  choose δ hδ hδW using fun n : ℤ ↦ (hK n).exists_thickening_subset_open hW
    (by rintro ⟨u, t⟩ ⟨hu : u = c, -⟩; exact hu ▸ hcW t)
  refine ⟨fun t ↦ δ ⌊t⌋ / 2, fun x ↦ ⟨min (δ ⌊x⌋) (δ (⌊x⌋ - 1)) / 2,
    half_pos (lt_min (hδ _) (hδ _)), ?_⟩, fun u t hut ↦ hδW ⌊t⌋ ?_⟩
  · have hx : Ioo ((⌊x⌋ : ℝ) - 1) (⌊x⌋ + 1) ∈ 𝓝 x :=
      Ioo_mem_nhds (by linarith [Int.floor_le x]) (Int.lt_floor_add_one x)
    filter_upwards [hx] with y hy
    have h₁ : ⌊x⌋ - 1 ≤ ⌊y⌋ := Int.le_floor.2 (by push_cast; exact hy.1.le)
    have h₂ : ⌊y⌋ < ⌊x⌋ + 1 := Int.floor_lt.2 (by push_cast; exact hy.2)
    obtain h | h : ⌊y⌋ = ⌊x⌋ ∨ ⌊y⌋ = ⌊x⌋ - 1 := by omega
    · rw [h]
      exact div_le_div_of_nonneg_right (min_le_left _ _) zero_le_two
    · rw [h]
      exact div_le_div_of_nonneg_right (min_le_right _ _) zero_le_two
  · refine mem_thickening_iff.2 ⟨(c, t), ⟨mem_singleton c, Int.floor_le t,
      (Int.lt_floor_add_one t).le⟩, ?_⟩
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
    exact hut.trans_lt (half_lt_self (hδ _))

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening

import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.MetricSpace.ProperSpace
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
-/

public section

open Set Metric Function
open scoped Topology

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

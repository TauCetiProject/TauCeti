/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Sets.Compacts

import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Topology.Order.DenselyOrdered
import TauCeti.Topology.ConnectedComponents

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
superlevel sets (`TauCeti.compl_cthickening_eq_setOf_lt_infDist`). If a compact set does not meet
the closed `δ`-thickening of a set `t`, its own closed `δ`-thickening does not meet `t`
(`IsCompact.disjoint_cthickening_left`). A point is not in the closed `δ`-thickening of the
complement of a ball around it of larger radius (`TauCeti.notMem_cthickening_compl_ball`). In a
proper space, the closed `δ`-thickening of a compact set is compact
(`TopologicalSpace.Compacts.cthickening`). If balls of radius `η` cover a set `T`, the closed
balls of radius `η` meeting `T` among them lie in the closed `2 η`-thickening of `T`, so their
union contains `T` and has extended diameter at most `ediam T + 4 η`
(`TauCeti.exists_subset_biUnion_closedBall_and_ediam_le`).

A closed set in a pseudometric space is the intersection of an antitone sequence of open sets
inside any set whose interior contains it, namely the intersections of that interior with
thickenings of radii `1 / (n + 1)` (`IsClosed.exists_antitone_isOpen_iInter_eq`). In a locally
compact, locally connected pseudometrizable space, a compact set has an antitone basis of open
neighbourhoods, each with compact closure inside the previous one and with every connected
component meeting the set (`IsCompact.exists_hasAntitoneBasis_nhdsSet`). Holomorphic germs along
a compact subset of `ℂⁿ` are the inductive limit of the bounded holomorphic functions on such a
basis, whose restriction maps are then compact and injective.
If the `δ`-thickenings of two sets are disjoint, every point of the first is at distance at least
`δ / 2` from the closed `δ / 2`-thickening of the second
(`Disjoint.half_le_dist_of_mem_cthickening`).

On the real line, the terms of an injective two-sided sequence tending to `-∞` and `+∞` at its two
ends have pairwise disjoint closed intervals around them forming a locally finite family
(`TauCeti.exists_closedBall_pairwiseDisjoint_locallyFinite`). An open subset of `X × ℝ` containing
a vertical line contains a tube around it, whose radius is locally bounded below by positive
constants (`IsOpen.exists_tube_subset`).

For an open set `s` with nonempty complement and `δ → 0`, the sets `{y | δ < infDist y sᶜ}`
exhaust `s` from the inside, eventually containing a ball around each point of `s`
(`IsOpen.exists_eventually_closedBall_subset_setOf_lt_infDist`). If `s` is moreover bounded in a
proper space, a function continuous on `closure s` and at most `m` on `frontier s` is below
`m + η` near the complement of `s` (`IsOpen.exists_pos_forall_lt_add_of_infDist_lt`).
A compact subset `K` of an open set `U` has a radius `δ > 0` such that the closed `δ`-balls
around the points of `cthickening δ K` stay in `U`
(`IsCompact.exists_forall_closedBall_subset_of_isOpen`).
In a proper space, a compact subset of an open set `Ω` has an open neighbourhood with compact
closure inside `Ω` containing all closed balls of small enough radius about its points
(`IsCompact.exists_isOpen_closedBall_subset`).
Under a `K`-Lipschitz map, the `R / K`-thickening of a preimage lies in the preimage of the
`R`-thickening (`LipschitzWith.thickening_preimage_subset_preimage_thickening`), and likewise for
closed thickenings (`LipschitzWith.cthickening_preimage_subset_preimage_cthickening`). Removing a
positive-radius open thickening of `tᶜ` from any set `s` keeps the result inside `t`
(`Metric.sdiff_thickening_compl_subset`).
-/

public section

open Set Metric Function
open scoped Topology NNReal ENNReal

namespace Metric

/-- Removing a positive-radius open thickening of `tᶜ` from any set `s` keeps the result inside
`t`. -/
theorem sdiff_thickening_compl_subset {X : Type*} [PseudoEMetricSpace X] (s t : Set X) {δ : ℝ}
    (hδ : 0 < δ) : s \ thickening δ tᶜ ⊆ t := by
  rintro x ⟨-, hx⟩
  by_contra hxt
  exact hx (self_subset_thickening hδ tᶜ hxt)

end Metric

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

/-- If the open balls `ball p η`, `p ∈ J`, cover a set `T`, then `T` lies in the union of the closed
balls `closedBall p η` about the centres `p ∈ J` whose balls meet `T`, and this union has extended
diameter at most `ediam T + 4 η`: it lies in the closed `2 η`-thickening of `T`. -/
theorem exists_subset_biUnion_closedBall_and_ediam_le {X : Type*} [PseudoMetricSpace X]
    {J : Set X} {η : ℝ} (hη : 0 ≤ η) {T : Set X} (hT : T ⊆ ⋃ p ∈ J, ball p η) :
    ∃ I ⊆ J, T ⊆ ⋃ p ∈ I, closedBall p η ∧
      ediam (⋃ p ∈ I, closedBall p η) ≤ ediam T + ENNReal.ofReal (4 * η) := by
  refine ⟨{p ∈ J | (closedBall p η ∩ T).Nonempty}, sep_subset _ _, fun y hy => ?_, ?_⟩
  · obtain ⟨p, hpJ, hyp⟩ := mem_iUnion₂.1 (hT hy)
    exact mem_iUnion₂.2 ⟨p, ⟨hpJ, y, ball_subset_closedBall hyp, hy⟩, ball_subset_closedBall hyp⟩
  have hsub : ⋃ p ∈ {p ∈ J | (closedBall p η ∩ T).Nonempty}, closedBall p η ⊆
      cthickening (2 * η) T := iUnion₂_subset fun p ⟨_, t, htp, htT⟩ z hz =>
    mem_cthickening_of_dist_le z t _ T htT <| (dist_triangle z p t).trans <| by
      rw [dist_comm p t]
      linarith [mem_closedBall.1 hz, mem_closedBall.1 htp]
  rw [← Real.coe_toNNReal _ (by positivity : 0 ≤ 2 * η)] at hsub
  refine (ediam_mono hsub).trans <| (ediam_cthickening_le _).trans_eq ?_
  rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (by positivity), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul zero_le_two]
  ring_nf

/-- If a compact set `s` does not meet the closed `δ`-thickening of `t`, then the closed
`δ`-thickening of `s` does not meet `t`: a point of `t` within `δ` of `s` is within `δ` of a
point of `s`, since the distance to the compact set `s` is attained. -/
theorem _root_.IsCompact.disjoint_cthickening_left {X : Type*} [PseudoMetricSpace X]
    {s t : Set X} (hs : IsCompact s) {δ : ℝ} (h : Disjoint s (cthickening δ t)) :
    Disjoint (cthickening δ s) t := by
  rw [← cthickening_max_zero] at h ⊢
  rw [hs.cthickening_eq_biUnion_closedBall (le_max_left 0 δ), Set.disjoint_iUnion₂_left]
  refine fun x hx ↦ Set.disjoint_left.2 fun y hy hyt ↦ Set.disjoint_left.1 h hx ?_
  exact mem_cthickening_of_dist_le x y _ t hyt (by rw [dist_comm]; exact mem_closedBall.1 hy)

/-- A point does not lie in the closed `δ`-thickening of the complement of an open ball around it
of radius `r > δ`. -/
theorem notMem_cthickening_compl_ball {X : Type*} [PseudoMetricSpace X] {x : X} {δ r : ℝ}
    (hδr : δ < r) (hr : 0 < r) : x ∉ cthickening δ (ball x r)ᶜ := by
  rw [mem_cthickening_iff, not_le]
  refine lt_of_lt_of_le (b := ENNReal.ofReal r) (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hδr, hr⟩)
    (le_infEDist.2 fun y hy ↦ ?_)
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (not_lt.1 fun h ↦ hy (mem_ball'.2 h))

/-- The closed `δ`-thickening of a compact set in a proper pseudometric space, as a compact set. -/
def _root_.TopologicalSpace.Compacts.cthickening {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (δ : ℝ) (K : TopologicalSpace.Compacts X) : TopologicalSpace.Compacts X :=
  ⟨Metric.cthickening δ K, K.isCompact.cthickening⟩

@[simp]
theorem _root_.TopologicalSpace.Compacts.coe_cthickening {X : Type*} [PseudoMetricSpace X]
    [ProperSpace X] (δ : ℝ) (K : TopologicalSpace.Compacts X) :
    (K.cthickening δ : Set X) = Metric.cthickening δ K :=
  (rfl)

/-- Under a `K`-Lipschitz map, the `R / K`-thickening of a preimage lies in the preimage of the
`R`-thickening. -/
theorem _root_.LipschitzWith.thickening_preimage_subset_preimage_thickening
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {f : X → Y} {K : ℝ≥0} {R : ℝ}
    (hf : LipschitzWith K f) (S : Set Y) : thickening (R / K) (f ⁻¹' S) ⊆ f ⁻¹' thickening R S := by
  rcases eq_or_ne K 0 with rfl | hK
  · simp [thickening_of_nonpos]
  intro y hy
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.1 hy
  refine mem_thickening_iff.2 ⟨f z, mem_preimage.1 hz, (hf.dist_le_mul y z).trans_lt ?_⟩
  calc (K : ℝ) * dist y z < K * (R / K) := by gcongr
    _ = R := by field_simp

/-- Under a `K`-Lipschitz map, the closed `R / K`-thickening of a preimage lies in the preimage of
the closed `R`-thickening. -/
theorem _root_.LipschitzWith.cthickening_preimage_subset_preimage_cthickening
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] {f : X → Y} {K : ℝ≥0} {R : ℝ}
    (hf : LipschitzWith K f) (S : Set Y) :
    cthickening (R / K) (f ⁻¹' S) ⊆ f ⁻¹' cthickening R S := by
  intro x hx
  rcases eq_or_ne K 0 with rfl | hK
  · -- `f` is constant, so `f x ∈ S` as soon as the preimage of `S` is nonempty.
    obtain ⟨y, hy⟩ : (f ⁻¹' S).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      simp [h] at hx
    have h0 : f x ∈ cthickening 0 S :=
      mem_cthickening_of_dist_le (f x) (f y) 0 S hy (by simpa using hf.dist_le_mul x y)
    rcases le_total 0 R with hR | hR
    · exact cthickening_mono hR S h0
    · rw [cthickening_zero] at h0
      rwa [mem_preimage, cthickening_of_nonpos hR]
  rw [mem_cthickening_iff] at hx
  rw [mem_preimage, mem_cthickening_iff]
  have hK0 : (K : ℝ≥0∞) ≠ 0 := by simpa using hK
  have hle : infEDist (f x) S ≤ K * infEDist x (f ⁻¹' S) := by
    simp only [infEDist, ENNReal.mul_iInf_of_ne hK0 ENNReal.coe_ne_top]
    refine le_iInf₂ fun y hy ↦ ?_
    exact (infEDist_le_edist_of_mem (mem_preimage.1 hy)).trans (hf.edist_le_mul x y)
  refine hle.trans ((mul_le_mul' le_rfl hx).trans ?_)
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg,
    mul_div_cancel₀ _ (by simpa using hK)]

end TauCeti

/-- If the `δ`-thickenings of `A` and `s` are disjoint, every point of `A` is at distance at least
`δ / 2` from the closed `δ / 2`-thickening of `s`. -/
theorem Disjoint.half_le_dist_of_mem_cthickening {X : Type*} [PseudoMetricSpace X]
    {A s : Set X} {δ : ℝ} (h : Disjoint (thickening δ A) (thickening δ s)) (hδ : 0 < δ)
    {x y : X} (hx : x ∈ A) (hy : y ∈ cthickening (δ / 2) s) : δ / 2 ≤ dist x y := by
  by_contra! hxy
  exact disjoint_left.1 h
    (mem_thickening_iff.2 ⟨x, hx, ((dist_comm _ _).trans_lt hxy).trans (half_lt_self hδ)⟩)
    (cthickening_subset_thickening' hδ (half_lt_self hδ) s hy)

/-- A closed set `K` in a pseudometric space contained in the interior of a set `L` is the
intersection of an antitone sequence of open sets `W n` with `K ⊆ W n ⊆ L`. -/
theorem IsClosed.exists_antitone_isOpen_iInter_eq {X : Type*} [PseudoMetricSpace X]
    {K L : Set X} (hK : IsClosed K) (hKL : K ⊆ interior L) :
    ∃ W : ℕ → Set X, (∀ n, IsOpen (W n)) ∧ (∀ n, W n ⊆ L) ∧ (∀ n, K ⊆ W n) ∧ Antitone W ∧
      ⋂ n, W n = K := by
  set W : ℕ → Set X := fun n => interior L ∩ thickening (1 / ((n : ℝ) + 1)) K
  have hKW (n : ℕ) : K ⊆ W n := subset_inter hKL (self_subset_thickening (by positivity) K)
  refine ⟨W, fun n => isOpen_interior.inter isOpen_thickening,
    fun n => inter_subset_left.trans interior_subset, hKW, fun m n hmn =>
    inter_subset_inter_right _ (thickening_mono (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmn 1)) K), ?_⟩
  refine Subset.antisymm (fun x hx => ?_) (subset_iInter hKW)
  rw [← hK.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 (mem_iInter.1 hx n).2
  exact ⟨y, hy, hxy.trans hn⟩

/-- **A shrinking neighbourhood basis of a compact set.** In a locally compact, locally connected
pseudometrizable space, a compact set `K` inside an open set `W` has an antitone basis of open
neighbourhoods `U n` with compact closures, such that `closure (U 0) ⊆ W`,
`closure (U (n + 1)) ⊆ U n`, and every connected component of every `U n` meets `K`. -/
theorem IsCompact.exists_hasAntitoneBasis_nhdsSet {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X]
    [LocallyCompactSpace X] [LocallyConnectedSpace X] {K W : Set X} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ U : ℕ → Set X, (𝓝ˢ K).HasAntitoneBasis U ∧ closure (U 0) ⊆ W ∧
      ∀ n, IsOpen (U n) ∧ IsCompact (closure (U n)) ∧ closure (U (n + 1)) ⊆ U n ∧
        ∀ x ∈ U n, (connectedComponentIn (U n) x ∩ K).Nonempty := by
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  -- One step: shrink an open neighbourhood `O` of `K` to one with compact closure inside `O`,
  -- all of whose components meet `K`.
  have step (O : Set X) (hO : IsOpen O) (hKO : K ⊆ O) : ∃ U, IsOpen U ∧ K ⊆ U ∧
      closure U ⊆ O ∧ IsCompact (closure U) ∧
        ∀ x ∈ U, (connectedComponentIn U x ∩ K).Nonempty := by
    obtain ⟨V, hVo, hKV, hVO, hVc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
    obtain ⟨U, hUV, hUo, hKU, hcomp⟩ :=
      hVo.exists_subset_forall_connectedComponentIn_inter_nonempty hKV
    exact ⟨U, hUo, hKU, (closure_mono hUV).trans hVO,
      hVc.of_isClosed_subset isClosed_closure (closure_mono hUV), hcomp⟩
  choose! u huo hKu hu hUc hcomp using step
  -- Iterate the step, applying it at stage `n + 1` to `U n ∩ B (n + 1)`, where `B n` is the
  -- `1 / (n + 1)`-thickening of `K`.
  set B : ℕ → Set X := fun n => thickening (1 / ((n : ℝ) + 1)) K
  let U : ℕ → Set X := fun n => Nat.rec (u (W ∩ B 0)) (fun n S => u (S ∩ B (n + 1))) n
  let O : ℕ → Set X := fun n => Nat.casesOn n (W ∩ B 0) fun n => U n ∩ B (n + 1)
  have hUO (n : ℕ) : U n = u (O n) := by cases n <;> rfl
  have hOB (n : ℕ) : O n ⊆ B n := by cases n <;> exact inter_subset_right
  have hO (n : ℕ) : IsOpen (O n) ∧ K ⊆ O n := by
    induction n with
    | zero => exact ⟨hW.inter isOpen_thickening,
        subset_inter hKW (self_subset_thickening (by positivity) K)⟩
    | succ n ih =>
      exact ⟨(hUO n ▸ huo _ ih.1 ih.2).inter isOpen_thickening,
        subset_inter (hUO n ▸ hKu _ ih.1 ih.2) (self_subset_thickening (by positivity) K)⟩
  have hU (n : ℕ) : IsOpen (U n) ∧ K ⊆ U n ∧ closure (U n) ⊆ O n ∧
      IsCompact (closure (U n)) ∧
        ∀ x ∈ U n, (connectedComponentIn (U n) x ∩ K).Nonempty :=
    hUO n ▸ ⟨huo _ (hO n).1 (hO n).2, hKu _ (hO n).1 (hO n).2,
      hu _ (hO n).1 (hO n).2, hUc _ (hO n).1 (hO n).2, hcomp _ (hO n).1 (hO n).2⟩
  have hclO (n : ℕ) := (hU n).2.2.1
  refine ⟨U, ⟨(hasBasis_nhdsSet_thickening hK).to_hasBasis (fun δ hδ => ?_) fun n _ => ?_,
    antitone_nat_of_succ_le fun n => subset_closure.trans ((hclO (n + 1)).trans
      inter_subset_left)⟩, (hclO 0).trans inter_subset_left, fun n => ⟨(hU n).1,
    (hU n).2.2.2.1, (hclO (n + 1)).trans inter_subset_left, (hU n).2.2.2.2⟩⟩
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    exact ⟨n, trivial, subset_closure.trans ((hclO n).trans ((hOB n).trans
      (thickening_mono hn.le K)))⟩
  · exact hK.exists_thickening_subset_open (hU n).1 (hU n).2.1

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
    (disjoint_iUnion_right.2 fun j ↦ hdisj j.property.symm).exists_cthickenings (hK i)
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

/-- **Interior exhaustion by the distance to the complement.** If `δ` tends to `0`, then every
point `z` of an open set `s` with nonempty complement has a closed ball around it which eventually
lies in `{y | δ i < infDist y sᶜ}`. -/
theorem IsOpen.exists_eventually_closedBall_subset_setOf_lt_infDist {X ι : Type*}
    [PseudoMetricSpace X] {s : Set X} (hs : IsOpen s) (hc : sᶜ.Nonempty) {l : Filter ι}
    {δ : ι → ℝ} (hδ : Tendsto δ l (𝓝 0)) {z : X} (hz : z ∈ s) :
    ∃ r > 0, ∀ᶠ i in l, closedBall z r ⊆ {y | δ i < infDist y sᶜ} := by
  have hd := (hs.isClosed_compl.notMem_iff_infDist_pos hc).1 (not_not_intro hz)
  refine ⟨infDist z sᶜ / 2, half_pos hd, ?_⟩
  filter_upwards [hδ.eventually (gt_mem_nhds (half_pos hd))] with i hi w hw
  have := infDist_le_infDist_add_dist (x := z) (y := w) (s := sᶜ)
  rw [dist_comm] at this
  simp only [mem_ofPred_eq]
  linarith [mem_closedBall.1 hw]

/-- **Values near the frontier.** Let `f` be continuous on the closure of a bounded open set `s`
with nonempty complement in a proper space, and at most `m` on the frontier of `s`. Then for every
`η > 0`, `f < m + η` at the points of `s` close enough to the complement of `s`. -/
theorem IsOpen.exists_pos_forall_lt_add_of_infDist_lt {X : Type*} [PseudoMetricSpace X]
    [ProperSpace X] {s : Set X} (hs : IsOpen s) (hb : Bornology.IsBounded s) (hc : sᶜ.Nonempty)
    {f : X → ℝ} (hf : ContinuousOn f (closure s)) {m : ℝ} (hm : ∀ z ∈ frontier s, f z ≤ m)
    {η : ℝ} (hη : 0 < η) : ∃ δ > 0, ∀ z ∈ s, infDist z sᶜ < δ → f z < m + η := by
  -- The points of `closure s` where `f ≥ m + η` form a compact subset of `s`.
  set K := closure s ∩ f ⁻¹' Ici (m + η)
  have hK : IsCompact K := hb.isCompact_closure.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici) inter_subset_left
  have hKs : K ⊆ s := fun z ⟨hz, hzη⟩ => by
    by_contra hzs
    have := hm z ⟨hz, by rwa [hs.interior_eq]⟩
    simp only [mem_preimage, mem_Ici] at hzη
    linarith
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_cthickening_subset_open hs hKs
  refine ⟨δ, hδ, fun z hz hzδ => lt_of_not_ge fun hzη => hzδ.not_ge ?_⟩
  refine (le_infDist hc).2 fun w hw => le_of_not_gt fun hwz => hw (hδK ?_)
  exact mem_cthickening_of_dist_le w z δ K ⟨subset_closure hz, hzη⟩ (dist_comm w z ▸ hwz.le)

/-- **Uniform balls around a closed thickening.** A compact set `K` inside an open set `U` has a
radius `δ > 0` such that the closed `δ`-balls around the points of `cthickening δ K` lie in `U`. -/
theorem IsCompact.exists_forall_closedBall_subset_of_isOpen {X : Type*} [PseudoMetricSpace X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ > 0, ∀ z ∈ cthickening δ K, closedBall z δ ⊆ U := by
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hK.exists_cthickening_subset_open hU hKU
  have hδ : 0 < δ₀ / 2 := half_pos hδ₀
  exact ⟨δ₀ / 2, hδ, fun z hz => (closedBall_subset_cthickening hz _).trans <|
    (cthickening_cthickening_subset hδ.le hδ.le _).trans <| by rw [add_halves]; exact hδ₀U⟩

/-- A compact subset `K` of an open set `Ω` in a proper space has an open neighbourhood `U` with
compact closure inside `Ω` that contains the closed balls of radius at most some `δ > 0` about the
points of `K`. -/
theorem IsCompact.exists_isOpen_closedBall_subset {X : Type*} [PseudoMetricSpace X]
    [ProperSpace X] {K Ω : Set X} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ U : Set X, IsOpen U ∧ ∃ δ > 0, IsCompact (closure U) ∧ closure U ⊆ Ω ∧
      ∀ z ∈ K, ∀ r ≤ δ, closedBall z r ⊆ U := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  have hcl : closure (thickening δ K) ⊆ cthickening δ K := closure_thickening_subset_cthickening δ K
  exact ⟨thickening δ K, isOpen_thickening, δ / 2, half_pos hδ,
    hK.cthickening.of_isClosed_subset isClosed_closure hcl, hcl.trans hδΩ,
    fun z hz r hr => (closedBall_subset_ball (hr.trans_lt (half_lt_self hδ))).trans
      (ball_subset_thickening hz δ)⟩

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.AtomlessStandardBorel.Transport
import Mathlib.MeasureTheory.Integral.Indicator
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Allocating disjoint sets of prescribed mass in a laminar family

Let `μ` be an atomless measure on a standard Borel space. The main result is a Hall-type
theorem for a graded laminar family of sets of finite measure. Each member `A i` has a
level `lvl i`. Distinct members of one level are disjoint, and a member of a deeper level lies
inside or is disjoint from each member of a shallower level. If every member `A i` has room for
its own demand `m i` together with the demands of all members strictly below it, then there are
pairwise disjoint measurable sets `Z i ⊆ A i` with `μ (Z i) = m i`. This holds although the
family may be infinitely deep.

The proof follows Pratelli. For each `n` the demands of levels below `n` are allocated. To pass
to `n + 1`, the members of level `n` take any sets of the right mass; then, from level `n - 1`
up to level `0`, each member gives up what the members below it now occupy and takes the same
mass from free room in its own set, chosen by Sierpiński's theorem
`MeasureTheory.Measure.exists_subset_measure_eq_of_nullSingleton`. A member loses at most the
mass newly demanded below it, so each allocated set changes by summable amounts, and the
Borel--Cantelli lemma lets the allocations converge.

This is the allocation step in Pratelli's proof that Monge's infimum equals Kantorovich's
minimum for continuous costs and atomless sources: the members are the source sides of
disjoint rectangles on which the cost nearly is constant, and each demand is the mass a
transport plan puts on its rectangle.

## Main statements

* `MeasureTheory.Measure.exists_disjoint_subset_measure_eq_of_laminar`: the laminar
  allocation theorem.

## References

* A. Pratelli, *On the equality between Monge's infimum and Kantorovich's minimum in optimal
  mass transportation*, Ann. I. H. Poincaré Probab. Statist. 43 (2007), 1--13, §4, Steps II
  and III of the proof of Theorem B.
-/

public section

open Filter Function Set
open scoped ENNReal symmDiff Topology

namespace MeasureTheory.Measure

section Combinatorics

variable {X ι : Type*} {A : ι → Set X} {lvl : ι → ℕ} {m : ι → ℝ≥0∞}

/-- The indices of the members of the family strictly below the member `i`. -/
private def below (A : ι → Set X) (lvl : ι → ℕ) (i : ι) : Set ι :=
  {j | lvl i < lvl j ∧ A j ⊆ A i}

private theorem below_trans {i j k : ι} (hj : j ∈ below A lvl i) (hk : k ∈ below A lvl j) :
    k ∈ below A lvl i :=
  ⟨hj.1.trans hk.1, hk.2.trans hj.2⟩

private theorem below_inter_subset {n ℓ : ℕ} {i : ι} (hi : lvl i = ℓ) :
    below A lvl i ∩ {j | lvl j ≤ n} ⊆ {j | ℓ + 1 ≤ lvl j ∧ lvl j ≤ n} :=
  fun _ hj ↦ ⟨hi ▸ hj.1.1, hj.2⟩

/-- Replacing the part `s ∩ t` of `s` by `u` moves `s` by at most `u ∪ (s ∩ t)`. -/
private theorem symmDiff_sdiff_union_subset (s t u : Set X) : ((s \ t) ∪ u) ∆ s ⊆ u ∪ (s ∩ t) := by
  intro x hx
  simp only [mem_symmDiff, mem_union, Set.mem_sdiff, mem_inter_iff] at hx ⊢
  tauto

end Combinatorics

variable {X : Type*} [MeasurableSpace X]

/-- Replacing the part `s ∩ t` of `s` by a disjoint set `u` of the same mass keeps the mass. -/
private theorem measure_sdiff_union_eq {μ : Measure X} {s t u : Set X} (ht : MeasurableSet t)
    (hu : MeasurableSet u) (hus : Disjoint u s) (hμu : μ u = μ (s ∩ t)) :
    μ ((s \ t) ∪ u) = μ s := by
  rw [measure_union (hus.symm.mono_left sdiff_subset) hu, hμu, measure_sdiff_add_inter _ ht]

section Laminar

variable {ι : Type*} [Countable ι] {μ : Measure X} {A : ι → Set X} {lvl : ι → ℕ}
  {m : ι → ℝ≥0∞}

/-- `Z` allocates the demands of the members indexed by `S`: on `S`, the sets `Z i` are
measurable, pairwise disjoint, contained in `A i`, and of measure `m i`. -/
private structure IsAlloc (μ : Measure X) (A : ι → Set X) (m : ι → ℝ≥0∞) (S : Set ι)
    (Z : ι → Set X) : Prop where
  measurableSet : ∀ i ∈ S, MeasurableSet (Z i)
  subset : ∀ i ∈ S, Z i ⊆ A i
  measure_eq : ∀ i ∈ S, μ (Z i) = m i
  disjoint : S.PairwiseDisjoint Z

omit [Countable ι] in
private theorem IsAlloc.mono {S T : Set ι} {Z : ι → Set X} (h : IsAlloc μ A m S Z)
    (hT : T ⊆ S) : IsAlloc μ A m T Z :=
  ⟨fun i hi ↦ h.measurableSet i (hT hi), fun i hi ↦ h.subset i (hT hi),
    fun i hi ↦ h.measure_eq i (hT hi), h.disjoint.subset hT⟩

private theorem IsAlloc.measure_biUnion {S T : Set ι} {Z : ι → Set X}
    (h : IsAlloc μ A m S Z) (hT : T ⊆ S) : μ (⋃ j ∈ T, Z j) = ∑' j, T.indicator m j := by
  rw [MeasureTheory.measure_biUnion T.to_countable (h.disjoint.subset hT)
    (fun j hj ↦ h.measurableSet j (hT hj)), ← tsum_subtype T m]
  exact tsum_congr fun j ↦ h.measure_eq j (hT j.2)

private theorem IsAlloc.measurableSet_biUnion {S T : Set ι} {Z : ι → Set X}
    (h : IsAlloc μ A m S Z) (hT : T ⊆ S) : MeasurableSet (⋃ j ∈ T, Z j) :=
  .biUnion T.to_countable fun j hj ↦ h.measurableSet j (hT hj)

/-- The part of `A i` that `W` assigns to the members strictly below `i`, up to level `n`. -/
private def occupied (A : ι → Set X) (lvl : ι → ℕ) (n : ℕ) (W : ι → Set X) (i : ι) : Set X :=
  ⋃ j ∈ below A lvl i ∩ {j | lvl j ≤ n}, W j

/-- `Reallocated μ A lvl m n Z ℓ`: starting from an allocation `Z` of the levels below `n`, the
levels from `ℓ` to `n` have been reallocated by some `W`. The old set of a reallocated member
below level `n` is covered by its new set together with the new sets below it, and it moved by
at most twice the demand at level `n` below it. -/
private def Reallocated (μ : Measure X) (A : ι → Set X) (lvl : ι → ℕ) (m : ι → ℝ≥0∞) (n : ℕ)
    (Z : ι → Set X) (ℓ : ℕ) : Prop :=
  ∃ W : ι → Set X, IsAlloc μ A m {i | ℓ ≤ lvl i ∧ lvl i ≤ n} W ∧
    (∀ i, ℓ ≤ lvl i → lvl i < n → Z i ⊆ W i ∪ occupied A lvl n W i) ∧
    (∀ i, ℓ ≤ lvl i → lvl i < n →
      μ (W i ∆ Z i) ≤ 2 * ∑' j, (below A lvl i ∩ {j | lvl j = n}).indicator m j)

section Reallocation

variable {n ℓ : ℕ} {Z W : ι → Set X} {i : ι}

private theorem measurableSet_occupied (hW : IsAlloc μ A m {i | ℓ + 1 ≤ lvl i ∧ lvl i ≤ n} W)
    (hi : lvl i = ℓ) : MeasurableSet (occupied A lvl n W i) :=
  hW.measurableSet_biUnion (below_inter_subset hi)

omit [Countable ι] in
private theorem occupied_subset (hW : IsAlloc μ A m {i | ℓ + 1 ≤ lvl i ∧ lvl i ≤ n} W)
    (hi : lvl i = ℓ) : occupied A lvl n W i ⊆ A i :=
  iUnion₂_subset fun j hj ↦ (hW.subset j (below_inter_subset hi hj)).trans hj.1.2

/-- A member loses at most the demand newly added at level `n` below it: its old set is
disjoint from the old sets below it, which the new sets below it still cover. -/
private theorem measure_inter_occupied_le (hZ : IsAlloc μ A m {j | lvl j < n} Z)
    (hW : IsAlloc μ A m {j | ℓ + 1 ≤ lvl j ∧ lvl j ≤ n} W) (hi : lvl i = ℓ) (hℓn : ℓ < n)
    (hAi : μ (A i) ≠ ∞) (hcov : ∀ j, ℓ + 1 ≤ lvl j → lvl j < n → Z j ⊆ W j ∪ occupied A lvl n W j) :
    μ (Z i ∩ occupied A lvl n W i) ≤
      ∑' j, (below A lvl i ∩ {j | lvl j = n}).indicator m j := by
  set V := ⋃ j ∈ below A lvl i ∩ {j | lvl j < n}, Z j
  have hVsub : below A lvl i ∩ {j | lvl j < n} ⊆ {j | lvl j < n} := inter_subset_right
  have hVU : V ⊆ occupied A lvl n W i := by
    refine iUnion₂_subset fun j hj ↦ (hcov j (hi ▸ hj.1.1) hj.2).trans
      (union_subset ?_ (iUnion₂_subset fun k hk ↦ ?_))
    · exact subset_biUnion_of_mem (u := W) ⟨hj.1, (Nat.le_of_lt hj.2 : lvl j ≤ n)⟩
    · exact subset_biUnion_of_mem (u := W) ⟨below_trans hj.1 hk.1, hk.2⟩
  have hZV : Disjoint (Z i) V := by
    refine disjoint_iUnion₂_right.2 fun j hj ↦ hZ.disjoint (by simpa [hi] using hℓn) hj.2 ?_
    rintro rfl
    exact lt_irrefl _ hj.1.1
  calc μ (Z i ∩ occupied A lvl n W i) ≤ μ (occupied A lvl n W i \ V) :=
        measure_mono fun x hx ↦ ⟨hx.2, fun hxV ↦ disjoint_left.1 hZV hx.1 hxV⟩
    _ = μ (occupied A lvl n W i) - μ V :=
        measure_sdiff hVU (hZ.measurableSet_biUnion hVsub).nullMeasurableSet
          (ne_top_of_le_ne_top hAi (measure_mono (hVU.trans (occupied_subset hW hi))))
    _ ≤ ∑' j, (below A lvl i ∩ {j | lvl j = n}).indicator m j := by
        rw [occupied, hW.measure_biUnion (below_inter_subset hi),
          hZ.measure_biUnion hVsub, tsub_le_iff_left, ← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum fun j ↦ ?_
        by_cases hj : j ∈ below A lvl i
        · rcases lt_trichotomy (lvl j) n with h | h | h
          · simp [hj, h, h.le, h.ne]
          · simp [hj, h]
          · simp [hj, not_le.2 h, not_lt.2 h.le, h.ne']
        · simp [hj]

/-- The free room in `A i`, outside its old set and the new sets below it, holds what it lost. -/
private theorem measure_inter_occupied_le_sdiff (hZ : IsAlloc μ A m {j | lvl j < n} Z)
    (hW : IsAlloc μ A m {j | ℓ + 1 ≤ lvl j ∧ lvl j ≤ n} W) (hi : lvl i = ℓ) (hℓn : ℓ < n)
    (hAi : μ (A i) ≠ ∞) (hm : ∀ i, m i + ∑' j, (below A lvl i).indicator m j ≤ μ (A i)) :
    μ (Z i ∩ occupied A lvl n W i) ≤ μ (A i \ (Z i ∪ occupied A lvl n W i)) := by
  have hi' : i ∈ {j | lvl j < n} := by simpa [hi] using hℓn
  have hU := measurableSet_occupied hW hi
  have hZUA := union_subset (hZ.subset i hi') (occupied_subset hW hi)
  have hZU : μ (Z i ∪ occupied A lvl n W i) ≠ ∞ := ne_top_of_le_ne_top hAi (measure_mono hZUA)
  rw [measure_sdiff hZUA ((hZ.measurableSet i hi').union hU).nullMeasurableSet hZU]
  refine ENNReal.le_sub_of_add_le_left hZU ?_
  rw [measure_union_add_inter _ hU, hZ.measure_eq i hi', occupied,
    hW.measure_biUnion (below_inter_subset hi)]
  exact (add_le_add le_rfl (ENNReal.tsum_le_tsum fun j ↦
    indicator_le_indicator_of_subset inter_subset_left (fun _ ↦ zero_le) j)).trans (hm i)

end Reallocation

omit [Countable ι] in
/-- From the first stage allocating `i` on, the stages of `i` move by at most twice the demand
below `i` in total, which is at most `2 * μ (A i)`. -/
private theorem tsum_measure_symmDiff_stages_le
    (hm : ∀ i, m i + ∑' j, (below A lvl i).indicator m j ≤ μ (A i)) {Zs : ℕ → ι → Set X}
    (hZs : ∀ n i, lvl i < n →
      μ (Zs (n + 1) i ∆ Zs n i) ≤ 2 * ∑' j, (below A lvl i ∩ {j | lvl j = n}).indicator m j)
    (i : ι) : ∑' l, μ (Zs (l + 1 + (lvl i + 1)) i ∆ Zs (l + (lvl i + 1)) i) ≤ 2 * μ (A i) :=
  calc ∑' l, μ (Zs (l + 1 + (lvl i + 1)) i ∆ Zs (l + (lvl i + 1)) i)
      ≤ ∑' l, 2 * ∑' j, (below A lvl i ∩ {j | lvl j = l + (lvl i + 1)}).indicator m j :=
        ENNReal.tsum_le_tsum fun l ↦ by
          have := hZs (l + (lvl i + 1)) i (by omega)
          rwa [show l + (lvl i + 1) + 1 = l + 1 + (lvl i + 1) by omega] at this
    _ ≤ ∑' n, 2 * ∑' j, (below A lvl i ∩ {j | lvl j = n}).indicator m j :=
        ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective _)
          (fun n ↦ 2 * ∑' j, (below A lvl i ∩ {j | lvl j = n}).indicator m j)
    _ = 2 * ∑' j, (below A lvl i).indicator m j := by
        rw [ENNReal.tsum_mul_left, ← ENNReal.tsum_fiberwise _ lvl]
        refine congrArg (2 * ·) (tsum_congr fun n ↦ ?_)
        have hfib : lvl ⁻¹' {n} ∩ below A lvl i = below A lvl i ∩ {j | lvl j = n} := by
          ext j
          simp [and_comm]
        rw [tsum_subtype, indicator_indicator, hfib]
    _ ≤ 2 * μ (A i) := by
        gcongr
        exact le_add_self.trans (hm i)

variable [StandardBorelSpace X] [NullSingletonClass μ]
  (hA : ∀ i, MeasurableSet (A i)) (hAfin : ∀ i, μ (A i) ≠ ∞)
  (hlvl : ∀ i j, i ≠ j → lvl i = lvl j → Disjoint (A i) (A j))
  (hlam : ∀ i j, lvl i < lvl j → A j ⊆ A i ∨ Disjoint (A i) (A j))
include hA hAfin hlvl hlam

/-- Reallocating one more level. Each member `i` of level `ℓ` gives up the part of its old set
now occupied below it and takes the same mass from the free room of `A i`. -/
private theorem reallocated_of_succ
    (hm : ∀ i, m i + ∑' j, (below A lvl i).indicator m j ≤ μ (A i)) {n ℓ : ℕ} {Z : ι → Set X}
    (hZ : IsAlloc μ A m {i | lvl i < n} Z) (hℓn : ℓ < n)
    (ih : Reallocated μ A lvl m n Z (ℓ + 1)) : Reallocated μ A lvl m n Z ℓ := by
  obtain ⟨W, hW, hcov, hchg⟩ := ih
  -- `U i` is what the reallocated members below `i` occupy, and `G i` is the replacement room.
  set U := occupied A lvl n W
  have hZi {i : ι} (hi : lvl i = ℓ) : i ∈ {j | lvl j < n} := by simpa [hi] using hℓn
  choose! G hGsub hGm hGμ using fun i (hi : lvl i = ℓ) ↦
    exists_subset_measure_eq_of_nullSingleton μ
      ((hA i).diff ((hZ.measurableSet i (hZi hi)).union (measurableSet_occupied hW hi)))
      (ne_top_of_le_ne_top (hAfin i) (measure_mono sdiff_subset))
      (measure_inter_occupied_le_sdiff hZ hW hi hℓn (hAfin i) hm)
  -- The new sets: members of level `ℓ` are reallocated, deeper members keep their sets.
  set W' : ι → Set X := fun i ↦ if lvl i = ℓ then (Z i \ U i) ∪ G i else W i
  have hW'ℓ {i : ι} (hi : lvl i = ℓ) : W' i = (Z i \ U i) ∪ G i := by simp [W', hi]
  have hW'gt {i : ι} (hi : ℓ < lvl i) : W' i = W i := by simp [W', hi.ne']
  have hW'A {i : ι} (hi : lvl i = ℓ) : W' i ⊆ A i := by
    rw [hW'ℓ hi]
    exact union_subset (sdiff_subset.trans (hZ.subset i (hZi hi))) ((hGsub i hi).trans sdiff_subset)
  have hGZ {i : ι} (hi : lvl i = ℓ) : Disjoint (G i) (Z i) :=
    (disjoint_sdiff_left.mono_left (hGsub i hi)).mono_right subset_union_left
  have hGU {i : ι} (hi : lvl i = ℓ) : Disjoint (W' i) (U i) := by
    rw [hW'ℓ hi]
    exact disjoint_union_left.2 ⟨disjoint_sdiff_left,
      (disjoint_sdiff_left.mono_left (hGsub i hi)).mono_right subset_union_right⟩
  have hdisj {i j : ι} (hi : lvl i = ℓ) (hj : ℓ < lvl j) (hjn : lvl j ≤ n) :
      Disjoint (W' i) (W' j) := by
    rw [hW'gt hj]
    by_cases hb : j ∈ below A lvl i
    · exact (hGU hi).mono_right
        (subset_biUnion_of_mem (s := below A lvl i ∩ {j | lvl j ≤ n}) (u := W) ⟨hb, hjn⟩)
    · exact ((hlam i j (hi ▸ hj)).resolve_left fun h ↦ hb ⟨hi ▸ hj, h⟩).mono (hW'A hi)
        (hW.subset j ⟨hj, hjn⟩)
  -- Each property splits into the new members of level `ℓ` and the unchanged deeper members:
  -- measurability, containment, mass, disjointness, covering of old sets, and the moved mass.
  refine ⟨W', ⟨fun i hi ↦ ?_, fun i hi ↦ ?_, fun i hi ↦ ?_, fun i hi j hj hij ↦ ?_⟩,
    fun i hi hin ↦ ?_, fun i hi hin ↦ ?_⟩
  · rcases hi.1.eq_or_lt with h | h
    · rw [hW'ℓ h.symm]
      exact ((hZ.measurableSet i (hZi h.symm)).diff (measurableSet_occupied hW h.symm)).union
        (hGm i h.symm)
    · exact hW'gt h ▸ hW.measurableSet i ⟨h, hi.2⟩
  · rcases hi.1.eq_or_lt with h | h
    · exact hW'A h.symm
    · exact hW'gt h ▸ hW.subset i ⟨h, hi.2⟩
  · rcases hi.1.eq_or_lt with h | h
    · rw [hW'ℓ h.symm, measure_sdiff_union_eq (measurableSet_occupied hW h.symm) (hGm i h.symm)
        (hGZ h.symm) (hGμ i h.symm), hZ.measure_eq i (hZi h.symm)]
    · exact hW'gt h ▸ hW.measure_eq i ⟨h, hi.2⟩
  · rcases hi.1.eq_or_lt with h | h <;> rcases hj.1.eq_or_lt with h' | h'
    · exact (hlvl i j hij (h.symm.trans h')).mono (hW'A h.symm) (hW'A h'.symm)
    · exact hdisj h.symm h' hj.2
    · exact (hdisj h'.symm h hi.2).symm
    · rw [Function.onFun, hW'gt h, hW'gt h']
      exact hW.disjoint ⟨h, hi.2⟩ ⟨h', hj.2⟩ hij
  · have hU' : U i ⊆ occupied A lvl n W' i :=
      biUnion_mono subset_rfl fun j hj ↦ (hW'gt (hi.trans_lt hj.1.1)).ge
    rcases hi.eq_or_lt with h | h
    · rw [hW'ℓ h.symm]
      intro x hx
      by_cases hxU : x ∈ U i
      · exact Or.inr (hU' hxU)
      · exact Or.inl (Or.inl ⟨hx, hxU⟩)
    · rw [hW'gt h]
      exact (hcov i h hin).trans (union_subset_union_right _ hU')
  · rcases hi.eq_or_lt with h | h
    · have hi' := h.symm
      calc μ (W' i ∆ Z i) ≤ μ (G i ∪ (Z i ∩ U i)) := by
            rw [hW'ℓ hi']
            exact measure_mono (symmDiff_sdiff_union_subset _ _ _)
        _ ≤ μ (G i) + μ (Z i ∩ U i) := measure_union_le _ _
        _ ≤ 2 * ∑' j, (below A lvl i ∩ {j | lvl j = n}).indicator m j := by
            rw [hGμ i hi', ← two_mul]
            gcongr
            exact measure_inter_occupied_le hZ hW hi' hℓn (hAfin i) hcov
    · exact hW'gt h ▸ hchg i h hin

/-- One pass of the reallocation. Given an allocation `Z` of the levels below `n`, the members
of level `n` take sets of the right mass, and then the levels from `n - 1` down to `0` are
reallocated. A member `i` changes by at most twice the demand at level `n` below it. -/
private theorem exists_isAlloc_succ
    (hm : ∀ i, m i + ∑' j, (below A lvl i).indicator m j ≤ μ (A i)) {n : ℕ} {Z : ι → Set X}
    (hZ : IsAlloc μ A m {i | lvl i < n} Z) :
    ∃ W : ι → Set X, IsAlloc μ A m {i | lvl i < n + 1} W ∧ ∀ i, lvl i < n →
      μ (W i ∆ Z i) ≤ 2 * ∑' j, (below A lvl i ∩ {j | lvl j = n}).indicator m j := by
  have hP : Reallocated μ A lvl m n Z 0 := by
    refine Nat.decreasingInduction (motive := fun ℓ _ ↦ Reallocated μ A lvl m n Z ℓ)
      (fun ℓ hℓn ih ↦ reallocated_of_succ hA hAfin hlvl hlam hm hZ hℓn ih) ?_ (Nat.zero_le n)
    choose W hWA hWm hWμ using fun i ↦
      exists_subset_measure_eq_of_nullSingleton μ (hA i) (hAfin i) (le_self_add.trans (hm i))
    refine ⟨W, ⟨fun i _ ↦ hWm i, fun i _ ↦ hWA i, fun i _ ↦ hWμ i, ?_⟩,
      fun i h h' ↦ by omega, fun i h h' ↦ by omega⟩
    intro i hi j hj hij
    exact (hlvl i j hij (by simp only [mem_ofPred_eq] at hi hj; omega)).mono (hWA i) (hWA j)
  obtain ⟨W, hW, -, hchg⟩ := hP
  exact ⟨W, hW.mono fun i hi ↦ ⟨Nat.zero_le _, Nat.lt_succ_iff.1 hi⟩,
    fun i hi ↦ hchg i (Nat.zero_le _) hi⟩

/-- The stages of the reallocation: `Zs n` allocates the levels below `n`, and from stage `n` to
stage `n + 1` each allocated set moves by at most twice the demand at level `n` below it. -/
private theorem exists_isAlloc_seq
    (hm : ∀ i, m i + ∑' j, (below A lvl i).indicator m j ≤ μ (A i)) :
    ∃ Zs : ℕ → ι → Set X, ∀ n, IsAlloc μ A m {i | lvl i < n} (Zs n) ∧ ∀ i, lvl i < n →
      μ (Zs (n + 1) i ∆ Zs n i) ≤ 2 * ∑' j, (below A lvl i ∩ {j | lvl j = n}).indicator m j := by
  have step (n : ℕ) (Z : ι → Set X) : ∃ W : ι → Set X, IsAlloc μ A m {i | lvl i < n} Z →
      IsAlloc μ A m {i | lvl i < n + 1} W ∧ ∀ i, lvl i < n →
        μ (W i ∆ Z i) ≤ 2 * ∑' j, (below A lvl i ∩ {j | lvl j = n}).indicator m j := by
    by_cases hZ : IsAlloc μ A m {i | lvl i < n} Z
    · obtain ⟨W, hW⟩ := exists_isAlloc_succ hA hAfin hlvl hlam hm hZ
      exact ⟨W, fun _ ↦ hW⟩
    · exact ⟨Z, fun h ↦ absurd h hZ⟩
  choose F hF using step
  let Zs : ℕ → ι → Set X := fun n ↦ Nat.rec (motive := fun _ ↦ ι → Set X) (fun _ ↦ ∅) F n
  have hZs (n : ℕ) : IsAlloc μ A m {i | lvl i < n} (Zs n) := by
    induction n with
    | zero =>
      exact ⟨fun i hi ↦ absurd hi (Nat.not_lt_zero _), fun i hi ↦ absurd hi (Nat.not_lt_zero _),
        fun i hi ↦ absurd hi (Nat.not_lt_zero _), fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩
    | succ n ih => exact (hF n (Zs n) ih).1
  exact ⟨Zs, fun n ↦ ⟨hZs n, (hF n (Zs n) (hZs n)).2⟩⟩

end Laminar

/-- **Allocation in a graded laminar family.** Let `μ` be an atomless measure on a standard
Borel space, and let `A i` be measurable sets of finite measure carrying levels `lvl i`, such
that distinct members of one level are disjoint and a member of a deeper level lies inside or is
disjoint from each member of a shallower level. If each `A i` has room for the demand `m i`
together with the demands of all members strictly below it, then there are pairwise disjoint
measurable sets `Z i ⊆ A i` with `μ (Z i) = m i`.

The family may be infinitely deep. This is the allocation of source sets in Pratelli's proof that
Monge's infimum equals Kantorovich's minimum for continuous costs. -/
theorem exists_disjoint_subset_measure_eq_of_laminar [StandardBorelSpace X] (μ : Measure X)
    [NullSingletonClass μ] {ι : Type*} [Countable ι] {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i)) (hAfin : ∀ i, μ (A i) ≠ ∞) (lvl : ι → ℕ)
    (hlvl : ∀ i j, i ≠ j → lvl i = lvl j → Disjoint (A i) (A j))
    (hlam : ∀ i j, lvl i < lvl j → A j ⊆ A i ∨ Disjoint (A i) (A j)) (m : ι → ℝ≥0∞)
    (hm : ∀ i, m i + ∑' j : {j | lvl i < lvl j ∧ A j ⊆ A i}, m j ≤ μ (A i)) :
    ∃ Z : ι → Set X, (∀ i, MeasurableSet (Z i)) ∧ (∀ i, Z i ⊆ A i) ∧
      Pairwise (Disjoint on Z) ∧ ∀ i, μ (Z i) = m i := by
  have hm' (i : ι) : m i + ∑' j, (below A lvl i).indicator m j ≤ μ (A i) := by
    rw [below, ← tsum_subtype]
    exact hm i
  obtain ⟨Zs, hZs⟩ := exists_isAlloc_seq hA hAfin hlvl hlam hm'
  -- The stages of `i` from the first stage allocating `i` on, and their limit.
  set Y : ι → ℕ → Set X := fun i l ↦ Zs (l + (lvl i + 1)) i
  have hYlt (i : ι) (l : ℕ) : i ∈ {j | lvl j < l + (lvl i + 1)} := (by omega : lvl i < _)
  have hYm (i : ι) (l : ℕ) : MeasurableSet (Y i l) := (hZs _).1.measurableSet i (hYlt i l)
  refine ⟨fun i ↦ liminf (Y i) atTop, fun i ↦ MeasurableSet.measurableSet_liminf (hYm i),
    fun i x hx ↦ ?_, fun i j hij ↦ disjoint_left.2 fun x hxi hxj ↦ ?_, fun i ↦ ?_⟩
  · obtain ⟨l, hl⟩ := (mem_liminf_iff_eventually_mem.1 hx).exists
    exact (hZs _).1.subset i (hYlt i l) hl
  · -- A common point of the limits would lie in two allocated sets of one stage.
    obtain ⟨L, hL⟩ := eventually_atTop.1 (mem_liminf_iff_eventually_mem.1 hxi)
    obtain ⟨L', hL'⟩ := eventually_atTop.1 (mem_liminf_iff_eventually_mem.1 hxj)
    have h₁ := hL (L + L' + lvl j) (by omega)
    have h₂ := hL' (L + L' + lvl i) (by omega)
    simp only [Y, show L + L' + lvl j + (lvl i + 1) = L + L' + lvl i + (lvl j + 1) by omega] at h₁
    exact disjoint_left.1 ((hZs _).1.disjoint (by omega : lvl i < _) (hYlt j _) hij) h₁ h₂
  · -- The stages of `i` change by summable amounts, so they converge almost everywhere.
    have hsum : ∑' l, μ (Y i (l + 1) ∆ Y i l) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofNat_ne_top (n := 2)) (hAfin i))
        (tsum_measure_symmDiff_stages_le hm' (fun n ↦ (hZs n).2) i)
    have h := tendsto_measure_of_ae_tendsto_indicator atTop
      (MeasurableSet.measurableSet_liminf (hYm i)) (hYm i) (hA i) (hAfin i)
      (.of_forall fun l ↦ (hZs _).1.subset i (hYlt i l))
      (TauCeti.MeasureTheory.ae_eventually_mem_iff_mem_liminf hsum)
    have hYμ (l : ℕ) : μ (Y i l) = m i := (hZs _).1.measure_eq i (hYlt i l)
    simp only [hYμ] at h
    exact tendsto_nhds_unique h tendsto_const_nhds

end MeasureTheory.Measure

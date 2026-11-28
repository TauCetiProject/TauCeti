/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Algebra.Order.Group
import TauCeti.Data.Fin.Tuple.Sort

/-!
# Ranks of the entries of a finite tuple

The rank of the entry `x i` of a tuple `x : ι → α` in a linear order is the number of entries
at most `x i`, `rank x i = #{j | x j ≤ x i}`. For distinct entries it is the one-based position
of `x i` in the sorted tuple, and `fun i ↦ rank x i - 1` is the permutation inverse to
`Tuple.sort x`. With ties every tied entry gets the largest of the tied positions: the ranks of
`(0.3, 0.3)` are `(2, 2)`. The absolute rank `absRank x i` is the rank of `|x i|` among the
absolute values of the entries.

Ranks only see the relative order of the entries, so they are invariant under strictly
increasing maps, and they are equivariant under relabelling of the coordinates.

## Main definitions

* `TauCeti.rank` — the rank `#{j | x j ≤ x i}` of an entry of a finite tuple;
* `TauCeti.absRank` — the rank of `|x i|` among the absolute values of the entries.

## Main results

* `TauCeti.rank_le_rank_iff`, `TauCeti.rank_lt_rank_iff` — ranks order the entries as the
  entries themselves are ordered;
* `TauCeti.rank_comp_of_strictMono`, `TauCeti.rank_comp_equiv` — invariance under strictly
  increasing maps and equivariance under relabelling;
* `TauCeti.rank_eq_card_lt_add_one` — for distinct entries, `rank x i = #{j | x j < x i} + 1`;
* `TauCeti.rank_eq_sort_symm_add_one` — for distinct entries, `rank x i - 1` is the permutation
  inverse to `Tuple.sort x`;
* `TauCeti.forall_rank_eq_iff_sort_eq_symm` — for distinct entries, the ranks are `σ + 1`
  exactly when `Tuple.sort x = σ.symm`;
* `TauCeti.measurable_rank`, `TauCeti.measurable_absRank` — measurability.
-/

public section

open Finset Function

namespace TauCeti

section rank

variable {ι α : Type*} [Fintype ι] [LinearOrder α]

/-- The **rank** of the entry `x i` of a finite tuple: the number `#{j | x j ≤ x i}` of entries
at most `x i`. For distinct entries it is the one-based position of `x i` in the sorted tuple;
tied entries all get the largest of their positions. -/
def rank (x : ι → α) (i : ι) : ℕ :=
  #{j | x j ≤ x i}

theorem rank_def (x : ι → α) (i : ι) : rank x i = #{j | x j ≤ x i} := (rfl)

/-- Every rank is positive, since `x i` is at most itself. -/
theorem rank_pos (x : ι → α) (i : ι) : 0 < rank x i :=
  card_pos.2 ⟨i, by simp⟩

/-- No rank exceeds the number of entries. -/
theorem rank_le_card (x : ι → α) (i : ι) : rank x i ≤ Fintype.card ι :=
  card_filter_le _ _

/-- A larger entry has a larger rank. -/
theorem rank_le_rank_of_le {x : ι → α} {i j : ι} (h : x i ≤ x j) : rank x i ≤ rank x j :=
  card_le_card (monotone_filter_right _ fun _ _ hk ↦ hk.trans h)

/-- A strictly larger entry has a strictly larger rank. -/
theorem rank_lt_rank_of_lt {x : ι → α} {i j : ι} (h : x i < x j) : rank x i < rank x j :=
  card_lt_card <| (ssubset_iff_of_subset (monotone_filter_right _ fun _ _ hk ↦ hk.trans h.le)).2
    ⟨j, by simp, by simpa using h⟩

/-- Ranks order the entries as the entries themselves are ordered. -/
@[simp]
theorem rank_le_rank_iff {x : ι → α} {i j : ι} : rank x i ≤ rank x j ↔ x i ≤ x j :=
  ⟨fun h ↦ not_lt.1 fun hji ↦ h.not_gt (rank_lt_rank_of_lt hji), rank_le_rank_of_le⟩

/-- Ranks strictly order the entries as the entries themselves are ordered. -/
@[simp]
theorem rank_lt_rank_iff {x : ι → α} {i j : ι} : rank x i < rank x j ↔ x i < x j := by
  simpa only [not_le] using rank_le_rank_iff.not

/-- Ranks are invariant under a strictly increasing map applied to every entry. -/
theorem rank_comp_of_strictMono {β : Type*} [LinearOrder β] {f : α → β} (hf : StrictMono f)
    (x : ι → α) : rank (f ∘ x) = rank x := by
  ext i
  simp only [rank_def, comp_apply, hf.le_iff_le]

/-- Ranks are equivariant under relabelling of the coordinates. -/
theorem rank_comp_equiv {κ : Type*} [Fintype κ] (x : ι → α) (e : κ ≃ ι) (k : κ) :
    rank (x ∘ e) k = rank x (e k) := by
  simp only [rank_def, comp_apply]
  exact card_bij' (fun j _ ↦ e j) (fun j _ ↦ e.symm j) (by simp) (by simp) (by simp) (by simp)

/-- For distinct entries, the rank of `x i` is one more than the number of entries below `x i`. -/
theorem rank_eq_card_lt_add_one {x : ι → α} (hx : Injective x) (i : ι) :
    rank x i = #{j | x j < x i} + 1 := by
  classical
  have h : filter (fun j ↦ x j ≤ x i) univ = insert i (filter (fun j ↦ x j < x i) univ) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, le_iff_lt_or_eq, hx.eq_iff]
    tauto
  rw [rank_def, h, card_insert_of_notMem (by simp)]

/-- For distinct entries, `rank x - 1` is the permutation inverse to `Tuple.sort x`: the rank of
`x i` is one more than its position in the sorted tuple. -/
theorem rank_eq_sort_symm_add_one {n : ℕ} (x : Fin n → α) (hx : Injective x) (i : Fin n) :
    rank x i = ((Tuple.sort x).symm i : ℕ) + 1 := by
  rw [rank_eq_card_lt_add_one hx, Tuple.val_sort_symm_apply hx]

/-- For distinct entries, the ranks are the permutation `σ` shifted by one exactly when the
sorting permutation is `σ.symm`. -/
theorem forall_rank_eq_iff_sort_eq_symm {n : ℕ} {x : Fin n → α} (hx : Injective x)
    (σ : Equiv.Perm (Fin n)) :
    (∀ i, rank x i = (σ i : ℕ) + 1) ↔ Tuple.sort x = σ.symm := by
  simp only [rank_eq_sort_symm_add_one x hx, add_left_inj, Fin.val_inj]
  rw [← Equiv.ext_iff, eq_comm]
  exact ⟨fun h ↦ by rw [h, Equiv.symm_symm], fun h ↦ by rw [h, Equiv.symm_symm]⟩

variable [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] [OrderClosedTopology α]
  [SecondCountableTopology α]

/-- Each rank is a measurable function of the tuple. -/
@[fun_prop]
theorem measurable_rank (i : ι) : Measurable fun x : ι → α ↦ rank x i := by
  simp only [rank_def, card_filter]
  exact Finset.measurable_sum _ fun j _ ↦ Measurable.ite
    (measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i)) measurable_const
    measurable_const

end rank

section absRank

variable {ι α : Type*} [Fintype ι] [LinearOrder α] [AddGroup α]

/-- The **absolute rank** of the entry `x i` of a finite tuple: the rank of `|x i|` among the
absolute values `|x j|`, that is the number `#{j | |x j| ≤ |x i|}`. -/
def absRank (x : ι → α) (i : ι) : ℕ :=
  rank (fun j ↦ |x j|) i

theorem absRank_def (x : ι → α) (i : ι) : absRank x i = #{j | |x j| ≤ |x i|} := (rfl)

/-- The absolute ranks are the ranks of the absolute values. -/
theorem absRank_eq_rank (x : ι → α) : absRank x = rank fun j ↦ |x j| := (rfl)

/-- Absolute ranks only depend on the absolute values of the entries. -/
theorem absRank_congr {x y : ι → α} (h : ∀ j, |x j| = |y j|) : absRank x = absRank y := by
  rw [absRank_eq_rank, absRank_eq_rank, funext h]

/-- Absolute ranks are invariant under negation of the tuple. -/
@[simp]
theorem absRank_neg (x : ι → α) : absRank (-x) = absRank x :=
  absRank_congr fun j ↦ by simp

end absRank

/-- Each absolute rank is a measurable function of the tuple. -/
@[fun_prop]
theorem measurable_absRank {ι G : Type*} [Fintype ι] [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [TopologicalSpace G] [OrderTopology G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (i : ι) : Measurable fun x : ι → G ↦ absRank x i := by
  have habs : Measurable fun x : ι → G ↦ fun j ↦ |x j| :=
    Measurable.of_eval fun j ↦ continuous_abs.measurable.comp (measurable_pi_apply j)
  simp only [absRank_eq_rank]
  exact (measurable_rank i).comp habs

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finset.Powerset
public import TauCeti.Analysis.Convex.Majorization

import Mathlib.Data.Fintype.Fin

/-!
# Majorization through largest subset sums

For a vector `a : ι → M` on a finite type and `i < card ι`, `maxSubsetSum i a` is the largest sum
of `i` coordinates of `a`. A vector `x` is *majorized* by `y`, `Majorizes x y` (often written
`x ≺ y`), when both have the same total sum and every largest `i`-coordinate sum of `x` is at most
that of `y`; so `y` is the more spread out vector. It is *weakly (sub)majorized*,
`WeaklyMajorizes x y` (`x ≺_w y`), when the total sum of `x` is at most that of `y` and the same
inequalities hold. Neither definition uses an order on `ι`, and both make sense for vectors of any
sign.

On `Fin n` the largest sum of `k` coordinates is the prefix sum of length `k` of the decreasing
rearrangement `x ∘ Tuple.sortDesc x`, so majorization is the classical comparison of the prefix
sums of decreasing rearrangements. For antitone nonnegative tuples, weak majorization is
`TauCeti.IsWeaklyMajorizedBy`, which makes the transfer calculus of
`TauCeti.Analysis.Convex.Majorization` available for `WeaklyMajorizes`.

## Main definitions

* `TauCeti.maxSubsetSum i a`: the largest sum of `i` coordinates of `a`.
* `TauCeti.Majorizes x y`: `x` is majorized by `y`.
* `TauCeti.WeaklyMajorizes x y`: `x` is weakly submajorized by `y`.

## Main results

* `TauCeti.maxSubsetSum_le_iff`, `TauCeti.sum_le_maxSubsetSum`,
  `TauCeti.exists_sum_eq_maxSubsetSum`: `maxSubsetSum i a` is the largest sum of `i` coordinates.
* `TauCeti.maxSubsetSum_comp_equiv`, `TauCeti.maxSubsetSum_mono`, `TauCeti.maxSubsetSum_add_le`,
  `TauCeti.maxSubsetSum_smul`: largest subset sums are invariant under reindexing, monotone,
  subadditive and positively homogeneous.
* `TauCeti.maxSubsetSum_eq_prefixSum_sortDesc`: on `Fin n`, the largest sum of `i` coordinates is
  the prefix sum of length `i` of the decreasing rearrangement.
* `TauCeti.majorizes_iff_prefixSum`, `TauCeti.weaklyMajorizes_iff_prefixSum`: majorization and
  weak majorization through prefix sums of decreasing rearrangements.
* `TauCeti.weaklyMajorizes_iff_isWeaklyMajorizedBy`: for antitone nonnegative tuples, weak
  majorization is `TauCeti.IsWeaklyMajorizedBy`.
* `TauCeti.Majorizes.trans`, `TauCeti.WeaklyMajorizes.trans` and the `refl` lemmas:
  both relations are preorders; `TauCeti.majorizes_comp_equiv_iff`,
  `TauCeti.majorizes_comp_perm_left_iff` and their relatives: they are invariant under reindexing
  and under permuting either vector.
* `TauCeti.majorizes_and_majorizes_iff_exists_perm`: `x ≺ y` and `y ≺ x` exactly when `x` is a
  rearrangement of `y`.

## References

* A. W. Marshall, I. Olkin and B. C. Arnold, *Inequalities: Theory of Majorization and Its
  Applications*, 2nd ed., Springer, 2011: Definition 1.A.1 (p. 8) and Definition 1.A.2 (p. 12),
  stated through partial sums of decreasing rearrangements, which is
  `TauCeti.majorizes_iff_prefixSum`.

The formulation by largest subset sums over an arbitrary finite index type, and the direction
of `Majorizes`, follow the design of Mathlib pull request 41898 (majorization).
-/

public section

namespace TauCeti

open Finset

variable {ι κ M : Type*} [Fintype ι] [Fintype κ]

section LinearOrder

variable [AddCommMonoid M] [LinearOrder M]

/-- The largest sum of `i` coordinates of `a`, for `i < card ι`. At `i = 0` it is `0`; the sum of
all coordinates is not of this form and is treated separately by `Majorizes`. -/
def maxSubsetSum (i : Fin (Fintype.card ι)) (a : ι → M) : M :=
  (univ.powersetCard i).sup' (powersetCard_nonempty.2 (by rw [card_univ]; exact i.isLt.le))
    fun s ↦ ∑ j ∈ s, a j

/-- The sum of any `i` coordinates is at most `maxSubsetSum i a`. -/
theorem sum_le_maxSubsetSum {i : Fin (Fintype.card ι)} (a : ι → M) {s : Finset ι}
    (hs : #s = i) : ∑ j ∈ s, a j ≤ maxSubsetSum i a :=
  le_sup' (fun s ↦ ∑ j ∈ s, a j) (mem_powersetCard.2 ⟨subset_univ s, hs⟩)

/-- `maxSubsetSum i a` is bounded by `c` exactly when every sum of `i` coordinates is. -/
theorem maxSubsetSum_le_iff {i : Fin (Fintype.card ι)} {a : ι → M} {c : M} :
    maxSubsetSum i a ≤ c ↔ ∀ s : Finset ι, #s = i → ∑ j ∈ s, a j ≤ c := by
  simp [maxSubsetSum, sup'_le_iff, mem_powersetCard]

/-- The largest sum of `i` coordinates is attained. -/
theorem exists_sum_eq_maxSubsetSum (i : Fin (Fintype.card ι)) (a : ι → M) :
    ∃ s : Finset ι, #s = i ∧ ∑ j ∈ s, a j = maxSubsetSum i a := by
  obtain ⟨s, hs, h⟩ := exists_mem_eq_sup' (s := univ.powersetCard i)
    (powersetCard_nonempty.2 (by rw [card_univ]; exact i.isLt.le)) fun s ↦ ∑ j ∈ s, a j
  exact ⟨s, (mem_powersetCard.1 hs).2, h.symm⟩

/-- The largest sum of no coordinates is `0`. -/
theorem maxSubsetSum_of_val_eq_zero {i : Fin (Fintype.card ι)} (hi : (i : ℕ) = 0) (a : ι → M) :
    maxSubsetSum i a = 0 := by
  refine le_antisymm (maxSubsetSum_le_iff.2 fun s hs ↦ ?_) ?_
  · rw [card_eq_zero.1 (hs.trans hi), sum_empty]
  · simpa using sum_le_maxSubsetSum a (s := ∅) (by simp [hi])

/-- Largest subset sums are invariant under reindexing the coordinates. -/
theorem maxSubsetSum_comp_equiv (e : κ ≃ ι) (i : Fin (Fintype.card κ)) (a : ι → M) :
    maxSubsetSum i (a ∘ e) = maxSubsetSum (Fin.cast (Fintype.card_congr e) i) a := by
  refine le_antisymm (maxSubsetSum_le_iff.2 fun s hs ↦ ?_) (maxSubsetSum_le_iff.2 fun t ht ↦ ?_)
  · have h := sum_le_maxSubsetSum a (s := s.map e.toEmbedding)
      (i := Fin.cast (Fintype.card_congr e) i) (by simpa using hs)
    simpa [sum_map] using h
  · have h := sum_le_maxSubsetSum (a ∘ e) (s := t.map e.symm.toEmbedding) (i := i)
      (by simpa using ht)
    simpa [sum_map] using h

/-- Largest subset sums are invariant under permuting the coordinates. -/
@[simp]
theorem maxSubsetSum_comp_perm (σ : Equiv.Perm ι) (i : Fin (Fintype.card ι)) (a : ι → M) :
    maxSubsetSum i (a ∘ σ) = maxSubsetSum i a := by
  rw [maxSubsetSum_comp_equiv, Fin.cast_eq_self]

/-- Largest subset sums are monotone in the vector. -/
@[gcongr]
theorem maxSubsetSum_mono [IsOrderedAddMonoid M] (i : Fin (Fintype.card ι)) {a b : ι → M}
    (h : a ≤ b) : maxSubsetSum i a ≤ maxSubsetSum i b :=
  maxSubsetSum_le_iff.2 fun _ hs ↦ (sum_le_sum fun j _ ↦ h j).trans (sum_le_maxSubsetSum b hs)

/-- Largest subset sums are subadditive. -/
theorem maxSubsetSum_add_le [IsOrderedAddMonoid M] (i : Fin (Fintype.card ι)) (a b : ι → M) :
    maxSubsetSum i (a + b) ≤ maxSubsetSum i a + maxSubsetSum i b :=
  maxSubsetSum_le_iff.2 fun _ hs ↦ by
    simpa only [Pi.add_apply, sum_add_distrib] using
      add_le_add (sum_le_maxSubsetSum a hs) (sum_le_maxSubsetSum b hs)

/-- Largest subset sums are positively homogeneous. -/
theorem maxSubsetSum_smul {R : Type*} [Zero R] [Preorder R] [DistribSMul R M] [PosSMulMono R M]
    (i : Fin (Fintype.card ι)) {c : R} (hc : 0 ≤ c) (a : ι → M) :
    maxSubsetSum i (c • a) = c • maxSubsetSum i a := by
  obtain ⟨s, hs, hsa⟩ := exists_sum_eq_maxSubsetSum i a
  refine le_antisymm (maxSubsetSum_le_iff.2 fun t ht ↦ ?_) ?_
  · simpa only [Pi.smul_apply, smul_sum] using smul_le_smul_of_nonneg_left
      (sum_le_maxSubsetSum a ht) hc
  · simpa only [← hsa, smul_sum, Pi.smul_apply] using sum_le_maxSubsetSum (c • a) hs

/-- `x` is *majorized* by `y`, `x ≺ y`: the total sums agree, and for every `i < card ι` the
largest sum of `i` coordinates of `x` is at most that of `y`. -/
structure Majorizes (x y : ι → M) : Prop where
  /-- The total sums agree. -/
  sum_eq : ∑ j, x j = ∑ j, y j
  /-- Every largest `i`-coordinate sum of `x` is at most that of `y`. -/
  maxSubsetSum_le : ∀ i : Fin (Fintype.card ι), maxSubsetSum i x ≤ maxSubsetSum i y

/-- `x` is *weakly submajorized* by `y`, `x ≺_w y`: the total sum of `x` is at most that of `y`,
and for every `i < card ι` the largest sum of `i` coordinates of `x` is at most that of `y`. -/
structure WeaklyMajorizes (x y : ι → M) : Prop where
  /-- The total sum of `x` is at most that of `y`. -/
  sum_le : ∑ j, x j ≤ ∑ j, y j
  /-- Every largest `i`-coordinate sum of `x` is at most that of `y`. -/
  maxSubsetSum_le : ∀ i : Fin (Fintype.card ι), maxSubsetSum i x ≤ maxSubsetSum i y

variable {x y z : ι → M}

/-- The defining conditions of `Majorizes`. -/
theorem majorizes_iff : Majorizes x y ↔
    ∑ j, x j = ∑ j, y j ∧ ∀ i : Fin (Fintype.card ι), maxSubsetSum i x ≤ maxSubsetSum i y :=
  ⟨fun h ↦ ⟨h.sum_eq, h.maxSubsetSum_le⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- The defining conditions of `WeaklyMajorizes`. -/
theorem weaklyMajorizes_iff : WeaklyMajorizes x y ↔
    ∑ j, x j ≤ ∑ j, y j ∧ ∀ i : Fin (Fintype.card ι), maxSubsetSum i x ≤ maxSubsetSum i y :=
  ⟨fun h ↦ ⟨h.sum_le, h.maxSubsetSum_le⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Majorization is weak majorization with equal total sums. -/
theorem majorizes_iff_weaklyMajorizes_and_sum_eq :
    Majorizes x y ↔ WeaklyMajorizes x y ∧ ∑ j, x j = ∑ j, y j :=
  ⟨fun h ↦ ⟨⟨h.sum_eq.le, h.maxSubsetSum_le⟩, h.sum_eq⟩, fun h ↦ ⟨h.2, h.1.maxSubsetSum_le⟩⟩

/-- Majorization implies weak majorization. -/
theorem Majorizes.weaklyMajorizes (h : Majorizes x y) : WeaklyMajorizes x y :=
  (majorizes_iff_weaklyMajorizes_and_sum_eq.1 h).1

/-- Every vector is majorized by itself. -/
@[refl]
theorem Majorizes.refl (x : ι → M) : Majorizes x x :=
  ⟨rfl, fun _ ↦ le_rfl⟩

/-- Every vector is majorized by itself. -/
theorem Majorizes.rfl : Majorizes x x :=
  Majorizes.refl x

/-- Majorization is transitive. -/
@[trans]
theorem Majorizes.trans (hxy : Majorizes x y) (hyz : Majorizes y z) : Majorizes x z :=
  ⟨hxy.sum_eq.trans hyz.sum_eq, fun i ↦ (hxy.maxSubsetSum_le i).trans (hyz.maxSubsetSum_le i)⟩

/-- Every vector is weakly majorized by itself. -/
@[refl]
theorem WeaklyMajorizes.refl (x : ι → M) : WeaklyMajorizes x x :=
  ⟨le_rfl, fun _ ↦ le_rfl⟩

/-- Every vector is weakly majorized by itself. -/
theorem WeaklyMajorizes.rfl : WeaklyMajorizes x x :=
  WeaklyMajorizes.refl x

/-- Weak majorization is transitive. -/
@[trans]
theorem WeaklyMajorizes.trans (hxy : WeaklyMajorizes x y) (hyz : WeaklyMajorizes y z) :
    WeaklyMajorizes x z :=
  ⟨hxy.sum_le.trans hyz.sum_le, fun i ↦ (hxy.maxSubsetSum_le i).trans (hyz.maxSubsetSum_le i)⟩

/-- Decreasing the smaller vector preserves weak majorization. -/
theorem WeaklyMajorizes.mono_left [IsOrderedAddMonoid M] (hxy : WeaklyMajorizes x y)
    (hzx : z ≤ x) : WeaklyMajorizes z y :=
  ⟨(sum_le_sum fun j _ ↦ hzx j).trans hxy.sum_le,
    fun i ↦ (maxSubsetSum_mono i hzx).trans (hxy.maxSubsetSum_le i)⟩

/-- Increasing the larger vector preserves weak majorization. -/
theorem WeaklyMajorizes.mono_right [IsOrderedAddMonoid M] (hxy : WeaklyMajorizes x y)
    (hyz : y ≤ z) : WeaklyMajorizes x z :=
  ⟨hxy.sum_le.trans (sum_le_sum fun j _ ↦ hyz j),
    fun i ↦ (hxy.maxSubsetSum_le i).trans (maxSubsetSum_mono i hyz)⟩

/-- Majorization is invariant under reindexing both vectors along the same equivalence. -/
theorem majorizes_comp_equiv_iff (e : κ ≃ ι) : Majorizes (x ∘ e) (y ∘ e) ↔ Majorizes x y := by
  refine ⟨fun h ↦ ⟨?_, fun i ↦ ?_⟩, fun h ↦ ⟨?_, fun i ↦ ?_⟩⟩
  · simpa only [Function.comp_apply, Equiv.sum_comp] using h.sum_eq
  · simpa [maxSubsetSum_comp_equiv] using
      h.maxSubsetSum_le (Fin.cast (Fintype.card_congr e).symm i)
  · simpa only [Function.comp_apply, Equiv.sum_comp] using h.sum_eq
  · simpa [maxSubsetSum_comp_equiv] using h.maxSubsetSum_le (Fin.cast (Fintype.card_congr e) i)

/-- Weak majorization is invariant under reindexing both vectors along the same equivalence. -/
theorem weaklyMajorizes_comp_equiv_iff (e : κ ≃ ι) :
    WeaklyMajorizes (x ∘ e) (y ∘ e) ↔ WeaklyMajorizes x y := by
  refine ⟨fun h ↦ ⟨?_, fun i ↦ ?_⟩, fun h ↦ ⟨?_, fun i ↦ ?_⟩⟩
  · simpa only [Function.comp_apply, Equiv.sum_comp] using h.sum_le
  · simpa [maxSubsetSum_comp_equiv] using
      h.maxSubsetSum_le (Fin.cast (Fintype.card_congr e).symm i)
  · simpa only [Function.comp_apply, Equiv.sum_comp] using h.sum_le
  · simpa [maxSubsetSum_comp_equiv] using h.maxSubsetSum_le (Fin.cast (Fintype.card_congr e) i)

/-- Majorization is invariant under permuting the smaller vector. -/
@[simp]
theorem majorizes_comp_perm_left_iff (σ : Equiv.Perm ι) :
    Majorizes (x ∘ σ) y ↔ Majorizes x y := by
  simp only [majorizes_iff, Function.comp_apply, Equiv.sum_comp, maxSubsetSum_comp_perm]

/-- Majorization is invariant under permuting the larger vector. -/
@[simp]
theorem majorizes_comp_perm_right_iff (σ : Equiv.Perm ι) :
    Majorizes x (y ∘ σ) ↔ Majorizes x y := by
  simp only [majorizes_iff, Function.comp_apply, Equiv.sum_comp, maxSubsetSum_comp_perm]

/-- Weak majorization is invariant under permuting the smaller vector. -/
@[simp]
theorem weaklyMajorizes_comp_perm_left_iff (σ : Equiv.Perm ι) :
    WeaklyMajorizes (x ∘ σ) y ↔ WeaklyMajorizes x y := by
  simp only [weaklyMajorizes_iff, Function.comp_apply, Equiv.sum_comp, maxSubsetSum_comp_perm]

/-- Weak majorization is invariant under permuting the larger vector. -/
@[simp]
theorem weaklyMajorizes_comp_perm_right_iff (σ : Equiv.Perm ι) :
    WeaklyMajorizes x (y ∘ σ) ↔ WeaklyMajorizes x y := by
  simp only [weaklyMajorizes_iff, Function.comp_apply, Equiv.sum_comp, maxSubsetSum_comp_perm]

end LinearOrder

/-! ### Tuples indexed by `Fin n` -/

section Fin

variable {n : ℕ} [AddCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]

/-- For an antitone tuple, the largest sum of `i` coordinates is the sum of the first `i`. -/
theorem maxSubsetSum_eq_prefixSum_of_antitone {x : Fin n → M} (hx : Antitone x)
    (i : Fin (Fintype.card (Fin n))) : maxSubsetSum i x = prefixSum i x := by
  classical
  have hi : (i : ℕ) ≤ n := i.isLt.le.trans_eq (Fintype.card_fin n)
  refine le_antisymm (maxSubsetSum_le_iff.2 fun s hs ↦ hs ▸ sum_le_prefixSum_card hx s) ?_
  rw [prefixSum_def]
  exact sum_le_maxSubsetSum x (by rw [Fin.card_filter_val_lt, min_eq_right hi])

/-- On `Fin n`, the largest sum of `i` coordinates of `x` is the prefix sum of length `i` of its
decreasing rearrangement. -/
theorem maxSubsetSum_eq_prefixSum_sortDesc (x : Fin n → M) (i : Fin (Fintype.card (Fin n))) :
    maxSubsetSum i x = prefixSum i (x ∘ Tuple.sortDesc x) := by
  rw [← maxSubsetSum_eq_prefixSum_of_antitone (Tuple.antitone_sortDesc x), maxSubsetSum_comp_perm]

/-- On `Fin n`, `x ≺_w y` exactly when every prefix sum of the decreasing rearrangement of `x` is
at most the corresponding prefix sum of the decreasing rearrangement of `y`. -/
theorem weaklyMajorizes_iff_prefixSum {x y : Fin n → M} :
    WeaklyMajorizes x y ↔
      ∀ k, prefixSum k (x ∘ Tuple.sortDesc x) ≤ prefixSum k (y ∘ Tuple.sortDesc y) := by
  refine ⟨fun h k ↦ ?_, fun h ↦ ⟨?_, fun i ↦ ?_⟩⟩
  · rcases lt_or_ge k n with hk | hk
    · have := h.maxSubsetSum_le ⟨k, by rwa [Fintype.card_fin]⟩
      rwa [maxSubsetSum_eq_prefixSum_sortDesc, maxSubsetSum_eq_prefixSum_sortDesc] at this
    · simpa only [prefixSum_of_le hk, Function.comp_apply, Equiv.sum_comp] using h.sum_le
  · simpa only [prefixSum_of_le le_rfl, Function.comp_apply, Equiv.sum_comp] using h n
  · rw [maxSubsetSum_eq_prefixSum_sortDesc, maxSubsetSum_eq_prefixSum_sortDesc]
    exact h i

/-- On `Fin n`, `x ≺ y` exactly when every prefix sum of the decreasing rearrangement of `x` is at
most the corresponding prefix sum of the decreasing rearrangement of `y`, and the total sums
agree. -/
theorem majorizes_iff_prefixSum {x y : Fin n → M} :
    Majorizes x y ↔
      (∀ k, prefixSum k (x ∘ Tuple.sortDesc x) ≤ prefixSum k (y ∘ Tuple.sortDesc y)) ∧
        ∑ i, x i = ∑ i, y i := by
  rw [majorizes_iff_weaklyMajorizes_and_sum_eq, weaklyMajorizes_iff_prefixSum]

/-- For antitone nonnegative real tuples, weak majorization is `TauCeti.IsWeaklyMajorizedBy`. -/
theorem weaklyMajorizes_iff_isWeaklyMajorizedBy {x y : Fin n → ℝ} (hx : Antitone x)
    (hy : Antitone y) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) :
    WeaklyMajorizes x y ↔ IsWeaklyMajorizedBy x y := by
  have hxs : x ∘ Tuple.sortDesc x = x := by
    simpa using Tuple.unique_antitone (τ := 1) (Tuple.antitone_sortDesc x) (by simpa using hx)
  have hys : y ∘ Tuple.sortDesc y = y := by
    simpa using Tuple.unique_antitone (τ := 1) (Tuple.antitone_sortDesc y) (by simpa using hy)
  rw [weaklyMajorizes_iff_prefixSum, hxs, hys]
  exact ⟨fun h ↦ ⟨hx, hy, hx0, hy0, h⟩, IsWeaklyMajorizedBy.prefixSum_le⟩

/-- Tuples on `Fin n` that majorize each other have the same decreasing rearrangement. -/
theorem Majorizes.comp_sortDesc_eq [IsLeftCancelAdd M] {x y : Fin n → M} (hxy : Majorizes x y)
    (hyx : Majorizes y x) : x ∘ Tuple.sortDesc x = y ∘ Tuple.sortDesc y :=
  eq_of_forall_prefixSum_eq fun k ↦
    ((majorizes_iff_prefixSum.1 hxy).1 k).antisymm ((majorizes_iff_prefixSum.1 hyx).1 k)

end Fin

/-- `x ≺ y` and `y ≺ x` exactly when `x` is a rearrangement of `y`. -/
theorem majorizes_and_majorizes_iff_exists_perm [AddCommMonoid M] [LinearOrder M]
    [IsOrderedAddMonoid M] [IsLeftCancelAdd M] {x y : ι → M} :
    Majorizes x y ∧ Majorizes y x ↔ ∃ σ : Equiv.Perm ι, x = y ∘ σ := by
  refine ⟨fun ⟨hxy, hyx⟩ ↦ ?_, ?_⟩
  · set e := (Fintype.equivFin ι).symm
    have h := Majorizes.comp_sortDesc_eq ((majorizes_comp_equiv_iff e).2 hxy)
      ((majorizes_comp_equiv_iff e).2 hyx)
    refine ⟨(e.symm.trans (Tuple.sortDesc (x ∘ e)).symm).trans
      ((Tuple.sortDesc (y ∘ e)).trans e), funext fun i ↦ ?_⟩
    simpa using congrFun h ((Tuple.sortDesc (x ∘ e)).symm (e.symm i))
  · rintro ⟨σ, rfl⟩
    exact ⟨(majorizes_comp_perm_left_iff σ).2 .rfl, (majorizes_comp_perm_right_iff σ).2 .rfl⟩

end TauCeti

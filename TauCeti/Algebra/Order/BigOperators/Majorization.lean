/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Fin.Tuple.Sort
public import TauCeti.Algebra.BigOperators.Finset.PartialSum
public import TauCeti.Algebra.Order.BigOperators.Dominance
public import TauCeti.Data.Finset.Powerset
import TauCeti.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.NormNum

/-!
# Majorization and weak majorization of vectors

For a vector `a : ι → M` on a finite index type with values in a linearly ordered additive
commutative monoid, `TauCeti.maxSubsetSum i a` is the largest sum of `a` over a subset of `ι` of
size `i`, for `i : Fin (Fintype.card ι)`. The vector `a` is *majorized* by `b` (`a ≺ b`,
`TauCeti.Majorizes a b`) when the two have the same total and every largest subset sum of `a` is
at most the one of `b` of the same size; it is *weakly submajorized* by `b` (`a ≺_w b`,
`TauCeti.WeaklyMajorizes a b`) when the same holds with the total of `a` at most that of `b`.

These definitions need no order on the index type. On `Fin n`, the largest sum of `i`
coordinates is the sum of the first `i` coordinates of the decreasing rearrangement
`x ∘ Tuple.sortDesc x`, so majorization is the classical comparison of the prefix sums of the
decreasing rearrangements, which is the dominance order `TauCeti.Dominates` between them.

Majorization is a preorder and invariant under permuting either vector. For values in an ordered
cancellative additive monoid, two vectors majorize each other exactly when one is a permutation of
the other. Over a linearly ordered semifield, the
constant vector with the same total is majorized by every vector.

## Main definitions

* `TauCeti.maxSubsetSum i a`: the largest sum of `i` coordinates of `a`.
* `TauCeti.Majorizes a b`: majorization `a ≺ b`.
* `TauCeti.WeaklyMajorizes a b`: weak submajorization `a ≺_w b`.

## Main results

* `TauCeti.maxSubsetSum_le_iff`, `TauCeti.sum_le_maxSubsetSum`,
  `TauCeti.exists_sum_eq_maxSubsetSum`: `maxSubsetSum i a` is the maximum of the sums of `a`
  over the subsets of size `i`.
* `TauCeti.maxSubsetSum_comp_equiv`, `TauCeti.maxSubsetSum_comp_perm`: invariance under
  reindexing.
* `TauCeti.maxSubsetSum_mono`, `TauCeti.maxSubsetSum_add_le`, `TauCeti.maxSubsetSum_smul`:
  `maxSubsetSum i` is monotone, subadditive and positively homogeneous.
* `TauCeti.le_of_sum_eq_maxSubsetSum`: a set attaining `maxSubsetSum i a` contains the largest
  coordinates of `a`.
* `TauCeti.maxSubsetSum_eq_prefixSum_sortDesc`: on `Fin n`, the largest sum of `i` coordinates
  is a prefix sum of the decreasing rearrangement.
* `TauCeti.majorizes_iff_prefixSum`, `TauCeti.weaklyMajorizes_iff_prefixSum`,
  `TauCeti.majorizes_iff_dominates`: the sorted forms of majorization and weak majorization;
  `TauCeti.weaklyMajorizes_iff_prefixSum_of_antitone`: the same for antitone tuples, without
  rearranging.
* `TauCeti.majorizes_comp_equiv_iff`, `TauCeti.majorizes_comp_perm_left_iff`,
  `TauCeti.majorizes_comp_perm_right_iff`, and the same for `TauCeti.WeaklyMajorizes`:
  invariance under reindexing and under permuting either vector.
* `TauCeti.majorizes_antisymm_iff`: in an ordered cancellative additive monoid, `a ≺ b` and
  `b ≺ a` exactly when `a` is a permutation of `b`.
* `TauCeti.majorizes_const_sum_div_card`: the constant vector with the total of `b` is majorized
  by `b`.

## References

* A. W. Marshall, I. Olkin, B. C. Arnold, *Inequalities: Theory of Majorization and Its
  Applications*, 2nd ed., Springer (2011), 1.A.1 (p. 8) and 1.A.2 (p. 12).

The definitions follow the shape of Mathlib pull request #41898. The comparison of
subset sums with the prefix sums of the decreasing rearrangement
(`TauCeti.maxSubsetSum_eq_prefixSum_sortDesc`, and `Antitone.sum_le_prefixSum` in
`TauCeti.Algebra.BigOperators.Finset.PartialSum`) is adapted from `sum_le_sumInitial_of_antitone`
and `sum_le_sumLargest` in `CKMA/Analysis/Convex/Majorization.lean` of the lean-CKMA project.
-/

public section

open Finset

namespace TauCeti

variable {ι κ M : Type*} [Fintype ι] [Fintype κ]

/-! ### Largest subset sums -/

section MaxSubsetSum

variable [AddCommMonoid M] [LinearOrder M] {i : Fin (Fintype.card ι)} {a b : ι → M}

/-- The largest sum of `i` coordinates of `a`, the maximum of `∑ j ∈ s, a j` over the subsets
`s` of size `i`. -/
def maxSubsetSum (i : Fin (Fintype.card ι)) (a : ι → M) : M :=
  (univ.powersetCard i).sup' (powersetCard_univ_nonempty i) fun s ↦ ∑ j ∈ s, a j

/-- The defining formula of `maxSubsetSum` as a maximum over `Finset.powersetCard`. -/
theorem maxSubsetSum_def (i : Fin (Fintype.card ι)) (a : ι → M) :
    maxSubsetSum i a =
      (univ.powersetCard i).sup' (powersetCard_univ_nonempty i) fun s ↦ ∑ j ∈ s, a j := by
  rw [maxSubsetSum]

/-- `maxSubsetSum i a` is at most `c` exactly when every sum of `i` coordinates of `a` is. -/
theorem maxSubsetSum_le_iff {c : M} :
    maxSubsetSum i a ≤ c ↔ ∀ s : Finset ι, #s = i → ∑ j ∈ s, a j ≤ c := by
  simp [maxSubsetSum_def, Finset.sup'_le_iff, mem_powersetCard]

/-- `c` is at most `maxSubsetSum i a` exactly when `c` is at most some sum of `i` coordinates
of `a`. -/
theorem le_maxSubsetSum_iff {c : M} :
    c ≤ maxSubsetSum i a ↔ ∃ s : Finset ι, #s = i ∧ c ≤ ∑ j ∈ s, a j := by
  simp [maxSubsetSum_def, Finset.le_sup'_iff, mem_powersetCard]

/-- Every sum of `i` coordinates of `a` is at most `maxSubsetSum i a`. -/
theorem sum_le_maxSubsetSum {s : Finset ι} (hs : #s = i) : ∑ j ∈ s, a j ≤ maxSubsetSum i a :=
  le_maxSubsetSum_iff.mpr ⟨s, hs, le_rfl⟩

/-- `maxSubsetSum i a` is attained by a subset of size `i`. -/
theorem exists_sum_eq_maxSubsetSum (i : Fin (Fintype.card ι)) (a : ι → M) :
    ∃ s : Finset ι, #s = i ∧ ∑ j ∈ s, a j = maxSubsetSum i a := by
  obtain ⟨s, hs, h⟩ := exists_mem_eq_sup' (powersetCard_univ_nonempty i) fun s ↦ ∑ j ∈ s, a j
  exact ⟨s, (mem_powersetCard.mp hs).2, by rw [maxSubsetSum_def, h]⟩

/-- The largest sum of no coordinates is `0`. -/
@[simp]
theorem maxSubsetSum_of_val_eq_zero (hi : (i : ℕ) = 0) : maxSubsetSum i a = 0 := by
  obtain ⟨s, hs, h⟩ := exists_sum_eq_maxSubsetSum i a
  rw [← h, card_eq_zero.mp (hs.trans hi), sum_empty]

/-- Largest subset sums are invariant under reindexing along an equivalence `e : κ ≃ ι`; the
size `i` is transported along `Fintype.card κ = Fintype.card ι`. -/
theorem maxSubsetSum_comp_equiv (e : κ ≃ ι) (i : Fin (Fintype.card ι)) (a : ι → M) :
    maxSubsetSum (Fin.cast (Fintype.card_congr e).symm i) (a ∘ e) = maxSubsetSum i a := by
  refine le_antisymm (maxSubsetSum_le_iff.mpr fun s hs ↦ ?_) (maxSubsetSum_le_iff.mpr fun s hs ↦ ?_)
  · simpa [sum_map] using
      sum_le_maxSubsetSum (a := a) (s := s.map e.toEmbedding) (by simpa using hs)
  · simpa [sum_map] using
      sum_le_maxSubsetSum (a := a ∘ e) (s := s.map e.symm.toEmbedding) (by simpa using hs)

/-- Largest subset sums are invariant under permuting the coordinates. -/
@[simp]
theorem maxSubsetSum_comp_perm (σ : Equiv.Perm ι) (i : Fin (Fintype.card ι)) (a : ι → M) :
    maxSubsetSum i (a ∘ σ) = maxSubsetSum i a := by
  simpa using maxSubsetSum_comp_equiv σ i a

/-- `maxSubsetSum i` is positively homogeneous. -/
theorem maxSubsetSum_smul {R : Type*} [Zero R] [Preorder R] [DistribSMul R M] [PosSMulMono R M]
    {c : R} (hc : 0 ≤ c) (i : Fin (Fintype.card ι)) (a : ι → M) :
    maxSubsetSum i (c • a) = c • maxSubsetSum i a := by
  obtain ⟨s, hs, h⟩ := exists_sum_eq_maxSubsetSum i a
  refine le_antisymm (maxSubsetSum_le_iff.mpr fun t ht ↦ ?_) ?_
  · simpa only [Pi.smul_apply, ← smul_sum] using smul_le_smul_of_nonneg_left
      (sum_le_maxSubsetSum ht) hc
  · simpa only [← h, smul_sum, Pi.smul_apply] using sum_le_maxSubsetSum (a := c • a) hs

/-- A set of indices attaining the largest sum of `i` coordinates of `a` contains the largest
coordinates: every coordinate outside it is at most every coordinate inside it. -/
theorem le_of_sum_eq_maxSubsetSum [IsOrderedCancelAddMonoid M] {T : Finset ι} (hT : #T = i)
    (hTsum : ∑ j ∈ T, a j = maxSubsetSum i a) {j k : ι} (hj : j ∉ T) (hk : k ∈ T) :
    a j ≤ a k := by
  classical
  -- Otherwise exchanging `k` for `j` would increase the sum.
  have h := sum_le_maxSubsetSum (a := a) (s := insert j (T.erase k)) (i := i) (by
    rw [card_insert_of_notMem (by simp [hj]), card_erase_add_one hk, hT])
  rwa [sum_insert (by simp [hj]), ← hTsum, ← add_sum_erase T a hk, add_le_add_iff_right] at h

variable [IsOrderedAddMonoid M]

/-- `maxSubsetSum i` is monotone in the vector. -/
theorem maxSubsetSum_mono (i : Fin (Fintype.card ι)) :
    Monotone (maxSubsetSum i : (ι → M) → M) := fun _ _ hxy ↦
  maxSubsetSum_le_iff.mpr fun _ hs ↦ (sum_le_sum fun j _ ↦ hxy j).trans (sum_le_maxSubsetSum hs)

/-- `maxSubsetSum i` is subadditive. -/
theorem maxSubsetSum_add_le (i : Fin (Fintype.card ι)) (a b : ι → M) :
    maxSubsetSum i (a + b) ≤ maxSubsetSum i a + maxSubsetSum i b :=
  maxSubsetSum_le_iff.mpr fun _ hs ↦ by
    simpa only [Pi.add_apply, sum_add_distrib] using
      add_le_add (sum_le_maxSubsetSum hs) (sum_le_maxSubsetSum hs)

end MaxSubsetSum

/-! ### Largest subset sums of tuples -/

section Sorted

variable {n : ℕ} [AddCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]

/-- For an antitone tuple, the largest sum of `i` coordinates is the sum of the first `i`. -/
theorem _root_.Antitone.maxSubsetSum_eq_prefixSum {x : Fin n → M} (hx : Antitone x)
    (i : Fin (Fintype.card (Fin n))) : maxSubsetSum i x = prefixSum i x := by
  refine le_antisymm (maxSubsetSum_le_iff.mpr fun s hs ↦ hs ▸ hx.sum_le_prefixSum s) ?_
  rw [prefixSum_def]
  refine sum_le_maxSubsetSum ?_
  rw [Fin.card_filter_val_lt, min_eq_right (by simpa using i.isLt.le)]

/-- On `Fin n`, the largest sum of `i` coordinates of `x` is the sum of the first `i`
coordinates of its decreasing rearrangement. -/
theorem maxSubsetSum_eq_prefixSum_sortDesc (x : Fin n → M) (i : Fin (Fintype.card (Fin n))) :
    maxSubsetSum i x = prefixSum i (x ∘ Tuple.sortDesc x) := by
  rw [← (Tuple.antitone_sortDesc x).maxSubsetSum_eq_prefixSum, maxSubsetSum_comp_perm]

end Sorted

/-! ### Majorization -/

section Majorizes

variable [AddCommMonoid M] [LinearOrder M] {a b c : ι → M}

/-- Majorization `a ≺ b`, "`a` is majorized by `b`": the totals of `a` and `b` agree, and every
largest sum of `i` coordinates of `a` is at most that of `b`. -/
structure Majorizes (a b : ι → M) : Prop where
  sum : ∑ j, a j = ∑ j, b j
  sums : ∀ i : Fin (Fintype.card ι), maxSubsetSum i a ≤ maxSubsetSum i b

/-- Weak submajorization `a ≺_w b`: the total of `a` is at most that of `b`, and every largest
sum of `i` coordinates of `a` is at most that of `b`. -/
structure WeaklyMajorizes (a b : ι → M) : Prop where
  sum_le : ∑ j, a j ≤ ∑ j, b j
  sums : ∀ i : Fin (Fintype.card ι), maxSubsetSum i a ≤ maxSubsetSum i b

/-- Unfolding `Majorizes`. -/
theorem majorizes_iff :
    Majorizes a b ↔ ∑ j, a j = ∑ j, b j ∧ ∀ i, maxSubsetSum i a ≤ maxSubsetSum i b :=
  ⟨fun h ↦ ⟨h.sum, h.sums⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Unfolding `WeaklyMajorizes`. -/
theorem weaklyMajorizes_iff :
    WeaklyMajorizes a b ↔ ∑ j, a j ≤ ∑ j, b j ∧ ∀ i, maxSubsetSum i a ≤ maxSubsetSum i b :=
  ⟨fun h ↦ ⟨h.sum_le, h.sums⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Majorization is reflexive. -/
@[refl, simp]
theorem Majorizes.refl (a : ι → M) : Majorizes a a :=
  ⟨rfl, fun _ ↦ le_rfl⟩

/-- Majorization is reflexive. -/
theorem Majorizes.rfl : Majorizes a a :=
  .refl a

/-- Majorization is transitive. -/
@[trans]
theorem Majorizes.trans (hab : Majorizes a b) (hbc : Majorizes b c) : Majorizes a c :=
  ⟨hab.sum.trans hbc.sum, fun i ↦ (hab.sums i).trans (hbc.sums i)⟩

/-- Majorization implies weak majorization. -/
theorem Majorizes.weaklyMajorizes (h : Majorizes a b) : WeaklyMajorizes a b :=
  ⟨h.sum.le, h.sums⟩

/-- Weak majorization is reflexive. -/
@[refl, simp]
theorem WeaklyMajorizes.refl (a : ι → M) : WeaklyMajorizes a a :=
  ⟨le_rfl, fun _ ↦ le_rfl⟩

/-- Weak majorization is reflexive. -/
theorem WeaklyMajorizes.rfl : WeaklyMajorizes a a :=
  .refl a

/-- Weak majorization is transitive. -/
@[trans]
theorem WeaklyMajorizes.trans (hab : WeaklyMajorizes a b) (hbc : WeaklyMajorizes b c) :
    WeaklyMajorizes a c :=
  ⟨hab.sum_le.trans hbc.sum_le, fun i ↦ (hab.sums i).trans (hbc.sums i)⟩

/-- Majorization is invariant under reindexing both vectors along an equivalence. -/
theorem majorizes_comp_equiv_iff (e : κ ≃ ι) : Majorizes (a ∘ e) (b ∘ e) ↔ Majorizes a b := by
  simp only [majorizes_iff, Function.comp_apply, e.sum_comp]
  refine and_congr_right fun _ ↦ ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩
  · simpa only [maxSubsetSum_comp_equiv] using h (Fin.cast (Fintype.card_congr e).symm i)
  · have h' := h (Fin.cast (Fintype.card_congr e) i)
    rwa [← maxSubsetSum_comp_equiv e, ← maxSubsetSum_comp_equiv e, Fin.cast_cast,
      Fin.cast_eq_self] at h'

/-- Weak majorization is invariant under reindexing both vectors along an equivalence. -/
theorem weaklyMajorizes_comp_equiv_iff (e : κ ≃ ι) :
    WeaklyMajorizes (a ∘ e) (b ∘ e) ↔ WeaklyMajorizes a b := by
  simp only [weaklyMajorizes_iff, Function.comp_apply, e.sum_comp]
  refine and_congr_right fun _ ↦ ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩
  · simpa only [maxSubsetSum_comp_equiv] using h (Fin.cast (Fintype.card_congr e).symm i)
  · have h' := h (Fin.cast (Fintype.card_congr e) i)
    rwa [← maxSubsetSum_comp_equiv e, ← maxSubsetSum_comp_equiv e, Fin.cast_cast,
      Fin.cast_eq_self] at h'

/-- Majorization is invariant under permuting the coordinates of the smaller vector. -/
@[simp]
theorem majorizes_comp_perm_left_iff (σ : Equiv.Perm ι) : Majorizes (a ∘ σ) b ↔ Majorizes a b := by
  simp only [majorizes_iff, maxSubsetSum_comp_perm, Function.comp_apply, Equiv.sum_comp σ]

/-- Majorization is invariant under permuting the coordinates of the larger vector. -/
@[simp]
theorem majorizes_comp_perm_right_iff (σ : Equiv.Perm ι) :
    Majorizes a (b ∘ σ) ↔ Majorizes a b := by
  simp only [majorizes_iff, maxSubsetSum_comp_perm, Function.comp_apply, Equiv.sum_comp σ]

/-- Weak majorization is invariant under permuting the coordinates of the smaller vector. -/
@[simp]
theorem weaklyMajorizes_comp_perm_left_iff (σ : Equiv.Perm ι) :
    WeaklyMajorizes (a ∘ σ) b ↔ WeaklyMajorizes a b := by
  simp only [weaklyMajorizes_iff, maxSubsetSum_comp_perm, Function.comp_apply, Equiv.sum_comp σ]

/-- Weak majorization is invariant under permuting the coordinates of the larger vector. -/
@[simp]
theorem weaklyMajorizes_comp_perm_right_iff (σ : Equiv.Perm ι) :
    WeaklyMajorizes a (b ∘ σ) ↔ WeaklyMajorizes a b := by
  simp only [weaklyMajorizes_iff, maxSubsetSum_comp_perm, Function.comp_apply, Equiv.sum_comp σ]

section Ordered

variable [IsOrderedAddMonoid M]

/-- Decreasing the smaller vector coordinatewise preserves weak majorization. -/
theorem WeaklyMajorizes.mono_left (hbc : WeaklyMajorizes b c) (hab : a ≤ b) :
    WeaklyMajorizes a c :=
  ⟨(sum_le_sum fun j _ ↦ hab j).trans hbc.sum_le,
    fun i ↦ (maxSubsetSum_mono i hab).trans (hbc.sums i)⟩

/-- Increasing the larger vector coordinatewise preserves weak majorization. -/
theorem WeaklyMajorizes.mono_right (hab : WeaklyMajorizes a b) (hbc : b ≤ c) :
    WeaklyMajorizes a c :=
  ⟨hab.sum_le.trans (sum_le_sum fun j _ ↦ hbc j),
    fun i ↦ (hab.sums i).trans (maxSubsetSum_mono i hbc)⟩

variable {n : ℕ}

/-- The comparison of largest subset sums is the comparison of the prefix sums of the decreasing
rearrangements of length less than `n`. -/
theorem forall_maxSubsetSum_le_iff_prefixSum (x y : Fin n → M) :
    (∀ i, maxSubsetSum i x ≤ maxSubsetSum i y) ↔
      ∀ k < n, prefixSum k (x ∘ Tuple.sortDesc x) ≤ prefixSum k (y ∘ Tuple.sortDesc y) := by
  simp only [maxSubsetSum_eq_prefixSum_sortDesc]
  refine ⟨fun h k hk ↦ h ⟨k, by simpa using hk⟩, fun h i ↦ h i (by simpa using i.isLt)⟩

/-- **Sorted form of majorization.** On `Fin n`, `x ≺ y` exactly when every prefix sum of the
decreasing rearrangement of `x` is at most that of `y`, and the totals agree. -/
theorem majorizes_iff_prefixSum (x y : Fin n → M) :
    Majorizes x y ↔
      (∀ k, prefixSum k (x ∘ Tuple.sortDesc x) ≤ prefixSum k (y ∘ Tuple.sortDesc y)) ∧
        ∑ i, x i = ∑ i, y i := by
  rw [majorizes_iff, forall_maxSubsetSum_le_iff_prefixSum, and_comm]
  refine and_congr_left fun hsum ↦ ⟨fun h k ↦ ?_, fun h k _ ↦ h k⟩
  rcases lt_or_ge k n with hk | hk
  · exact h k hk
  · rw [prefixSum_of_le hk, prefixSum_of_le hk, Tuple.sum_comp_sortDesc, Tuple.sum_comp_sortDesc,
      hsum]

/-- For antitone tuples, `x ≺_w y` exactly when every prefix sum of `x` is at most that of `y`. -/
theorem weaklyMajorizes_iff_prefixSum_of_antitone {x y : Fin n → M} (hx : Antitone x)
    (hy : Antitone y) : WeaklyMajorizes x y ↔ ∀ k, prefixSum k x ≤ prefixSum k y := by
  simp only [weaklyMajorizes_iff, hx.maxSubsetSum_eq_prefixSum, hy.maxSubsetSum_eq_prefixSum]
  refine ⟨fun h k ↦ ?_, fun h ↦ ⟨?_, fun i ↦ h i⟩⟩
  · rcases lt_or_ge k n with hk | hk
    · exact h.2 ⟨k, by simpa using hk⟩
    · simpa only [prefixSum_of_le hk] using h.1
  · simpa only [prefixSum_of_le le_rfl] using h n

/-- **Sorted form of weak majorization.** On `Fin n`, `x ≺_w y` exactly when every prefix sum
of the decreasing rearrangement of `x` is at most that of `y`. -/
theorem weaklyMajorizes_iff_prefixSum (x y : Fin n → M) :
    WeaklyMajorizes x y ↔
      ∀ k, prefixSum k (x ∘ Tuple.sortDesc x) ≤ prefixSum k (y ∘ Tuple.sortDesc y) := by
  rw [← weaklyMajorizes_iff_prefixSum_of_antitone (Tuple.antitone_sortDesc x)
    (Tuple.antitone_sortDesc y), weaklyMajorizes_comp_perm_left_iff,
    weaklyMajorizes_comp_perm_right_iff]

/-- On `Fin n`, `x ≺ y` exactly when the decreasing rearrangement of `x` is below that of `y` in
the dominance order. -/
theorem majorizes_iff_dominates (x y : Fin n → M) :
    Majorizes x y ↔ Dominates (x ∘ Tuple.sortDesc x) (y ∘ Tuple.sortDesc y) := by
  rw [majorizes_iff_prefixSum, dominates_iff_forall_prefixSum_le, Tuple.sum_comp_sortDesc,
    Tuple.sum_comp_sortDesc, and_comm, eq_comm]

end Ordered

/-- Two vectors majorize each other exactly when one is a permutation of the other. -/
theorem majorizes_antisymm_iff [IsOrderedCancelAddMonoid M] {x y : ι → M} :
    Majorizes x y ∧ Majorizes y x ↔ ∃ σ : Equiv.Perm ι, x = y ∘ σ := by
  refine ⟨fun ⟨hxy, hyx⟩ ↦ ?_, fun ⟨σ, hσ⟩ ↦ ?_⟩
  · -- Transport to `Fin n`, where the decreasing rearrangements are equal by antisymmetry of
    -- the dominance order.
    let e := (Fintype.equivFin ι).symm
    rw [← majorizes_comp_equiv_iff e, majorizes_iff_dominates] at hxy hyx
    have h := Dominates.antisymm hxy hyx
    refine ⟨e.permCongr (Tuple.sortDesc (y ∘ e) * (Tuple.sortDesc (x ∘ e))⁻¹), funext fun j ↦ ?_⟩
    have hj := congrFun h ((Tuple.sortDesc (x ∘ e))⁻¹ (e.symm j))
    simpa [Equiv.permCongr_apply, Equiv.Perm.mul_apply] using hj
  · subst hσ
    simp only [majorizes_comp_perm_left_iff, majorizes_comp_perm_right_iff, and_self,
      Majorizes.rfl]

/-- Over a linearly ordered semifield, the constant vector with the same total as `b` is
majorized by `b`. -/
theorem majorizes_const_sum_div_card {K : Type*} [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] [ExistsAddOfLE K] (b : ι → K) :
    Majorizes (fun _ ↦ (∑ j, b j) / Fintype.card ι) b := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨by simp, fun i ↦ absurd (Fintype.card_pos_iff.mp (Fin.pos i)) (not_nonempty_iff.mpr hι)⟩
  have hcard : (0 : K) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine ⟨by simp [sum_const, card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hcard.ne'], fun i ↦ ?_⟩
  obtain ⟨T, hT, hTsum⟩ := exists_sum_eq_maxSubsetSum i b
  -- Chebyshev's sum inequality for `b` and the indicator of a set attaining the largest sum.
  have hmono : Monovary b fun j ↦ if j ∈ T then (1 : K) else 0 := fun j k hjk ↦ by
    by_cases hj : j ∈ T <;> by_cases hk : k ∈ T <;> norm_num [hj, hk] at hjk
    exact le_of_sum_eq_maxSubsetSum hT hTsum hj hk
  have hcheb := hmono.sum_mul_sum_le_card_mul_sum
  simp only [mul_ite, mul_one, mul_zero, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul,
    hT] at hcheb
  refine maxSubsetSum_le_iff.mpr fun s hs ↦ ?_
  rw [sum_const, hs, nsmul_eq_mul, ← hTsum, mul_div_assoc', div_le_iff₀ hcard, mul_comm,
    mul_comm (∑ j ∈ T, b j)]
  exact hcheb

end Majorizes

end TauCeti

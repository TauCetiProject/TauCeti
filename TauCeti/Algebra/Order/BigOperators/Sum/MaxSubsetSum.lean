/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finset.Powerset
public import TauCeti.Algebra.BigOperators.Finset.PartialSum
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Data.Fintype.Fin

/-!
# Largest subset sums

For a vector `a : ι → M` on a finite index type with values in a linearly ordered additive
commutative monoid, `TauCeti.maxSubsetSum i a` is the largest sum of `a` over a subset of `ι` of
size `i`, for `i : Fin (Fintype.card ι)`. It needs no order on the index type, and no
compatibility of the order with addition. When addition preserves the order
(`IsOrderedAddMonoid M`), it is monotone and subadditive in the vector, and on `Fin n` it is the
prefix sum of length `i` of the decreasing rearrangement `x ∘ Tuple.sortDesc x`.

## Main definitions

* `TauCeti.maxSubsetSum i a`: the largest sum of `i` coordinates of `a`.

## Main results

* `TauCeti.maxSubsetSum_le_iff`, `TauCeti.sum_le_maxSubsetSum`,
  `TauCeti.exists_sum_eq_maxSubsetSum`: `maxSubsetSum i a` is the maximum of the sums of `a`
  over the subsets of size `i`.
* `TauCeti.maxSubsetSum_of_val_eq_zero`, `TauCeti.maxSubsetSum_of_val_eq_one`,
  `TauCeti.maxSubsetSum_const`: the values at sizes `0` and `1`, and on constant vectors.
* `TauCeti.maxSubsetSum_comp_equiv`, `TauCeti.maxSubsetSum_comp_perm`: invariance under
  reindexing.
* `TauCeti.maxSubsetSum_smul`: `maxSubsetSum i` is positively homogeneous.
* `TauCeti.le_of_sum_eq_maxSubsetSum`: in an ordered cancellative additive monoid, a set
  attaining `maxSubsetSum i a` contains the largest coordinates of `a`.
* `TauCeti.exists_card_eq_forall_notMem_le`: some set of `i` indices carries the `i` largest
  coordinates.
* `TauCeti.maxSubsetSum_mono`, `TauCeti.maxSubsetSum_add_le`: in an ordered additive monoid,
  `maxSubsetSum i` is monotone and subadditive.
* `TauCeti.nsmul_sum_le_card_nsmul_maxSubsetSum`: in an ordered additive monoid,
  `i • ∑ j, a j ≤ card ι • maxSubsetSum i a`.
* `Antitone.maxSubsetSum_eq_prefixSum`, `TauCeti.maxSubsetSum_eq_prefixSum_sortDesc`: in an
  ordered additive monoid, on `Fin n`, the largest sum of `i` coordinates is a prefix sum of the
  decreasing rearrangement.

## References

The definition follows the shape of Mathlib pull request #41898. The comparison of subset sums
with the prefix sums of the decreasing rearrangement
(`TauCeti.maxSubsetSum_eq_prefixSum_sortDesc`, and `Antitone.sum_le_prefixSum` in
`TauCeti.Algebra.BigOperators.Finset.PartialSum`) is adapted from `sum_le_sumInitial_of_antitone`
and `sum_le_sumLargest` in `CKMA/Analysis/Convex/Majorization.lean` of the lean-CKMA project.
-/

public section

open Finset

namespace TauCeti

variable {ι κ M : Type*} [Fintype ι] [Fintype κ]

/-- Some set of `i` indices carries the `i` largest coordinates of `a`: every coordinate outside
it is at most every coordinate inside it. -/
theorem exists_card_eq_forall_notMem_le [LinearOrder M] (i : Fin (Fintype.card ι)) (a : ι → M) :
    ∃ T : Finset ι, #T = i ∧ ∀ j ∉ T, ∀ k ∈ T, a j ≤ a k := by
  classical
  -- Take the first `i` indices of the decreasing rearrangement of `a` on `Fin (card ι)`.
  let e := Fintype.equivFin ι
  let σ := Tuple.sortDesc (a ∘ e.symm)
  refine ⟨({p | (p : ℕ) < i} : Finset (Fin (Fintype.card ι))).map (σ.trans e.symm).toEmbedding,
    ?_, ?_⟩
  · rw [card_map, Fin.card_filter_val_lt, min_eq_right i.isLt.le]
  · intro j hj k hk
    obtain ⟨p, hp, rfl⟩ := mem_map.mp hk
    have hq : ¬ ((σ.symm (e j) : Fin _) : ℕ) < i := fun hq ↦
      hj (mem_map.mpr ⟨σ.symm (e j), by simpa using hq, by simp⟩)
    have h := Tuple.antitone_sortDesc (a ∘ e.symm)
      (show p ≤ σ.symm (e j) by simp only [mem_filter, mem_univ, true_and] at hp; omega)
    simpa [σ] using h

section MaxSubsetSum

variable [AddCommMonoid M] [LinearOrder M] {i : Fin (Fintype.card ι)} {a b : ι → M}

/-- The largest sum of `i` coordinates of `a`, the maximum of `∑ j ∈ s, a j` over the subsets
`s` of size `i`. -/
def maxSubsetSum (i : Fin (Fintype.card ι)) (a : ι → M) : M :=
  (univ.powersetCard i).sup' (powersetCard_nonempty.mpr (by rw [card_univ]; exact i.isLt.le))
    fun s ↦ ∑ j ∈ s, a j

/-- The defining formula of `maxSubsetSum` as a maximum over `Finset.powersetCard`. -/
theorem maxSubsetSum_def (i : Fin (Fintype.card ι)) (a : ι → M) :
    maxSubsetSum i a =
      (univ.powersetCard i).sup' (powersetCard_nonempty.mpr (by rw [card_univ]; exact i.isLt.le))
        fun s ↦ ∑ j ∈ s, a j := by
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
  obtain ⟨s, hs, h⟩ := exists_mem_eq_sup' (s := univ.powersetCard i)
    (powersetCard_nonempty.mpr (by rw [card_univ]; exact i.isLt.le)) fun s ↦ ∑ j ∈ s, a j
  exact ⟨s, (mem_powersetCard.mp hs).2, by rw [maxSubsetSum_def, h]⟩

/-- The largest sum of no coordinates is `0`. -/
@[simp]
theorem maxSubsetSum_of_val_eq_zero (hi : (i : ℕ) = 0) : maxSubsetSum i a = 0 := by
  obtain ⟨s, hs, h⟩ := exists_sum_eq_maxSubsetSum i a
  rw [← h, card_eq_zero.mp (hs.trans hi), sum_empty]

/-- The largest sum of one coordinate of `a` is its largest coordinate. -/
theorem maxSubsetSum_of_val_eq_one (hi : (i : ℕ) = 1) :
    maxSubsetSum i a = univ.sup' (univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp i.pos)) a := by
  refine le_antisymm (maxSubsetSum_le_iff.mpr fun s hs ↦ ?_) ?_
  · obtain ⟨j, rfl⟩ := card_eq_one.mp (hs.trans hi)
    rw [sum_singleton]
    exact le_sup' a (mem_univ j)
  · obtain ⟨j, -, hj⟩ := exists_mem_eq_sup'
      (univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp i.pos)) a
    simpa [hj] using sum_le_maxSubsetSum (a := a) (s := {j}) (by simp [hi])

/-- The largest sum of `i` coordinates of a constant vector `c` is `i • c`. -/
@[simp]
theorem maxSubsetSum_const (i : Fin (Fintype.card ι)) (c : M) :
    maxSubsetSum i (fun _ ↦ c) = (i : ℕ) • c := by
  obtain ⟨s, hs, h⟩ := exists_sum_eq_maxSubsetSum i fun _ ↦ c
  rw [← h, sum_const, hs]

/-- Largest subset sums are invariant under reindexing along an equivalence `e : κ ≃ ι`; the
size `i` is transported along `Fintype.card κ = Fintype.card ι`. -/
theorem maxSubsetSum_comp_equiv (e : κ ≃ ι) (i : Fin (Fintype.card ι)) (a : ι → M) :
    maxSubsetSum (Fin.cast (Fintype.card_congr e).symm i) (a ∘ e) = maxSubsetSum i a := by
  simp only [maxSubsetSum_def, Fin.val_cast]
  conv_rhs => simp only [← map_univ_equiv e, powersetCard_map]
  rw [sup'_map]
  simp [Function.comp_def, sum_map]

/-- Largest subset sums are invariant under permuting the coordinates. -/
@[simp]
theorem maxSubsetSum_comp_perm (σ : Equiv.Perm ι) (i : Fin (Fintype.card ι)) (a : ι → M) :
    maxSubsetSum i (a ∘ σ) = maxSubsetSum i a := by
  simpa using maxSubsetSum_comp_equiv σ i a

/-- `maxSubsetSum i` is positively homogeneous. -/
theorem maxSubsetSum_smul {R : Type*} [Zero R] [Preorder R] [DistribSMul R M] [PosSMulMono R M]
    {c : R} (hc : 0 ≤ c) (i : Fin (Fintype.card ι)) (a : ι → M) :
    maxSubsetSum i (c • a) = c • maxSubsetSum i a := by
  simp only [maxSubsetSum_def, Pi.smul_apply, ← smul_sum]
  exact (apply_sup'_eq_sup'_comp _ (c • · : M → M) (smul_max_of_nonneg hc)).symm

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

/-- The largest sum of `i` coordinates is at least `i / card ι` times the total:
`i • ∑ j, a j ≤ card ι • maxSubsetSum i a`. -/
theorem nsmul_sum_le_card_nsmul_maxSubsetSum (i : Fin (Fintype.card ι)) (a : ι → M) :
    (i : ℕ) • ∑ j, a j ≤ Fintype.card ι • maxSubsetSum i a := by
  classical
  obtain ⟨T, hT, hsep⟩ := exists_card_eq_forall_notMem_le i a
  refine le_trans ?_ (nsmul_le_nsmul_right (sum_le_maxSubsetSum hT) _)
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · simp [← hT]
  -- Every coordinate in `T` is at least `m`, and every coordinate outside `T` at most `m`.
  set m := T.inf' hTne a
  have hin : (i : ℕ) • m ≤ ∑ k ∈ T, a k := hT ▸ card_nsmul_le_sum T a m fun k hk ↦ inf'_le a hk
  have hout : ∑ j ∈ Tᶜ, a j ≤ (Fintype.card ι - i) • m := by
    rw [← hT, ← card_compl]
    exact sum_le_card_nsmul Tᶜ a m fun j hj ↦ le_inf' hTne a (hsep j (mem_compl.mp hj))
  have hn : Fintype.card ι = (Fintype.card ι - i) + i := (Nat.sub_add_cancel i.isLt.le).symm
  calc (i : ℕ) • ∑ j, a j = (i : ℕ) • ∑ k ∈ T, a k + (i : ℕ) • ∑ j ∈ Tᶜ, a j := by
        rw [← sum_add_sum_compl T, nsmul_add]
    _ ≤ (i : ℕ) • ∑ k ∈ T, a k + (Fintype.card ι - i) • ((i : ℕ) • m) := by
        rw [smul_comm]
        exact add_le_add_right (nsmul_le_nsmul_right hout _) _
    _ ≤ (i : ℕ) • ∑ k ∈ T, a k + (Fintype.card ι - i) • ∑ k ∈ T, a k :=
        add_le_add_right (nsmul_le_nsmul_right hin _) _
    _ = Fintype.card ι • ∑ k ∈ T, a k := by
        rw [add_comm, ← add_nsmul, ← hn]

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

end TauCeti

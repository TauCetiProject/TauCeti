/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylDimension.Basic
import TauCeti.Data.Fin.Rev

/-!
# The Hodge–Tate numbers of a dominant `GL n` weight

A regular algebraic automorphic representation of `GL n` over a number field has, at each
embedding `τ`, a dominant weight `a_τ = (a_{τ,1} ≥ ⋯ ≥ a_{τ,n})`, possibly with repeated entries.
The Galois representation attached to it is expected to have, at `τ`, the Hodge–Tate numbers

`HT_τ(a) = {a_{τ,i} + n - i : 1 ≤ i ≤ n}`,

in the convention where the cyclotomic character has Hodge–Tate number `-1`.  This file builds
that dictionary from a single dominant weight to a multiset of integers, before any Galois
representation is attached: in `Fin n` coordinates the shifted entries are
`TauCeti.DominantWeight.hodgeShift`, `i ↦ λᵢ + (n - 1 - i)`, and the multiset of its values is
`TauCeti.DominantWeight.hodgeMultiset`.

The shift is the point.  The entries of a dominant weight may repeat, but the shifted ones never
do, so the Hodge–Tate numbers are always distinct
(`TauCeti.DominantWeight.nodup_hodgeMultiset`): a Galois representation with these Hodge–Tate
numbers is regular.  The shift is the classical `λ + ρ` up to translation, and is
`TauCeti.DominantWeight.rhoShift` translated by `n - 1`.

The multiset records more than its sum: the sum `∑ λᵢ + n(n - 1)/2` is the Hodge–Tate number of
the determinant, but different weights can share it.  A determinant twist `λ ↦ λ + m` translates
every Hodge–Tate number by `m`, and the contragredient weight reflects them,
`h ↦ n - 1 - h`.  These two rules are what makes the Hodge–Tate numbers at conjugate embeddings
of a CM field pair off to sum to `w + n - 1` for a weight in `(ℤⁿ)_w`; this sum `w + n - 1` is the
purity weight.

Finally, a weight is **extremely regular** when equal-sized subsets of its shifted entries are
determined by their sums (`TauCeti.DominantWeight.IsExtremelyRegular`).  This is stronger than the
distinctness of the entries: for `λ = 0` and `n = 4` the shifted entries `3, 2, 1, 0` already
have `3 + 0 = 2 + 1`.  Barnet-Lamb, Gee, Geraghty and Taylor use this condition in their
irreducibility results for the Galois representations attached to such weights.

## Main definitions

* `TauCeti.DominantWeight.hodgeShift`: the strictly decreasing sequence `λᵢ + (n - 1 - i)`.
* `TauCeti.DominantWeight.hodgeMultiset`: the multiset of its values, the Hodge–Tate numbers.
* `TauCeti.DominantWeight.IsExtremelyRegular`: equal-sized subsets of shifted entries with equal
  sums are equal.

## Main results

* `TauCeti.DominantWeight.nodup_hodgeMultiset`, `TauCeti.DominantWeight.card_hodgeMultiset`:
  the Hodge–Tate multiset consists of `n` distinct integers.
* `TauCeti.DominantWeight.sum_hodgeMultiset`: its sum is `∑ λᵢ + n(n - 1)/2`.
* `TauCeti.DominantWeight.hodgeMultiset_shift`, `TauCeti.DominantWeight.hodgeMultiset_dual`:
  the effect of a determinant twist and of the contragredient.
* `TauCeti.DominantWeight.hodgeMultiset_zero`: the zero weight gives `{0, 1, …, n - 1}`.
* `TauCeti.DominantWeight.isExtremelyRegular_shift_iff`: extreme regularity is invariant under
  determinant twists.

## References

* T. Barnet-Lamb, T. Gee, D. Geraghty and R. Taylor, *Potential automorphy and change of
  weight*, Ann. of Math. 179 (2014), §2.1.
-/

public section

namespace TauCeti

open Finset

namespace DominantWeight

variable {n : ℕ}

/-- The **Hodge shift** `λᵢ + (n - 1 - i)` of a dominant weight, in `Fin n` coordinates: the
classical `λ + ρ` up to translation.  Its values are the Hodge–Tate numbers attached to `λ`. -/
def hodgeShift (l : DominantWeight n) (i : Fin n) : ℤ := l.rhoShift i + ((n : ℤ) - 1)

theorem hodgeShift_apply (l : DominantWeight n) (i : Fin n) :
    l.hodgeShift i = l.val i + ((n : ℤ) - 1 - i) := by
  simp only [hodgeShift, rhoShift_apply]; ring

/-- The Hodge shift is strictly decreasing, even where the weight has repeated entries. -/
theorem hodgeShift_strictAnti (l : DominantWeight n) : StrictAnti l.hodgeShift :=
  fun _ _ h => add_lt_add_left (l.rhoShift_strictAnti h) _

theorem hodgeShift_injective (l : DominantWeight n) : Function.Injective l.hodgeShift :=
  l.hodgeShift_strictAnti.injective

/-- A determinant twist `λ ↦ λ + m·(1, …, 1)` translates the Hodge shift by `m`. -/
@[simp]
theorem hodgeShift_shift_apply (l : DominantWeight n) (m : ℤ) (i : Fin n) :
    (l.shift m).hodgeShift i = l.hodgeShift i + m := by
  simp only [hodgeShift_apply, shift_apply]; ring

/-- The contragredient weight reflects the Hodge shift: `h ↦ n - 1 - h`, with the index
reversed. -/
@[simp]
theorem hodgeShift_dual_apply (l : DominantWeight n) (i : Fin n) :
    l.dual.hodgeShift i = ((n : ℤ) - 1) - l.hodgeShift i.rev := by
  simp only [hodgeShift_apply, dual_apply, Fin.natCast_val_rev]
  ring

/-- The **Hodge–Tate multiset** `{λᵢ + n - i : 1 ≤ i ≤ n}` of a dominant weight: the multiset of
values of `TauCeti.DominantWeight.hodgeShift`. -/
def hodgeMultiset (l : DominantWeight n) : Multiset ℤ :=
  (univ : Finset (Fin n)).val.map l.hodgeShift

@[simp]
theorem mem_hodgeMultiset {l : DominantWeight n} {h : ℤ} :
    h ∈ l.hodgeMultiset ↔ ∃ i, l.hodgeShift i = h := by
  simp [hodgeMultiset]

/-- The Hodge–Tate numbers attached to a dominant weight are pairwise distinct. -/
theorem nodup_hodgeMultiset (l : DominantWeight n) : l.hodgeMultiset.Nodup :=
  univ.nodup.map l.hodgeShift_injective

@[simp]
theorem card_hodgeMultiset (l : DominantWeight n) : l.hodgeMultiset.card = n := by
  simp [hodgeMultiset]

/-- The Hodge–Tate multiset as the image of `Finset.univ`, a `Finset` of cardinality `n`. -/
theorem hodgeMultiset_eq_image_val (l : DominantWeight n) :
    l.hodgeMultiset = (univ.image l.hodgeShift).val := by
  rw [image_val_of_injOn l.hodgeShift_injective.injOn]
  rfl

/-- The Hodge–Tate multiset read along the reversed indices `Fin.rev`. -/
theorem hodgeMultiset_eq_map_rev (l : DominantWeight n) :
    l.hodgeMultiset = (univ : Finset (Fin n)).val.map (fun i => l.hodgeShift i.rev) := by
  conv_lhs => rw [hodgeMultiset, ← Multiset.map_univ_val_equiv Fin.revPerm, Multiset.map_map]
  simp only [Function.comp_def, Fin.revPerm_apply]

/-- The sum of the Hodge–Tate numbers is `∑ λᵢ + n(n - 1)/2`, the Hodge–Tate number of the
determinant.  It does not determine the multiset. -/
theorem sum_hodgeMultiset (l : DominantWeight n) :
    l.hodgeMultiset.sum = ∑ i, l.val i + (n * (n - 1) / 2 : ℕ) := by
  have hrev : ∑ i : Fin n, (((n : ℤ) - 1) - i) = ∑ i : Fin n, ((i : ℕ) : ℤ) := by
    refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
    simp only [Fin.revPerm_apply, Fin.natCast_val_rev]
  have hgauss : ∑ i : Fin n, ((i : ℕ) : ℤ) = (n * (n - 1) / 2 : ℕ) := by
    rw [← Finset.sum_range_id, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range]
  rw [hodgeMultiset, ← Finset.sum_eq_multiset_sum]
  simp only [hodgeShift_apply, Finset.sum_add_distrib, hrev, hgauss]

/-- A determinant twist `λ ↦ λ + m·(1, …, 1)` translates every Hodge–Tate number by `m`. -/
@[simp]
theorem hodgeMultiset_shift (l : DominantWeight n) (m : ℤ) :
    (l.shift m).hodgeMultiset = l.hodgeMultiset.map (· + m) := by
  simp only [hodgeMultiset, Multiset.map_map, Function.comp_def, hodgeShift_shift_apply]

/-- The contragredient weight reflects the Hodge–Tate numbers, `h ↦ n - 1 - h`. -/
@[simp]
theorem hodgeMultiset_dual (l : DominantWeight n) :
    l.dual.hodgeMultiset = l.hodgeMultiset.map (((n : ℤ) - 1) - ·) := by
  rw [l.hodgeMultiset_eq_map_rev, Multiset.map_map]
  simp [hodgeMultiset]

/-- The zero weight has Hodge–Tate numbers `{0, 1, …, n - 1}`: the Hodge–Tate numbers of the
`(n - 1)`-st symmetric power of the dual Tate module of an elliptic curve. -/
@[simp]
theorem hodgeMultiset_zero :
    (0 : DominantWeight n).hodgeMultiset = (Multiset.range n).map (↑) := by
  have h : ∀ i : Fin n, (0 : DominantWeight n).hodgeShift i.rev = ((i : ℕ) : ℤ) := fun i => by
    simp only [hodgeShift_apply, zero_apply, Fin.natCast_val_rev]
    ring
  refine ((nodup_hodgeMultiset 0).ext ((Multiset.nodup_range n).map Nat.cast_injective)).2
    fun x => ?_
  simp [hodgeMultiset_eq_map_rev, h, Fin.exists_iff]

/-- For `GL 2` the Hodge–Tate multiset of `(λ₁, λ₂)` is `{λ₁ + 1, λ₂}`; for the weight
`(k - 2, 0)` of a classical eigenform of weight `k` it is `{k - 1, 0}`. -/
theorem hodgeMultiset_fin_two (l : DominantWeight 2) :
    l.hodgeMultiset = {l.val 0 + 1, l.val 1} := by
  simp [hodgeMultiset, Fin.univ_val_map, List.ofFn_succ, hodgeShift_apply, ← Multiset.cons_coe]

/-- A dominant weight is **extremely regular** when equal-sized sets of its shifted entries
`λᵢ + (n - 1 - i)` are determined by their sums.  Since the shifted entries are distinct, this
says that two distinct sets of `k` Hodge–Tate numbers never have the same sum. -/
def IsExtremelyRegular (l : DominantWeight n) : Prop :=
  ∀ ⦃S T : Finset (Fin n)⦄, S.card = T.card →
    ∑ i ∈ S, l.hodgeShift i = ∑ i ∈ T, l.hodgeShift i → S = T

theorem isExtremelyRegular_iff (l : DominantWeight n) :
    l.IsExtremelyRegular ↔ ∀ S T : Finset (Fin n), S.card = T.card →
      ∑ i ∈ S, l.hodgeShift i = ∑ i ∈ T, l.hodgeShift i → S = T :=
  Iff.rfl

/-- Extreme regularity is invariant under determinant twists. -/
@[simp]
theorem isExtremelyRegular_shift_iff (l : DominantWeight n) (m : ℤ) :
    (l.shift m).IsExtremelyRegular ↔ l.IsExtremelyRegular := by
  refine forall₂_congr fun S T => forall_congr' fun hST => ?_
  simp only [hodgeShift_shift_apply, Finset.sum_add_distrib, Finset.sum_const, hST, add_left_inj]

/-- In rank one every dominant weight is extremely regular. -/
theorem isExtremelyRegular_of_subsingleton [Subsingleton (Fin n)] (l : DominantWeight n) :
    l.IsExtremelyRegular :=
  fun S T hST _ => Finset.eq_of_subset_of_card_le (fun i hi => by
    obtain ⟨j, hj⟩ := Finset.card_pos.1 (hST ▸ Finset.card_pos.2 ⟨i, hi⟩)
    exact Subsingleton.elim j i ▸ hj) hST.symm.le

end DominantWeight

end TauCeti

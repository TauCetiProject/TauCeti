/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import TauCeti.Algebra.Order.BigOperators.Dominance
public import TauCeti.Algebra.Order.BigOperators.Sum.MaxSubsetSum
import Mathlib.Algebra.Order.Field.Basic

/-!
# Majorization and weak majorization of vectors

For vectors `a b : ι → M` on a finite index type with values in a linearly ordered additive
commutative monoid, `a` is *majorized* by `b` (`a ≺ b`, `TauCeti.Majorizes a b`) when the two
have the same total and every largest subset sum `TauCeti.maxSubsetSum i a` is at most the one
of `b` of the same size; `a` is *weakly submajorized* by `b` (`a ≺_w b`,
`TauCeti.WeaklyMajorizes a b`) when the same holds with the total of `a` at most that of `b`.
The largest subset sums are in `TauCeti.Algebra.Order.BigOperators.Sum.MaxSubsetSum`.

These definitions need no order on the index type and no compatibility of the order with
addition; majorization is then a preorder and invariant under permuting either vector. When
addition preserves the order (`IsOrderedAddMonoid M`), weak majorization is monotone in both
vectors, and on `Fin n` majorization is the classical comparison of the prefix sums of the
decreasing rearrangements `x ∘ Tuple.sortDesc x`, which is the dominance order
`TauCeti.Dominates` between them; for antitone tuples no rearrangement is needed. In an ordered
cancellative additive monoid, two vectors majorize each other exactly when one is a permutation
of the other. Over a linearly ordered semifield, the constant vector with the same total is
majorized by every vector.

## Main definitions

* `TauCeti.Majorizes a b`: majorization `a ≺ b`.
* `TauCeti.WeaklyMajorizes a b`: weak submajorization `a ≺_w b`.

## Main results

* `TauCeti.Majorizes.refl`, `TauCeti.Majorizes.trans`, `TauCeti.Majorizes.weaklyMajorizes`, and
  the same for `TauCeti.WeaklyMajorizes`: the preorder structure.
* `TauCeti.majorizes_comp_equiv_iff`, `TauCeti.majorizes_comp_perm_left_iff`,
  `TauCeti.majorizes_comp_perm_right_iff`, and the same for `TauCeti.WeaklyMajorizes`:
  invariance under reindexing and under permuting either vector.
* `TauCeti.WeaklyMajorizes.mono_left`, `TauCeti.WeaklyMajorizes.mono_right`: in an ordered
  additive monoid, weak majorization is antitone in the smaller and monotone in the larger
  vector.
* `TauCeti.majorizes_iff_prefixSum`, `TauCeti.weaklyMajorizes_iff_prefixSum`,
  `TauCeti.majorizes_iff_dominates`: in an ordered additive monoid, the sorted forms of
  majorization and weak majorization on `Fin n`;
  `TauCeti.majorizes_iff_prefixSum_of_antitone`,
  `TauCeti.weaklyMajorizes_iff_prefixSum_of_antitone`: the same for antitone tuples, without
  rearranging.
* `TauCeti.majorizes_antisymm_iff`: in an ordered cancellative additive monoid, `a ≺ b` and
  `b ≺ a` exactly when `a` is a permutation of `b`.
* `TauCeti.majorizes_const_sum_div_card`: over a linearly ordered semifield, the constant vector
  with the total of `b` is majorized by `b`.

## References

* A. W. Marshall, I. Olkin, B. C. Arnold, *Inequalities: Theory of Majorization and Its
  Applications*, 2nd ed., Springer (2011), 1.A.1 (p. 8) and 1.A.2 (p. 12).

The definitions follow the shape of Mathlib pull request #41898.
-/

public section

open Finset

namespace TauCeti

variable {ι κ M : Type*} [Fintype ι] [Fintype κ]

/-! ### Majorization -/

section Majorizes

variable [AddCommMonoid M] [LinearOrder M] {a b c : ι → M}

/-- Majorization `a ≺ b`, "`a` is majorized by `b`": the totals of `a` and `b` agree, and every
largest sum of `i` coordinates of `a` is at most that of `b`. -/
structure Majorizes (a b : ι → M) : Prop where
  sum : ∑ j, a j = ∑ j, b j
  sums : ∀ i : Fin (Fintype.card ι), maxSubsetSum i a ≤ maxSubsetSum i b

attribute [grind →] Majorizes.sum

/-- Weak submajorization `a ≺_w b`: the total of `a` is at most that of `b`, and every largest
sum of `i` coordinates of `a` is at most that of `b`. -/
structure WeaklyMajorizes (a b : ι → M) : Prop where
  sum_le : ∑ j, a j ≤ ∑ j, b j
  sums : ∀ i : Fin (Fintype.card ι), maxSubsetSum i a ≤ maxSubsetSum i b

attribute [grind →] WeaklyMajorizes.sum_le

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

/-- Weak majorization is transitive. -/
@[trans]
theorem WeaklyMajorizes.trans (hab : WeaklyMajorizes a b) (hbc : WeaklyMajorizes b c) :
    WeaklyMajorizes a c :=
  ⟨hab.sum_le.trans hbc.sum_le, fun i ↦ (hab.sums i).trans (hbc.sums i)⟩

/-- Majorization is invariant under reindexing both vectors along an equivalence. -/
theorem majorizes_comp_equiv_iff (e : κ ≃ ι) : Majorizes (a ∘ e) (b ∘ e) ↔ Majorizes a b := by
  simp only [majorizes_iff, Function.comp_apply, e.sum_comp]
  refine and_congr_right fun _ ↦ (finCongr (Fintype.card_congr e)).forall_congr' fun i ↦ ?_
  simp only [finCongr_symm, finCongr_apply, maxSubsetSum_comp_equiv]

/-- Weak majorization is invariant under reindexing both vectors along an equivalence. -/
theorem weaklyMajorizes_comp_equiv_iff (e : κ ≃ ι) :
    WeaklyMajorizes (a ∘ e) (b ∘ e) ↔ WeaklyMajorizes a b := by
  simp only [weaklyMajorizes_iff, Function.comp_apply, e.sum_comp]
  refine and_congr_right fun _ ↦ (finCongr (Fintype.card_congr e)).forall_congr' fun i ↦ ?_
  simp only [finCongr_symm, finCongr_apply, maxSubsetSum_comp_equiv]

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
  · simp only [prefixSum_of_le hk, Function.comp_apply, Equiv.sum_comp, hsum, le_rfl]

/-- For antitone tuples, `x ≺_w y` exactly when every prefix sum of `x` is at most that of `y`. -/
theorem weaklyMajorizes_iff_prefixSum_of_antitone {x y : Fin n → M} (hx : Antitone x)
    (hy : Antitone y) : WeaklyMajorizes x y ↔ ∀ k, prefixSum k x ≤ prefixSum k y := by
  simp only [weaklyMajorizes_iff, hx.maxSubsetSum_eq_prefixSum, hy.maxSubsetSum_eq_prefixSum]
  refine ⟨fun h k ↦ ?_, fun h ↦ ⟨?_, fun i ↦ h i⟩⟩
  · rcases lt_or_ge k n with hk | hk
    · exact h.2 ⟨k, by simpa using hk⟩
    · simpa only [prefixSum_of_le hk] using h.1
  · simpa only [prefixSum_of_le le_rfl] using h n

/-- For antitone tuples, `x ≺ y` exactly when every prefix sum of `x` is at most that of `y`,
and the totals agree. -/
theorem majorizes_iff_prefixSum_of_antitone {x y : Fin n → M} (hx : Antitone x)
    (hy : Antitone y) :
    Majorizes x y ↔ (∀ k, prefixSum k x ≤ prefixSum k y) ∧ ∑ i, x i = ∑ i, y i := by
  rw [majorizes_iff, and_comm]
  refine and_congr_left fun hsum ↦ ?_
  rw [← weaklyMajorizes_iff_prefixSum_of_antitone hx hy, weaklyMajorizes_iff,
    and_iff_right hsum.le]

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
  simp only [majorizes_iff_prefixSum, dominates_iff_forall_prefixSum_le, Function.comp_apply,
    Equiv.sum_comp, and_comm, eq_comm]

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
      Majorizes.refl]

/-- Over a linearly ordered semifield, the constant vector with the same total as `b` is
majorized by `b`. -/
theorem majorizes_const_sum_div_card {K : Type*} [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] (b : ι → K) :
    Majorizes (fun _ ↦ (∑ j, b j) / Fintype.card ι) b := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨by simp, fun i ↦ absurd (Fintype.card_pos_iff.mp (Fin.pos i)) (not_nonempty_iff.mpr hι)⟩
  have hcard : (0 : K) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine ⟨by simp [sum_const, card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hcard.ne'], fun i ↦ ?_⟩
  have h := nsmul_sum_le_card_nsmul_maxSubsetSum i b
  rw [nsmul_eq_mul, nsmul_eq_mul] at h
  rw [maxSubsetSum_const, nsmul_eq_mul, mul_div_assoc', div_le_iff₀ hcard,
    mul_comm (maxSubsetSum i b)]
  exact h

end Majorizes

end TauCeti

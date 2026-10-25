/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Absolute
import TauCeti.NumberTheory.Height.FiniteOrder

/-!
# Boundary cases and field embeddings for Northcott sets

The algebraic elements satisfying a fixed rational-degree bound and absolute-height bound
form a Northcott set. Height bounds below one give the empty set. When both bounds are one,
the set consists of minus one, zero, and one. Taking the preimage under a homomorphism of
characteristic-zero fields preserves these sets, without choosing a complex embedding.
-/

public section
open NumberField Height
namespace TauCeti

/-- A Northcott set is empty if its absolute-height bound is below one. -/
theorem setOf_absMulHeight₁_le_eq_empty_of_lt_one (F : Type*) [Field F] [CharZero F]
    (d : ℕ) {B : ℝ} (hB : B < 1) :
    {x : F | IsAlgebraic ℚ x ∧
      (minpoly ℚ x).natDegree ≤ d ∧ absMulHeight₁ x ≤ B} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (hB.trans_le (one_le_absMulHeight₁ x)).not_ge hx.2.2

private theorem rat_height_one_iff (q : ℚ) :
    mulHeight₁ q ≤ 1 ↔ q = -1 ∨ q = 0 ∨ q = 1 := by
  rw [Rat.mulHeight₁_eq_max, Nat.cast_max, max_le_iff]
  constructor
  · rintro ⟨hnum, hden⟩
    have hn : q.num.natAbs ≤ 1 := by exact_mod_cast hnum
    have hd : q.den ≤ 1 := by exact_mod_cast hden
    have hdeq : q.den = 1 := by have := q.pos; omega
    have hq : q = (q.num : ℚ) := by simpa [hdeq] using (Rat.num_div_den q).symm
    have hnumBounds : -1 ≤ q.num ∧ q.num ≤ 1 := by omega
    obtain h | h | h : q.num = -1 ∨ q.num = 0 ∨ q.num = 1 := by omega
    · left; simpa [h] using hq
    · right; left; simpa [h] using hq
    · right; right; simpa [h] using hq
  · rintro (rfl | rfl | rfl) <;> norm_num

/-- In every characteristic-zero field, the algebraic elements of degree and absolute height
at most one are exactly minus one, zero, and one. -/
theorem setOf_degree_le_one_absMulHeight₁_le_one (F : Type*) [Field F] [CharZero F] :
    {x : F | IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ 1 ∧ absMulHeight₁ x ≤ 1} =
      {-1, 0, 1} := by
  ext x
  constructor
  · rintro ⟨hx, hd, hH⟩
    have heq : (minpoly ℚ x).natDegree = 1 := by
      have := minpoly.natDegree_pos hx.isIntegral
      omega
    obtain ⟨q, rfl⟩ := minpoly.natDegree_eq_one_iff.mp heq
    have hq : mulHeight₁ q ≤ 1 := by
      simpa only [eq_ratCast, absMulHeight₁_ratCast] using hH
    rcases (rat_height_one_iff q).mp hq with rfl | rfl | rfl <;> simp
  · have hmem (q : ℚ) (hq : mulHeight₁ q ≤ 1) :
        IsAlgebraic ℚ (algebraMap ℚ F q) ∧
          (minpoly ℚ (algebraMap ℚ F q)).natDegree ≤ 1 ∧
          absMulHeight₁ (algebraMap ℚ F q) ≤ 1 := by
      refine ⟨isIntegral_algebraMap.isAlgebraic, ?_, ?_⟩
      · exact (minpoly.natDegree_eq_one_iff.mpr ⟨q, rfl⟩).le
      · simpa only [eq_ratCast, absMulHeight₁_ratCast] using hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl)
    · simpa using hmem (-1) ((rat_height_one_iff _).mpr (Or.inl rfl))
    · simpa using hmem 0 ((rat_height_one_iff _).mpr (Or.inr (Or.inl rfl)))
    · simpa using hmem 1 ((rat_height_one_iff _).mpr (Or.inr (Or.inr rfl)))

/-- Algebraicity, rational degree, and absolute height are preserved by a field embedding.
Thus a Northcott set pulls back to the Northcott set with the same bounds. -/
theorem preimage_setOf_absMulHeight₁_le {F E : Type*}
    [Field F] [CharZero F] [Field E] [CharZero E]
    (f : F →+* E) (d : ℕ) (B : ℝ) :
    f ⁻¹' {x : E | IsAlgebraic ℚ x ∧
      (minpoly ℚ x).natDegree ≤ d ∧ absMulHeight₁ x ≤ B} =
      {x : F | IsAlgebraic ℚ x ∧
        (minpoly ℚ x).natDegree ≤ d ∧ absMulHeight₁ x ≤ B} := by
  ext x
  change (IsAlgebraic ℚ (f x) ∧ _ ∧ _) ↔
    (IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ d ∧ absMulHeight₁ x ≤ B)
  have hi : IsIntegral ℚ (f x) ↔ IsIntegral ℚ x :=
    isIntegral_algHom_iff f.toRatAlgHom f.injective
  have hm : minpoly ℚ (f x) = minpoly ℚ x :=
    minpoly.algHom_eq f.toRatAlgHom f.injective x
  rw [isAlgebraic_iff_isIntegral, isAlgebraic_iff_isIntegral, hi, hm, absMulHeight₁_map]


end TauCeti

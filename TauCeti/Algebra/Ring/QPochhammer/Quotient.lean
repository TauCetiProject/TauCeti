/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.QPochhammer.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Regular quotients of q-Pochhammer products

The coefficient of a bilateral basic hypergeometric series uses two lists of parameters
`A` and `B`. At a nonnegative index it is the product of the shifted factorials of `A`
divided by the corresponding product for `B`. At a negative index the lists exchange roles,
and both sets of parameters are shifted by the same power of the base.

`List.qPochhammerRatio` takes a proof that the denominator on the appropriate half-line is
a unit. In particular a parameter `q` in `B` can terminate the negative tail even though
the individual shifted factorial `(q; q)_{-1}` has a pole. The adjacent-coefficient law
`List.qPochhammerRatio_add_one_mul` also applies at a terminating factor.

## References

* George Gasper, *Lecture notes for an introductory minicourse on q-series* (1995),
  equations (2.1.8) and (3.1.13).
-/

public section

open TauCeti

namespace List

variable {R : Type*} [CommRing R]

/-- The finite numerator after moving negative-index products across the fraction bar. -/
private def ratioNumerator (A B : List R) (q : Rˣ) (j : ℤ) : R :=
  if 0 ≤ j then (A.map fun a ↦ qPochhammer a q.val j.toNat).prod
  else (B.map fun b ↦ qPochhammer (b * (q ^ j).val) q.val (-j).toNat).prod

private theorem ratioNumerator_natCast (A B : List R) (q : Rˣ) (n : ℕ) :
    ratioNumerator A B q n = (A.map fun a ↦ qPochhammer a q.val n).prod := by
  simp [ratioNumerator]

private theorem ratioNumerator_neg_natCast (A B : List R) (q : Rˣ) (n : ℕ) :
    ratioNumerator A B q (-n) =
      (B.map fun b ↦ qPochhammer (b * (q ^ (-(n : ℤ))).val) q.val n).prod := by
  cases n with
  | zero => simp [ratioNumerator]
  | succ n => rw [ratioNumerator, ite_eq_right (by omega), neg_neg, Int.toNat_natCast]

/-- Indices at which the regular quotient with numerator parameters `A` and denominator
parameters `B` is defined. Only the denominator of the finite product ratio must be a unit. -/
def qPochhammerRatioDomain (A B : List R) (q : Rˣ) : Set ℤ :=
  {j | IsUnit (ratioNumerator B A q j)}

variable {A B : List R} {q : Rˣ}

/-- An index is admissible exactly when its denominator is a unit. The denominator uses `B`
at nonnegative indices and the shifted parameters of `A` at negative indices. -/
theorem mem_qPochhammerRatioDomain_iff {j : ℤ} :
    j ∈ A.qPochhammerRatioDomain B q ↔
      if 0 ≤ j then IsUnit ((B.map fun b ↦ qPochhammer b q.val j.toNat).prod)
      else IsUnit ((A.map fun a ↦ qPochhammer (a * (q ^ j).val) q.val (-j).toNat).prod) := by
  simp only [qPochhammerRatioDomain, Set.mem_ofPred_eq, ratioNumerator, apply_ite IsUnit]

/-- At a natural index only the shifted factorials of `B` occur in the denominator. -/
theorem natCast_mem_qPochhammerRatioDomain_iff (n : ℕ) :
    (n : ℤ) ∈ A.qPochhammerRatioDomain B q ↔
      IsUnit ((B.map fun b ↦ qPochhammer b q.val n).prod) := by
  simp only [qPochhammerRatioDomain, Set.mem_ofPred_eq, ratioNumerator_natCast]

/-- At `-n` only the shifted factorials of `A`, starting at exponent `-n`, occur in the
denominator. -/
theorem neg_natCast_mem_qPochhammerRatioDomain_iff (n : ℕ) :
    -(n : ℤ) ∈ A.qPochhammerRatioDomain B q ↔
      IsUnit ((A.map fun a ↦ qPochhammer (a * (q ^ (-(n : ℤ))).val) q.val n).prod) := by
  simp only [qPochhammerRatioDomain, Set.mem_ofPred_eq, ratioNumerator_neg_natCast]

/-- The index zero is admissible for all parameter lists. -/
@[simp] theorem zero_mem_qPochhammerRatioDomain : 0 ∈ A.qPochhammerRatioDomain B q := by
  simpa using (natCast_mem_qPochhammerRatioDomain_iff (A := A) (B := B) (q := q) 0).2 (by simp)

/-- The regular quotient of two lists of q-shifted factorials at an admissible integer index. -/
noncomputable def qPochhammerRatio (A B : List R) (q : Rˣ) (j : ℤ)
    (h : j ∈ A.qPochhammerRatioDomain B q) : R :=
  ratioNumerator A B q j * ↑((h : IsUnit (ratioNumerator B A q j)).unit⁻¹)

private theorem ratio_eq_mul_inverse {j : ℤ} (h : j ∈ A.qPochhammerRatioDomain B q) :
    A.qPochhammerRatio B q j h =
      ratioNumerator A B q j * Ring.inverse (ratioNumerator B A q j) := by
  have hu : IsUnit (ratioNumerator B A q j) := h
  rw [qPochhammerRatio, ← Ring.inverse_unit, hu.unit_spec]

/-- At a nonnegative integer index the regular quotient uses the finite products for `A` and `B`. -/
theorem qPochhammerRatio_of_nonneg {j : ℤ} (hj : 0 ≤ j) (h : j ∈ A.qPochhammerRatioDomain B q) :
    A.qPochhammerRatio B q j h =
      (A.map fun a ↦ qPochhammer a q.val j.toNat).prod *
        Ring.inverse ((B.map fun b ↦ qPochhammer b q.val j.toNat).prod) := by
  simp only [ratio_eq_mul_inverse, ratioNumerator, ite_eq_left hj]

/-- At a negative integer index the regular quotient exchanges the parameter lists and shifts
each parameter by `q ^ j`. -/
theorem qPochhammerRatio_of_neg {j : ℤ} (hj : j < 0) (h : j ∈ A.qPochhammerRatioDomain B q) :
    A.qPochhammerRatio B q j h =
      (B.map fun b ↦ qPochhammer (b * (q ^ j).val) q.val (-j).toNat).prod *
        Ring.inverse ((A.map fun a ↦ qPochhammer (a * (q ^ j).val) q.val (-j).toNat).prod) := by
  simp only [ratio_eq_mul_inverse, ratioNumerator, ite_eq_right hj.not_ge]

/-- The regular quotient at `n ≥ 0` is the ordinary finite product ratio. -/
@[simp] theorem qPochhammerRatio_natCast (n : ℕ) (h : (n : ℤ) ∈ A.qPochhammerRatioDomain B q) :
    A.qPochhammerRatio B q n h =
      (A.map fun a ↦ qPochhammer a q.val n).prod *
        Ring.inverse ((B.map fun b ↦ qPochhammer b q.val n).prod) := by
  simp only [ratio_eq_mul_inverse, ratioNumerator_natCast]

/-- At a numeral index the regular quotient is the ratio of the two finite products. -/
@[simp low] theorem qPochhammerRatio_ofNat (n : ℕ)
    (h : (ofNat(n) : ℤ) ∈ A.qPochhammerRatioDomain B q) :
    A.qPochhammerRatio B q ofNat(n) h =
      (A.map fun a ↦ qPochhammer a q.val ofNat(n)).prod *
        Ring.inverse ((B.map fun b ↦ qPochhammer b q.val ofNat(n)).prod) :=
  qPochhammerRatio_natCast n h

/-- At `-n` the parameters in `B` move into the numerator. Their factors may vanish. -/
theorem qPochhammerRatio_neg_natCast (n : ℕ) (h : -(n : ℤ) ∈ A.qPochhammerRatioDomain B q) :
    A.qPochhammerRatio B q (-n) h =
      (B.map fun b ↦ qPochhammer (b * (q ^ (-(n : ℤ))).val) q.val n).prod *
        Ring.inverse ((A.map fun a ↦ qPochhammer (a * (q ^ (-(n : ℤ))).val) q.val n).prod) := by
  simp only [ratio_eq_mul_inverse, ratioNumerator_neg_natCast]

/-- The constant coefficient of the regular quotient is one. -/
@[simp] theorem qPochhammerRatio_zero (h : 0 ∈ A.qPochhammerRatioDomain B q) :
    A.qPochhammerRatio B q 0 h = 1 := by
  simp

private theorem ratio_mul_denominator {j : ℤ} (h : j ∈ A.qPochhammerRatioDomain B q) :
    A.qPochhammerRatio B q j h * ratioNumerator B A q j = ratioNumerator A B q j := by
  rw [ratio_eq_mul_inverse, Ring.inverse_mul_cancel_right _ _ h]

/-- At a nonnegative index, multiplying the regular quotient by the product for `B` gives the
product for `A`. -/
theorem qPochhammerRatio_mul_prod_of_nonneg {j : ℤ} (hj : 0 ≤ j)
    (h : j ∈ A.qPochhammerRatioDomain B q) :
    A.qPochhammerRatio B q j h * (B.map fun b ↦ qPochhammer b q.val j.toNat).prod =
      (A.map fun a ↦ qPochhammer a q.val j.toNat).prod := by
  simpa only [ratioNumerator, ite_eq_left hj] using ratio_mul_denominator h

/-- At a negative index, multiplying the regular quotient by the shifted product for `A` gives the
shifted product for `B`. -/
theorem qPochhammerRatio_mul_prod_of_neg {j : ℤ} (hj : j < 0)
    (h : j ∈ A.qPochhammerRatioDomain B q) :
    A.qPochhammerRatio B q j h *
        (A.map fun a ↦ qPochhammer (a * (q ^ j).val) q.val (-j).toNat).prod =
      (B.map fun b ↦ qPochhammer (b * (q ^ j).val) q.val (-j).toNat).prod := by
  simpa only [ratioNumerator, ite_eq_right hj.not_ge] using ratio_mul_denominator h

private theorem ratioNumerator_add_one_of_nonneg {j : ℤ} (hj : 0 ≤ j) (A B : List R) (q : Rˣ) :
    ratioNumerator A B q (j + 1) =
      ratioNumerator A B q j * (A.map fun a ↦ 1 - a * (q ^ j).val).prod := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  rw [← Nat.cast_succ, ratioNumerator_natCast, ratioNumerator_natCast]
  simp [qPochhammer_succ]

private theorem ratioNumerator_add_one_of_neg {j : ℤ} (hj : j < 0) (A B : List R) (q : Rˣ) :
    ratioNumerator A B q j =
      (B.map fun b ↦ 1 - b * (q ^ j).val).prod * ratioNumerator A B q (j + 1) := by
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat (by omega : j + 1 ≤ 0)
  have hjn : j = -((n + 1 : ℕ) : ℤ) := by omega
  rw [hn, ratioNumerator_neg_natCast, hjn, ratioNumerator_neg_natCast]
  have hshift : q ^ (-((n + 1 : ℕ) : ℤ)) * q = q ^ (-(n : ℤ)) := by
    rw [← zpow_add_one]
    congr 1
    omega
  simp only [qPochhammer_succ', mul_assoc, ← Units.val_mul, hshift, prod_map_mul]

/-- The adjacent coefficients satisfy the cross-multiplied ratio law on their common domain,
including at zeros of numerator factors. -/
theorem qPochhammerRatio_add_one_mul {j : ℤ} (h : j ∈ A.qPochhammerRatioDomain B q)
    (h' : j + 1 ∈ A.qPochhammerRatioDomain B q) :
    A.qPochhammerRatio B q (j + 1) h' * (B.map fun b ↦ 1 - b * (q ^ j).val).prod =
      A.qPochhammerRatio B q j h * (A.map fun a ↦ 1 - a * (q ^ j).val).prod := by
  have h₀ := ratio_mul_denominator h
  have h₁ := ratio_mul_denominator h'
  rcases le_or_gt 0 j with hj | hj
  · apply (h : IsUnit (ratioNumerator B A q j)).mul_left_inj.mp
    rw [ratioNumerator_add_one_of_nonneg hj B A, ratioNumerator_add_one_of_nonneg hj A B] at h₁
    linear_combination h₁ - (A.map fun a ↦ 1 - a * (q ^ j).val).prod * h₀
  · apply (h' : IsUnit (ratioNumerator B A q (j + 1))).mul_left_inj.mp
    rw [ratioNumerator_add_one_of_neg hj B A, ratioNumerator_add_one_of_neg hj A B] at h₀
    linear_combination (B.map fun b ↦ 1 - b * (q ^ j).val).prod * h₁ - h₀

/-- For one parameter on each side the coefficient at `-1` is `(q - b) / (q - a)`. -/
theorem qPochhammerRatio_singleton_neg_one (a b : R)
    (h : (-1 : ℤ) ∈ [a].qPochhammerRatioDomain [b] q) :
    [a].qPochhammerRatio [b] q (-1) h = (q.val - b) * Ring.inverse (q.val - a) := by
  have hfactor (x : R) : 1 - x * q⁻¹.val = (q.val - x) * q⁻¹.val := by
    rw [sub_mul, q.mul_inv]
  simpa [hfactor, Ring.mul_inverse_rev, Ring.inverse_unit, mul_assoc] using
    qPochhammerRatio_neg_natCast 1 h

private theorem prod_qPochhammerInt_neg_natCast (C : List R) (n : ℕ)
    (h : ∀ c ∈ C, -(n : ℤ) ∈ qPochhammerIntDomain c q) :
    (C.attach.map fun c ↦ qPochhammerInt c.val q (-n) (h c.val c.property)).prod =
      Ring.inverse ((C.map fun c ↦ qPochhammer (c * (q ^ (-(n : ℤ))).val) q.val n).prod) := by
  rw [← MonoidWithZero.inverse_apply, map_list_prod]
  simp [List.map_map, Function.comp_def, qPochhammerInt_neg_natCast]

private theorem isUnit_prod_shifted_iff (C : List R) (n : ℕ) :
    IsUnit ((C.map fun c ↦ qPochhammer (c * (q ^ (-(n : ℤ))).val) q.val n).prod) ↔
      ∀ c ∈ C, -(n : ℤ) ∈ qPochhammerIntDomain c q := by
  simp [prod_isUnit_iff, neg_natCast_mem_qPochhammerIntDomain_iff]

/-- When the integer-indexed products for `B` exist, the regular quotient is defined exactly
when those for `A` exist and the product for `B` is a unit. -/
theorem mem_qPochhammerRatioDomain_iff_forall_mem_and_isUnit {j : ℤ}
    (hB : ∀ b ∈ B, j ∈ qPochhammerIntDomain b q) :
    j ∈ A.qPochhammerRatioDomain B q ↔
      (∀ a ∈ A, j ∈ qPochhammerIntDomain a q) ∧
        IsUnit ((B.attach.map fun b ↦ qPochhammerInt b.val q j (hB b.val b.property)).prod) := by
  rcases le_or_gt 0 j with hj | hj
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    simp [natCast_mem_qPochhammerRatioDomain_iff]
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hj.le
    rw [neg_natCast_mem_qPochhammerRatioDomain_iff, prod_qPochhammerInt_neg_natCast,
      isUnit_ringInverse, isUnit_prod_shifted_iff, isUnit_prod_shifted_iff]
    exact (and_iff_left hB).symm

/-- On the common domain the regular coefficient agrees with the quotient of the
integer-indexed q-Pochhammer products. -/
theorem qPochhammerRatio_eq_prod_qPochhammerInt_mul_ringInverse {j : ℤ}
    (h : j ∈ A.qPochhammerRatioDomain B q)
    (hB : ∀ b ∈ B, j ∈ qPochhammerIntDomain b q) :
    A.qPochhammerRatio B q j h =
      (A.attach.map fun a ↦ qPochhammerInt a.val q j
        (((mem_qPochhammerRatioDomain_iff_forall_mem_and_isUnit hB).mp h).1 _ a.property)).prod *
        Ring.inverse
          ((B.attach.map fun b ↦ qPochhammerInt b.val q j (hB b.val b.property)).prod) := by
  rcases le_or_gt 0 j with hj | hj
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    simp
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hj.le
    rw [qPochhammerRatio_neg_natCast, prod_qPochhammerInt_neg_natCast,
      prod_qPochhammerInt_neg_natCast, Ring.inverse_inverse ((isUnit_prod_shifted_iff B n).2 hB),
      mul_comm]

/-- A denominator parameter `q^k` with `1 ≤ k ≤ n` makes the regular coefficient at `-n` vanish. -/
theorem qPochhammerRatio_neg_natCast_eq_zero_of_pow_mem {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (hB : q.val ^ k ∈ B) (h : -(n : ℤ) ∈ A.qPochhammerRatioDomain B q) :
    A.qPochhammerRatio B q (-n) h = 0 := by
  rw [qPochhammerRatio_neg_natCast]
  apply mul_eq_zero_of_left
  apply prod_eq_zero
  refine mem_map.mpr ⟨_, hB, qPochhammer_eq_zero_of_mul_pow_eq_one (i := n - k) (by omega) ?_⟩
  have hexp : (k : ℤ) + -n + (n - k : ℕ) = 0 := by omega
  simpa [zpow_add] using congrArg (fun i : ℤ ↦ (q ^ i).val) hexp

end List

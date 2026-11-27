/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Monovary
public import TauCeti.Algebra.BigOperators.Finset.WeightedVariance
public import TauCeti.Algebra.Order.Ring.Basic
public import TauCeti.Logic.Function.Basic

/-!
# Weighted Chebyshev inequalities

For nonnegative weights, similarly ordered vectors in an ordered commutative semiring
satisfy the weighted Chebyshev inequality. Oppositely ordered vectors satisfy the reverse
inequality. With positive weights, equality holds exactly when one vector is constant.
Both finite-set forms allow arbitrary total weight; normalized whole-type forms are
provided through the `Monovary` and `Antivary` dot-notation APIs.

The proofs compare the two subtraction-free weighted double sums. In particular, the
results apply to natural numbers and nonnegative real numbers as well as ordered rings.

## References

Hardy, Littlewood and Pólya, *Inequalities*, Theorem 43;
Bullen, *Handbook of Means and Their Inequalities*, Chapter II, §5.3, Theorem 4.
-/

public section

open Finset
variable {ι R : Type*} [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
  [ExistsAddOfLE R]

private theorem monovary_pair_le {s : Finset ι} {a b : ι → R}
    (hab : MonovaryOn a b s) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    a i * b j + a j * b i ≤ a i * b i + a j * b j := by
  rcases lt_trichotomy (a i) (a j) with h | h | h
  · exact mul_add_mul_le_mul_add_mul h.le (hab.symm hi hj h)
  · simp [h, add_comm]
  · simpa only [add_comm] using mul_add_mul_le_mul_add_mul h.le (hab.symm hj hi h)

private theorem antivary_pair_le {s : Finset ι} {a b : ι → R}
    (hab : AntivaryOn a b s) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    a i * b i + a j * b j ≤ a i * b j + a j * b i := by
  rcases lt_trichotomy (a i) (a j) with h | h | h
  · exact mul_add_mul_le_mul_add_mul h.le (hab.symm hi hj h)
  · simp [h, add_comm]
  · simpa only [add_comm] using mul_add_mul_le_mul_add_mul h.le (hab.symm hj hi h)

private theorem weighted_pair_eq_iff {s : Finset ι} {w a b : ι → R}
    (hw : ∀ i ∈ s, 0 < w i)
    (hpair : (∀ i ∈ s, ∀ j ∈ s, a i * b j + a j * b i ≤ a i * b i + a j * b j) ∨
      (∀ i ∈ s, ∀ j ∈ s, a i * b i + a j * b j ≤ a i * b j + a j * b i)) :
    (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) =
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) ↔
      (∀ i ∈ s, ∀ j ∈ s, a i = a j) ∨ (∀ i ∈ s, ∀ j ∈ s, b i = b j) := by
  constructor
  · intro heq
    have hs : (∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i * b j + a j * b i)) =
        ∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i * b i + a j * b j) := by
      rw [sum_sum_weight_mul_cross, sum_sum_weight_mul_diagonal, heq]
    have hterm (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
        a i * b j + a j * b i = a i * b i + a j * b j := by
      apply mul_left_cancel₀ (mul_pos (hw i hi) (hw j hj)).ne'
      rcases hpair with hp | hp
      · have hle i hi j hj := mul_le_mul_of_nonneg_left (hp i hi j hj)
          (mul_pos (hw i hi) (hw j hj)).le
        exact (sum_eq_sum_iff_of_le (hle i hi)).mp
          ((sum_eq_sum_iff_of_le fun i hi ↦ sum_le_sum (hle i hi)).mp hs i hi) j hj
      · have hle i hi j hj := mul_le_mul_of_nonneg_left (hp i hi j hj)
          (mul_pos (hw i hi) (hw j hj)).le
        exact ((sum_eq_sum_iff_of_le (hle i hi)).mp
          ((sum_eq_sum_iff_of_le fun i hi ↦ sum_le_sum (hle i hi)).mp hs.symm i hi) j hj).symm
    have hp := Function.forall_eq_or_forall_eq_of_forall_eq_or_eq
      (a := fun i : {i // i ∈ s} ↦ a i) (b := fun i : {i // i ∈ s} ↦ b i)
      (fun i j ↦ TauCeti.mul_add_mul_eq_mul_add_mul_iff.mp (hterm i i.property j j.property))
    rcases hp with ha | hb
    · exact Or.inl fun i hi j hj ↦ ha ⟨i, hi⟩ ⟨j, hj⟩
    · exact Or.inr fun i hi j hj ↦ hb ⟨i, hi⟩ ⟨j, hj⟩
  · intro hconst
    apply (mul_left_cancel₀ (two_ne_zero : (2 : R) ≠ 0))
    rw [← sum_sum_weight_mul_cross, ← sum_sum_weight_mul_diagonal]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    congr 1
    exact TauCeti.mul_add_mul_eq_mul_add_mul_iff.mpr
      (hconst.elim (fun ha ↦ Or.inl (ha i hi j hj)) (fun hb ↦ Or.inr (hb i hi j hj)))

/-- Weighted Chebyshev inequality on a finite set, with arbitrary nonnegative total weight. -/
theorem MonovaryOn.sum_mul_sum_le_sum_mul_sum {s : Finset ι} {w a b : ι → R}
    (hab : MonovaryOn a b s) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) := by
  have h := sum_le_sum (s := s) fun i hi ↦ sum_le_sum (s := s) fun j hj ↦
    mul_le_mul_of_nonneg_left (monovary_pair_le hab hi hj) (mul_nonneg (hw i hi) (hw j hj))
  rw [sum_sum_weight_mul_cross, sum_sum_weight_mul_diagonal] at h
  exact (mul_le_mul_iff_right₀ (zero_lt_two : (0 : R) < 2)).mp h

/-- Equality in finite weighted Chebyshev with positive weights characterizes constant vectors. -/
theorem MonovaryOn.sum_mul_sum_eq_sum_mul_sum_iff {s : Finset ι} {w a b : ι → R}
    (hab : MonovaryOn a b s) (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) =
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) ↔
      (∀ i ∈ s, ∀ j ∈ s, a i = a j) ∨ (∀ i ∈ s, ∀ j ∈ s, b i = b j) :=
  weighted_pair_eq_iff hw (Or.inl fun _ hi _ hj ↦ monovary_pair_le hab hi hj)

/-- Reversed weighted Chebyshev inequality on a finite set, without normalized weights. -/
theorem AntivaryOn.sum_mul_sum_le_sum_mul_sum {s : Finset ι} {w a b : ι → R}
    (hab : AntivaryOn a b s) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) ≤
      (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) := by
  have h := sum_le_sum (s := s) fun i hi ↦ sum_le_sum (s := s) fun j hj ↦
    mul_le_mul_of_nonneg_left (antivary_pair_le hab hi hj) (mul_nonneg (hw i hi) (hw j hj))
  rw [sum_sum_weight_mul_diagonal, sum_sum_weight_mul_cross] at h
  exact (mul_le_mul_iff_right₀ (zero_lt_two : (0 : R) < 2)).mp h

/-- Equality in the reversed finite weighted inequality with positive weights. -/
theorem AntivaryOn.sum_mul_sum_eq_sum_mul_sum_iff {s : Finset ι} {w a b : ι → R}
    (hab : AntivaryOn a b s) (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) =
      (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) ↔
      (∀ i ∈ s, ∀ j ∈ s, a i = a j) ∨ (∀ i ∈ s, ∀ j ∈ s, b i = b j) :=
  eq_comm.trans (weighted_pair_eq_iff hw (Or.inr fun _ hi _ hj ↦ antivary_pair_le hab hi hj))

variable [Fintype ι]

/-- Chebyshev's inequality for nonnegative weights of total mass one. -/
theorem Monovary.sum_mul_sum_le_sum_mul {w a b : ι → R} (hab : Monovary a b)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    (∑ i, w i * a i) * (∑ i, w i * b i) ≤ ∑ i, w i * (a i * b i) := by
  simpa only [hw1, one_mul, mul_assoc] using
    (hab.monovaryOn (↑(univ : Finset ι))).sum_mul_sum_le_sum_mul_sum (fun i _ ↦ hw i)

/-- The reversed weighted Chebyshev inequality for oppositely ordered vectors. -/
theorem Antivary.sum_mul_le_sum_mul_sum {w a b : ι → R} (hab : Antivary a b)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    (∑ i, w i * (a i * b i)) ≤ (∑ i, w i * a i) * (∑ i, w i * b i) := by
  simpa only [hw1, one_mul, mul_assoc] using
    (hab.antivaryOn (↑(univ : Finset ι))).sum_mul_sum_le_sum_mul_sum (fun i _ ↦ hw i)

/-- Equality in normalized weighted Chebyshev with positive weights. -/
theorem Monovary.sum_mul_sum_eq_sum_mul_iff {w a b : ι → R} (hab : Monovary a b)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) :
    (∑ i, w i * a i) * (∑ i, w i * b i) = (∑ i, w i * (a i * b i)) ↔
      (∀ i j, a i = a j) ∨ (∀ i j, b i = b j) := by
  simpa only [hw1, one_mul, mul_assoc, mem_univ, forall_true_left] using
    (hab.monovaryOn (↑(univ : Finset ι))).sum_mul_sum_eq_sum_mul_sum_iff (fun i _ ↦ hw i)

/-- Equality in the reversed weighted Chebyshev inequality for positive normalized weights. -/
theorem Antivary.sum_mul_eq_sum_mul_sum_iff {w a b : ι → R} (hab : Antivary a b)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) :
    (∑ i, w i * (a i * b i)) = (∑ i, w i * a i) * (∑ i, w i * b i) ↔
      (∀ i j, a i = a j) ∨ (∀ i j, b i = b j) := by
  simpa only [hw1, one_mul, mul_assoc, mem_univ, forall_true_left] using
    (hab.antivaryOn (↑(univ : Finset ι))).sum_mul_sum_eq_sum_mul_sum_iff (fun i _ ↦ hw i)

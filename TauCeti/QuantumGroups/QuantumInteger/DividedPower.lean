/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.QuantumGroups.QuantumInteger.Factorial

import Mathlib.Tactic.FieldSimp
import TauCeti.Algebra.Group.Action.Semiconj

/-!
# Quantum divided powers in associative algebras

For an element `x` of an associative `K`-algebra over a field and `q : K`, this file defines the
`n`-th quantum divided power `x^(n) = [n]_q!⁻¹ • x^n` and the length-`m` `q`-Serre element
`quantumSerre q m x y = ∑_{r = 0}^m (-1)^r • (x^(r) * y * x^(m - r))`, proving the divided-power
`q`-binomial theorem (`quantumDividedPower_add`), unconditional left `q`-commuting pullout
(`quantumSerre_mul_left`), and coproduct stability (`quantumSerre_add`, `quantumSerre_add_eq_zero`).

## References

* G. Lusztig, *Introduction to Quantum Groups*, Birkhäuser, 1993, §1.3 and §3.1.
* J. C. Jantzen, *Lectures on Quantum Groups*, American Mathematical Society, 1996, Chapter 4.
-/

public section

open Finset
open scoped TensorProduct

namespace TauCeti

section Semiring

variable {K A : Type*} [Field K] [Semiring A] [Algebra K A]

/-- The `n`-th **quantum divided power** `x^(n) = [n]_q!⁻¹ • x^n` in an associative `K`-algebra. -/
noncomputable def quantumDividedPower (q : K) (x : A) (n : ℕ) : A :=
  (quantumFactorial q n)⁻¹ • x ^ n
theorem quantumDividedPower_def (q : K) (x : A) (n : ℕ) :
    quantumDividedPower q x n = (quantumFactorial q n)⁻¹ • x ^ n := (rfl)
@[simp] theorem quantumDividedPower_zero (q : K) (x : A) : quantumDividedPower q x 0 = 1 := by
  simp [quantumDividedPower_def]
@[simp] theorem quantumDividedPower_one {q : K} (hq : q - q⁻¹ ≠ 0) (x : A) :
    quantumDividedPower q x 1 = x := by simp [quantumDividedPower_def, quantumInteger_one hq]
@[simp] theorem quantumDividedPower_eval_zero (q : K) {n : ℕ} (hn : n ≠ 0) :
    quantumDividedPower q (0 : A) n = 0 := by simp [quantumDividedPower_def, hn]
@[simp] theorem quantumDividedPower_eq_zero_of_sub_inv_eq_zero {q : K} (hq : q - q⁻¹ = 0) {n : ℕ}
    (hn : n ≠ 0) (x : A) : quantumDividedPower q x n = 0 := by
  simp [quantumDividedPower_def,
    not_ne_iff.mp fun h => sub_inv_ne_zero_of_quantumFactorial_ne_zero hn h hq]
@[simp] theorem quantumDividedPower_inv (q : K) (x : A) (n : ℕ) :
    quantumDividedPower q⁻¹ x n = quantumDividedPower q x n := by simp [quantumDividedPower_def]
theorem quantumFactorial_smul_quantumDividedPower {q : K} (x : A) {n : ℕ}
    (hn : quantumFactorial q n ≠ 0) :
    quantumFactorial q n • quantumDividedPower q x n = x ^ n := by
  rw [quantumDividedPower_def, smul_smul, mul_inv_cancel₀ hn, one_smul]
theorem quantumDividedPower_smul (q : K) (c : K) (x : A) (n : ℕ) :
    quantumDividedPower q (c • x) n = c ^ n • quantumDividedPower q x n := by
  rw [quantumDividedPower_def, quantumDividedPower_def, smul_pow, smul_comm]
@[simp] theorem map_quantumDividedPower {B F : Type*} [Semiring B] [Algebra K B]
    [FunLike F A B] [AlgHomClass F K A B] (φ : F) (q : K) (x : A) (n : ℕ) :
    φ (quantumDividedPower q x n) = quantumDividedPower q (φ x) n := by
  rw [quantumDividedPower_def, quantumDividedPower_def, map_smul, map_pow]
theorem quantumDividedPower_mul_quantumDividedPower {q : K} (x : A) {m n : ℕ}
    (hmn : quantumFactorial q (m + n) ≠ 0) :
    quantumDividedPower q x m * quantumDividedPower q x n =
      quantumBinomial q (m + n) m • quantumDividedPower q x (m + n) := by
  rw [quantumDividedPower_def, quantumDividedPower_def, quantumDividedPower_def,
    smul_mul_smul_comm, ← pow_add, quantumBinomial_eq_div hmn (Nat.le_add_right m n),
    Nat.add_sub_cancel_left, smul_smul]
  have hm := quantumFactorial_ne_zero_of_le (Nat.le_add_right m n) hmn
  have hn := quantumFactorial_ne_zero_of_le (Nat.le_add_left n m) hmn
  congr 1; field_simp
/-- **Divided-power `q`-binomial theorem**: if `y * x = q² • (x * y)` and `[n]_q! ≠ 0`, then
`(x + y)^(n) = ∑_{k = 0}^n q^(k(n - k)) • (x^(k) * y^(n - k))`. -/
theorem quantumDividedPower_add {q : K} {x y : A} (h : y * x = q ^ 2 • (x * y)) {n : ℕ}
    (hn : quantumFactorial q n ≠ 0) :
    quantumDividedPower q (x + y) n = ∑ k ∈ range (n + 1),
      q ^ (k * (n - k)) • (quantumDividedPower q x k * quantumDividedPower q y (n - k)) :=
  inv_quantumFactorial_smul_add_pow h hn
theorem mul_quantumDividedPower_of_mul_eq_smul_mul (q : K) {u x : A} {c : K}
    (h : u * x = c • (x * u)) (n : ℕ) :
    u * quantumDividedPower q x n = c ^ n • (quantumDividedPower q x n * u) := by
  have hsc : SemiconjBy u x (c • x) := by rw [SemiconjBy, smul_mul_assoc, h]
  rw [quantumDividedPower_def, mul_smul_comm, (hsc.pow_right n).eq, smul_pow, smul_mul_assoc,
    smul_comm, smul_mul_assoc]
theorem quantumDividedPower_mul_of_mul_eq_smul_mul (q : K) {u x : A} {c : K}
    (h : x * u = c • (u * x)) (n : ℕ) :
    quantumDividedPower q x n * u = c ^ n • (u * quantumDividedPower q x n) := by
  have hsc : SemiconjBy u (c • x) x := by rw [SemiconjBy, mul_smul_comm, h]
  rw [quantumDividedPower_def, smul_mul_assoc, ← (hsc.pow_right n).eq, smul_pow, mul_smul_comm,
    smul_comm, mul_smul_comm]
@[simp] theorem quantumDividedPower_op (q : K) (x : A) (n : ℕ) :
    quantumDividedPower q (MulOpposite.op x) n = MulOpposite.op (quantumDividedPower q x n) := by
  rw [quantumDividedPower_def, quantumDividedPower_def, ← MulOpposite.op_pow, MulOpposite.op_smul]
theorem quantumDividedPower_mul_left_of_mul_eq_smul_mul (q : K) {u x : A} {c : K}
    (h : x * u = c • (u * x)) (n : ℕ) :
    quantumDividedPower q (u * x) n = c ^ n.choose 2 • (u ^ n * quantumDividedPower q x n) := by
  rw [quantumDividedPower_def, quantumDividedPower_def, mul_pow_of_mul_eq_smul_mul h,
    smul_comm, mul_smul_comm]
theorem quantumDividedPower_mul_left_of_mul_eq_sq_smul_mul (q : K) {u x : A} {c : K}
    (h : x * u = c ^ 2 • (u * x)) (n : ℕ) :
    quantumDividedPower q (u * x) n =
      c ^ (n * (n - 1)) • (u ^ n * quantumDividedPower q x n) := by
  rw [quantumDividedPower_def, quantumDividedPower_def, mul_pow_of_mul_eq_sq_smul_mul h,
    smul_comm, mul_smul_comm]
theorem quantumDividedPower_tmul_left {B : Type*} [Semiring B] [Algebra K B] (q : K) (a : A)
    (b : B) (n : ℕ) :
    quantumDividedPower q (a ⊗ₜ[K] b) n = quantumDividedPower q a n ⊗ₜ[K] (b ^ n) := by
  rw [quantumDividedPower_def, quantumDividedPower_def, Algebra.TensorProduct.tmul_pow,
    TensorProduct.smul_tmul']
theorem quantumDividedPower_tmul_right {B : Type*} [Semiring B] [Algebra K B] (q : K) (a : A)
    (b : B) (n : ℕ) :
    quantumDividedPower q (a ⊗ₜ[K] b) n = (a ^ n) ⊗ₜ[K] quantumDividedPower q b n := by
  rw [quantumDividedPower_def, quantumDividedPower_def, Algebra.TensorProduct.tmul_pow,
    TensorProduct.tmul_smul]

end Semiring

section Ring

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

theorem quantumDividedPower_neg (q : K) (x : A) (n : ℕ) :
    quantumDividedPower q (-x) n = (-1 : K) ^ n • quantumDividedPower q x n := by
  simpa only [neg_one_smul] using quantumDividedPower_smul q (-1 : K) x n

/-- The **`q`-Serre element** `∑_{r = 0}^m (-1)^r • (x^(r) * y * x^(m - r))` built from quantum
divided powers in an associative `K`-algebra. -/
noncomputable def quantumSerre (q : K) (m : ℕ) (x y : A) : A :=
  ∑ r ∈ range (m + 1),
    (-1 : K) ^ r • (quantumDividedPower q x r * y * quantumDividedPower q x (m - r))
theorem quantumSerre_def (q : K) (m : ℕ) (x y : A) :
    quantumSerre q m x y = ∑ r ∈ range (m + 1),
      (-1 : K) ^ r • (quantumDividedPower q x r * y * quantumDividedPower q x (m - r)) := (rfl)
@[simp] theorem quantumSerre_zero (q : K) (x y : A) : quantumSerre q 0 x y = y := by
  simp [quantumSerre_def]
@[simp] theorem quantumSerre_inv (q : K) (m : ℕ) (x y : A) :
    quantumSerre q⁻¹ m x y = quantumSerre q m x y := by simp [quantumSerre_def]
@[simp] theorem map_quantumSerre {B F : Type*} [Ring B] [Algebra K B]
    [FunLike F A B] [AlgHomClass F K A B] (φ : F) (q : K) (m : ℕ) (x y : A) :
    φ (quantumSerre q m x y) = quantumSerre q m (φ x) (φ y) := by simp [quantumSerre_def]
theorem quantumSerre_one {q : K} (hq : q - q⁻¹ ≠ 0) (x y : A) :
    quantumSerre q 1 x y = y * x - x * y := by
  rw [quantumSerre_def, sum_range_succ, sum_range_one]
  simp [quantumDividedPower_one hq, sub_eq_add_neg]
theorem quantumSerre_add_right (q : K) (m : ℕ) (x y₁ y₂ : A) :
    quantumSerre q m x (y₁ + y₂) = quantumSerre q m x y₁ + quantumSerre q m x y₂ := by
  simp [quantumSerre_def, mul_add, add_mul, smul_add, sum_add_distrib]
theorem quantumSerre_smul (q : K) (m : ℕ) (c d : K) (x y : A) :
    quantumSerre q m (c • x) (d • y) = (c ^ m * d) • quantumSerre q m x y := by
  rw [quantumSerre_def, quantumSerre_def, smul_sum]; refine sum_congr rfl fun r hr => ?_
  have hrm : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
  simp only [quantumDividedPower_smul, smul_mul_assoc, mul_smul_comm, smul_smul]; congr 1
  have hc : c ^ r * c ^ (m - r) = c ^ m := by rw [← pow_add, Nat.add_sub_of_le hrm]
  linear_combination (-1 : K) ^ r * d * hc
@[simp] theorem quantumSerre_zero_left (q : K) {m : ℕ} (hm : m ≠ 0) (y : A) :
    quantumSerre q m 0 y = 0 := by
  rw [quantumSerre_def]
  exact sum_eq_zero fun r _ => if hr : r = 0 then by subst hr; simp [hm] else by simp [hr]
@[simp] theorem quantumSerre_zero_right (q : K) (m : ℕ) (x : A) :
    quantumSerre q m x 0 = 0 := by simp [quantumSerre_def]
@[simp] theorem quantumSerre_eq_zero_of_sub_inv_eq_zero {q : K} (hq : q - q⁻¹ = 0) {m : ℕ}
    (hm : m ≠ 0) (x y : A) : quantumSerre q m x y = 0 := by
  rw [quantumSerre_def]
  exact sum_eq_zero fun r _ => if hr : r = 0 then by subst hr; simp [hq, hm] else by simp [hq, hr]
theorem quantumSerre_op (q : K) (m : ℕ) (x y : A) :
    quantumSerre q m (MulOpposite.op x) (MulOpposite.op y) =
      MulOpposite.op ((-1 : K) ^ m • quantumSerre q m x y) := by
  rw [quantumSerre_def, quantumSerre_def, ← sum_range_reflect, smul_sum, op_sum]
  refine sum_congr rfl fun r hr => ?_
  have hrm : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
  simp only [Nat.add_sub_cancel, quantumDividedPower_op, ← MulOpposite.op_mul,
    ← MulOpposite.op_smul, mul_assoc, smul_smul, Nat.sub_sub_self hrm]
  congr 2; nth_rw 2 [← Nat.sub_add_cancel hrm]
  rw [pow_add, mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, mul_one]
theorem quantumSerre_tmul_left {B : Type*} [Ring B] [Algebra K B] (q : K) (m : ℕ)
    {x₁ x₂ : A} {k₁ k₂ : B} (hk : Commute k₁ k₂) :
    quantumSerre q m (x₁ ⊗ₜ[K] k₁) (x₂ ⊗ₜ[K] k₂) =
      quantumSerre q m x₁ x₂ ⊗ₜ[K] (k₁ ^ m * k₂) := by
  rw [quantumSerre_def, quantumSerre_def, TensorProduct.sum_tmul]
  refine sum_congr rfl fun r hr => ?_
  have hrm : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
  rw [quantumDividedPower_tmul_left, quantumDividedPower_tmul_left,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_assoc (k₁ ^ r),
    (hk.symm.pow_right (m - r)).eq, ← mul_assoc (k₁ ^ r), ← pow_add, Nat.add_sub_of_le hrm,
    ← TensorProduct.smul_tmul']
theorem quantumSerre_tmul_right {B : Type*} [Ring B] [Algebra K B] (q : K) (m : ℕ)
    {k₁ k₂ : A} {x₁ x₂ : B} (hk : Commute k₁ k₂) :
    quantumSerre q m (k₁ ⊗ₜ[K] x₁) (k₂ ⊗ₜ[K] x₂) =
      (k₁ ^ m * k₂) ⊗ₜ[K] quantumSerre q m x₁ x₂ := by
  rw [quantumSerre_def, quantumSerre_def, TensorProduct.tmul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hrm : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
  rw [quantumDividedPower_tmul_right, quantumDividedPower_tmul_right,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_assoc,
    (hk.symm.pow_right (m - r)).eq, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hrm,
    TensorProduct.tmul_smul]
/-- Multiplying `(x₁, x₂)` on the left by commuting elements `(u₁, u₂)` satisfying the Serre-degree
`q`-commutation relations pulls `u₁^m * u₂` out of `quantumSerre q m` on the left. -/
theorem quantumSerre_mul_left {q : K} (m : ℕ) {u₁ x₁ u₂ x₂ : A}
    (hx₁u₁ : x₁ * u₁ = q ^ 2 • (u₁ * x₁)) (hx₁u₂ : x₁ * u₂ = q ^ (1 - (m : ℤ)) • (u₂ * x₁))
    (hx₂u₁ : x₂ * u₁ = q ^ (1 - (m : ℤ)) • (u₁ * x₂)) (hu : Commute u₁ u₂) :
    quantumSerre q m (u₁ * x₁) (u₂ * x₂) = u₁ ^ m * u₂ * quantumSerre q m x₁ x₂ := by
  rcases eq_or_ne q 0 with rfl | hq; · rcases m with _ | m <;> simp
  have hpow {u x : A} {c : K} (h : x * u = c • (u * x)) (k : ℕ) :
      x * u ^ k = c ^ k • (u ^ k * x) := by
    have hsc : SemiconjBy x u (c • u) := by rw [SemiconjBy, smul_mul_assoc, h]
    rw [(hsc.pow_right k).eq, smul_pow, smul_mul_assoc]
  rw [quantumSerre_def, quantumSerre_def, mul_sum]; refine sum_congr rfl fun r hr => ?_
  have hrm : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
  rw [quantumDividedPower_mul_left_of_mul_eq_sq_smul_mul q hx₁u₁ r,
    quantumDividedPower_mul_left_of_mul_eq_sq_smul_mul q hx₁u₁ (m - r)]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  rw [← mul_assoc (quantumDividedPower q x₁ r) u₂,
    quantumDividedPower_mul_of_mul_eq_smul_mul q hx₁u₂ r, ← mul_assoc x₂ (u₁ ^ (m - r)),
    hpow hx₂u₁ (m - r)]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  rw [← mul_assoc (quantumDividedPower q x₁ r) (u₁ ^ (m - r)),
    quantumDividedPower_mul_of_mul_eq_smul_mul q (hpow hx₁u₁ (m - r)) r]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc]
  rw [mul_assoc (u₁ ^ r) u₂, (hu.symm.pow_right (m - r)).eq, ← mul_assoc (u₁ ^ r), ← pow_add,
    Nat.add_sub_of_le hrm]
  simp only [mul_assoc]; congr 1
  have hpred (n : ℕ) : (n : ℤ) * ((n - 1 : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by cases n <;> simp
  have hexp : q ^ ((m - r) * (m - r - 1)) * (q ^ (r * (r - 1)) * ((q ^ (1 - (m : ℤ))) ^ (m - r) *
      ((q ^ (1 - (m : ℤ))) ^ r * ((q ^ 2) ^ (m - r)) ^ r))) = 1 := by
    simp only [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq, Nat.cast_mul]
    rw [hpred r, hpred (m - r), Nat.cast_sub hrm]
    exact (congrArg (q ^ ·) (by push_cast; ring)).trans (zpow_zero q)
  rw [hexp, mul_one]

private theorem quantumSerre_add_left_inner {q : K} (hq : q ≠ 0) {m : ℕ}
    (hfac : quantumFactorial q m ≠ 0) {x₁ x₂ y : A}
    (hx : x₂ * x₁ = q ^ 2 • (x₁ * x₂)) (hxy : x₂ * y = q ^ (1 - (m : ℤ)) • (y * x₂))
    (a c : ℕ) (hac : a + c ≤ m) :
    (∑ u ∈ range (m - a - c + 1),
      (-1 : K) ^ (a + u) • ((q ^ (a * (a + u - a)) •
        (quantumDividedPower q x₁ a * quantumDividedPower q x₂ (a + u - a))) * y *
        (q ^ (c * (m - (a + u) - c)) •
          (quantumDividedPower q x₁ c * quantumDividedPower q x₂ (m - (a + u) - c))))) =
    if m - a - c = 0 then
      (-1 : K) ^ a • (quantumDividedPower q x₁ a * y * quantumDividedPower q x₁ c)
    else 0 := by
  set n := m - a - c
  have hterm : ∀ u ∈ range (n + 1),
      (-1 : K) ^ (a + u) • ((q ^ (a * (a + u - a)) •
        (quantumDividedPower q x₁ a * quantumDividedPower q x₂ (a + u - a))) * y *
        (q ^ (c * (m - (a + u) - c)) •
          (quantumDividedPower q x₁ c * quantumDividedPower q x₂ (m - (a + u) - c)))) =
      ((-1 : K) ^ a * q ^ (c * n) *
        ((-1 : K) ^ u * q ^ (-((u : ℤ) * ((n : ℤ) - 1))) * quantumBinomial q n u)) •
        ((quantumDividedPower q x₁ a * y * quantumDividedPower q x₁ c) *
          quantumDividedPower q x₂ n) := fun u hu => by
    have hun : u ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hu)
    have hsub : m - (a + u) - c = n - u := by omega
    have hcomm : quantumDividedPower q x₂ u * quantumDividedPower q x₁ c =
        q ^ (2 * c * u) • (quantumDividedPower q x₁ c * quantumDividedPower q x₂ u) := by
      simpa only [← pow_mul] using quantumDividedPower_mul_of_mul_eq_smul_mul q
        (mul_quantumDividedPower_of_mul_eq_smul_mul q hx c) u
    have hfn : quantumFactorial q (u + (n - u)) ≠ 0 :=
      (Nat.add_sub_of_le hun).symm ▸ quantumFactorial_ne_zero_of_le (by omega) hfac
    simp only [Nat.add_sub_cancel_left, hsub, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    rw [← mul_assoc (quantumDividedPower q x₂ u) y,
      quantumDividedPower_mul_of_mul_eq_smul_mul q hxy u]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    rw [← mul_assoc (quantumDividedPower q x₂ u), hcomm]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    rw [quantumDividedPower_mul_quantumDividedPower x₂ hfn, Nat.add_sub_of_le hun]
    simp only [mul_smul_comm, smul_smul, mul_assoc]; congr 1
    have hqexp : q ^ (c * (n - u)) * (q ^ (a * u) * ((q ^ (1 - (m : ℤ))) ^ u *
        (q ^ (2 * c * u) * 1))) = q ^ (c * n) * q ^ (-((u : ℤ) * ((n : ℤ) - 1))) := by
      have hn_cast : (n : ℤ) = (m : ℤ) - a - c := by omega
      simp only [mul_one, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq, Nat.cast_mul,
        Nat.cast_sub hun, hn_cast]
      exact congrArg (q ^ ·) (by ring)
    rw [pow_add]
    linear_combination ((-1 : K) ^ a * (-1 : K) ^ u * quantumBinomial q n u) * hqexp
  rw [sum_congr rfl hterm, ← sum_smul, ← mul_sum,
    sum_neg_one_pow_mul_zpow_neg_mul_quantumBinomial hq n]
  split_ifs with hn <;> simp [hn, mul_assoc]

private theorem quantumSerre_add_left {q : K} (hq : q ≠ 0) {m : ℕ}
    (hfac : quantumFactorial q m ≠ 0) {x₁ x₂ y : A}
    (hx : x₂ * x₁ = q ^ 2 • (x₁ * x₂)) (hxy : x₂ * y = q ^ (1 - (m : ℤ)) • (y * x₂)) :
    quantumSerre q m (x₁ + x₂) y = quantumSerre q m x₁ y := by
  have expand : quantumSerre q m (x₁ + x₂) y = ∑ r ∈ range (m + 1), ∑ a ∈ range (r + 1),
      ∑ c ∈ range (m - r + 1), (-1 : K) ^ r • ((q ^ (a * (r - a)) •
        (quantumDividedPower q x₁ a * quantumDividedPower q x₂ (r - a))) * y *
        (q ^ (c * (m - r - c)) •
          (quantumDividedPower q x₁ c * quantumDividedPower q x₂ (m - r - c)))) := by
    rw [quantumSerre_def]; refine sum_congr rfl fun r hr => ?_
    have hrm : r ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hr)
    rw [quantumDividedPower_add hx (quantumFactorial_ne_zero_of_le hrm hfac),
      quantumDividedPower_add hx (quantumFactorial_ne_zero_of_le (Nat.sub_le m r) hfac),
      sum_mul, sum_mul, smul_sum]
    exact sum_congr rfl fun _ _ => by rw [mul_sum, smul_sum]
  have hreindex (F : ℕ → ℕ → ℕ → A) :
      (∑ r ∈ range (m + 1), ∑ a ∈ range (r + 1), ∑ c ∈ range (m - r + 1), F r a c) =
      ∑ a ∈ range (m + 1), ∑ c ∈ range (m - a + 1), ∑ u ∈ range (m - a - c + 1),
        F (a + u) a c := by
    simp only [sum_sigma']
    refine sum_nbij' (fun x => ⟨x.2.1, ⟨x.2.2, x.1 - x.2.1⟩⟩)
      (fun y => ⟨y.1 + y.2.2, ⟨y.1, y.2.1⟩⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨r, ⟨a, c⟩⟩ hx; simp only [mem_sigma, mem_range] at hx ⊢; omega
    · rintro ⟨a, ⟨c, u⟩⟩ hy; simp only [mem_sigma, mem_range] at hy ⊢; omega
    · rintro ⟨r, ⟨a, c⟩⟩ hx; simp only [mem_sigma, mem_range] at hx
      exact Sigma.ext (by dsimp; omega) (heq_of_eq rfl)
    · rintro ⟨a, ⟨c, u⟩⟩ _
      exact Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Nat.add_sub_cancel_left a u))))
    · rintro ⟨r, ⟨a, c⟩⟩ hx; simp only [mem_sigma, mem_range] at hx ⊢
      exact congrArg (F · a c) (by omega)
  rw [expand, hreindex, quantumSerre_def]; refine sum_congr rfl fun a ha => ?_
  have ham : a ≤ m := Nat.lt_succ_iff.mp (mem_range.mp ha)
  rw [sum_range_succ, sum_eq_zero (fun c hc => by
    have hne : m - a - c ≠ 0 := by have := mem_range.mp hc; omega
    rw [quantumSerre_add_left_inner hq hfac hx hxy a c (by omega)]; simp [hne]),
    zero_add, quantumSerre_add_left_inner hq hfac hx hxy a (m - a) (by omega)]
  simp

/-- **Additivity of the quantum Serre expression** on `q`-commuting summands when `[m]_q! ≠ 0`. -/
theorem quantumSerre_add {q : K} {m : ℕ} (hfac : quantumFactorial q m ≠ 0)
    {x₁ x₂ y₁ y₂ : A} (hx : x₂ * x₁ = q ^ 2 • (x₁ * x₂))
    (hx₂y₁ : x₂ * y₁ = q ^ (1 - (m : ℤ)) • (y₁ * x₂))
    (hy₂x₁ : y₂ * x₁ = q ^ (1 - (m : ℤ)) • (x₁ * y₂)) :
    quantumSerre q m (x₁ + x₂) (y₁ + y₂) = quantumSerre q m x₁ y₁ + quantumSerre q m x₂ y₂ := by
  rcases eq_or_ne m 0 with rfl | hm; · simp
  have hq : q ≠ 0 :=
    ne_zero_of_sub_inv_ne_zero (sub_inv_ne_zero_of_quantumFactorial_ne_zero hm hfac)
  have hop : quantumSerre q m (MulOpposite.op x₂ + MulOpposite.op x₁) (MulOpposite.op y₂) =
      quantumSerre q m (MulOpposite.op x₂) (MulOpposite.op y₂) :=
    quantumSerre_add_left hq hfac
      (by rw [← MulOpposite.op_mul, hx, MulOpposite.op_smul, MulOpposite.op_mul])
      (by rw [← MulOpposite.op_mul, hy₂x₁, MulOpposite.op_smul, MulOpposite.op_mul])
  rw [← MulOpposite.op_add, add_comm x₂ x₁, quantumSerre_op (A := A),
    quantumSerre_op (A := A)] at hop
  have hsign : ∀ z : A, (-1 : K) ^ m • ((-1 : K) ^ m • z) = z := fun z => by
    rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  have hright : quantumSerre q m (x₁ + x₂) y₂ = quantumSerre q m x₂ y₂ := by
    simpa only [hsign] using congrArg ((-1 : K) ^ m • ·) (MulOpposite.op_injective hop)
  rw [quantumSerre_add_right, quantumSerre_add_left hq hfac hx hx₂y₁, hright]

/-- **Coproduct stability of the quantum Serre relation** on `q`-commuting summands. -/
theorem quantumSerre_add_eq_zero {q : K} {m : ℕ} (hfac : quantumFactorial q m ≠ 0)
    {x₁ x₂ y₁ y₂ : A} (hx : x₂ * x₁ = q ^ 2 • (x₁ * x₂))
    (hx₂y₁ : x₂ * y₁ = q ^ (1 - (m : ℤ)) • (y₁ * x₂))
    (hy₂x₁ : y₂ * x₁ = q ^ (1 - (m : ℤ)) • (x₁ * y₂))
    (hs₁ : quantumSerre q m x₁ y₁ = 0) (hs₂ : quantumSerre q m x₂ y₂ = 0) :
    quantumSerre q m (x₁ + x₂) (y₁ + y₂) = 0 := by
  rw [quantumSerre_add hfac hx hx₂y₁ hy₂x₁, hs₁, hs₂, add_zero]

end Ring
end TauCeti

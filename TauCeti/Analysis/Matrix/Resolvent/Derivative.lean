/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Basic
public import TauCeti.Analysis.Matrix.L2OpNorm
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

import TauCeti.Analysis.Matrix.Trace.Rank
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Derivative of a matrix resolvent

For Hermitian `A` and `B`, differentiating the resolvent of `A + t • B` along a real parameter
gives `-R * B * R`, where `R = (A + t • B - z • 1)⁻¹` and `z` is nonreal.

## Main results

* `Matrix.IsHermitian.hasDerivAt_inv_add_smul_sub_smul_one` gives the matrix derivative.
* `Matrix.IsHermitian.hasDerivAt_inv_add_smul_sub_smul_one_apply` gives the entrywise derivative.
* `Matrix.IsHermitian.hasDerivAt_inv_add_smul_single_sub_smul_one_apply` specializes to a
  diagonal matrix unit: the derivative of entry `(i,j)` is `-R i k * R k j`.
* `Matrix.IsHermitian.iteratedDeriv_inv_add_smul_sub_smul_one` gives the derivative of every
  order: `R⁽ᵏ⁾ = (-1)ᵏ k! R (B R)ᵏ`.
* `Matrix.IsHermitian.norm_iteratedDeriv_inv_add_smul_sub_smul_one_le` bounds it uniformly by
  `k! ‖B‖ᵏ / |Im z|ᵏ⁺¹` in the Euclidean operator norm.
* `Matrix.IsHermitian.norm_iteratedDeriv_succ_normalized_trace_inv_add_smul_sub_smul_one_le`
  gives the rank-sensitive bound for normalized resolvent traces, after a real linear scalar test.

These uniform bounds supply the derivative hypotheses in Lindeberg replacement of matrix entries.

## References

* T. Tao, *Topics in Random Matrix Theory*, American Mathematical Society (2012), §§2.2, 2.4.
-/

public section

noncomputable section

open scoped Matrix.Norms.L2Operator ContDiff Nat

/-- The real normed algebra structure induced by the matrix Euclidean operator norm. -/
local instance matrixComplexNormedAlgebraReal (n : Type*) [Fintype n] [DecidableEq n] :
    NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.l2OpNormedAlgebraReal

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
include hA hB

/-- The derivative of the resolvent along a Hermitian perturbation. -/
theorem hasDerivAt_inv_add_smul_sub_smul_one (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ (A + s • B - z • 1)⁻¹)
      (-((A + t • B - z • 1)⁻¹ * B * (A + t • B - z • 1)⁻¹)) t := by
  have h : (A + t • B).IsHermitian := by
    apply hA.add
    exact hB.smul (by simp [IsSelfAdjoint])
  obtain ⟨u, hu⟩ := h.isUnit_sub_smul_one_of_im_ne_zero hz
  have hd : HasDerivAt (fun s : ℝ ↦ A + s • B - z • 1) B t := by
    simpa only [one_smul] using! (((hasDerivAt_id t).smul_const B).const_add A).sub_const
      (z • (1 : Matrix n n ℂ))
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℝ) u).comp_hasDerivAt_of_eq t hd hu
  simpa [Matrix.nonsing_inv_eq_ringInverse, hu, ContinuousLinearMap.mulLeftRight_apply] using! hi

/-- The derivative of an individual entry of the resolvent. -/
theorem hasDerivAt_inv_add_smul_sub_smul_one_apply (t : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i j : n) :
    HasDerivAt (fun s : ℝ ↦ (A + s • B - z • 1)⁻¹ i j)
      (-((A + t • B - z • 1)⁻¹ * B * (A + t • B - z • 1)⁻¹) i j) t := by
  have h := (entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hA.hasDerivAt_inv_add_smul_sub_smul_one hB t hz)
  simpa using! h

/-- The resolvent along a Hermitian perturbation is smooth on the whole real line, of every
finite or infinite order, whenever the spectral parameter is nonreal. -/
theorem contDiff_inv_add_smul_sub_smul_one {z : ℂ} (hz : z.im ≠ 0) (k : ℕ∞ω) :
    ContDiff ℝ k (fun t : ℝ ↦ (A + t • B - z • 1)⁻¹) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have h : (A + t • B).IsHermitian := hA.add (hB.smul (by simp [IsSelfAdjoint]))
  obtain ⟨u, hu⟩ := h.isUnit_sub_smul_one_of_im_ne_zero hz
  have hd : ContDiffAt ℝ k (fun s : ℝ ↦ A + s • B - z • 1) t := by fun_prop
  have hi : ContDiffAt ℝ k Ring.inverse (A + t • B - z • 1) :=
    hu ▸ contDiffAt_ringInverse ℝ u
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using! hi.comp t hd

private theorem hasDerivAt_resolventWord (k : ℕ) (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt
      (fun s : ℝ ↦ (A + s • B - z • 1)⁻¹ * (B * (A + s • B - z • 1)⁻¹) ^ k)
      (-((k + 1 : ℕ) : ℝ) •
        ((A + t • B - z • 1)⁻¹ * (B * (A + t • B - z • 1)⁻¹) ^ (k + 1))) t := by
  let R := fun s : ℝ ↦ (A + s • B - z • 1)⁻¹
  have hR := hA.hasDerivAt_inv_add_smul_sub_smul_one hB t hz
  induction k with
  | zero => simpa [R, pow_one, mul_assoc] using hR
  | succ k ih =>
    have hd := ih.fun_mul (hR.const_mul B)
    simp only [pow_succ, ← mul_assoc] at hd ⊢
    convert hd using 1
    simp only [Matrix.smul_mul, mul_neg, mul_assoc, Nat.cast_add, Nat.cast_one,
      neg_add, add_smul, neg_one_smul, add_mul, neg_mul]

/-- All real derivatives of a Hermitian resolvent along a Hermitian perturbation, in their
noncommutative order. No commutation of `A` and `B` is assumed. -/
theorem iteratedDeriv_inv_add_smul_sub_smul_one (k : ℕ) (t : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) :
    iteratedDeriv k (fun s : ℝ ↦ (A + s • B - z • 1)⁻¹) t =
      ((-1 : ℝ) ^ k * (Nat.factorial k : ℝ)) •
        ((A + t • B - z • 1)⁻¹ * (B * (A + t • B - z • 1)⁻¹) ^ k) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, funext ih]
    have hd := (hA.hasDerivAt_resolventWord hB k t hz).fun_const_smul
      ((-1 : ℝ) ^ k * (Nat.factorial k : ℝ))
    have he := hd.deriv
    simp only [smul_smul] at he
    rw [he]
    congr 1
    simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- Uniform operator-norm bounds for the derivatives of a Hermitian resolvent, including order
zero and empty matrix index types. -/
theorem norm_iteratedDeriv_inv_add_smul_sub_smul_one_le (k : ℕ) (t : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) :
    ‖iteratedDeriv k (fun s : ℝ ↦ (A + s • B - z • 1)⁻¹) t‖ ≤
      (Nat.factorial k : ℝ) * ‖B‖ ^ k * |z.im|⁻¹ ^ (k + 1) := by
  by_cases hn : IsEmpty n
  · let := hn
    rw [Subsingleton.elim (iteratedDeriv k (fun s : ℝ ↦ (A + s • B - z • 1)⁻¹) t) 0,
      norm_zero]
    positivity
  · have : Nonempty n := not_isEmpty_iff.mp hn
    rw [hA.iteratedDeriv_inv_add_smul_sub_smul_one hB k t hz, norm_smul]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
    have hH : (A + t • B).IsHermitian := hA.add (hB.smul (by simp [IsSelfAdjoint]))
    have hR : ‖(A + t • B - z • 1)⁻¹‖ ≤ |z.im|⁻¹ :=
      hH.l2_opNorm_inv_sub_smul_one_le hz
    calc
      _ ≤ (Nat.factorial k : ℝ) *
          (‖(A + t • B - z • 1)⁻¹‖ * (‖B‖ * ‖(A + t • B - z • 1)⁻¹‖) ^ k) := by
        gcongr
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
          ((norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (norm_mul_le _ _) _))
          (norm_nonneg _))
      _ ≤ (Nat.factorial k : ℝ) * (|z.im|⁻¹ * (‖B‖ * |z.im|⁻¹) ^ k) := by gcongr
      _ = _ := by rw [mul_pow, pow_succ]; ring

/-- Every positive-order derivative of a resolvent has rank at most that of the perturbation. -/
theorem rank_iteratedDeriv_succ_inv_add_smul_sub_smul_one_le
    (k : ℕ) (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (iteratedDeriv (k + 1) (fun s : ℝ ↦ (A + s • B - z • 1)⁻¹) t).rank ≤ B.rank := by
  rw [hA.iteratedDeriv_inv_add_smul_sub_smul_one hB (k + 1) t hz]
  let R := (A + t • B - z • 1)⁻¹
  let c := (-1 : ℝ) ^ (k + 1) * (Nat.factorial (k + 1) : ℝ)
  calc
    _ = (((c • R) * B) * (R * (B * R) ^ k)).rank := by
      congr 1
      simp only [R, c, pow_succ', Matrix.smul_mul, mul_assoc]
    _ ≤ ((c • R) * B).rank := rank_mul_le_left _ _
    _ ≤ B.rank := rank_mul_le_right _ _

/-- Positive-order derivatives of normalized resolvent traces have a bound proportional to the
rank of the perturbation divided by the dimension. Any continuous real linear scalar test may
be used; `Complex.reCLM` and `Complex.imCLM` give the real and imaginary components.
The matrix norm is the Euclidean operator norm, and empty index types are allowed. -/
theorem norm_iteratedDeriv_succ_normalized_trace_inv_add_smul_sub_smul_one_le
    (l : ℂ →L[ℝ] ℝ) (k : ℕ) (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ‖iteratedDeriv (k + 1)
      (fun s : ℝ ↦ l ((Fintype.card n : ℂ)⁻¹ * (A + s • B - z • 1)⁻¹.trace)) t‖ ≤
      ‖l‖ * ((B.rank : ℝ) / Fintype.card n *
        ((Nat.factorial (k + 1) : ℝ) * ‖B‖ ^ (k + 1) * |z.im|⁻¹ ^ (k + 2))) := by
  let L : Matrix n n ℂ →L[ℝ] ℝ :=
    l.comp
      ((((Fintype.card n : ℂ)⁻¹ • (traceLinearMap n ℂ ℂ)).restrictScalars ℝ).toContinuousLinearMap)
  have hL (M : Matrix n n ℂ) : L M = l ((Fintype.card n : ℂ)⁻¹ * M.trace) := rfl
  have hs := hA.contDiff_inv_add_smul_sub_smul_one hB hz (k + 1)
  have heq : (fun s : ℝ ↦ l ((Fintype.card n : ℂ)⁻¹ *
      (A + s • B - z • 1)⁻¹.trace)) = L ∘ (fun s : ℝ ↦ (A + s • B - z • 1)⁻¹) := by
    ext s
    exact (hL _).symm
  rw [heq, L.iteratedDeriv_comp_left hs.contDiffAt le_rfl, hL]
  let D := iteratedDeriv (k + 1) (fun s : ℝ ↦ (A + s • B - z • 1)⁻¹) t
  have hr : D.rank ≤ B.rank := hA.rank_iteratedDeriv_succ_inv_add_smul_sub_smul_one_le hB k t hz
  have ht : ‖(Fintype.card n : ℂ)⁻¹ * D.trace‖ ≤
      (Fintype.card n : ℝ)⁻¹ * ((B.rank : ℝ) * ‖D‖) := by
    rw [norm_mul, norm_inv, RCLike.norm_natCast]
    gcongr
    exact (norm_trace_le_rank_mul_l2_opNorm D).trans (by gcongr)
  calc
    _ ≤ ‖l‖ * ‖(Fintype.card n : ℂ)⁻¹ * D.trace‖ := l.le_opNorm _
    _ ≤ ‖l‖ * ((Fintype.card n : ℝ)⁻¹ * ((B.rank : ℝ) *
        ((Nat.factorial (k + 1) : ℝ) * ‖B‖ ^ (k + 1) * |z.im|⁻¹ ^ (k + 2)))) := by
      gcongr
      exact ht.trans (by
        gcongr
        exact hA.norm_iteratedDeriv_inv_add_smul_sub_smul_one_le hB (k + 1) t hz)
    _ = _ := by simp only [div_eq_mul_inv]; ring

end Matrix.IsHermitian

namespace Matrix

/-- Perturbing one diagonal entry gives the negative product of the corresponding column and row
of the resolvent. -/
theorem IsHermitian.hasDerivAt_inv_add_smul_single_sub_smul_one_apply
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) (i j k : n) :
    HasDerivAt (fun s : ℝ ↦ (A + s • single k k (1 : ℂ) - z • 1)⁻¹ i j)
      (-((A + t • single k k (1 : ℂ) - z • 1)⁻¹ i k *
        (A + t • single k k (1 : ℂ) - z • 1)⁻¹ k j)) t := by
  have hB : (single k k (1 : ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_single]
  have h := hA.hasDerivAt_inv_add_smul_sub_smul_one_apply hB t hz i j
  have hm (R : Matrix n n ℂ) : (R * single k k (1 : ℂ) * R) i j = R i k * R k j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hbk
      rw [mul_single_apply_of_ne _ k k i b hbk]
      simp
    · simp
  simpa only [hm, neg_apply] using h

end Matrix

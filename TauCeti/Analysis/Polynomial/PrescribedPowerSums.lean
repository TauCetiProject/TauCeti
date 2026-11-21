/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.PrescribedPowerSums
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Ring.GeomSum
import TauCeti.Analysis.Polynomial.Monic.RootBound

/-!
# Bounds on Newton coefficients and on the roots of the Newton polynomial

Let `M : ℕ → K` be a sequence in `ℝ` or `ℂ` with `‖M k‖ ≤ V Rᵏ` for `k ≥ 1`, as for the
moments `M k = ∫ wᵏ dσ` of a signed measure `σ` of total variation at most `V` carried by the
closed disc of radius `R`. This file bounds the Newton coefficients `b_j` of `M`
(`TauCeti.newtonCoeff`) and the roots of the Newton polynomial
`P = Xᵐ - b₁ Xᵐ⁻¹ + ⋯ + (-1)ᵐ bₘ` (`TauCeti.newtonPolynomial`) in terms of `V` and `R` alone:

* `‖b_j‖ ≤ ((V + 1) R)ʲ` (`TauCeti.norm_newtonCoeff_le`);
* every root `z` of `P` satisfies `‖z‖ ≤ 2 (V + 1) R`
  (`TauCeti.norm_le_of_mem_roots_newtonPolynomial`).

Only finitely many moments enter: the bound on `b_j` uses `1 ≤ k ≤ j`, the bound on the roots
uses `1 ≤ k ≤ m`.

Both bounds are homogeneous in `R`, as they must be: rescaling the points by `t` multiplies `M k`
by `tᵏ` and `b_j` by `tʲ`. They hold whatever the sequence is, before `P` is known to
approximate any point configuration, and they depend on no lower bound on the masses. The first
follows from Newton's recursion `j b_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} M_k` by induction and the
geometric sum `V ∑_{i<j} (V + 1)ⁱ = (V + 1)ʲ - 1`; the second from the first and Fujiwara's root
bound `Polynomial.IsRoot.norm_le_two_mul`.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford (1995), Ch. I,
  §2.
-/

public section

open Finset Polynomial

namespace TauCeti

variable {K : Type*} [RCLike K]

/-- **Newton coefficients of a bounded sequence.** If `‖M k‖ ≤ V Rᵏ` for every `1 ≤ k ≤ j`, with
`V, R ≥ 0`, then the `j`-th Newton coefficient of `M` satisfies `‖b_j‖ ≤ ((V + 1) R)ʲ`. -/
theorem norm_newtonCoeff_le {M : ℕ → K} {V R : ℝ} (hV : 0 ≤ V) (hR : 0 ≤ R) {j : ℕ}
    (hM : ∀ k ≠ 0, k ≤ j → ‖M k‖ ≤ V * R ^ k) : ‖newtonCoeff M j‖ ≤ ((V + 1) * R) ^ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  -- Newton's recursion bounds `j ‖b_j‖` by `∑_{i<j} ((V + 1) R)ⁱ V R^(j-i) = ((V + 1)ʲ - 1) Rʲ`.
  have hsum : (j : ℝ) * ‖newtonCoeff M j‖ ≤
      ∑ i ∈ range j, R ^ j * ((V + 1) ^ i * (V + 1 - 1)) := by
    have h := congrArg norm (mul_newtonCoeff_eq_sum M j)
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, RCLike.norm_natCast] at h
    rw [h, sum_filter, Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => if i < j then (-1) ^ i * newtonCoeff M i * M k else 0), sum_range_succ,
      ite_eq_right (lt_irrefl j), add_zero]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
    rw [mem_range] at hi
    rw [ite_eq_left hi]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖newtonCoeff M i‖ * ‖M (j - i)‖ ≤ ((V + 1) * R) ^ i * (V * R ^ (j - i)) := by
          gcongr
          exacts [ih i hi fun k hk hki => hM k hk (hki.trans hi.le), hM _ (by omega) (by omega)]
      _ = R ^ j * ((V + 1) ^ i * (V + 1 - 1)) := by
        rw [mul_pow, ← pow_sub_mul_pow R hi.le]
        ring
  rw [← mul_sum, ← sum_mul, geom_sum_mul] at hsum
  calc ‖newtonCoeff M j‖ ≤ (j : ℝ) * ‖newtonCoeff M j‖ :=
        le_mul_of_one_le_left (norm_nonneg _) (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj)
    _ ≤ R ^ j * ((V + 1) ^ j - 1) := by simpa using hsum
    _ ≤ ((V + 1) * R) ^ j := by
      rw [mul_pow, mul_comm]
      gcongr
      linarith

/-- **Roots of the Newton polynomial of a bounded sequence.** If `‖M k‖ ≤ V Rᵏ` for every
`1 ≤ k ≤ m`, with `V, R ≥ 0`, then every root `z` of the Newton polynomial
`Xᵐ - b₁ Xᵐ⁻¹ + ⋯ + (-1)ᵐ bₘ` of `M` satisfies `‖z‖ ≤ 2 (V + 1) R`. -/
theorem norm_le_of_mem_roots_newtonPolynomial {M : ℕ → K} {V R : ℝ} (hV : 0 ≤ V) (hR : 0 ≤ R)
    {m : ℕ} (hM : ∀ k ≠ 0, k ≤ m → ‖M k‖ ≤ V * R ^ k) {z : K}
    (hz : z ∈ (newtonPolynomial M m).roots) :
    ‖z‖ ≤ 2 * ((V + 1) * R) := by
  refine IsRoot.norm_le_two_mul (monic_newtonPolynomial M m) (fun i hi => ?_)
    (isRoot_of_mem_roots hz)
  rw [natDegree_newtonPolynomial] at hi ⊢
  have h := coeff_newtonPolynomial_sub M (Nat.sub_le m i)
  rw [Nat.sub_sub_self hi.le] at h
  simpa [h] using norm_newtonCoeff_le hV hR fun k hk hki => hM k hk (hki.trans (Nat.sub_le m i))

end TauCeti

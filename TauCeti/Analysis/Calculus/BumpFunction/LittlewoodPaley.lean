/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Normed.Module.Ball

/-!
# Littlewood–Paley cutoffs

Let `φ : E → ℝ` be a smooth bump function on a real normed space, equal to `1` on
`closedBall 0 φ.rIn` and supported in `ball 0 φ.rOut`. Its dyadic differences

`ψⱼ ξ = φ (2^{-j} ξ) - φ (2^{1-j} ξ)`, `j ∈ ℤ`,

form a smooth **Littlewood–Paley partition of unity** of `E \ {0}`: each `ψⱼ` is supported in the
annulus `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`, the partial sums telescope,
`∑_{a < j ≤ b} ψⱼ ξ = φ (2^{-b} ξ) - φ (2^{-a} ξ)`, and `∑ⱼ ψⱼ ξ = 1` for every `ξ ≠ 0`, with
only finitely many nonzero terms. In finite dimension, the `k`-th derivative of `ψⱼ` is
`O(2^{-jk})` uniformly in `j`.

## Main declarations

* `ContDiffBump.littlewoodPaley`: the dyadic cutoff `ψⱼ`.
* `ContDiffBump.sum_littlewoodPaley_Ioc`: the telescoping partial sums.
* `ContDiffBump.hasSum_littlewoodPaley`: `∑ⱼ ψⱼ ξ = 1` for `ξ ≠ 0`.
* `ContDiffBump.exists_norm_iteratedFDeriv_littlewoodPaley_le`: `‖D^k ψⱼ‖ ≤ B 2^{-jk}`.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 6.2.2 (proof of Theorem 6.2.7).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV,
  Section 3.
-/

public section

open Metric Set TauCeti
open scoped ContDiff

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Rescaling by `2^{-j}` turns an upper bound `‖ξ‖ ≤ 2^j r` into `‖2^{-j} ξ‖ ≤ r`. -/
private lemma norm_two_zpow_inv_smul_le_iff {j : ℤ} {ξ : E} {r : ℝ} :
    ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ ≤ r ↔ ‖ξ‖ ≤ 2 ^ j * r := by
  rw [norm_inv_smul_of_nonneg (zpow_nonneg zero_le_two _), div_le_iff₀ (zpow_pos two_pos _),
    mul_comm]

/-- Rescaling by `2^{-j}` turns a lower bound `2^j r ≤ ‖ξ‖` into `r ≤ ‖2^{-j} ξ‖`. -/
private lemma le_norm_two_zpow_inv_smul_iff {j : ℤ} {ξ : E} {r : ℝ} :
    r ≤ ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ ↔ 2 ^ j * r ≤ ‖ξ‖ := by
  rw [norm_inv_smul_of_nonneg (zpow_nonneg zero_le_two _), le_div_iff₀ (zpow_pos two_pos _),
    mul_comm]

/-- Rescaling by `2^{-j}` shrinks a vector at least as much as rescaling by `2^{1-j}`. -/
private lemma norm_two_zpow_inv_smul_le_sub_one (j : ℤ) (ξ : E) :
    ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ ≤ ‖((2 : ℝ) ^ (j - 1))⁻¹ • ξ‖ := by
  rw [norm_inv_smul_of_nonneg (zpow_nonneg zero_le_two _),
    norm_inv_smul_of_nonneg (zpow_nonneg zero_le_two _)]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (zpow_pos two_pos _)
    (zpow_le_zpow_right₀ one_le_two (by omega))

section HasContDiffBump

variable [HasContDiffBump E] (φ : ContDiffBump (0 : E))

/-- The **Littlewood–Paley cutoff** at scale `2^j` built from the bump function `φ`:
`ψⱼ ξ = φ (2^{-j} ξ) - φ (2^{1-j} ξ)`. It is supported in the annulus
`2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`, and these cutoffs sum to `1` on `E \ {0}`. -/
noncomputable def littlewoodPaley (j : ℤ) (ξ : E) : ℝ :=
  φ (((2 : ℝ) ^ j)⁻¹ • ξ) - φ (((2 : ℝ) ^ (j - 1))⁻¹ • ξ)

/-- Unfolding `ContDiffBump.littlewoodPaley`. -/
@[simp]
theorem littlewoodPaley_apply (j : ℤ) (ξ : E) :
    φ.littlewoodPaley j ξ = φ (((2 : ℝ) ^ j)⁻¹ • ξ) - φ (((2 : ℝ) ^ (j - 1))⁻¹ • ξ) :=
  (rfl)

/-- Each Littlewood–Paley cutoff is smooth. -/
theorem contDiff_littlewoodPaley {n : ℕ∞} (j : ℤ) : ContDiff ℝ n (φ.littlewoodPaley j) :=
  (φ.contDiff.comp (contDiff_const_smul ((2 : ℝ) ^ j)⁻¹)).sub
    (φ.contDiff.comp (contDiff_const_smul ((2 : ℝ) ^ (j - 1))⁻¹))

/-- The cutoff `ψⱼ` vanishes on the closed ball of radius `2^{j-1} φ.rIn`, where both terms
are `1`. -/
theorem littlewoodPaley_eq_zero_of_norm_le {j : ℤ} {ξ : E}
    (hξ : ‖ξ‖ ≤ 2 ^ (j - 1) * φ.rIn) : φ.littlewoodPaley j ξ = 0 := by
  have h1 : ‖((2 : ℝ) ^ (j - 1))⁻¹ • ξ‖ ≤ φ.rIn := norm_two_zpow_inv_smul_le_iff.2 hξ
  have h2 := (norm_two_zpow_inv_smul_le_sub_one j ξ).trans h1
  rw [littlewoodPaley_apply, φ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 h1),
    φ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 h2), sub_self]

/-- The cutoff `ψⱼ` vanishes outside the open ball of radius `2^j φ.rOut`, where both terms
are `0`. -/
theorem littlewoodPaley_eq_zero_of_le_norm {j : ℤ} {ξ : E}
    (hξ : 2 ^ j * φ.rOut ≤ ‖ξ‖) : φ.littlewoodPaley j ξ = 0 := by
  have h1 : φ.rOut ≤ ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ := le_norm_two_zpow_inv_smul_iff.2 hξ
  have h2 := h1.trans (norm_two_zpow_inv_smul_le_sub_one j ξ)
  rw [littlewoodPaley_apply, φ.zero_of_le_dist (by rwa [dist_zero_right]),
    φ.zero_of_le_dist (by rwa [dist_zero_right]), sub_self]

/-- The cutoff `ψⱼ` is supported in the closed annulus `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`. -/
theorem tsupport_littlewoodPaley_subset (j : ℤ) :
    tsupport (φ.littlewoodPaley j) ⊆
      {ξ | 2 ^ (j - 1) * φ.rIn ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 ^ j * φ.rOut} := by
  refine closure_minimal (fun ξ hξ ↦ ⟨?_, ?_⟩) ?_
  · by_contra h
    exact hξ (φ.littlewoodPaley_eq_zero_of_norm_le (not_le.1 h).le)
  · by_contra h
    exact hξ (φ.littlewoodPaley_eq_zero_of_le_norm (not_le.1 h).le)
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)

/-- The partial sums of the Littlewood–Paley cutoffs telescope:
`∑_{a < j ≤ b} ψⱼ ξ = φ (2^{-b} ξ) - φ (2^{-a} ξ)`. -/
theorem sum_littlewoodPaley_Ioc {a b : ℤ} (hab : a ≤ b) (ξ : E) :
    ∑ j ∈ Finset.Ioc a b, φ.littlewoodPaley j ξ =
      φ (((2 : ℝ) ^ b)⁻¹ • ξ) - φ (((2 : ℝ) ^ a)⁻¹ • ξ) := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hab ih =>
    rw [← Order.succ_eq_add_one, ← Finset.insert_Ioc_right_eq_Ioc_succ hab,
      Finset.sum_insert (by simp), ih, Order.succ_eq_add_one, littlewoodPaley_apply,
      add_sub_cancel_right]
    ring

/-- For `ξ ≠ 0`, only the cutoffs `ψⱼ` with `a < j ≤ b` can be nonzero at `ξ`, for suitable
`a ≤ b`, and on that range they sum to `1`. -/
private lemma exists_Ioc_littlewoodPaley {ξ : E} (hξ : ξ ≠ 0) :
    ∃ a b : ℤ, a ≤ b ∧ (∀ j ∉ Finset.Ioc a b, φ.littlewoodPaley j ξ = 0) ∧
      φ (((2 : ℝ) ^ b)⁻¹ • ξ) = 1 ∧ φ (((2 : ℝ) ^ a)⁻¹ • ξ) = 0 := by
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  obtain ⟨a, ha, -⟩ := exists_mem_Ioc_zpow (div_pos hξ0 φ.rOut_pos) one_lt_two
  obtain ⟨b, -, hb⟩ := exists_mem_Ioc_zpow (div_pos hξ0 φ.rIn_pos) one_lt_two
  have ha' : 2 ^ a * φ.rOut ≤ ‖ξ‖ := (lt_div_iff₀ φ.rOut_pos).1 ha |>.le
  have hb' : ‖ξ‖ ≤ 2 ^ (b + 1) * φ.rIn := (div_le_iff₀ φ.rIn_pos).1 hb
  have hab : a ≤ b + 1 := by
    have h : (2 : ℝ) ^ a * φ.rOut < 2 ^ (b + 1) * φ.rOut := ha'.trans_lt (hb'.trans_lt
      (mul_lt_mul_of_pos_left φ.rIn_lt_rOut (zpow_pos two_pos _)))
    exact ((zpow_lt_zpow_iff_right₀ one_lt_two).1 (lt_of_mul_lt_mul_right h φ.rOut_pos.le)).le
  refine ⟨a, b + 1, hab, fun j hj ↦ ?_, ?_, ?_⟩
  · rcases le_or_gt j a with hja | hja
    · refine φ.littlewoodPaley_eq_zero_of_le_norm (le_trans ?_ ha')
      exact mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ one_le_two hja) φ.rOut_pos.le
    · have hjb : b + 1 < j := by
        by_contra h
        exact hj (Finset.mem_Ioc.2 ⟨hja, not_lt.1 h⟩)
      refine φ.littlewoodPaley_eq_zero_of_norm_le (hb'.trans ?_)
      exact mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ one_le_two (by omega))
        φ.rIn_pos.le
  · exact φ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 (norm_two_zpow_inv_smul_le_iff.2 hb'))
  · exact φ.zero_of_le_dist (by rw [dist_zero_right]; exact le_norm_two_zpow_inv_smul_iff.2 ha')

/-- **The Littlewood–Paley partition of unity.** For `ξ ≠ 0`, `∑ⱼ ψⱼ ξ = 1`, the sum having
only finitely many nonzero terms. -/
theorem hasSum_littlewoodPaley {ξ : E} (hξ : ξ ≠ 0) :
    HasSum (fun j ↦ φ.littlewoodPaley j ξ) 1 := by
  obtain ⟨a, b, hab, hzero, hb, ha⟩ := φ.exists_Ioc_littlewoodPaley hξ
  have : HasSum (fun j ↦ φ.littlewoodPaley j ξ) _ := hasSum_sum_of_ne_finset_zero hzero
  rwa [φ.sum_littlewoodPaley_Ioc hab, hb, ha, sub_zero] at this

end HasContDiffBump

section FiniteDimensional

variable [FiniteDimensional ℝ E] (φ : ContDiffBump (0 : E))

/-- **Derivative bounds for the Littlewood–Paley cutoffs.** The `k`-th derivative of `ψⱼ` is
bounded by `B / 2^{jk}`, with `B` independent of `j`. -/
theorem exists_norm_iteratedFDeriv_littlewoodPaley_le (k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ (j : ℤ) (ξ : E),
      ‖iteratedFDeriv ℝ k (φ.littlewoodPaley j) ξ‖ ≤ B / (2 ^ j) ^ k := by
  obtain ⟨M, hM⟩ := (φ.contDiff.continuous_iteratedFDeriv (m := k) (mod_cast le_top)
    |>.norm).bounded_above_of_compact_support
    (φ.hasCompactSupport.iteratedFDeriv k).norm
  simp only [norm_norm] at hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- Each term `φ (c • ξ)` has `k`-th derivative of norm at most `|c|^k M`.
  have hterm : ∀ (c : ℝ) (ξ : E),
      ‖iteratedFDeriv ℝ k (fun y ↦ φ (c • y)) ξ‖ ≤ |c| ^ k * M := fun c ξ ↦ by
    rw [iteratedFDeriv_comp_const_smul c φ.contDiff, norm_smul, norm_pow, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM _) (by positivity)
  refine ⟨(1 + 2 ^ k) * M, by positivity, fun j ξ ↦ ?_⟩
  have hsub : ‖iteratedFDeriv ℝ k (φ.littlewoodPaley j) ξ‖ ≤
      ‖iteratedFDeriv ℝ k (fun y ↦ φ (((2 : ℝ) ^ j)⁻¹ • y)) ξ‖ +
        ‖iteratedFDeriv ℝ k (fun y ↦ φ (((2 : ℝ) ^ (j - 1))⁻¹ • y)) ξ‖ := by
    unfold littlewoodPaley
    rw [fun_iteratedFDeriv_sub_apply (f := fun y ↦ φ (((2 : ℝ) ^ j)⁻¹ • y))
        (g := fun y ↦ φ (((2 : ℝ) ^ (j - 1))⁻¹ • y))
        ((φ.contDiff.comp (contDiff_const_smul _)).contDiffAt)
        ((φ.contDiff.comp (contDiff_const_smul _)).contDiffAt)]
    exact norm_sub_le _ _
  refine hsub.trans ((add_le_add (hterm _ ξ) (hterm _ ξ)).trans_eq ?_)
  rw [zpow_sub_one₀ two_ne_zero]
  simp only [abs_inv, abs_mul, abs_zpow, abs_two, inv_pow, mul_pow]
  field_simp

end FiniteDimensional

end ContDiffBump

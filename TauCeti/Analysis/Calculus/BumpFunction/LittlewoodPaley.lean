/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Distribution.TemperateGrowth
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

Keeping `φ` itself as a low-frequency piece and discarding the cutoffs with `j ≤ 0` gives the
**inhomogeneous** partition `ψ₀ = φ, ψ₁, ψ₂, …`, which sums to `1` on all of `E`. Its partial sums
are `∑_{j ≤ N} ψⱼ = φ (2^{-N} ·)`, each `ψ_{j+1}` is the rescaling `ψ₁ (2^{-j} ·)`, and pieces whose
indices differ by at least a fixed `L` have disjoint supports. This is the partition used to
decompose a tempered distribution into frequency blocks for Besov and Bessel-potential spaces.

## Main declarations

* `ContDiffBump.littlewoodPaley`: the dyadic cutoff `ψⱼ`.
* `ContDiffBump.sum_littlewoodPaley_Ioc`: the telescoping partial sums.
* `ContDiffBump.hasSum_littlewoodPaley`: `∑ⱼ ψⱼ ξ = 1` for `ξ ≠ 0`.
* `ContDiffBump.exists_norm_iteratedFDeriv_littlewoodPaley_le`: `‖D^k ψⱼ‖ ≤ B 2^{-jk}`.
* `ContDiffBump.inhomogeneousLittlewoodPaley`: the inhomogeneous partition `ψ₀ = φ, ψ₁, ψ₂, …`.
* `ContDiffBump.hasSum_inhomogeneousLittlewoodPaley`: `∑ⱼ ψⱼ ξ = 1` for every `ξ`.
* `ContDiffBump.exists_inhomogeneousLittlewoodPaley_mul_eq_zero`: finite overlap of the pieces.
* `ContDiffBump.exists_norm_iteratedFDeriv_inhomogeneousLittlewoodPaley_le`: the uniform rescaled
  derivative bounds for the inhomogeneous partition, and
  `ContDiffBump.exists_norm_iteratedFDeriv_inhomogeneousLittlewoodPaley_mul_le`: their weighted
  form `‖D^k ψⱼ ξ‖ (1 + ‖ξ‖) ^ k ≤ B`, so the pieces form a bounded family of symbols of order
  zero.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 6.2.2 (proof of Theorem 6.2.7).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV,
  Section 3.
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Section 6.2 (the
  inhomogeneous partition).
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

/-! ### The inhomogeneous partition -/

/-- The **inhomogeneous Littlewood–Paley partition** built from the bump function `φ`: the
low-frequency piece `ψ₀ = φ`, and the dyadic cutoffs `ψⱼ = φ (2^{-j} ·) - φ (2^{1-j} ·)` for
`j ≥ 1`. The piece `ψ₀` is supported in the ball of radius `φ.rOut`, each `ψⱼ` with `j ≥ 1` in
the annulus `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`, and these functions sum to `1` on all of `E`. -/
noncomputable def inhomogeneousLittlewoodPaley (j : ℕ) (ξ : E) : ℝ :=
  if j = 0 then φ ξ else φ.littlewoodPaley j ξ

/-- The low-frequency piece of the inhomogeneous partition is the bump function itself. -/
@[simp]
theorem inhomogeneousLittlewoodPaley_zero : φ.inhomogeneousLittlewoodPaley 0 = φ := by
  funext ξ
  simp [inhomogeneousLittlewoodPaley]

/-- Away from the low-frequency piece, the inhomogeneous partition consists of the dyadic
cutoffs `ψⱼ`. -/
theorem inhomogeneousLittlewoodPaley_of_ne_zero {j : ℕ} (hj : j ≠ 0) :
    φ.inhomogeneousLittlewoodPaley j = φ.littlewoodPaley j := by
  funext ξ
  simp [inhomogeneousLittlewoodPaley, hj]

/-- The pieces `ψ_{j+1}` of the inhomogeneous partition are the dyadic cutoffs. -/
@[simp]
theorem inhomogeneousLittlewoodPaley_succ (j : ℕ) :
    φ.inhomogeneousLittlewoodPaley (j + 1) = φ.littlewoodPaley ((j + 1 : ℕ) : ℤ) :=
  φ.inhomogeneousLittlewoodPaley_of_ne_zero j.succ_ne_zero

/-- The value of `ψ_{j+1}` in terms of the bump function, with natural-number powers. -/
theorem inhomogeneousLittlewoodPaley_succ_apply (j : ℕ) (ξ : E) :
    φ.inhomogeneousLittlewoodPaley (j + 1) ξ =
      φ (((2 : ℝ) ^ (j + 1))⁻¹ • ξ) - φ (((2 : ℝ) ^ j)⁻¹ • ξ) := by
  rw [inhomogeneousLittlewoodPaley_succ, littlewoodPaley_apply]
  push_cast
  simp [← zpow_natCast]

/-- **Scaling of the dyadic pieces.** Each `ψ_{j+1}` is the first dyadic piece rescaled to
frequency `2^j`: `ψ_{j+1} ξ = ψ₁ (2^{-j} ξ)`. -/
theorem inhomogeneousLittlewoodPaley_succ_apply_eq_one_apply (j : ℕ) (ξ : E) :
    φ.inhomogeneousLittlewoodPaley (j + 1) ξ =
      φ.inhomogeneousLittlewoodPaley 1 (((2 : ℝ) ^ j)⁻¹ • ξ) := by
  simp [inhomogeneousLittlewoodPaley_succ_apply, smul_smul, pow_succ, mul_comm]

/-- Each piece of the inhomogeneous partition is smooth. -/
@[fun_prop]
theorem contDiff_inhomogeneousLittlewoodPaley {n : ℕ∞} (j : ℕ) :
    ContDiff ℝ n (φ.inhomogeneousLittlewoodPaley j) := by
  rcases j with _ | j
  · rw [inhomogeneousLittlewoodPaley_zero]
    exact φ.contDiff
  · rw [inhomogeneousLittlewoodPaley_succ]
    exact φ.contDiff_littlewoodPaley _

/-- Every piece `ψⱼ` vanishes outside the open ball of radius `2^j φ.rOut`. -/
theorem inhomogeneousLittlewoodPaley_eq_zero_of_le_norm {j : ℕ} {ξ : E}
    (hξ : 2 ^ j * φ.rOut ≤ ‖ξ‖) : φ.inhomogeneousLittlewoodPaley j ξ = 0 := by
  rcases j with _ | j
  · rw [inhomogeneousLittlewoodPaley_zero]
    exact φ.zero_of_le_dist (by simpa using hξ)
  · rw [inhomogeneousLittlewoodPaley_succ]
    exact φ.littlewoodPaley_eq_zero_of_le_norm (by rwa [zpow_natCast])

/-- The piece `ψ_{j+1}` vanishes on the closed ball of radius `2^j φ.rIn`. -/
theorem inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le {j : ℕ} {ξ : E}
    (hξ : ‖ξ‖ ≤ 2 ^ j * φ.rIn) : φ.inhomogeneousLittlewoodPaley (j + 1) ξ = 0 := by
  rw [inhomogeneousLittlewoodPaley_succ]
  exact φ.littlewoodPaley_eq_zero_of_norm_le (by simpa using hξ)

/-- The low-frequency piece `ψ₀` is supported in the closed ball of radius `φ.rOut`. -/
theorem tsupport_inhomogeneousLittlewoodPaley_zero_subset :
    tsupport (φ.inhomogeneousLittlewoodPaley 0) ⊆ closedBall 0 φ.rOut := by
  rw [inhomogeneousLittlewoodPaley_zero, φ.tsupport_eq]

/-- The piece `ψ_{j+1}` is supported in the closed annulus
`2^j φ.rIn ≤ ‖ξ‖ ≤ 2^{j+1} φ.rOut`. -/
theorem tsupport_inhomogeneousLittlewoodPaley_succ_subset (j : ℕ) :
    tsupport (φ.inhomogeneousLittlewoodPaley (j + 1)) ⊆
      {ξ | 2 ^ j * φ.rIn ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 ^ (j + 1) * φ.rOut} := by
  rw [inhomogeneousLittlewoodPaley_succ]
  refine (φ.tsupport_littlewoodPaley_subset _).trans fun ξ hξ ↦ ?_
  simpa [← zpow_natCast] using hξ

/-- Every piece `ψⱼ` of the inhomogeneous partition is supported in the closed ball of radius
`2^j φ.rOut`. -/
theorem tsupport_inhomogeneousLittlewoodPaley_subset_closedBall (j : ℕ) :
    tsupport (φ.inhomogeneousLittlewoodPaley j) ⊆ closedBall 0 (2 ^ j * φ.rOut) := by
  rcases j with _ | j
  · simpa using φ.tsupport_inhomogeneousLittlewoodPaley_zero_subset
  · exact (φ.tsupport_inhomogeneousLittlewoodPaley_succ_subset j).trans fun ξ hξ ↦
      mem_closedBall_zero_iff.2 hξ.2

/-- The partial sums of the inhomogeneous partition telescope:
`∑_{j ≤ N} ψⱼ ξ = φ (2^{-N} ξ)`. -/
theorem sum_inhomogeneousLittlewoodPaley_range (N : ℕ) (ξ : E) :
    ∑ j ∈ Finset.range (N + 1), φ.inhomogeneousLittlewoodPaley j ξ =
      φ (((2 : ℝ) ^ N)⁻¹ • ξ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, inhomogeneousLittlewoodPaley_succ_apply]
    ring

/-- **The inhomogeneous Littlewood–Paley partition of unity.** For every `ξ`, `∑ⱼ ψⱼ ξ = 1`, the
sum having only finitely many nonzero terms. -/
theorem hasSum_inhomogeneousLittlewoodPaley (ξ : E) :
    HasSum (fun j ↦ φ.inhomogeneousLittlewoodPaley j ξ) 1 := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (‖ξ‖ / φ.rIn) (one_lt_two (α := ℝ))
  have hN' : ‖ξ‖ ≤ 2 ^ N * φ.rIn := ((div_lt_iff₀ φ.rIn_pos).1 hN).le
  have hzero : ∀ j ∉ Finset.range (N + 1), φ.inhomogeneousLittlewoodPaley j ξ = 0 := by
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 :=
      Nat.exists_eq_add_one.2 (by simp only [Finset.mem_range, not_lt] at hj; omega)
    refine φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le (hN'.trans ?_)
    simp only [Finset.mem_range, not_lt, add_le_add_iff_right] at hj
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hj) φ.rIn_pos.le
  have : HasSum (fun j ↦ φ.inhomogeneousLittlewoodPaley j ξ) _ :=
    hasSum_sum_of_ne_finset_zero hzero
  rwa [φ.sum_inhomogeneousLittlewoodPaley_range, φ.one_of_mem_closedBall] at this
  rw [mem_closedBall_zero_iff, norm_inv_smul_of_nonneg (pow_nonneg zero_le_two _),
    div_le_iff₀ (pow_pos two_pos _), mul_comm]
  exact hN'

/-- **Finite overlap.** There is `L` such that the pieces `ψⱼ` and `ψₖ` have disjoint supports
whenever `j + L ≤ k`. -/
theorem exists_inhomogeneousLittlewoodPaley_mul_eq_zero :
    ∃ L : ℕ, ∀ j k : ℕ, j + L ≤ k → ∀ ξ : E,
      φ.inhomogeneousLittlewoodPaley j ξ * φ.inhomogeneousLittlewoodPaley k ξ = 0 := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (φ.rOut / φ.rIn) (one_lt_two (α := ℝ))
  have hn' : φ.rOut ≤ 2 ^ n * φ.rIn := ((div_lt_iff₀ φ.rIn_pos).1 hn).le
  refine ⟨n + 1, fun j k hjk ξ ↦ ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := Nat.exists_eq_add_one.2 (by omega)
  rcases le_or_gt ‖ξ‖ (2 ^ k * φ.rIn) with hξ | hξ
  · rw [φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le hξ, mul_zero]
  · refine mul_eq_zero_of_left (φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm ?_) _
    refine le_trans ?_ hξ.le
    calc (2 : ℝ) ^ j * φ.rOut ≤ 2 ^ j * (2 ^ n * φ.rIn) :=
          mul_le_mul_of_nonneg_left hn' (pow_nonneg zero_le_two _)
      _ = 2 ^ (j + n) * φ.rIn := by rw [pow_add, mul_assoc]
      _ ≤ 2 ^ k * φ.rIn :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) φ.rIn_pos.le

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

/-- Each piece of the inhomogeneous partition is compactly supported. -/
theorem hasCompactSupport_inhomogeneousLittlewoodPaley (j : ℕ) :
    HasCompactSupport (φ.inhomogeneousLittlewoodPaley j) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 ^ j * φ.rOut)) fun ξ hξ ↦
    φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm
      (not_le.1 (by simpa [mem_closedBall_zero_iff] using hξ)).le

/-- Each piece of the inhomogeneous partition has temperate growth, so it is a Fourier multiplier
on Schwartz functions and on tempered distributions. -/
@[fun_prop]
theorem hasTemperateGrowth_inhomogeneousLittlewoodPaley (j : ℕ) :
    (φ.inhomogeneousLittlewoodPaley j).HasTemperateGrowth :=
  (φ.hasCompactSupport_inhomogeneousLittlewoodPaley j).hasTemperateGrowth
    (φ.contDiff_inhomogeneousLittlewoodPaley j)

/-- The pieces of the inhomogeneous partition, viewed as complex-valued symbols, have temperate
growth, so they are Fourier multipliers on Schwartz functions and on tempered distributions. -/
theorem hasTemperateGrowth_ofReal_inhomogeneousLittlewoodPaley (j : ℕ) :
    (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)).HasTemperateGrowth := by
  fun_prop

/-- **Derivative bounds for the inhomogeneous partition.** The `k`-th derivative of `ψⱼ` is
bounded by `B / 2^{jk}`, with `B` independent of `j`. -/
theorem exists_norm_iteratedFDeriv_inhomogeneousLittlewoodPaley_le (k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ (j : ℕ) (ξ : E),
      ‖iteratedFDeriv ℝ k (φ.inhomogeneousLittlewoodPaley j) ξ‖ ≤ B / (2 ^ j) ^ k := by
  obtain ⟨B, hB0, hB⟩ := φ.exists_norm_iteratedFDeriv_littlewoodPaley_le k
  obtain ⟨M, -, hM⟩ := φ.hasCompactSupport.exists_bound_iteratedFDeriv φ.contDiff k
  refine ⟨max B M, le_max_of_le_left hB0, fun j ξ ↦ ?_⟩
  rcases j with _ | j
  · simpa using (hM k le_rfl ξ).trans (le_max_right B M)
  · rw [inhomogeneousLittlewoodPaley_succ]
    refine (hB _ ξ).trans ?_
    rw [zpow_natCast]
    exact div_le_div_of_nonneg_right (le_max_left B M) (by positivity)

/-- **The cutoffs are a bounded family of symbols of order zero.** The `k`-th derivative of `ψⱼ`
satisfies `‖D^k ψⱼ ξ‖ (1 + ‖ξ‖) ^ k ≤ B` with `B` independent of `j`: the factor `2^{-jk}` from the
derivative compensates `1 + ‖ξ‖ ≤ 2^j (1 + φ.rOut)` on the support of `ψⱼ`. -/
theorem exists_norm_iteratedFDeriv_inhomogeneousLittlewoodPaley_mul_le (k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ (j : ℕ) (ξ : E),
      ‖iteratedFDeriv ℝ k (φ.inhomogeneousLittlewoodPaley j) ξ‖ * (1 + ‖ξ‖) ^ k ≤ B := by
  obtain ⟨B, hB0, hB⟩ := φ.exists_norm_iteratedFDeriv_inhomogeneousLittlewoodPaley_le k
  have hr := φ.rOut_pos
  refine ⟨B * (1 + φ.rOut) ^ k, by positivity, fun j ξ ↦ ?_⟩
  by_cases hξ : ξ ∈ tsupport (φ.inhomogeneousLittlewoodPaley j)
  · have hξ' : ‖ξ‖ ≤ 2 ^ j * φ.rOut :=
      mem_closedBall_zero_iff.1 (φ.tsupport_inhomogeneousLittlewoodPaley_subset_closedBall j hξ)
    have h2 : (0 : ℝ) < (2 ^ j) ^ k := by positivity
    calc ‖iteratedFDeriv ℝ k (φ.inhomogeneousLittlewoodPaley j) ξ‖ * (1 + ‖ξ‖) ^ k
        ≤ B / (2 ^ j) ^ k * (2 ^ j * (1 + φ.rOut)) ^ k := by
          refine mul_le_mul (hB j ξ) ?_ (by positivity) (by positivity)
          gcongr
          have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
          nlinarith
      _ = B * (1 + φ.rOut) ^ k := by
          rw [mul_pow]
          field_simp
  · rw [Function.notMem_support.1 (fun h ↦ hξ (support_iteratedFDeriv_subset (𝕜 := ℝ) k h)),
      norm_zero, zero_mul]
    positivity

end FiniteDimensional

end ContDiffBump

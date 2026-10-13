/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Littlewood–Paley pieces of a Mihlin symbol

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real normed space, equal to `1`
on `closedBall 0 φ.rIn` and supported in `ball 0 φ.rOut`. Its dyadic differences

`ψⱼ ξ = φ (2^{-j} ξ) - φ (2^{1-j} ξ)`, `j ∈ ℤ`,

form a smooth **Littlewood–Paley partition of unity** of `E \ {0}`: each `ψⱼ` is supported in the
annulus `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`, the `k`-th derivative of `ψⱼ` is `O(2^{-jk})`
uniformly in `j`, the partial sums telescope,
`∑_{a < j ≤ b} ψⱼ ξ = φ (2^{-b} ξ) - φ (2^{-a} ξ)`, and `∑ⱼ ψⱼ ξ = 1` for every `ξ ≠ 0`, with
only finitely many nonzero terms.

Cutting a symbol `m` that is smooth away from the origin by this partition gives the Schwartz
functions `ψⱼ • m`, which sum to `m` pointwise on `E \ {0}`. If `m` satisfies Mihlin's condition
of order `N` with constant `A`,

`‖D^k m ξ‖ ≤ A ‖ξ‖^{-k}` for `k ≤ N` and `ξ ≠ 0`,

then each piece is supported in `closedBall 0 (2^j φ.rOut)` and its derivatives satisfy the
scale-invariant bounds `‖D^k (ψⱼ • m) ξ‖ ≤ C A 2^{-jk}` for `k ≤ N`, with `C` depending only on
`φ` and `N`. On the annulus carrying `ψⱼ`, the Leibniz rule pairs the factor `2^{-ji}` from `i`
derivatives of `ψⱼ` with the factor `‖ξ‖^{-(k-i)} ≈ 2^{-j(k-i)}` from the remaining derivatives
of `m`.

This is the decomposition at the start of the proof of the Mihlin–Hörmander multiplier theorem:
each piece is band-limited at scale `2^j` with derivative bounds independent of `j`, which is the
input to the kernel estimates that establish Hörmander's condition for the kernel of the
multiplier.

## Main declarations

* `ContDiffBump.littlewoodPaley`: the dyadic cutoff `ψⱼ`.
* `ContDiffBump.sum_littlewoodPaley_Ioc`: the telescoping partial sums.
* `ContDiffBump.hasSum_littlewoodPaley`: `∑ⱼ ψⱼ ξ = 1` for `ξ ≠ 0`.
* `ContDiffBump.exists_norm_iteratedFDeriv_littlewoodPaley_le`: `‖D^k ψⱼ‖ ≤ B 2^{-jk}`.
* `ContDiffBump.littlewoodPaleyPiece`: the Schwartz function `ψⱼ • m`.
* `ContDiffBump.hasSum_littlewoodPaleyPiece`: the pieces sum to `m` away from the origin.
* `ContDiffBump.exists_norm_iteratedFDeriv_littlewoodPaleyPiece_le`: the scale-invariant
  derivative bounds for the pieces of a symbol satisfying Mihlin's condition.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 6.2.2 (proof of Theorem 6.2.7).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV,
  Section 3.
-/

public section

open Metric Set
open scoped ContDiff SchwartzMap

namespace ContDiffBump

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `‖2^{-j} ξ‖ = ‖ξ‖ / 2^j`. -/
private lemma norm_inv_zpow_smul (j : ℤ) (ξ : E) :
    ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ = ‖ξ‖ / 2 ^ j := by
  rw [norm_smul, norm_inv, norm_zpow, Real.norm_two, inv_mul_eq_div]

section HasContDiffBump

variable [HasContDiffBump E] (φ : ContDiffBump (0 : E))

/-- The **Littlewood–Paley cutoff** at scale `2^j` built from the bump function `φ`:
`ψⱼ ξ = φ (2^{-j} ξ) - φ (2^{1-j} ξ)`. It is supported in the annulus
`2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`, and these cutoffs sum to `1` on `E \ {0}`. -/
noncomputable def littlewoodPaley (j : ℤ) (ξ : E) : ℝ :=
  φ (((2 : ℝ) ^ j)⁻¹ • ξ) - φ (((2 : ℝ) ^ (j - 1))⁻¹ • ξ)

/-- Unfolding `ContDiffBump.littlewoodPaley`. -/
theorem littlewoodPaley_apply (j : ℤ) (ξ : E) :
    φ.littlewoodPaley j ξ = φ (((2 : ℝ) ^ j)⁻¹ • ξ) - φ (((2 : ℝ) ^ (j - 1))⁻¹ • ξ) :=
  (rfl)

/-- Each Littlewood–Paley cutoff is smooth. -/
theorem contDiff_littlewoodPaley {n : ℕ∞} (j : ℤ) : ContDiff ℝ n (φ.littlewoodPaley j) := by
  rw [show φ.littlewoodPaley j = _ from funext (φ.littlewoodPaley_apply j)]
  exact (φ.contDiff.comp (contDiff_const_smul ((2 : ℝ) ^ j)⁻¹)).sub
    (φ.contDiff.comp (contDiff_const_smul ((2 : ℝ) ^ (j - 1))⁻¹))

/-- The cutoff `ψⱼ` vanishes on the closed ball of radius `2^{j-1} φ.rIn`, where both terms
are `1`. -/
theorem littlewoodPaley_eq_zero_of_norm_le {j : ℤ} {ξ : E}
    (hξ : ‖ξ‖ ≤ 2 ^ (j - 1) * φ.rIn) : φ.littlewoodPaley j ξ = 0 := by
  have hj : (0 : ℝ) < 2 ^ (j - 1) := zpow_pos two_pos _
  have h1 : ‖((2 : ℝ) ^ (j - 1))⁻¹ • ξ‖ ≤ φ.rIn := by
    rw [norm_inv_zpow_smul, div_le_iff₀ hj, mul_comm]
    exact hξ
  have h2 : ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ ≤ φ.rIn := by
    refine le_trans ?_ h1
    rw [norm_inv_zpow_smul, norm_inv_zpow_smul]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hj
      (zpow_le_zpow_right₀ one_le_two (by omega))
  rw [littlewoodPaley_apply, φ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 h1),
    φ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 h2), sub_self]

/-- The cutoff `ψⱼ` vanishes outside the open ball of radius `2^j φ.rOut`, where both terms
are `0`. -/
theorem littlewoodPaley_eq_zero_of_le_norm {j : ℤ} {ξ : E}
    (hξ : 2 ^ j * φ.rOut ≤ ‖ξ‖) : φ.littlewoodPaley j ξ = 0 := by
  have hj : (0 : ℝ) < 2 ^ (j - 1) := zpow_pos two_pos _
  have h1 : φ.rOut ≤ ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ := by
    rw [norm_inv_zpow_smul, le_div_iff₀ (zpow_pos two_pos _), mul_comm]
    exact hξ
  have h2 : φ.rOut ≤ ‖((2 : ℝ) ^ (j - 1))⁻¹ • ξ‖ := by
    refine h1.trans ?_
    rw [norm_inv_zpow_smul, norm_inv_zpow_smul]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hj
      (zpow_le_zpow_right₀ one_le_two (by omega))
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
  · refine φ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 ?_)
    rw [norm_inv_zpow_smul, div_le_iff₀ (zpow_pos two_pos _), mul_comm]
    exact hb'
  · refine φ.zero_of_le_dist ?_
    rw [dist_zero_right, norm_inv_zpow_smul, le_div_iff₀ (zpow_pos two_pos _), mul_comm]
    exact ha'

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
  have h2j : (0 : ℝ) < 2 ^ j := zpow_pos two_pos _
  have hsub : ‖iteratedFDeriv ℝ k (φ.littlewoodPaley j) ξ‖ ≤
      ‖iteratedFDeriv ℝ k (fun y ↦ φ (((2 : ℝ) ^ j)⁻¹ • y)) ξ‖ +
        ‖iteratedFDeriv ℝ k (fun y ↦ φ (((2 : ℝ) ^ (j - 1))⁻¹ • y)) ξ‖ := by
    rw [show φ.littlewoodPaley j = fun y ↦ φ (((2 : ℝ) ^ j)⁻¹ • y) -
        φ (((2 : ℝ) ^ (j - 1))⁻¹ • y) from funext (φ.littlewoodPaley_apply j),
      fun_iteratedFDeriv_sub_apply (f := fun y ↦ φ (((2 : ℝ) ^ j)⁻¹ • y))
        (g := fun y ↦ φ (((2 : ℝ) ^ (j - 1))⁻¹ • y))
        ((φ.contDiff.comp (contDiff_const_smul _)).contDiffAt)
        ((φ.contDiff.comp (contDiff_const_smul _)).contDiffAt)]
    exact norm_sub_le _ _
  refine hsub.trans ((add_le_add (hterm _ ξ) (hterm _ ξ)).trans_eq ?_)
  rw [abs_inv, abs_inv, abs_of_pos h2j, abs_of_pos (zpow_pos two_pos _), zpow_sub_one₀ two_ne_zero,
    mul_inv, inv_inv, mul_pow, inv_pow]
  field_simp

variable {m : E → F}

/-- The product `ψⱼ • m` of a Littlewood–Paley cutoff with a function smooth away from the origin
is smooth: near the origin it vanishes identically. -/
private lemma contDiff_littlewoodPaley_smul (hm : ContDiffOn ℝ ∞ m {0}ᶜ) (j : ℤ) :
    ContDiff ℝ ∞ (fun ξ ↦ φ.littlewoodPaley j ξ • m ξ) := by
  refine contDiff_iff_contDiffAt.2 fun ξ ↦ ?_
  rcases eq_or_ne ξ 0 with rfl | hξ
  · refine contDiffAt_const (c := (0 : F)).congr_of_eventuallyEq ?_
    have hr : (0 : ℝ) < 2 ^ (j - 1) * φ.rIn := mul_pos (zpow_pos two_pos _) φ.rIn_pos
    filter_upwards [ball_mem_nhds (0 : E) hr] with y hy
    rw [φ.littlewoodPaley_eq_zero_of_norm_le (mem_ball_zero_iff.1 hy).le, zero_smul]
  · exact (φ.contDiff_littlewoodPaley j).contDiffAt.smul
      (hm.contDiffAt (isOpen_compl_singleton.mem_nhds hξ))

private lemma hasCompactSupport_littlewoodPaley_smul (j : ℤ) :
    HasCompactSupport (fun ξ ↦ φ.littlewoodPaley j ξ • m ξ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 ^ j * φ.rOut)) fun ξ hξ ↦ by
    rw [φ.littlewoodPaley_eq_zero_of_le_norm
      (not_le.1 (by simpa [mem_closedBall_zero_iff] using hξ)).le, zero_smul]

/-- The **Littlewood–Paley piece** `ψⱼ • m` of a function `m` smooth away from the origin, as a
Schwartz function. It is supported in `closedBall 0 (2^j φ.rOut)`, and the pieces sum to `m` on
`E \ {0}`. -/
noncomputable def littlewoodPaleyPiece (hm : ContDiffOn ℝ ∞ m {0}ᶜ) (j : ℤ) : 𝓢(E, F) :=
  (φ.hasCompactSupport_littlewoodPaley_smul j).toSchwartzMap
    (φ.contDiff_littlewoodPaley_smul hm j)

/-- The values of the piece `ψⱼ • m`. -/
@[simp]
theorem littlewoodPaleyPiece_apply (hm : ContDiffOn ℝ ∞ m {0}ᶜ) (j : ℤ) (ξ : E) :
    φ.littlewoodPaleyPiece hm j ξ = φ.littlewoodPaley j ξ • m ξ :=
  (rfl)

/-- The piece `ψⱼ • m` is supported in the closed ball of radius `2^j φ.rOut`. -/
theorem tsupport_littlewoodPaleyPiece_subset (hm : ContDiffOn ℝ ∞ m {0}ᶜ) (j : ℤ) :
    tsupport (φ.littlewoodPaleyPiece hm j) ⊆ closedBall 0 (2 ^ j * φ.rOut) := by
  refine (tsupport_smul_subset_left _ _).trans ((φ.tsupport_littlewoodPaley_subset j).trans ?_)
  exact fun ξ hξ ↦ mem_closedBall_zero_iff.2 hξ.2

/-- The partial sums of the pieces are the truncations
`∑_{a < j ≤ b} ψⱼ • m = (φ (2^{-b} ·) - φ (2^{-a} ·)) • m`. -/
theorem sum_littlewoodPaleyPiece_Ioc (hm : ContDiffOn ℝ ∞ m {0}ᶜ) {a b : ℤ} (hab : a ≤ b)
    (ξ : E) :
    ∑ j ∈ Finset.Ioc a b, φ.littlewoodPaleyPiece hm j ξ =
      (φ (((2 : ℝ) ^ b)⁻¹ • ξ) - φ (((2 : ℝ) ^ a)⁻¹ • ξ)) • m ξ := by
  simp only [littlewoodPaleyPiece_apply, ← Finset.sum_smul, φ.sum_littlewoodPaley_Ioc hab]

/-- The Littlewood–Paley pieces of `m` sum to `m` away from the origin. -/
theorem hasSum_littlewoodPaleyPiece (hm : ContDiffOn ℝ ∞ m {0}ᶜ) {ξ : E} (hξ : ξ ≠ 0) :
    HasSum (fun j ↦ φ.littlewoodPaleyPiece hm j ξ) (m ξ) := by
  simpa using (φ.hasSum_littlewoodPaley hξ).smul_const (m ξ)

/-- On the support of `ψⱼ`, where `‖ξ‖ ≥ 2^{j-1} φ.rIn`, a Mihlin bound `A / ‖ξ‖^l` for the
`l`-th derivative of `m` becomes `A (2 / φ.rIn)^l / 2^{jl}`. -/
private lemma norm_iteratedFDeriv_le_of_mem_tsupport_littlewoodPaley {A : ℝ} (hA : 0 ≤ A)
    {l : ℕ} (hmA : ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ l m ξ‖ ≤ A / ‖ξ‖ ^ l) {j : ℤ} {ξ : E}
    (hξ : ξ ∈ tsupport (φ.littlewoodPaley j)) :
    ‖iteratedFDeriv ℝ l m ξ‖ ≤ A * (2 / φ.rIn) ^ l / (2 ^ j) ^ l := by
  have hann := φ.tsupport_littlewoodPaley_subset j hξ
  have hρ : 0 < 2 ^ (j - 1) * φ.rIn := mul_pos (zpow_pos two_pos _) φ.rIn_pos
  refine (hmA ξ (norm_pos_iff.1 (hρ.trans_le hann.1))).trans ?_
  have heq : A * (2 / φ.rIn) ^ l / (2 ^ j) ^ l = A / (2 ^ (j - 1) * φ.rIn) ^ l := by
    rw [zpow_sub_one₀ two_ne_zero, div_pow, mul_pow, mul_pow, inv_pow]
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_left hA (pow_pos hρ _) (pow_le_pow_left₀ hρ.le hann.1 _)

/-- The derivative bound for a single order `k`, with an explicit constant built from bounds `B i`
on the derivatives of the cutoffs. -/
private lemma norm_iteratedFDeriv_littlewoodPaleyPiece_le (hm : ContDiffOn ℝ ∞ m {0}ᶜ) {k : ℕ}
    {B : ℕ → ℝ} (hB0 : ∀ i, 0 ≤ B i) (hB : ∀ i (j : ℤ) (ξ : E),
      ‖iteratedFDeriv ℝ i (φ.littlewoodPaley j) ξ‖ ≤ B i / (2 ^ j) ^ i)
    {A : ℝ} (hA : 0 ≤ A) (hmA : ∀ l ≤ k, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ l m ξ‖ ≤ A / ‖ξ‖ ^ l)
    (j : ℤ) (ξ : E) :
    ‖iteratedFDeriv ℝ k (φ.littlewoodPaleyPiece hm j) ξ‖ ≤
      (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B i * (2 / φ.rIn) ^ (k - i)) * A /
        (2 ^ j) ^ k := by
  have h2j : (0 : ℝ) < 2 ^ j := zpow_pos two_pos _
  have hC : 0 ≤ (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B i * (2 / φ.rIn) ^ (k - i)) *
      A / (2 ^ j) ^ k := by
    have := φ.rIn_pos
    refine div_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ ↦ ?_) hA) (by positivity)
    have := hB0 i
    positivity
  rw [show ⇑(φ.littlewoodPaleyPiece hm j) = fun y ↦ φ.littlewoodPaley j y • m y from
    funext (φ.littlewoodPaleyPiece_apply hm j)]
  by_cases hξ : ξ ∈ tsupport (φ.littlewoodPaley j)
  swap
  · -- Off the support of the cutoff the piece vanishes near `ξ`.
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hξ ((tsupport_iteratedFDeriv_subset k).trans
      (tsupport_smul_subset_left _ _) h)), norm_zero]
    exact hC
  have hξ0 : 0 < ‖ξ‖ :=
    (mul_pos (zpow_pos two_pos _) φ.rIn_pos).trans_le (φ.tsupport_littlewoodPaley_subset j hξ).1
  have hU : IsOpen ({0}ᶜ : Set E) := isOpen_compl_singleton
  have hξU : ξ ∈ ({0}ᶜ : Set E) := norm_pos_iff.1 hξ0
  -- The Leibniz rule on the open set `E \ {0}`, where `m` is smooth.
  have hleib := norm_iteratedFDerivWithin_smul_le
    (φ.contDiff_littlewoodPaley j (n := ⊤)).contDiffOn hm hU.uniqueDiffOn hξU
    (n := k) (mod_cast le_top)
  simp only [iteratedFDerivWithin_of_isOpen _ hU hξU] at hleib
  refine hleib.trans ?_
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hmξ := φ.norm_iteratedFDeriv_le_of_mem_tsupport_littlewoodPaley hA
    (hmA (k - i) (Nat.sub_le _ _)) hξ
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (φ.littlewoodPaley j) ξ‖ *
        ‖iteratedFDeriv ℝ (k - i) m ξ‖
      ≤ (k.choose i : ℝ) * (B i / (2 ^ j) ^ i) *
          (A * (2 / φ.rIn) ^ (k - i) / (2 ^ j) ^ (k - i)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (hB i j ξ) (Nat.cast_nonneg _)) hmξ
          (norm_nonneg _) ?_
        have := hB0 i
        positivity
    _ = (k.choose i : ℝ) * B i * (2 / φ.rIn) ^ (k - i) * A / (2 ^ j) ^ k := by
        rw [← Nat.add_sub_cancel' hik, pow_add]
        simp only [Nat.add_sub_cancel_left]
        field_simp

/-- **Littlewood–Paley pieces of a Mihlin symbol.** Let `m` be smooth on `E \ {0}` and satisfy
Mihlin's condition of order `N` with constant `A ≥ 0`: `‖D^k m ξ‖ ≤ A / ‖ξ‖^k` for `k ≤ N` and
`ξ ≠ 0`. Then every Littlewood–Paley piece `ψⱼ • m`, which is supported in
`closedBall 0 (2^j φ.rOut)`, satisfies `‖D^k (ψⱼ • m) ξ‖ ≤ C A / 2^{jk}` for `k ≤ N`, where `C`
depends only on `φ` and `N`. -/
theorem exists_norm_iteratedFDeriv_littlewoodPaleyPiece_le (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ {m : E → F} (hm : ContDiffOn ℝ ∞ m {0}ᶜ) {A : ℝ}, 0 ≤ A →
      (∀ k ≤ N, ∀ ξ ≠ 0, ‖iteratedFDeriv ℝ k m ξ‖ ≤ A / ‖ξ‖ ^ k) →
        ∀ (j : ℤ), ∀ k ≤ N, ∀ ξ,
          ‖iteratedFDeriv ℝ k (φ.littlewoodPaleyPiece hm j) ξ‖ ≤ C * A / (2 ^ j) ^ k := by
  choose B hB0 hB using φ.exists_norm_iteratedFDeriv_littlewoodPaley_le
  set c : ℕ → ℝ := fun k ↦
    ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B i * (2 / φ.rIn) ^ (k - i)
  have hc0 : ∀ k, 0 ≤ c k := fun k ↦ by
    have := φ.rIn_pos
    exact Finset.sum_nonneg fun i _ ↦ by have := hB0 i; positivity
  refine ⟨∑ k ∈ Finset.range (N + 1), c k, Finset.sum_nonneg fun k _ ↦ hc0 k,
    fun hm A hA hmA j k hk ξ ↦ ?_⟩
  refine (φ.norm_iteratedFDeriv_littlewoodPaleyPiece_le hm hB0 hB hA
    (fun l hl ↦ hmA l (hl.trans hk)) j ξ).trans ?_
  gcongr
  exact Finset.single_le_sum (fun k _ ↦ hc0 k) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

end FiniteDimensional

end ContDiffBump

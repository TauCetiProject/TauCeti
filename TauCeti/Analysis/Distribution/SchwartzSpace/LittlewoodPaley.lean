/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import TauCeti.Analysis.Calculus.BumpFunction.LittlewoodPaley
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Littlewood–Paley pieces of a Mihlin symbol

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real normed space, and let
`ψⱼ ξ = φ (2^{-j} ξ) - φ (2^{1-j} ξ)` be the dyadic Littlewood–Paley cutoffs built from it
(`ContDiffBump.littlewoodPaley`), which form a smooth partition of unity of `E \ {0}` with each
`ψⱼ` supported in the annulus `2^{j-1} φ.rIn ≤ ‖ξ‖ ≤ 2^j φ.rOut`.

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

section FiniteDimensional

variable [FiniteDimensional ℝ E] (φ : ContDiffBump (0 : E)) {m : E → F}

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

/-- The piece `ψⱼ • m`, as a function. -/
theorem coe_littlewoodPaleyPiece (hm : ContDiffOn ℝ ∞ m {0}ᶜ) (j : ℤ) :
    ⇑(φ.littlewoodPaleyPiece hm j) = fun ξ ↦ φ.littlewoodPaley j ξ • m ξ :=
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
    rw [zpow_sub_one₀ two_ne_zero]
    simp only [div_pow, mul_pow, inv_pow]
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
  rw [coe_littlewoodPaleyPiece]
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

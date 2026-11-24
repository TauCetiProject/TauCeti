/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Algebra.Field.GeomSum
import TauCeti.Analysis.Asymptotics.Sum.Rpow
import TauCeti.Analysis.SpecialFunctions.Pow.ForwardDiff

/-!
# Asymptotics of oscillatory and geometric power sums via summation by parts

Summation by parts converts oscillatory or alternating partial sums
`∑_{j=1}^{n-1} j^α • z^j` with `z ≠ 1` and `‖z‖ ≤ 1` into boundary terms of order `n^α` and `1`
plus a remainder weighted by the forward differences `j^α - (j + 1)^α`. Whereas the triangle
inequality (`TauCeti.norm_sum_Ico_rpow_smul_le`, paired with the uncancelled partial-sum regimes in
`TauCeti.Analysis.Asymptotics.Sum.Rpow`) only yields `O(1)` (`α < -1`), `O(log n)` (`α = -1`), or
`O(n^{α+1})` (`α > -1`), expanding `j^α - (j + 1)^α = -α j^{α-1} + O(α (α - 1) j^{α-2})` gains a
full power of `n` for `α ≥ 0` (improving `O(n^{α+1})` to `O(n^α)`) and makes the partial sums
`O(1)` across `-1 ≤ α ≤ 0` (eliminating growth on `-1 < α ≤ 0` and the `log n` divergence at
`α = -1`):

1. **Exact summation by parts for oscillatory real-power sums.** Specializing
   `TauCeti.sum_Ico_smul_pow_eq` to `z = e^{iβ} ≠ 1` and `1 ≤ n` gives
   `∑_{j=1}^{n-1} e^{ijβ} j^α = (e^{iβ} / (e^{iβ} - 1)) *
     (e^{i(n-1)β} n^α - 1 + ∑_{j=1}^{n-1} e^{ijβ} (j^α - (j + 1)^α))`.
2. **Asymptotic reduction, uniform order bound, and leading-term approximation.** In any real
   normed division ring `𝕜` (covering real alternating sums `z = -1`, complex oscillatory sums
   `z = e^{iβ}`, and unit quaternions), for every `z ≠ 1` with `‖z‖ ≤ 1` and every real `α`,
   writing `S_z(α, n) := ∑_{j=1}^{n-1} j^α • z^j`:
   * one-step reduction:
     `S_z(α, n) = n^α • (z^n / (z - 1)) - (z / (z - 1)) * (α • S_z(α - 1, n)) + O(n^{α-1} + 1)`;
   * uniform order improvement: `S_z(α, n) = O(n^α + 1)`;
   * resubstituted leading-term approximation:
     `S_z(α, n) = n^α • (z^n / (z - 1)) + O(n^{α-1} + 1)`, specializing to `O(n^{α-1})` when
     `1 ≤ α` and `O(1)` when `α ≤ 1`.

Specializing `𝕜 = ℂ` and `z = e^{iβ}` with `e^{iβ} ≠ 1` (so `‖z‖ = 1` holds automatically) yields
the oscillatory approximation
`∑_{j=1}^{n-1} e^{ijβ} j^α = e^{inβ} / (e^{iβ} - 1) * n^α + O(n^{α-1} + 1)`.

## Main results

* `TauCeti.norm_sum_Ico_rpow_smul_le` and `TauCeti.norm_sum_Ico_cexp_mul_rpow_le`: triangle
  inequality bounds for bounded-norm and oscillatory weights.
* `TauCeti.sum_Ico_cexp_mul_rpow_eq`: exact summation by parts for oscillatory real-power sums.
* `TauCeti.isBigO_sum_Ico_rpow_smul_pow_sub_sub`, `TauCeti.isBigO_sum_Ico_rpow_smul_pow`,
  `TauCeti.isBigO_sum_Ico_rpow_smul_pow_sub`,
  `TauCeti.isBigO_sum_Ico_rpow_smul_pow_sub_of_one_le`, and
  `TauCeti.isBigO_sum_Ico_rpow_smul_pow_sub_one_of_le_one`: general normed-division-ring
  asymptotics.
* `TauCeti.isBigO_sum_Ico_cexp_mul_rpow_sub_sub`, `TauCeti.isBigO_sum_Ico_cexp_mul_rpow`, and
  `TauCeti.isBigO_sum_Ico_cexp_mul_rpow_sub`: complex oscillatory specializations.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(ii), formulas 2.10.9, 2.10.12,
  2.10.14, and 2.10.16–2.10.18.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §4.
-/

public section

open Asymptotics Filter Finset

namespace TauCeti

/-! ### Triangle-inequality bounds and exact summation by parts -/

/-- **Triangle-inequality bound for bounded-norm vector weights (DLMF 2.10.12, general form).**
Whenever `‖u j‖ ≤ 1` for `1 ≤ j < n`, `‖∑_{j=1}^{n-1} j^α • u j‖ ≤ ∑_{j=1}^{n-1} j^α`. -/
theorem norm_sum_Ico_rpow_smul_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ) {u : ℕ → E} {n : ℕ} (hu : ∀ j ∈ Ico 1 n, ‖u j‖ ≤ 1) :
    ‖∑ j ∈ Ico 1 n, (j : ℝ) ^ α • u j‖ ≤ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α :=
  (norm_sum_le _ _).trans <| sum_le_sum fun j hj ↦ by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (hu j hj)

/-- **Triangle-inequality bound for oscillatory power sums (DLMF 2.10.12).** For all real `α`, `β`
and natural `n`, `‖∑_{j=1}^{n-1} e^{ijβ} j^α‖ ≤ ∑_{j=1}^{n-1} j^α`. -/
theorem norm_sum_Ico_cexp_mul_rpow_le (α β : ℝ) (n : ℕ) :
    ‖∑ j ∈ Ico 1 n, Complex.exp (j * β * Complex.I) * ↑((j : ℝ) ^ α)‖ ≤
      ∑ j ∈ Ico 1 n, (j : ℝ) ^ α := by
  have heq : ∀ j : ℕ, Complex.exp (j * β * Complex.I) * ↑((j : ℝ) ^ α) =
      (j : ℝ) ^ α • Complex.exp (j * β * Complex.I) := fun j ↦ by
    rw [Complex.real_smul, mul_comm]
  simp_rw [heq]
  exact norm_sum_Ico_rpow_smul_le α fun j _ ↦ by
    have : (j : ℂ) * (β : ℂ) * Complex.I = ((j * β : ℝ) : ℂ) * Complex.I := by push_cast; rfl
    rw [this, Complex.norm_exp_ofReal_mul_I]

/-- **Exact summation by parts for oscillatory real-power sums (DLMF 2.10.14).** For `e^{iβ} ≠ 1`
and `1 ≤ n`,
`∑_{j=1}^{n-1} e^{ijβ} j^α = (e^{iβ} / (e^{iβ} - 1)) *
  (e^{i(n-1)β} n^α - 1 + ∑_{j=1}^{n-1} e^{ijβ} (j^α - (j + 1)^α))`. -/
theorem sum_Ico_cexp_mul_rpow_eq (α : ℝ) {β : ℝ} (hβ : Complex.exp (β * Complex.I) ≠ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Ico 1 n, Complex.exp (j * β * Complex.I) * ↑((j : ℝ) ^ α) =
      Complex.exp (β * Complex.I) / (Complex.exp (β * Complex.I) - 1) *
        (Complex.exp ((n - 1 : ℕ) * β * Complex.I) * ↑((n : ℝ) ^ α) - 1 +
          ∑ j ∈ Ico 1 n, Complex.exp (j * β * Complex.I) *
            ↑((j : ℝ) ^ α - ((j + 1 : ℕ) : ℝ) ^ α)) := by
  let z : ℂ := Complex.exp (β * Complex.I)
  have hpow : ∀ k : ℕ, Complex.exp (k * β * Complex.I) = z ^ k := fun k ↦ by
    simpa only [z, mul_assoc] using Complex.exp_natCast_mul k (β * Complex.I)
  have h := sum_Ico_smul_pow_eq (fun j : ℕ ↦ (j : ℝ) ^ α) hβ hn
  simp only [Nat.cast_one, Real.one_rpow, one_smul, Complex.real_smul, pow_one] at h
  simp_rw [hpow]
  have hzn : z ^ n = z * z ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ']
  have hswap : (∑ j ∈ Ico 1 n, z ^ j * ↑((j : ℝ) ^ α)) =
      ∑ j ∈ Ico 1 n, ↑((j : ℝ) ^ α) * z ^ j :=
    sum_congr rfl fun _ _ ↦ mul_comm _ _
  rw [hswap, h, hzn]
  have hsum : ∑ j ∈ Ico 1 n,
      ↑((j : ℝ) ^ α - ((j + 1 : ℕ) : ℝ) ^ α) * (z ^ (j + 1) / (z - 1)) =
      (z / (z - 1)) * ∑ j ∈ Ico 1 n,
        z ^ j * ↑((j : ℝ) ^ α - ((j + 1 : ℕ) : ℝ) ^ α) := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [pow_succ']
    ring
  rw [hsum]
  ring

/-! ### Asymptotics of power-weighted geometric and oscillatory sums -/

/-- Remainder sum bound for one summation-by-parts step: the sum of second-order forward-difference
errors against `z ^ (j + 1) / (z - 1)` is `O(n ^ (α - 1) + 1)` for all real `α`. -/
private theorem isBigO_sum_Ico_forwardDiff_err_smul {𝕜 : Type*} [NormedDivisionRing 𝕜]
    [NormedSpace ℝ 𝕜] (α : ℝ) {z : 𝕜} (hzn : ‖z‖ ≤ 1) :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n,
      (((j : ℝ) ^ α - ((j + 1 : ℕ) : ℝ) ^ α) + α * (j : ℝ) ^ (α - 1)) •
        (z ^ (j + 1) / (z - 1))) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (α - 1) + 1 := by
  rcases eq_or_ne α 1 with rfl | hα₁
  · refine (isBigO_zero _ _).congr' (Eventually.of_forall fun n ↦ ?_) .rfl
    symm
    refine sum_eq_zero fun j _ ↦ ?_
    simp [Real.rpow_one, Real.rpow_zero]
  · let K : ℝ := 2⁻¹ * max 1 (2 ^ (α - 2)) * |α * (α - 1)| * ‖(z - 1)⁻¹‖
    have hle : (fun n : ℕ ↦ ∑ j ∈ Ico 1 n,
        (((j : ℝ) ^ α - ((j + 1 : ℕ) : ℝ) ^ α) + α * (j : ℝ) ^ (α - 1)) •
          (z ^ (j + 1) / (z - 1))) =O[atTop]
        fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ (α - 2) := by
      refine .of_bound K (Eventually.of_forall fun n ↦ ?_)
      rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity), mul_sum]
      refine (norm_sum_le _ _).trans (sum_le_sum fun j hj ↦ ?_)
      have hj₁ : (1 : ℝ) ≤ j := Nat.one_le_cast.mpr (mem_Ico.mp hj).1
      have herr := Real.abs_rpow_sub_add_one_rpow_add_mul_le α hj₁
      rw [← Nat.cast_add_one] at herr
      have hzpow : ‖z ^ (j + 1) / (z - 1)‖ ≤ ‖(z - 1)⁻¹‖ := by
        rw [div_eq_mul_inv, norm_mul, norm_pow]
        exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg z) hzn)
      rw [norm_smul, Real.norm_eq_abs]
      calc |((j : ℝ) ^ α - ((j + 1 : ℕ) : ℝ) ^ α) + α * (j : ℝ) ^ (α - 1)| *
            ‖z ^ (j + 1) / (z - 1)‖
          ≤ (2⁻¹ * max 1 (2 ^ (α - 2)) * |α * (α - 1)| * (j : ℝ) ^ (α - 2)) * ‖(z - 1)⁻¹‖ :=
            mul_le_mul herr hzpow (norm_nonneg _) (by positivity)
        _ = K * (j : ℝ) ^ (α - 2) := by simp only [K]; ring
    have hsum := isBigO_sum_Ico_rpow_rpow_add_one_add_one_iff (α := α - 2).mpr
      (fun h ↦ hα₁ (by linarith))
    have hexp : α - 2 + 1 = α - 1 := by ring
    simpa only [hexp] using hle.trans hsum

/-- **One-step summation-by-parts asymptotic reduction (DLMF 2.10.16, general form).** In any real
normed division ring `𝕜`, for `z ≠ 1` with `‖z‖ ≤ 1` and every real `α`,
`(∑_{j=1}^{n-1} j^α • z^j) - (n^α • (z^n / (z - 1))
  - (z / (z - 1)) * (α • ∑_{j=1}^{n-1} j^{α-1} • z^j)) = O(n^{α-1} + 1)`. -/
theorem isBigO_sum_Ico_rpow_smul_pow_sub_sub {𝕜 : Type*} [NormedDivisionRing 𝕜]
    [NormedSpace ℝ 𝕜] (α : ℝ) {z : 𝕜} (hz : z ≠ 1) (hzn : ‖z‖ ≤ 1) :
    (fun n : ℕ ↦ (∑ j ∈ Ico 1 n, (j : ℝ) ^ α • z ^ j) -
      ((n : ℝ) ^ α • (z ^ n / (z - 1)) -
        (z / (z - 1)) * (α • ∑ j ∈ Ico 1 n, (j : ℝ) ^ (α - 1) • z ^ j))) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (α - 1) + 1 := by
  have hconst : (fun _ : ℕ ↦ -(z / (z - 1))) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (α - 1) + 1 := by
    refine .of_bound ‖z / (z - 1)‖ (Eventually.of_forall fun n ↦ ?_)
    have hnn : 0 ≤ (n : ℝ) ^ (α - 1) := by positivity
    rw [norm_neg, Real.norm_of_nonneg (by positivity)]
    nlinarith [norm_nonneg (z / (z - 1))]
  refine (hconst.add (isBigO_sum_Ico_forwardDiff_err_smul α hzn)).congr' ?_ .rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hid := sum_Ico_smul_pow_eq (fun j : ℕ ↦ (j : ℝ) ^ α) hz hn
  rw [Nat.cast_one, Real.one_rpow, one_smul, pow_one] at hid
  have hcomm : Commute z (z - 1)⁻¹ :=
    ((Commute.refl z).sub_right (Commute.one_right z)).inv_right₀
  have : SMulCommClass ℝ 𝕜 𝕜 :=
    ⟨fun r a b ↦ (map_real_smul (AddMonoidHom.mulLeft a) (continuous_const_mul a) r b).symm⟩
  have hlin : (z / (z - 1)) * (α • ∑ j ∈ Ico 1 n, (j : ℝ) ^ (α - 1) • z ^ j) =
      ∑ j ∈ Ico 1 n, (α * (j : ℝ) ^ (α - 1)) • (z ^ (j + 1) / (z - 1)) := by
    rw [smul_sum, mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [smul_smul, mul_smul_comm, div_eq_mul_inv, div_eq_mul_inv, pow_succ',
      mul_assoc z (z ^ j), (hcomm.pow_left j).eq, ← mul_assoc]
  rw [hid, hlin]
  have hsplit : ∑ j ∈ Ico 1 n,
      (((j : ℝ) ^ α - ((j + 1 : ℕ) : ℝ) ^ α) + α * (j : ℝ) ^ (α - 1)) •
        (z ^ (j + 1) / (z - 1)) =
      (∑ j ∈ Ico 1 n, ((j : ℝ) ^ α - ((j + 1 : ℕ) : ℝ) ^ α) • (z ^ (j + 1) / (z - 1))) +
        ∑ j ∈ Ico 1 n, (α * (j : ℝ) ^ (α - 1)) • (z ^ (j + 1) / (z - 1)) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun _ _ ↦ add_smul _ _ _
  rw [hsplit]
  abel

/-- **Uniform order bound for power-weighted geometric sums (DLMF 2.10.17, general form).**
In any real normed division ring `𝕜`, for `z ≠ 1` with `‖z‖ ≤ 1` and every real `α`,
`∑_{j=1}^{n-1} j^α • z^j = O(n^α + 1)` as `n → ∞`. -/
theorem isBigO_sum_Ico_rpow_smul_pow {𝕜 : Type*} [NormedDivisionRing 𝕜] [NormedSpace ℝ 𝕜]
    (α : ℝ) {z : 𝕜} (hz : z ≠ 1) (hzn : ‖z‖ ≤ 1) :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α • z ^ j) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ α + 1 := by
  suffices ∀ k : ℕ, ∀ β : ℝ, β < -1 + k →
      (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ β • z ^ j) =O[atTop]
        fun n : ℕ ↦ (n : ℝ) ^ β + 1 by
    exact this (⌈α + 1⌉₊ + 1) α (by push_cast; linarith [Nat.le_ceil (α + 1)])
  intro k
  induction k with
  | zero =>
    intro β hβ
    rw [Nat.cast_zero, add_zero] at hβ
    have hnorm : (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ β • z ^ j) =O[atTop]
        fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ β := by
      refine .of_bound 1 (Eventually.of_forall fun n ↦ ?_)
      rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity), one_mul]
      exact norm_sum_Ico_rpow_smul_le β fun j _ ↦
        (norm_pow z j).le.trans (pow_le_one₀ (norm_nonneg z) hzn)
    refine (hnorm.trans (isBigO_sum_Ico_rpow_one_iff.mpr hβ)).trans
      (.of_bound 1 (Eventually.of_forall fun n ↦ ?_))
    have hnn : 0 ≤ (n : ℝ) ^ β := by positivity
    rw [norm_one, Real.norm_of_nonneg (by positivity), one_mul]
    linarith
  | succ k ih =>
    intro β hβ
    have hprev := ih (β - 1) (by push_cast at hβ ⊢; linarith)
    have hlead : (fun n : ℕ ↦ (n : ℝ) ^ β • (z ^ n / (z - 1))) =O[atTop]
        fun n : ℕ ↦ (n : ℝ) ^ β + 1 := by
      refine .of_bound ‖(z - 1)⁻¹‖ (Eventually.of_forall fun n ↦ ?_)
      have hnn : 0 ≤ (n : ℝ) ^ β := by positivity
      have hzpow : ‖z ^ n / (z - 1)‖ ≤ ‖(z - 1)⁻¹‖ := by
        rw [div_eq_mul_inv, norm_mul, norm_pow]
        exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg z) hzn)
      rw [norm_smul, Real.norm_of_nonneg hnn, Real.norm_of_nonneg (by positivity)]
      calc (n : ℝ) ^ β * ‖z ^ n / (z - 1)‖ ≤ (n : ℝ) ^ β * ‖(z - 1)⁻¹‖ :=
            mul_le_mul_of_nonneg_left hzpow hnn
        _ ≤ ‖(z - 1)⁻¹‖ * ((n : ℝ) ^ β + 1) := by nlinarith [norm_nonneg (z - 1)⁻¹]
    have hscale : (fun n : ℕ ↦ (n : ℝ) ^ (β - 1) + 1) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ β + 1 := by
      refine .of_bound 1 ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hle := Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn)
        (by linarith : β - 1 ≤ β)
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
      linarith
    have hsub := ((isBigO_sum_Ico_rpow_smul_pow_sub_sub β hz hzn).sub
      ((hprev.const_smul_left β).const_mul_left (z / (z - 1)))).trans hscale
    exact (hlead.add hsub).congr_left fun n ↦ by
      simp only [Pi.smul_apply]
      abel

/-- **Leading-term asymptotic approximation via summation by parts (DLMF 2.10.18, general form).**
In any real normed division ring `𝕜`, for `z ≠ 1` with `‖z‖ ≤ 1` and every real `α`,
`∑_{j=1}^{n-1} j^α • z^j - n^α • (z^n / (z - 1)) = O(n^{α-1} + 1)` as `n → ∞`. -/
theorem isBigO_sum_Ico_rpow_smul_pow_sub {𝕜 : Type*} [NormedDivisionRing 𝕜] [NormedSpace ℝ 𝕜]
    (α : ℝ) {z : 𝕜} (hz : z ≠ 1) (hzn : ‖z‖ ≤ 1) :
    (fun n : ℕ ↦ (∑ j ∈ Ico 1 n, (j : ℝ) ^ α • z ^ j) -
      (n : ℝ) ^ α • (z ^ n / (z - 1))) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (α - 1) + 1 := by
  have hstep := isBigO_sum_Ico_rpow_smul_pow_sub_sub α hz hzn
  have hprev := ((isBigO_sum_Ico_rpow_smul_pow (α - 1) hz hzn).const_smul_left α).const_mul_left
    (z / (z - 1))
  exact (hstep.sub hprev).congr_left fun n ↦ by
    simp only [Pi.smul_apply]
    abel

/-- For `1 ≤ α`, `z ≠ 1`, and `‖z‖ ≤ 1`, the remainder in summation by parts is purely
`O(n^{α-1})`. -/
theorem isBigO_sum_Ico_rpow_smul_pow_sub_of_one_le {𝕜 : Type*} [NormedDivisionRing 𝕜]
    [NormedSpace ℝ 𝕜] {α : ℝ} (hα : 1 ≤ α) {z : 𝕜} (hz : z ≠ 1) (hzn : ‖z‖ ≤ 1) :
    (fun n : ℕ ↦ (∑ j ∈ Ico 1 n, (j : ℝ) ^ α • z ^ j) -
      (n : ℝ) ^ α • (z ^ n / (z - 1))) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (α - 1) := by
  refine (isBigO_sum_Ico_rpow_smul_pow_sub α hz hzn).trans (.of_bound 2 ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (α - 1) :=
    Real.one_le_rpow (Nat.one_le_cast.mpr hn) (by linarith)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  linarith

/-- For `α ≤ 1`, `z ≠ 1`, and `‖z‖ ≤ 1`, the remainder in summation by parts is `O(1)`. -/
theorem isBigO_sum_Ico_rpow_smul_pow_sub_one_of_le_one {𝕜 : Type*} [NormedDivisionRing 𝕜]
    [NormedSpace ℝ 𝕜] {α : ℝ} (hα : α ≤ 1) {z : 𝕜} (hz : z ≠ 1) (hzn : ‖z‖ ≤ 1) :
    (fun n : ℕ ↦ (∑ j ∈ Ico 1 n, (j : ℝ) ^ α • z ^ j) -
      (n : ℝ) ^ α • (z ^ n / (z - 1))) =O[atTop]
      fun _ : ℕ ↦ (1 : ℝ) := by
  refine (isBigO_sum_Ico_rpow_smul_pow_sub α hz hzn).trans (.of_bound 2 ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : (n : ℝ) ^ (α - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.mpr hn) (by linarith)
  rw [Real.norm_of_nonneg (by positivity), norm_one]
  linarith

/-- Rewriting helper identifying `e^{ijβ} j^α` with `(j : ℝ) ^ α • (e^{iβ}) ^ j`. -/
private theorem cexp_mul_rpow_eq_smul_pow (α β : ℝ) (j : ℕ) :
    Complex.exp (j * β * Complex.I) * ↑((j : ℝ) ^ α) =
      (j : ℝ) ^ α • Complex.exp (β * Complex.I) ^ j := by
  rw [Complex.real_smul, mul_comm, ← Complex.exp_natCast_mul, mul_assoc]

/-- **One-step summation-by-parts reduction for oscillatory power sums (DLMF 2.10.16).** For all
real `α`, `β` with `e^{iβ} ≠ 1`,
`∑_{j=1}^{n-1} e^{ijβ} j^α - (e^{inβ} / (e^{iβ} - 1) * n^α
  - α * (e^{iβ} / (e^{iβ} - 1)) * ∑_{j=1}^{n-1} e^{ijβ} j^{α-1}) = O(n^{α-1} + 1)`. -/
theorem isBigO_sum_Ico_cexp_mul_rpow_sub_sub (α : ℝ) {β : ℝ}
    (hβ : Complex.exp (β * Complex.I) ≠ 1) :
    (fun n : ℕ ↦ (∑ j ∈ Ico 1 n, Complex.exp (j * β * Complex.I) * ↑((j : ℝ) ^ α)) -
      (Complex.exp (n * β * Complex.I) / (Complex.exp (β * Complex.I) - 1) * ↑((n : ℝ) ^ α) -
        (α : ℂ) * (Complex.exp (β * Complex.I) / (Complex.exp (β * Complex.I) - 1)) *
          ∑ j ∈ Ico 1 n, Complex.exp (j * β * Complex.I) * ↑((j : ℝ) ^ (α - 1)))) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (α - 1) + 1 := by
  have hzn : ‖Complex.exp (β * Complex.I)‖ ≤ 1 :=
    (Complex.norm_exp_ofReal_mul_I β).le
  refine (isBigO_sum_Ico_rpow_smul_pow_sub_sub α hβ hzn).congr_left fun n ↦ ?_
  simp_rw [cexp_mul_rpow_eq_smul_pow, Complex.real_smul]
  have hpow : Complex.exp (n * β * Complex.I) = Complex.exp (β * Complex.I) ^ n := by
    rw [← Complex.exp_natCast_mul, mul_assoc]
  rw [hpow]
  ring

/-- **Uniform order bound for oscillatory power sums (DLMF 2.10.17).** For all real `α`, `β` with
`e^{iβ} ≠ 1`, `∑_{j=1}^{n-1} e^{ijβ} j^α = O(n^α + 1)` as `n → ∞`. -/
theorem isBigO_sum_Ico_cexp_mul_rpow (α : ℝ) {β : ℝ}
    (hβ : Complex.exp (β * Complex.I) ≠ 1) :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, Complex.exp (j * β * Complex.I) * ↑((j : ℝ) ^ α)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ α + 1 := by
  have hzn : ‖Complex.exp (β * Complex.I)‖ ≤ 1 :=
    (Complex.norm_exp_ofReal_mul_I β).le
  refine (isBigO_sum_Ico_rpow_smul_pow α hβ hzn).congr_left fun n ↦ ?_
  simp_rw [cexp_mul_rpow_eq_smul_pow]

/-- **Asymptotic approximation of oscillatory power sums (DLMF 2.10.18).** For all real `α`, `β`
with `e^{iβ} ≠ 1`,
`∑_{j=1}^{n-1} e^{ijβ} j^α - e^{inβ} / (e^{iβ} - 1) * n^α = O(n^{α-1} + 1)` as `n → ∞`. -/
theorem isBigO_sum_Ico_cexp_mul_rpow_sub (α : ℝ) {β : ℝ}
    (hβ : Complex.exp (β * Complex.I) ≠ 1) :
    (fun n : ℕ ↦ (∑ j ∈ Ico 1 n, Complex.exp (j * β * Complex.I) * ↑((j : ℝ) ^ α)) -
      Complex.exp (n * β * Complex.I) / (Complex.exp (β * Complex.I) - 1) *
        ↑((n : ℝ) ^ α)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (α - 1) + 1 := by
  have hzn : ‖Complex.exp (β * Complex.I)‖ ≤ 1 :=
    (Complex.norm_exp_ofReal_mul_I β).le
  refine (isBigO_sum_Ico_rpow_smul_pow_sub α hβ hzn).congr_left fun n ↦ ?_
  simp_rw [cexp_mul_rpow_eq_smul_pow, Complex.real_smul]
  have hpow : Complex.exp (n * β * Complex.I) = Complex.exp (β * Complex.I) ^ n := by
    rw [← Complex.exp_natCast_mul, mul_assoc]
  rw [hpow]
  ring

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Topology.Instances.RealVectorSpace
import TauCeti.Algebra.Field.GeomSum
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.ForwardDiff

/-!
# Asymptotics of oscillatory and geometric power sums via summation by parts

Summation by parts converts oscillatory or alternating partial sums
`∑_{j=1}^{n-1} j^α z^j` with `z ≠ 1` and `‖z‖ ≤ 1` into boundary terms of order `n^α` and `1` plus
a remainder weighted by the forward differences `j^α - (j + 1)^α`. Whereas the triangle inequality
only yields `O(1)` (`α < -1`), `O(log n)` (`α = -1`), or `O(n^{α+1})` (`α > -1`), expanding
`j^α - (j + 1)^α = -α j^{α-1} + O(α (α - 1) j^{α-2})` gains a full power of `n` across every
growing regime and eliminates the logarithmic divergence at `α = -1`:

1. **Uncancelled real-power partial sums.** For real `α`, the partial sum
   `∑_{j=1}^{n-1} j^α` has exact order `Θ(1)` iff `α < -1`, `Θ(log n)` iff `α = -1`, and
   `Θ(n^{α+1})` iff `-1 < α` (with the explicit upper bound `∑_{j=1}^{n-1} j^α ≤ n^{α+1} / (α + 1)`
   for every `n : ℕ` when `-1 < α`), and is `O(n^{α+1} + 1)` iff `α ≠ -1`.
2. **Exact summation by parts for oscillatory real-power sums.** Specializing
   `TauCeti.sum_Ico_smul_geom_eq` to `z = e^{iβ} ≠ 1` and `1 ≤ n` gives
   `∑_{j=1}^{n-1} e^{ijβ} j^α = (e^{iβ} / (e^{iβ} - 1)) *
     (e^{i(n-1)β} n^α - 1 + ∑_{j=1}^{n-1} e^{ijβ} (j^α - (j + 1)^α))`.
3. **Asymptotic reduction, uniform order bound, and leading-term approximation.** In any real
   normed division ring `𝕜` (covering real alternating sums `z = -1`, complex oscillatory sums
   `z = e^{iβ}`, and unit quaternions), for every `z ≠ 1` with `‖z‖ ≤ 1` and every real `α`:
   * one-step reduction:
     `S_z(α, n) = n^α • z^n / (z - 1) - (z / (z - 1)) * α • S_z(α - 1, n) + O(n^{α-1} + 1)`;
   * uniform order improvement: `S_z(α, n) = O(n^α + 1)`;
   * resubstituted leading-term approximation:
     `S_z(α, n) = n^α • z^n / (z - 1) + O(n^{α-1} + 1)`, specializing to `O(n^{α-1})` when
     `1 ≤ α` and `O(1)` when `α ≤ 1`.

Specializing `𝕜 = ℂ` and `z = e^{iβ}` with `e^{iβ} ≠ 1` (so `‖z‖ = 1` holds automatically) yields
the oscillatory approximation
`∑_{j=1}^{n-1} e^{ijβ} j^α = e^{inβ} / (e^{iβ} - 1) * n^α + O(n^{α-1} + 1)`.

## Main results

* `TauCeti.sum_Ico_rpow_le`: `∑ j ∈ Ico 1 n, (j : ℝ) ^ α ≤ (n : ℝ) ^ (α + 1) / (α + 1)` for
  `-1 < α`.
* `TauCeti.isTheta_sum_Ico_rpow_const_iff`, `TauCeti.isTheta_sum_Ico_rpow_log_iff`,
  `TauCeti.isTheta_sum_Ico_rpow_rpow_add_one_iff`, and their `IsBigO` counterparts
  `TauCeti.isBigO_sum_Ico_rpow_const_iff`, `TauCeti.isBigO_sum_Ico_rpow_log_iff`,
  `TauCeti.isBigO_sum_Ico_rpow_rpow_add_one_iff`,
  `TauCeti.isBigO_sum_Ico_rpow_rpow_add_one_add_one_iff`.
* `TauCeti.norm_sum_Ico_rpow_smul_le` and `TauCeti.norm_sum_Ico_cexp_mul_rpow_le`: triangle
  inequality bounds for bounded-norm and oscillatory weights.
* `TauCeti.sum_Ico_cexp_mul_rpow_eq`: exact summation by parts for oscillatory real-power sums.
* `TauCeti.isBigO_sum_Ico_rpow_smul_geom_sub_step`, `TauCeti.isBigO_sum_Ico_rpow_smul_geom`,
  `TauCeti.isBigO_sum_Ico_rpow_smul_geom_sub`,
  `TauCeti.isBigO_sum_Ico_rpow_smul_geom_sub_of_one_le`, and
  `TauCeti.isBigO_sum_Ico_rpow_smul_geom_sub_const_of_le_one`: general normed-division-ring
  asymptotics.
* `TauCeti.isBigO_sum_Ico_cexp_mul_rpow_sub_step`, `TauCeti.isBigO_sum_Ico_cexp_mul_rpow`, and
  `TauCeti.isBigO_sum_Ico_cexp_mul_rpow_sub`: complex oscillatory specializations.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(ii), formulas 2.10.9–2.10.12,
  2.10.14, and 2.10.16–2.10.18.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §4.
-/

public section

open Asymptotics Filter Finset Topology

namespace TauCeti

/-! ### Growth of uncancelled real-power partial sums -/

/-- **Explicit upper bound on partial sums of real powers.** For `-1 < α` and every natural number
`n`, `∑ j ∈ Ico 1 n, (j : ℝ) ^ α ≤ (n : ℝ) ^ (α + 1) / (α + 1)`. -/
theorem sum_Ico_rpow_le {α : ℝ} (hα : -1 < α) (n : ℕ) :
    ∑ j ∈ Ico 1 n, (j : ℝ) ^ α ≤ (n : ℝ) ^ (α + 1) / (α + 1) := by
  have hα₁ : 0 < α + 1 := by linarith
  rcases eq_or_ne n 0 with rfl | hn₀
  · simp [Real.zero_rpow hα₁.ne']
  have hn₁ : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn₀
  rcases le_total 0 α with hα₀ | hα₀
  · have hstep : ∀ j ∈ Ico 1 n,
        (j : ℝ) ^ α ≤ (((j + 1 : ℕ) : ℝ) ^ (α + 1) - (j : ℝ) ^ (α + 1)) / (α + 1) := by
      intro j _
      have h := Real.rpow_add_mul_rpow_sub_one_mul_sub_le_rpow (p := α + 1)
        (u := (j + 1 : ℕ)) (v := j) (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      rw [add_sub_cancel_right, Nat.cast_add, Nat.cast_one, add_sub_cancel_left, mul_one] at h
      rw [le_div_iff₀ hα₁, Nat.cast_add, Nat.cast_one]
      linarith
    calc ∑ j ∈ Ico 1 n, (j : ℝ) ^ α
        ≤ ∑ j ∈ Ico 1 n, (((j + 1 : ℕ) : ℝ) ^ (α + 1) - (j : ℝ) ^ (α + 1)) / (α + 1) :=
          sum_le_sum hstep
      _ = ((n : ℝ) ^ (α + 1) - (1 : ℝ) ^ (α + 1)) / (α + 1) := by
          rw [← sum_div, sum_Ico_sub (fun k : ℕ ↦ (k : ℝ) ^ (α + 1)) hn₁, Nat.cast_one]
      _ ≤ (n : ℝ) ^ (α + 1) / (α + 1) := by
          rw [Real.one_rpow]
          exact div_le_div_of_nonneg_right (by linarith) hα₁.le
  · calc ∑ j ∈ Ico 1 n, (j : ℝ) ^ α
        ≤ ∑ j ∈ Ico 1 n, ((j : ℝ) ^ (α + 1) - ((j - 1 : ℕ) : ℝ) ^ (α + 1)) / (α + 1) :=
          sum_le_sum fun j hj ↦ by
            rw [Nat.cast_sub (mem_Ico.mp hj).1, Nat.cast_one]
            exact Real.rpow_le_rpow_sub_sub_one_rpow_div hα hα₀
              (Nat.one_le_cast.mpr (mem_Ico.mp hj).1)
      _ = (((n - 1 : ℕ) : ℝ) ^ (α + 1) - (0 : ℝ) ^ (α + 1)) / (α + 1) := by
          have htel : ∑ j ∈ Ico 1 n, ((j : ℝ) ^ (α + 1) - ((j - 1 : ℕ) : ℝ) ^ (α + 1)) =
              ((n - 1 : ℕ) : ℝ) ^ (α + 1) - (0 : ℝ) ^ (α + 1) := by
            simpa only [Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero] using
              sum_Ico_sub (fun k : ℕ ↦ ((k - 1 : ℕ) : ℝ) ^ (α + 1)) hn₁
          rw [← sum_div, htel]
      _ ≤ (n : ℝ) ^ (α + 1) / (α + 1) := by
          rw [Real.zero_rpow hα₁.ne', sub_zero]
          exact div_le_div_of_nonneg_right
            (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le n 1) hα₁.le)
            hα₁.le

/-- Lower bound matching `sum_Ico_rpow_le` for `-1 < α`: `(n : ℝ) ^ (α + 1) = O(∑_{j=1}^{n-1} j^α)`
as `n → ∞`. -/
private theorem isBigO_rpow_add_one_sum_Ico_rpow {α : ℝ} (hα : -1 < α) :
    (fun n : ℕ ↦ (n : ℝ) ^ (α + 1)) =O[atTop] fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α := by
  have hα₁ : 0 < α + 1 := by linarith
  rcases le_total 0 α with hα₀ | hα₀
  · refine .of_bound ((2 : ℝ) ^ (α + 1) * (α + 1)) ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hstep : ∀ j ∈ Ico 1 n,
        ((j : ℝ) ^ (α + 1) - ((j - 1 : ℕ) : ℝ) ^ (α + 1)) / (α + 1) ≤ (j : ℝ) ^ α := by
      intro j hj
      have h := Real.rpow_add_mul_rpow_sub_one_mul_sub_le_rpow (p := α + 1)
        (u := (j - 1 : ℕ)) (v := j) (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      rw [add_sub_cancel_right, Nat.cast_sub (mem_Ico.mp hj).1, Nat.cast_one] at h
      rw [div_le_iff₀ hα₁, Nat.cast_sub (mem_Ico.mp hj).1, Nat.cast_one]
      linarith
    have htel : (((n - 1 : ℕ) : ℝ) ^ (α + 1)) / (α + 1) ≤ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α := by
      have hs := sum_le_sum hstep
      have ht : ∑ j ∈ Ico 1 n, ((j : ℝ) ^ (α + 1) - ((j - 1 : ℕ) : ℝ) ^ (α + 1)) =
          ((n - 1 : ℕ) : ℝ) ^ (α + 1) - (0 : ℝ) ^ (α + 1) := by
        simpa only [Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero] using
          sum_Ico_sub (fun k : ℕ ↦ ((k - 1 : ℕ) : ℝ) ^ (α + 1)) (by omega : 1 ≤ n)
      rwa [← sum_div, ht, Real.zero_rpow hα₁.ne', sub_zero] at hs
    have hhalf : (n : ℝ) / 2 ≤ ((n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hpow := Real.rpow_le_rpow (by positivity) hhalf hα₁.le
    rw [Real.div_rpow (Nat.cast_nonneg n) zero_le_two, div_le_iff₀ (by positivity)] at hpow
    rw [div_le_iff₀ hα₁] at htel
    rw [Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity)]
    calc (n : ℝ) ^ (α + 1) ≤ ((n - 1 : ℕ) : ℝ) ^ (α + 1) * (2 : ℝ) ^ (α + 1) := hpow
      _ ≤ ((∑ j ∈ Ico 1 n, (j : ℝ) ^ α) * (α + 1)) * (2 : ℝ) ^ (α + 1) :=
          mul_le_mul_of_nonneg_right htel (by positivity)
      _ = (2 : ℝ) ^ (α + 1) * (α + 1) * ∑ j ∈ Ico 1 n, (j : ℝ) ^ α := by ring
  · refine .of_bound (2 * (α + 1)) ?_
    have htend : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (α + 1)) atTop atTop :=
      (tendsto_rpow_atTop hα₁).comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 1, htend.eventually_ge_atTop 2] with n hn hn₂
    have htel : ((n : ℝ) ^ (α + 1) - 1) / (α + 1) ≤ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α := by
      have hs := sum_le_sum (s := Ico 1 n) fun j hj ↦ by
        simpa only [← Nat.cast_add_one] using
          Real.add_one_rpow_sub_rpow_div_le_rpow hα₀ (Nat.cast_pos.mpr (mem_Ico.mp hj).1)
      rwa [← sum_div, sum_Ico_sub (fun k : ℕ ↦ (k : ℝ) ^ (α + 1)) hn, Nat.cast_one,
        Real.one_rpow] at hs
    rw [Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity)]
    have hmul := mul_le_mul_of_nonneg_left htel (by positivity : 0 ≤ 2 * (α + 1))
    field_simp at hmul
    linarith

/-- For `α = -1`, `∑ j ∈ Ico 1 n, (j : ℝ) ^ (-1 : ℝ) = Θ(log n)` as `n → ∞`. -/
private theorem isTheta_sum_Ico_rpow_neg_one_log :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ (-1 : ℝ)) =Θ[atTop] fun n : ℕ ↦ Real.log n := by
  have heq : ∀ n : ℕ, 1 ≤ n →
      ∑ j ∈ Ico 1 n, (j : ℝ) ^ (-1 : ℝ) = (harmonic (n - 1) : ℝ) := by
    intro n hn
    rw [harmonic_eq_sum_Icc, Rat.cast_sum, ← Ico_add_one_right_eq_Icc, Nat.sub_add_cancel hn]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [Real.rpow_neg_one, Rat.cast_inv, Rat.cast_natCast]
  refine ⟨.of_bound 2 ?_, .of_bound 1 ?_⟩
  · have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 2, hlog.eventually_ge_atTop 1] with n _ hln
    rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity), heq n (by omega),
      Real.norm_of_nonneg (by linarith)]
    have h₁ : (harmonic (n - 1) : ℝ) ≤ 1 + Real.log (n - 1 : ℕ) := harmonic_le_one_add_log (n - 1)
    have h₂ : Real.log (n - 1 : ℕ) ≤ Real.log n :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast Nat.sub_le n 1)
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hlog_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    rw [Real.norm_of_nonneg hlog_nn, Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity),
      heq n hn, one_mul]
    simpa only [Nat.sub_add_cancel hn] using log_add_one_le_harmonic (n - 1)

/-- **Boundedness characterization of real-power partial sums.** `∑_{j=1}^{n-1} j^α = O(1)` as
`n → ∞` if and only if `α < -1`. -/
theorem isBigO_sum_Ico_rpow_const_iff {α : ℝ} :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α) =O[atTop] (fun _ : ℕ ↦ (1 : ℝ)) ↔ α < -1 := by
  constructor
  · intro h
    by_contra! hα
    have hmono : (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ (-1 : ℝ)) =O[atTop]
        fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α := by
      refine .of_bound 1 (Eventually.of_forall fun n ↦ ?_)
      rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity),
        Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity), one_mul]
      exact sum_le_sum fun j hj ↦
        Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (mem_Ico.mp hj).1) hα
    have hlo := (Real.isLittleO_const_log_atTop (c := (1 : ℝ)).comp_tendsto
      tendsto_natCast_atTop_atTop).trans_isBigO
      (isTheta_sum_Ico_rpow_neg_one_log.2.trans (hmono.trans h))
    obtain ⟨_, hhalf⟩ := (hlo.def one_half_pos).exists
    dsimp only [Function.comp_apply] at hhalf
    norm_num at hhalf
  · intro hα
    have hsum : Summable (fun j : ℕ ↦ (j : ℝ) ^ α) := Real.summable_nat_rpow.mpr hα
    refine .of_bound (∑' j : ℕ, (j : ℝ) ^ α) (Eventually.of_forall fun n ↦ ?_)
    rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity), norm_one, mul_one]
    exact hsum.sum_le_tsum (Ico 1 n) fun j _ ↦ by positivity

/-- **Exact `Θ(1)` characterization of real-power partial sums.** `∑_{j=1}^{n-1} j^α = Θ(1)` as
`n → ∞` if and only if `α < -1`. -/
theorem isTheta_sum_Ico_rpow_const_iff {α : ℝ} :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α) =Θ[atTop] (fun _ : ℕ ↦ (1 : ℝ)) ↔ α < -1 := by
  refine ⟨fun h ↦ isBigO_sum_Ico_rpow_const_iff.mp h.1,
    fun hα ↦ ⟨isBigO_sum_Ico_rpow_const_iff.mpr hα, ?_⟩⟩
  refine .of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [norm_one, Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity), one_mul]
  have h1 : ((1 : ℕ) : ℝ) ^ α ≤ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α :=
    single_le_sum (f := fun j : ℕ ↦ (j : ℝ) ^ α) (fun j _ ↦ by positivity)
      (mem_Ico.mpr ⟨le_rfl, hn⟩)
  simpa using h1

/-- **Logarithmic big-O characterization of real-power partial sums.**
`∑_{j=1}^{n-1} j^α = O(log n)` as `n → ∞` if and only if `α ≤ -1`. -/
theorem isBigO_sum_Ico_rpow_log_iff {α : ℝ} :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α) =O[atTop] (fun n : ℕ ↦ Real.log n) ↔ α ≤ -1 := by
  constructor
  · intro h
    by_contra! hα
    have hpow := (isBigO_rpow_add_one_sum_Ico_rpow hα).trans h
    have hlo : (fun n : ℕ ↦ Real.log n) =o[atTop] fun n : ℕ ↦ (n : ℝ) ^ (α + 1) :=
      (isLittleO_log_rpow_atTop (by linarith : 0 < α + 1)).comp_tendsto tendsto_natCast_atTop_atTop
    have hlt := hpow.trans_isLittleO hlo
    obtain ⟨n, hn, hhalf⟩ := ((eventually_gt_atTop 0).and (hlt.def one_half_pos)).exists
    have hpos : 0 < ‖(n : ℝ) ^ (α + 1)‖ :=
      norm_pos_iff.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _).ne'
    linarith
  · intro hα
    rcases hα.lt_or_eq with hlt | rfl
    · exact (isBigO_sum_Ico_rpow_const_iff.mpr hlt).trans
        (Real.isLittleO_const_log_atTop.comp_tendsto tendsto_natCast_atTop_atTop).isBigO
    · exact isTheta_sum_Ico_rpow_neg_one_log.1

/-- **Exact `Θ(log n)` characterization of real-power partial sums.**
`∑_{j=1}^{n-1} j^α = Θ(log n)` as `n → ∞` if and only if `α = -1`. -/
theorem isTheta_sum_Ico_rpow_log_iff {α : ℝ} :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α) =Θ[atTop] (fun n : ℕ ↦ Real.log n) ↔ α = -1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ isTheta_sum_Ico_rpow_neg_one_log⟩
  have hle : α ≤ -1 := isBigO_sum_Ico_rpow_log_iff.mp h.1
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    have hlo := (Real.isLittleO_const_log_atTop (c := (1 : ℝ)).comp_tendsto
      tendsto_natCast_atTop_atTop).trans_isBigO
      (h.2.trans (isBigO_sum_Ico_rpow_const_iff.mpr hlt))
    obtain ⟨_, hhalf⟩ := (hlo.def one_half_pos).exists
    dsimp only [Function.comp_apply] at hhalf
    norm_num at hhalf
  · exact heq

/-- **Power-growth big-O characterization of real-power partial sums.**
`∑_{j=1}^{n-1} j^α = O(n^{α+1})` as `n → ∞` if and only if `-1 < α`. -/
theorem isBigO_sum_Ico_rpow_rpow_add_one_iff {α : ℝ} :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (α + 1)) ↔
      -1 < α := by
  constructor
  · intro h
    by_contra! hα
    rcases hα.lt_or_eq with hlt | rfl
    · have hone := (isTheta_sum_Ico_rpow_const_iff.mpr hlt).2.trans h
      have hzero : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (α + 1)) atTop (𝓝 0) :=
        ((tendsto_rpow_neg_atTop (by linarith : 0 < -(α + 1))).comp
          tendsto_natCast_atTop_atTop).congr fun n ↦ by
            dsimp only [Function.comp_apply]
            rw [neg_neg]
      have hlim := hone.trans_tendsto hzero
      exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)
    · have hbdd : (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ (-1 : ℝ)) =O[atTop]
          fun _ : ℕ ↦ (1 : ℝ) := by
        simpa only [neg_add_cancel, Real.rpow_zero] using h
      exact (lt_irrefl (-1 : ℝ)) (isBigO_sum_Ico_rpow_const_iff.mp hbdd)
  · intro hα
    refine .of_bound (α + 1)⁻¹ (Eventually.of_forall fun n ↦ ?_)
    have : 0 < α + 1 := by linarith
    rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity),
      Real.norm_of_nonneg (by positivity), inv_mul_eq_div]
    exact sum_Ico_rpow_le hα n

/-- **Exact `Θ(n^{α+1})` characterization of real-power partial sums.**
`∑_{j=1}^{n-1} j^α = Θ(n^{α+1})` as `n → ∞` if and only if `-1 < α`. -/
theorem isTheta_sum_Ico_rpow_rpow_add_one_iff {α : ℝ} :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α) =Θ[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (α + 1)) ↔
      -1 < α :=
  ⟨fun h ↦ isBigO_sum_Ico_rpow_rpow_add_one_iff.mp h.1,
    fun hα ↦ ⟨isBigO_sum_Ico_rpow_rpow_add_one_iff.mpr hα, isBigO_rpow_add_one_sum_Ico_rpow hα⟩⟩

/-- **Combined scale characterization of real-power partial sums.**
`∑_{j=1}^{n-1} j^α = O(n^{α+1} + 1)` as `n → ∞` if and only if `α ≠ -1`. -/
theorem isBigO_sum_Ico_rpow_rpow_add_one_add_one_iff {α : ℝ} :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (α + 1) + 1) ↔
      α ≠ -1 := by
  constructor
  · rintro h rfl
    have hbdd : (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ (-1 : ℝ)) =O[atTop]
        fun _ : ℕ ↦ (1 : ℝ) := by
      refine (h.congr_right fun n ↦ ?_).trans (isBigO_const_const (2 : ℝ) one_ne_zero atTop)
      rw [neg_add_cancel, Real.rpow_zero]
      norm_num
    exact (lt_irrefl (-1 : ℝ)) (isBigO_sum_Ico_rpow_const_iff.mp hbdd)
  · intro hne
    rcases hne.lt_or_gt with hlt | hgt
    · refine (isBigO_sum_Ico_rpow_const_iff.mpr hlt).trans
        (.of_bound 1 (Eventually.of_forall fun n ↦ ?_))
      have hnn : 0 ≤ (n : ℝ) ^ (α + 1) := by positivity
      rw [norm_one, Real.norm_of_nonneg (by positivity), one_mul]
      linarith
    · refine (isBigO_sum_Ico_rpow_rpow_add_one_iff.mpr hgt).trans
        (.of_bound 1 (Eventually.of_forall fun n ↦ ?_))
      have hnn : 0 ≤ (n : ℝ) ^ (α + 1) := by positivity
      rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (by positivity), one_mul]
      linarith

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

/-! ### Exact summation by parts for oscillatory power sums -/

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
    simpa only [z, mul_assoc] using Complex.exp_nat_mul (β * Complex.I) k
  have h := sum_Ico_smul_geom_eq (fun j : ℕ ↦ (j : ℝ) ^ α) hβ hn
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
      have herr := abs_rpow_sub_add_one_rpow_add_mul_le α hj₁
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
`S_z(α, n) = n^α • z^n / (z - 1) - (z / (z - 1)) * α • S_z(α - 1, n) + O(n^{α-1} + 1)`. -/
theorem isBigO_sum_Ico_rpow_smul_geom_sub_step {𝕜 : Type*} [NormedDivisionRing 𝕜]
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
  have hid := sum_Ico_smul_geom_eq (fun j : ℕ ↦ (j : ℝ) ^ α) hz hn
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
theorem isBigO_sum_Ico_rpow_smul_geom {𝕜 : Type*} [NormedDivisionRing 𝕜] [NormedSpace ℝ 𝕜]
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
    refine (hnorm.trans (isBigO_sum_Ico_rpow_const_iff.mpr hβ)).trans
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
    have hsub := ((isBigO_sum_Ico_rpow_smul_geom_sub_step β hz hzn).sub
      ((hprev.const_smul_left β).const_mul_left (z / (z - 1)))).trans hscale
    exact (hlead.add hsub).congr_left fun n ↦ by
      simp only [Pi.smul_apply]
      abel

/-- **Leading-term asymptotic approximation via summation by parts (DLMF 2.10.18, general form).**
In any real normed division ring `𝕜`, for `z ≠ 1` with `‖z‖ ≤ 1` and every real `α`,
`∑_{j=1}^{n-1} j^α • z^j - n^α • z^n / (z - 1) = O(n^{α-1} + 1)` as `n → ∞`. -/
theorem isBigO_sum_Ico_rpow_smul_geom_sub {𝕜 : Type*} [NormedDivisionRing 𝕜] [NormedSpace ℝ 𝕜]
    (α : ℝ) {z : 𝕜} (hz : z ≠ 1) (hzn : ‖z‖ ≤ 1) :
    (fun n : ℕ ↦ (∑ j ∈ Ico 1 n, (j : ℝ) ^ α • z ^ j) -
      (n : ℝ) ^ α • (z ^ n / (z - 1))) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (α - 1) + 1 := by
  have hstep := isBigO_sum_Ico_rpow_smul_geom_sub_step α hz hzn
  have hprev := ((isBigO_sum_Ico_rpow_smul_geom (α - 1) hz hzn).const_smul_left α).const_mul_left
    (z / (z - 1))
  exact (hstep.sub hprev).congr_left fun n ↦ by
    simp only [Pi.smul_apply]
    abel

/-- For `1 ≤ α`, `z ≠ 1`, and `‖z‖ ≤ 1`, the remainder in summation by parts is purely
`O(n^{α-1})`. -/
theorem isBigO_sum_Ico_rpow_smul_geom_sub_of_one_le {𝕜 : Type*} [NormedDivisionRing 𝕜]
    [NormedSpace ℝ 𝕜] {α : ℝ} (hα : 1 ≤ α) {z : 𝕜} (hz : z ≠ 1) (hzn : ‖z‖ ≤ 1) :
    (fun n : ℕ ↦ (∑ j ∈ Ico 1 n, (j : ℝ) ^ α • z ^ j) -
      (n : ℝ) ^ α • (z ^ n / (z - 1))) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (α - 1) := by
  refine (isBigO_sum_Ico_rpow_smul_geom_sub α hz hzn).trans (.of_bound 2 ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (α - 1) :=
    Real.one_le_rpow (Nat.one_le_cast.mpr hn) (by linarith)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  linarith

/-- For `α ≤ 1`, `z ≠ 1`, and `‖z‖ ≤ 1`, the remainder in summation by parts is `O(1)`. -/
theorem isBigO_sum_Ico_rpow_smul_geom_sub_const_of_le_one {𝕜 : Type*} [NormedDivisionRing 𝕜]
    [NormedSpace ℝ 𝕜] {α : ℝ} (hα : α ≤ 1) {z : 𝕜} (hz : z ≠ 1) (hzn : ‖z‖ ≤ 1) :
    (fun n : ℕ ↦ (∑ j ∈ Ico 1 n, (j : ℝ) ^ α • z ^ j) -
      (n : ℝ) ^ α • (z ^ n / (z - 1))) =O[atTop]
      fun _ : ℕ ↦ (1 : ℝ) := by
  refine (isBigO_sum_Ico_rpow_smul_geom_sub α hz hzn).trans (.of_bound 2 ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : (n : ℝ) ^ (α - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.mpr hn) (by linarith)
  rw [Real.norm_of_nonneg (by positivity), norm_one]
  linarith

/-- Rewriting helper identifying `e^{ijβ} j^α` with `(j : ℝ) ^ α • (e^{iβ}) ^ j`. -/
private theorem cexp_mul_rpow_eq_smul_pow (α β : ℝ) (j : ℕ) :
    Complex.exp (j * β * Complex.I) * ↑((j : ℝ) ^ α) =
      (j : ℝ) ^ α • Complex.exp (β * Complex.I) ^ j := by
  rw [Complex.real_smul, mul_comm, ← Complex.exp_nat_mul, mul_assoc]

/-- **One-step summation-by-parts reduction for oscillatory power sums (DLMF 2.10.16).** For all
real `α`, `β` with `e^{iβ} ≠ 1`,
`∑_{j=1}^{n-1} e^{ijβ} j^α - (e^{inβ} / (e^{iβ} - 1) * n^α
  - α * e^{iβ} / (e^{iβ} - 1) * ∑_{j=1}^{n-1} e^{ijβ} j^{α-1}) = O(n^{α-1} + 1)`. -/
theorem isBigO_sum_Ico_cexp_mul_rpow_sub_step (α : ℝ) {β : ℝ}
    (hβ : Complex.exp (β * Complex.I) ≠ 1) :
    (fun n : ℕ ↦ (∑ j ∈ Ico 1 n, Complex.exp (j * β * Complex.I) * ↑((j : ℝ) ^ α)) -
      (Complex.exp (n * β * Complex.I) / (Complex.exp (β * Complex.I) - 1) * ↑((n : ℝ) ^ α) -
        (α : ℂ) * (Complex.exp (β * Complex.I) / (Complex.exp (β * Complex.I) - 1)) *
          ∑ j ∈ Ico 1 n, Complex.exp (j * β * Complex.I) * ↑((j : ℝ) ^ (α - 1)))) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (α - 1) + 1 := by
  have hzn : ‖Complex.exp (β * Complex.I)‖ ≤ 1 :=
    (Complex.norm_exp_ofReal_mul_I β).le
  refine (isBigO_sum_Ico_rpow_smul_geom_sub_step α hβ hzn).congr_left fun n ↦ ?_
  simp_rw [cexp_mul_rpow_eq_smul_pow, Complex.real_smul]
  have hpow : Complex.exp (n * β * Complex.I) = Complex.exp (β * Complex.I) ^ n := by
    rw [← Complex.exp_nat_mul, mul_assoc]
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
  refine (isBigO_sum_Ico_rpow_smul_geom α hβ hzn).congr_left fun n ↦ ?_
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
  refine (isBigO_sum_Ico_rpow_smul_geom_sub α hβ hzn).congr_left fun n ↦ ?_
  simp_rw [cexp_mul_rpow_eq_smul_pow, Complex.real_smul]
  have hpow : Complex.exp (n * β * Complex.I) = Complex.exp (β * Complex.I) ^ n := by
    rw [← Complex.exp_nat_mul, mul_assoc]
  rw [hpow]
  ring

end TauCeti

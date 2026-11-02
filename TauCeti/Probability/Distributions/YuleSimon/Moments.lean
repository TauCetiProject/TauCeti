/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import TauCeti.Probability.Distributions.YuleSimon.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import TauCeti.Analysis.SpecialFunctions.Gamma
import TauCeti.Probability.Moments.IntegrableExpMul

/-!
# Moments of the Yule–Simon distribution

The Yule–Simon mass `ρ B(k, ρ + 1)` decays like `ρ Γ(ρ + 1) k ^ (-(ρ + 1))`, so the law is
heavy-tailed: its natural moment of order `m` exists exactly when `m < ρ`, and its exponential
moments exist exactly at nonpositive arguments.

Below the threshold, the rising-factorial moments have the closed form
`E[X (X + 1) ⋯ (X + m - 1)] = ρ m! / (ρ - m)`. The summands `ρ Γ(ρ + 1) Γ(k + m) / Γ(k + ρ + 1)`
telescope against the Gamma quotients `Γ(k + m) / Γ(k + ρ)`, which tend to zero by Euler's limit
formula. The mean `ρ / (ρ - 1)` and variance `ρ² / ((ρ - 1)² (ρ - 2))` are the first two
instances.

All statements concern the real cast of the law, which is its analytic interface.

## Main results

* `integrable_pow_map_cast_yuleSimonMeasure_iff`: the `m`-th moment exists exactly when `m < ρ`;
* `integrableExpSet_id_map_cast_yuleSimonMeasure`: the exponential-integrability domain is
  `(-∞, 0]`;
* `integral_ascPochhammer_map_cast_yuleSimonMeasure`: the rising-factorial moments;
* `integral_id_map_cast_yuleSimonMeasure` and `variance_id_map_cast_yuleSimonMeasure`: the mean
  and variance.

## References

* H. A. Simon, *On a class of skew distribution functions*, Biometrika 42 (1955), 425–440.
* N. L. Johnson, A. W. Kemp, and S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Section 6.10.3.
-/

public section

noncomputable section

open Asymptotics Filter MeasureTheory ProbabilityTheory Real Set
open scoped Nat Topology

namespace TauCeti

namespace Probability

variable {ρ : ℝ}

/-- The Yule–Simon masses decay like `ρ Γ(ρ + 1) n ^ (-(ρ + 1))`. -/
private theorem isEquivalent_yuleSimonWeightReal_add_one (hρ : 0 < ρ) :
    (fun n : ℕ => yuleSimonWeightReal ρ (n + 1)) ~[atTop]
      fun n => ρ * Gamma (ρ + 1) * (n : ℝ) ^ (-(ρ + 1)) := by
  have hequiv := ((IsEquivalent.refl (u := fun n : ℕ => ρ * Gamma (ρ + 1) * (n ! : ℝ))).mul
    (isEquivalent_Gamma_natCast_add_one_add (ρ + 1)).inv)
  refine (hequiv.congr_left ?_).congr_right ?_
  · refine Eventually.of_forall fun n => ?_
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [yuleSimonWeightReal_def, beta, Nat.cast_succ, Real.Gamma_nat_eq_factorial,
      add_assoc (n : ℝ) 1 (ρ + 1)]
    ring
  · filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hfac : (n ! : ℝ) ≠ 0 := by positivity
    simp only [Pi.mul_apply, Pi.inv_apply, rpow_neg hn'.le]
    field_simp

/-- On the natural numbers, the `m`-th power is integrable for a Yule–Simon law exactly when
`m < ρ`. -/
private theorem integrable_pow_yuleSimonMeasure_iff (hρ : 0 < ρ) (m : ℕ) :
    Integrable (fun k : ℕ => (k : ℝ) ^ m) (yuleSimonMeasure ρ) ↔ (m : ℝ) < ρ := by
  rw [yuleSimonMeasure_eq_sum_dirac hρ,
    integrable_sum_dirac_iff (yuleSimonWeight_ne_top ρ), ← summable_nat_add_iff 1]
  have hC : ρ * Gamma (ρ + 1) ≠ 0 := (mul_pos hρ (Gamma_pos_of_pos (by positivity))).ne'
  have hlin : (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) ~[atTop] fun n => (n : ℝ) :=
    (IsEquivalent.refl.add_isLittleO ((isLittleO_const_id_atTop (1 : ℝ)).comp_tendsto
      tendsto_natCast_atTop_atTop)).congr_left (Eventually.of_forall fun n => by simp)
  have hequiv := (isEquivalent_yuleSimonWeightReal_add_one hρ).mul (hlin.pow m)
  have hterm : (fun n : ℕ => (yuleSimonWeight ρ (n + 1)).toReal * ‖((n + 1 : ℕ) : ℝ) ^ m‖) =
      (fun n : ℕ => yuleSimonWeightReal ρ (n + 1)) * (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) ^ m := by
    funext n
    rw [yuleSimonWeight_toReal hρ.le, norm_pow, Real.norm_natCast, Pi.mul_apply, Pi.pow_apply]
  rw [hterm, ((hequiv.congr_right (?_ : _ =ᶠ[atTop] fun n : ℕ =>
      ρ * Gamma (ρ + 1) * (n : ℝ) ^ ((m : ℝ) - (ρ + 1))))).summable_iff_nat,
    summable_mul_left_iff hC, summable_nat_rpow]
  · constructor <;> intro h <;> linarith
  · filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [sub_eq_add_neg, rpow_add hn', rpow_natCast]
    ring

/-- The `m`-th moment of the real cast of a Yule–Simon law exists exactly when `m < ρ`. -/
theorem integrable_pow_map_cast_yuleSimonMeasure_iff (hρ : 0 < ρ) (m : ℕ) :
    Integrable (fun x : ℝ => x ^ m) ((yuleSimonMeasure ρ).map (Nat.cast : ℕ → ℝ)) ↔
      (m : ℝ) < ρ := by
  rw [MeasurableEmbedding.natCast.integrable_map_iff]
  exact integrable_pow_yuleSimonMeasure_iff hρ m

/-- The exponential moments of the real cast of a Yule–Simon law exist exactly at nonpositive
arguments. -/
theorem integrableExpSet_id_map_cast_yuleSimonMeasure (hρ : 0 < ρ) :
    integrableExpSet id ((yuleSimonMeasure ρ).map (Nat.cast : ℕ → ℝ)) = Iic 0 := by
  have := isProbabilityMeasure_yuleSimonMeasure hρ
  have hnonneg : ∀ᵐ x ∂((yuleSimonMeasure ρ).map (Nat.cast : ℕ → ℝ)), (0 : ℝ) ≤ id x :=
    MeasurableEmbedding.natCast.ae_map_iff.2 (Eventually.of_forall fun k => Nat.cast_nonneg k)
  refine integrableExpSet_eq_Iic_of_not_integrable_pow aemeasurable_id hnonneg ⌈ρ⌉₊ ?_
  exact fun hi => (Nat.le_ceil ρ).not_gt ((integrable_pow_map_cast_yuleSimonMeasure_iff hρ _).1 hi)

/-! ### Rising-factorial moments -/

/-- The rising-factorial-weighted Yule–Simon masses telescope against the Gamma quotients
`Γ(k + m) / Γ(k + ρ)`. -/
private theorem yuleSimonWeightReal_mul_ascPochhammer_eq {m : ℕ} (hm : (m : ℝ) < ρ)
    {k : ℕ} (hk : k ≠ 0) :
    yuleSimonWeightReal ρ k * (ascPochhammer ℝ m).eval (k : ℝ) =
      ρ * Gamma (ρ + 1) / (ρ - m) *
        (Gamma (k + m) / Gamma (k + ρ) - Gamma ((k + 1 : ℕ) + m) / Gamma ((k + 1 : ℕ) + ρ)) := by
  have hρ : 0 < ρ := (Nat.cast_nonneg m).trans_lt hm
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hΓk := Gamma_pos_of_pos hk'
  have hasc : (ascPochhammer ℝ m).eval (k : ℝ) * Gamma k = Gamma (k + m) := by
    have hk_ne (j : ℕ) : (k : ℝ) ≠ -j := by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
    rw [← Gamma_add_nat_div_Gamma_eq _ hk_ne, div_mul_cancel₀ _ hΓk.ne']
  have hΓρ := Gamma_pos_of_pos (show 0 < (k : ℝ) + ρ by positivity)
  have hsub : ρ - m ≠ 0 := (sub_pos.mpr hm).ne'
  have h1 : Gamma (k + (ρ + 1)) = (k + ρ) * Gamma (k + ρ) := by
    rw [← add_assoc, Gamma_add_one (by positivity)]
  have h2 : Gamma ((k + 1 : ℕ) + m) = (k + m) * Gamma (k + m) := by
    rw [Nat.cast_succ, add_right_comm, Gamma_add_one (by positivity)]
  have h3 : Gamma ((k + 1 : ℕ) + ρ) = (k + ρ) * Gamma (k + ρ) := by
    rw [Nat.cast_succ, add_right_comm, Gamma_add_one (by positivity)]
  rw [yuleSimonWeightReal_def, beta, h1, h2, h3, ← hasc]
  field_simp
  ring

/-- The rising-factorial moment `E[X (X + 1) ⋯ (X + m - 1)]` of the real cast of a Yule–Simon law
is `ρ m! / (ρ - m)` whenever `m < ρ`. -/
theorem integral_ascPochhammer_map_cast_yuleSimonMeasure {m : ℕ} (hm : (m : ℝ) < ρ) :
    ∫ x, (ascPochhammer ℝ m).eval x ∂((yuleSimonMeasure ρ).map (Nat.cast : ℕ → ℝ)) =
      ρ * m ! / (ρ - m) := by
  have hρ : 0 < ρ := (Nat.cast_nonneg m).trans_lt hm
  rw [MeasurableEmbedding.natCast.integral_map, yuleSimonMeasure_eq_sum_dirac hρ,
    integral_sum_dirac (yuleSimonWeight_ne_top ρ)]
  simp only [smul_eq_mul, yuleSimonWeight_toReal hρ.le]
  set r : ℕ → ℝ := fun n => Gamma ((n + 1 : ℕ) + m) / Gamma ((n + 1 : ℕ) + ρ)
  set C := ρ * Gamma (ρ + 1) / (ρ - m)
  have hshift : (fun n : ℕ => yuleSimonWeightReal ρ (n + 1) *
      (ascPochhammer ℝ m).eval ((n + 1 : ℕ) : ℝ)) = fun n => C * (r n - r (n + 1)) := by
    funext n
    rw [yuleSimonWeightReal_mul_ascPochhammer_eq hm n.succ_ne_zero]
  -- The shifted partial sums telescope to `C (r 0 - r N)`, and `r N → 0`.
  have hsum : HasSum (fun k : ℕ => yuleSimonWeightReal ρ k * (ascPochhammer ℝ m).eval (k : ℝ))
      (C * r 0) := by
    rw [← hasSum_nat_add_iff' 1, Finset.sum_range_one, Nat.cast_zero, yuleSimonWeightReal_zero,
      zero_mul, sub_zero, hasSum_iff_tendsto_nat_of_nonneg fun n => mul_nonneg
        (yuleSimonWeightReal_nonneg hρ.le _) (ascPochhammer_pos m _ (by positivity)).le, hshift]
    have hlim := (((tendsto_Gamma_natCast_add_div_Gamma_natCast_add_atTop hm).comp
      (tendsto_add_atTop_nat 1)).const_sub (r 0)).const_mul C
    rw [sub_zero] at hlim
    refine hlim.congr fun N => ?_
    rw [← Finset.mul_sum, Finset.sum_range_sub']
    rfl
  rw [hsum.tsum_eq]
  have hρΓ : Gamma (1 + ρ) ≠ 0 := (Gamma_pos_of_pos (by positivity)).ne'
  simp only [C, r, zero_add, Nat.cast_one]
  rw [add_comm (1 : ℝ) m, Gamma_nat_eq_factorial, add_comm ρ 1]
  field_simp

/-! ### Mean and variance -/

/-- The mean of the real cast of a Yule–Simon law is `ρ / (ρ - 1)` for `ρ > 1`. -/
theorem integral_id_map_cast_yuleSimonMeasure (hρ : 1 < ρ) :
    ∫ x, x ∂((yuleSimonMeasure ρ).map (Nat.cast : ℕ → ℝ)) = ρ / (ρ - 1) := by
  simpa using integral_ascPochhammer_map_cast_yuleSimonMeasure (m := 1) (by simpa using hρ)

/-- The variance of the real cast of a Yule–Simon law is `ρ² / ((ρ - 1)² (ρ - 2))` for
`ρ > 2`. -/
theorem variance_id_map_cast_yuleSimonMeasure (hρ : 2 < ρ) :
    variance id ((yuleSimonMeasure ρ).map (Nat.cast : ℕ → ℝ)) =
      ρ ^ 2 / ((ρ - 1) ^ 2 * (ρ - 2)) := by
  have hρ0 : 0 < ρ := by linarith
  have := isProbabilityMeasure_yuleSimonMeasure hρ0
  have hint1 := (integrable_pow_map_cast_yuleSimonMeasure_iff hρ0 1).2 (by norm_num; linarith)
  have hint2 := (integrable_pow_map_cast_yuleSimonMeasure_iff hρ0 2).2 (by norm_num; linarith)
  -- The second rising-factorial moment is `E[X²] + E[X] = 2ρ / (ρ - 2)`.
  have hasc := integral_ascPochhammer_map_cast_yuleSimonMeasure (m := 2) (by norm_num; linarith)
  have heval (x : ℝ) : (ascPochhammer ℝ 2).eval x = x ^ 2 + x ^ 1 := by
    simp [ascPochhammer_succ_right]
    ring
  simp_rw [heval] at hasc
  rw [integral_add hint2 hint1] at hasc
  have hmean := integral_id_map_cast_yuleSimonMeasure (by linarith : 1 < ρ)
  rw [variance_eq_sub ((memLp_two_iff_integrable_sq (f := id) (by fun_prop)).2 hint2)]
  simp only [Pi.pow_apply, id_eq, pow_one, Nat.factorial_two, Nat.cast_ofNat] at hasc ⊢
  rw [hmean, eq_sub_of_add_eq hasc, hmean]
  have h1 : ρ - 1 ≠ 0 := by linarith
  have h2 : ρ - 2 ≠ 0 := by linarith
  field_simp
  ring

end Probability

end TauCeti

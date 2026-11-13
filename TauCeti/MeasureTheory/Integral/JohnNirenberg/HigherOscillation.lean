/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.JohnNirenberg
public import TauCeti.MeasureTheory.Integral.MaximalFunction
import Mathlib.Probability.Moments.IntegrableExpMul
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Higher mean oscillations of functions of bounded mean oscillation

On `ℝⁿ = ι → ℝ` with the sup distance, balls are cubes, and the John–Nirenberg inequality
(`TauCeti.setLIntegral_exp_mul_norm_sub_setAverage_closedBall_le`) bounds every power of the
oscillation of a function of bounded mean oscillation by the same power of its BMO seminorm.
Combined with Hölder's inequality and the maximal function, this controls products of a BMO
function with an `Lᵠ` function on a cube.

## Main results

* `TauCeti.setLAverage_enorm_sub_setAverage_rpow_le_of_bmoSeminorm_le`: every power of the
  oscillation of a function of bounded mean oscillation on a cube has average bounded by the
  corresponding power of its BMO seminorm.
* `TauCeti.setLIntegral_enorm_sub_mul_enorm_rpow_le`, `TauCeti.setLIntegral_enorm_sub_mul_enorm_le`:
  on a cube containing `x`, the `Lᵗ` norm of `|b - a| ‖f‖` for a function `b` of bounded mean
  oscillation is controlled by `‖b‖_{BMO}` and the maximal function of `‖f‖^q` at `x`, `t < q`,
  with the constant `TauCeti.bmoHolderConst`.

## References

* F. John and L. Nirenberg, *On functions of bounded mean oscillation*, Comm. Pure Appl. Math.
  **14** (1961), 415–426.
* L. Grafakos, *Modern Fourier Analysis*, Theorem 3.1.6 and the corollary following it.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section HigherOscillation

/-! ### Higher mean oscillations

On `ℝⁿ = ι → ℝ` with the sup distance, balls are cubes, and a function with `‖f‖_{BMO} ≤ M`
satisfies the hypothesis of the John–Nirenberg inequality on every cube. The resulting exponential
integrability bounds every power of the oscillation: `⨍_B ‖f - f_B‖^q ≤ C(n, q) M^q`. -/

open Filter Metric Topology

variable [Nonempty ι] [CompleteSpace E] {μ : Measure (ι → ℝ)} [μ.IsAddHaarMeasure]

/-- The bound on higher mean oscillations for a positive bound `M` on the BMO seminorm and a
ball of positive radius. -/
private theorem setLAverage_enorm_sub_setAverage_rpow_le_of_pos {f : (ι → ℝ) → E}
    (hf : LocallyIntegrable f μ) {M : ℝ≥0} (hM0 : 0 < M) (hM : bmoSeminorm f μ ≤ M) {q : ℝ}
    (hq : 0 < q) (c : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    ⨍⁻ x in ball c r, ‖f x - ⨍ y in ball c r, f y ∂μ‖ₑ ^ q ∂μ ≤
      ENNReal.ofReal (7 * (2 ^ (Fintype.card ι + 1) * q / Real.log (3 / 2)) ^ q) * M ^ q := by
  set n := Fintype.card ι
  set K : ℝ := 2 ^ (n + 1) * q / Real.log (3 / 2)
  have hK : 0 < K := by positivity
  -- Closed and open balls agree up to a null set, so the BMO bound applies to closed balls.
  have hMc : ∀ y ρ, closedBall y ρ ⊆ closedBall c r →
      ⨍⁻ x in closedBall y ρ, ‖f x - ⨍ z in closedBall y ρ, f z ∂μ‖ₑ ∂μ ≤ M := fun y ρ _ => by
    rw [μ.restrict_closedBall_eq_restrict_ball y ρ]
    exact (setLAverage_enorm_sub_setAverage_le_bmoSeminorm f μ y ρ).trans hM
  -- John–Nirenberg at the rate `σ` with `exp (2ⁿ⁺¹ σ M) = 3 / 2`.
  set σ : ℝ := Real.log (3 / 2) / (2 ^ (n + 1) * M)
  have hσ : 0 < σ := by positivity
  have hσM : Real.exp (σ * (2 ^ (n + 1) * M)) = 3 / 2 := by
    rw [div_mul_cancel₀ _ (by positivity), Real.exp_log (by norm_num)]
  have hJN := setLIntegral_exp_mul_norm_sub_setAverage_closedBall_le (μ := μ)
    (hf.integrableOn_isCompact (isCompact_closedBall c r)) hMc (σ := σ) (by rw [hσM]; norm_num)
  rw [hσM, μ.restrict_closedBall_eq_restrict_ball c r,
    measure_congr (μ.addHaar_closedBall_ae_eq_ball c r)] at hJN
  norm_num at hJN
  have h0 : μ (ball c r) ≠ 0 := (measure_ball_pos μ c hr).ne'
  have htop : μ (ball c r) ≠ ∞ := measure_ball_lt_top.ne
  have hqσ : q / σ = K * M := by
    simp only [σ, K]
    field_simp
  rw [setLAverage_eq, ENNReal.div_le_iff h0 htop]
  calc ∫⁻ x in ball c r, ‖f x - ⨍ y in ball c r, f y ∂μ‖ₑ ^ q ∂μ
      ≤ ∫⁻ x in ball c r, ENNReal.ofReal ((q / σ) ^ q) *
          ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in ball c r, f y ∂μ‖)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        simpa only [abs_norm, abs_of_pos hσ] using
          ProbabilityTheory.rpow_abs_le_mul_exp_abs ‖f x - ⨍ y in ball c r, f y ∂μ‖ hq.le hσ.ne'
    _ = ENNReal.ofReal ((q / σ) ^ q) * ∫⁻ x in ball c r,
          ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in ball c r, f y ∂μ‖)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((q / σ) ^ q) * (7 * μ (ball c r)) := by gcongr
    _ = ENNReal.ofReal (7 * K ^ q) * M ^ q * μ (ball c r) := by
        rw [hqσ, Real.mul_rpow hK.le M.coe_nonneg, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat,
          ← ENNReal.ofReal_rpow_of_nonneg M.coe_nonneg hq.le, ENNReal.ofReal_coe_nnreal]
        ring

/-- **Higher mean oscillations of a function of bounded mean oscillation.** On `ℝⁿ = ι → ℝ`,
`n ≥ 1`, with the sup distance and an additive Haar measure `μ`, let `f` be locally integrable
with `‖f‖_{BMO} ≤ M`. Then for every `0 < q` and every ball `B`,

`⨍_B ‖f - f_B‖^q ≤ 7 (2ⁿ⁺¹ q / log (3 / 2))^q M^q`.

So every `Lᵠ` mean oscillation of `f`, not only the `L¹` one, is controlled by its BMO seminorm;
this is a consequence of the exponential integrability given by the John–Nirenberg inequality. -/
theorem setLAverage_enorm_sub_setAverage_rpow_le_of_bmoSeminorm_le {f : (ι → ℝ) → E}
    (hf : LocallyIntegrable f μ) {M : ℝ≥0} (hM : bmoSeminorm f μ ≤ M) {q : ℝ} (hq : 0 < q)
    (c : ι → ℝ) (r : ℝ) :
    ⨍⁻ x in ball c r, ‖f x - ⨍ y in ball c r, f y ∂μ‖ₑ ^ q ∂μ ≤
      ENNReal.ofReal (7 * (2 ^ (Fintype.card ι + 1) * q / Real.log (3 / 2)) ^ q) * M ^ q := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  set C := ENNReal.ofReal (7 * (2 ^ (Fintype.card ι + 1) * q / Real.log (3 / 2)) ^ q)
  -- Apply the bound with `M + ε` in place of `M` and let `ε → 0`.
  have hlim : Tendsto (fun ε : ℝ≥0 => C * ((M + ε : ℝ≥0) : ℝ≥0∞) ^ q) (𝓝[>] 0)
      (𝓝 (C * (M : ℝ≥0∞) ^ q)) := by
    have hcont : Continuous fun ε : ℝ≥0 => C * ((M + ε : ℝ≥0) : ℝ≥0∞) ^ q :=
      (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
        ((ENNReal.continuous_rpow_const).comp
          (ENNReal.continuous_coe.comp (continuous_const.add continuous_id)))
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  refine setLAverage_enorm_sub_setAverage_rpow_le_of_pos hf (add_pos_of_nonneg_of_pos M.2 hε)
    (hM.trans ?_) hq c hr
  exact ENNReal.coe_le_coe.2 le_self_add

end HigherOscillation

section Product

/-! ### Products with functions of bounded mean oscillation

Hölder's inequality combines the higher mean oscillation bound with the maximal function: on a
ball `S` containing `x`, the `Lᵗ` norm of `|b - a| ‖f‖` is controlled by `‖b‖_{BMO}` and
`(M(‖f‖^q) x)^{1/q}` for `t < q`. -/

open Metric

variable [Nonempty ι] [CompleteSpace E] {μ : Measure (ι → ℝ)} [μ.IsAddHaarMeasure]
  {G : Type*} [NormedAddCommGroup G]

/-- The constant `C_p^{1/p}`, `p = t q / (q - t)`, of the Hölder estimate
`TauCeti.setLIntegral_enorm_sub_mul_enorm_rpow_le`, where `C_p = 7 (2ⁿ⁺¹ p / log (3 / 2))^p` is the
constant of `TauCeti.setLAverage_enorm_sub_setAverage_rpow_le_of_bmoSeminorm_le` in dimension
`n`. -/
noncomputable def bmoHolderConst (n : ℕ) (t q : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (7 * (2 ^ (n + 1) * (t * (q / (q - t))) / Real.log (3 / 2)) ^
    (t * (q / (q - t)))) ^ (t * (q / (q - t)))⁻¹

/-- The constant `TauCeti.bmoHolderConst n t q` is finite. -/
theorem bmoHolderConst_ne_top (n : ℕ) {t q : ℝ} (ht : 0 < t) (htq : t < q) :
    bmoHolderConst n t q ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 (mul_pos ht (div_pos (ht.trans htq)
    (sub_pos.2 htq))).le) ENNReal.ofReal_ne_top

/-- **Products of a BMO function with an `L^q` function on a ball.** Let `‖b‖_{BMO} ≤ M`, let
`S = B(c, ρ)` contain `x`, and let `‖b_S - a‖ ≤ κ M`. For `1 ≤ t < q`, Hölder's inequality with the
exponents `q / (q - t)` and `q / t`, the John–Nirenberg inequality at the exponent
`p = t q / (q - t)` and the maximal function at `x` give

`∫_S (|b - a| ‖f‖)^t ≤ ((C_p^{1/p} + κ) M)^t 2^{n t / q} |S| (M(‖f‖^q) x)^{t / q}`. -/
theorem setLIntegral_enorm_sub_mul_enorm_rpow_le {b : (ι → ℝ) → E} (hb : LocallyIntegrable b μ)
    {M : ℝ≥0} (hM : bmoSeminorm b μ ≤ M) {f : (ι → ℝ) → G} (hf : AEStronglyMeasurable f μ)
    {t q : ℝ} (ht : 1 ≤ t) (htq : t < q) {c x : ι → ℝ} {ρ : ℝ} (hx : x ∈ ball c ρ) {a : E}
    {κ : ℝ≥0∞} (ha : ‖(⨍ y in ball c ρ, b y ∂μ) - a‖ₑ ≤ κ * M) :
    ∫⁻ y in ball c ρ, (‖b y - a‖ₑ * ‖f y‖ₑ) ^ t ∂μ ≤
      ((bmoHolderConst (Fintype.card ι) t q + κ) * M) ^ t *
        (2 ^ Fintype.card ι : ℝ≥0∞) ^ (t / q) * μ (ball c ρ) *
          maximalFunction μ (fun y => ‖f y‖ₑ ^ q) x ^ (t / q) := by
  unfold bmoHolderConst
  set n := Fintype.card ι
  set S := ball c ρ
  set a' : ℝ := q / (q - t)
  set p : ℝ := t * a'
  set J := ENNReal.ofReal (7 * (2 ^ (n + 1) * p / Real.log (3 / 2)) ^ p)
  set Mf := maximalFunction μ (fun y => ‖f y‖ₑ ^ q) x
  have ht0 : 0 < t := one_pos.trans_le ht
  have hq0 : 0 < q := ht0.trans htq
  have hqt : 0 < q - t := sub_pos.2 htq
  have ha'1 : 1 < a' := (one_lt_div hqt).2 (by linarith)
  have hp1 : 1 ≤ p := one_le_mul_of_one_le_of_one_le ht ha'1.le
  have hp0 : 0 < p := one_pos.trans_le hp1
  have hS0 : μ S ≠ 0 := (measure_ball_pos μ c (pos_of_mem_ball hx)).ne'
  have hStop : μ S ≠ ∞ := measure_ball_lt_top.ne
  have hconj : a'.HolderConjugate (q / t) := by
    rw [Real.holderConjugate_iff]
    refine ⟨ha'1, ?_⟩
    simp only [a', inv_div]
    field_simp
    ring
  have hbm : AEMeasurable (fun y => ‖b y - a‖ₑ) (μ.restrict S) :=
    (hb.aestronglyMeasurable.sub aestronglyMeasurable_const).eNorm.restrict
  have hfm : AEMeasurable (fun y => ‖f y‖ₑ) (μ.restrict S) := hf.eNorm.restrict
  -- The `Lᵖ` norm of `b - a` on `S`, by Minkowski's inequality and John–Nirenberg.
  have hLp : (∫⁻ y in S, ‖b y - a‖ₑ ^ p ∂μ) ^ p⁻¹ ≤ (J ^ p⁻¹ + κ) * M * μ S ^ p⁻¹ := by
    set bS := ⨍ y in S, b y ∂μ
    have hpt : ∀ y, ‖b y - a‖ₑ ≤ ‖b y - bS‖ₑ + ‖bS - a‖ₑ := fun y => by
      simpa only [sub_add_sub_cancel] using eNorm_add_le (b y - bS) (bS - a)
    have hosc : ∫⁻ y in S, ‖b y - bS‖ₑ ^ p ∂μ ≤ J * (M : ℝ≥0∞) ^ p * μ S := by
      rw [← measure_mul_setLAverage _ hStop, mul_comm]
      gcongr
      exact setLAverage_enorm_sub_setAverage_rpow_le_of_bmoSeminorm_le hb hM hp0 c ρ
    calc (∫⁻ y in S, ‖b y - a‖ₑ ^ p ∂μ) ^ p⁻¹
        ≤ (∫⁻ y in S, (‖b y - bS‖ₑ + ‖bS - a‖ₑ) ^ p ∂μ) ^ p⁻¹ := by
          gcongr with y
          exact hpt y
      _ ≤ (∫⁻ y in S, ‖b y - bS‖ₑ ^ p ∂μ) ^ (1 / p) +
            (∫⁻ _ in S, ‖bS - a‖ₑ ^ p ∂μ) ^ (1 / p) := by
          rw [inv_eq_one_div]
          exact ENNReal.lintegral_Lp_add_le
            (hb.aestronglyMeasurable.sub aestronglyMeasurable_const).eNorm.restrict
            aemeasurable_const hp1
      _ ≤ (J * (M : ℝ≥0∞) ^ p * μ S) ^ (1 / p) + (κ * M) * μ S ^ p⁻¹ := by
          gcongr
          rw [setLIntegral_const, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
            ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one, one_div]
          gcongr
      _ = (J ^ p⁻¹ + κ) * M * μ S ^ p⁻¹ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hp0.ne', ENNReal.rpow_one, one_div]
          ring
  -- The `L^q` norm of `f` on `S`, by the maximal function at `x ∈ S`.
  have hLq : ∫⁻ y in S, ‖f y‖ₑ ^ q ∂μ ≤ 2 ^ n * μ S * Mf := by
    have := setLIntegral_ball_le_two_pow_mul_measure_mul_maximalFunction μ
      (fun y => ‖f y‖ₑ ^ q) hx
    simpa only [eNorm_eq_self, Module.finrank_fintype_fun_eq_card] using this
  -- Hölder's inequality with the exponents `a' = q / (q - t)` and `q / t`.
  have hexp1 : (p⁻¹) * t = 1 / a' := by
    simp only [p]
    field_simp
  have hexp2 : t * (q / t) = q := by field_simp
  have hsum : t * p⁻¹ + t / q = 1 := by
    simp only [p, a']
    field_simp
    ring
  calc ∫⁻ y in S, (‖b y - a‖ₑ * ‖f y‖ₑ) ^ t ∂μ
      = ∫⁻ y in S, ((fun y => ‖b y - a‖ₑ ^ t) * fun y => ‖f y‖ₑ ^ t) y ∂μ := by
        refine lintegral_congr fun y => ?_
        simp only [Pi.mul_apply]
        exact ENNReal.mul_rpow_of_nonneg _ _ ht0.le
    _ ≤ (∫⁻ y in S, (‖b y - a‖ₑ ^ t) ^ a' ∂μ) ^ (1 / a') *
          (∫⁻ y in S, (‖f y‖ₑ ^ t) ^ (q / t) ∂μ) ^ (1 / (q / t)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _ hconj (hbm.pow_const t) (hfm.pow_const t)
    _ = ((∫⁻ y in S, ‖b y - a‖ₑ ^ p ∂μ) ^ p⁻¹) ^ t * (∫⁻ y in S, ‖f y‖ₑ ^ q ∂μ) ^ (t / q) := by
        simp_rw [← ENNReal.rpow_mul, hexp2, hexp1, one_div_div]
        rfl
    _ ≤ ((J ^ p⁻¹ + κ) * M * μ S ^ p⁻¹) ^ t * (2 ^ n * μ S * Mf) ^ (t / q) := by
        gcongr
    _ = ((J ^ p⁻¹ + κ) * M) ^ t * (2 ^ n : ℝ≥0∞) ^ (t / q) *
          (μ S ^ (t * p⁻¹) * μ S ^ (t / q)) * Mf ^ (t / q) := by
        have htq0 : 0 ≤ t / q := by positivity
        rw [ENNReal.mul_rpow_of_nonneg _ _ ht0.le, ENNReal.mul_rpow_of_nonneg _ Mf htq0,
          ENNReal.mul_rpow_of_nonneg _ (μ S) htq0, ← ENNReal.rpow_mul, mul_comm p⁻¹ t]
        ring
    _ = ((J ^ p⁻¹ + κ) * M) ^ t * (2 ^ n : ℝ≥0∞) ^ (t / q) * μ S * Mf ^ (t / q) := by
        rw [← ENNReal.rpow_add _ _ hS0 hStop, hsum, ENNReal.rpow_one]

/-- The case `t = 1` of `TauCeti.setLIntegral_enorm_sub_mul_enorm_rpow_le`. -/
theorem setLIntegral_enorm_sub_mul_enorm_le {b : (ι → ℝ) → E} (hb : LocallyIntegrable b μ)
    {M : ℝ≥0} (hM : bmoSeminorm b μ ≤ M) {f : (ι → ℝ) → G} (hf : AEStronglyMeasurable f μ)
    {q : ℝ} (hq : 1 < q) {c x : ι → ℝ} {ρ : ℝ} (hx : x ∈ ball c ρ) {a : E} {κ : ℝ≥0∞}
    (ha : ‖(⨍ y in ball c ρ, b y ∂μ) - a‖ₑ ≤ κ * M) :
    ∫⁻ y in ball c ρ, ‖b y - a‖ₑ * ‖f y‖ₑ ∂μ ≤
      (bmoHolderConst (Fintype.card ι) 1 q + κ) * M * (2 ^ Fintype.card ι : ℝ≥0∞) ^ q⁻¹ *
        μ (ball c ρ) * maximalFunction μ (fun y => ‖f y‖ₑ ^ q) x ^ q⁻¹ := by
  simpa only [ENNReal.rpow_one, one_div] using
    setLIntegral_enorm_sub_mul_enorm_rpow_le hb hM hf le_rfl hq hx ha

end Product

end TauCeti

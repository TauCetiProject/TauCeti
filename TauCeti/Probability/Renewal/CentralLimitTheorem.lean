/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.CentralLimitTheorem
public import TauCeti.Probability.Renewal.Count
import TauCeti.MeasureTheory.Function.TendstoInDistribution
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cdf

/-!
# The renewal central limit theorem

Let `T 0, T 1, …` be independent, identically distributed nonnegative waiting times on a
probability space `(Ω, P)` whose common law has finite second moment and strictly positive variance
`σ² = Var[T 0; P] ≠ 0` (in Mathlib, `Var[X; P]` vanishes outside `L²`, so `Var[T 0; P] ≠ 0` encodes
both `MemLp (T 0) 2 P` and `0 < σ²`). Then the increments are not almost surely zero, their
extended mean `∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P` is finite and strictly positive, and its real value agrees
with the Bochner expectation `μ = P[fun ω ↦ (T 0 ω : ℝ)] > 0`.

Writing `N_t = renewalCountNat T t` for the natural-valued renewal count at time `t : ℝ≥0`, this
file proves that as `t → ∞`,

```text
((N_t : ℝ) - t / μ) / (σ * √(t / μ ^ 3))  ⟶  𝒩(0, 1)
```

in distribution (`MeasureTheory.TendstoInDistribution`).

## Proof outline

Following Feller's inversion argument, fix `x : ℝ` and set

```text
u(t) = t / μ + x * σ * √(t / μ ^ 3),     m(t) = ⌊u(t)⌋₊ + 1.
```

1. **Pathwise inversion** (`renewalCountNat_sub_div_le_iff`): on a nonexplosive path, once `t > 0`
   and `u(t) ≥ 0`, the count inequality `((N_t : ℝ) - t / μ) / (σ * √(t / μ ^ 3)) ≤ x` is
   equivalent to `N_t < m(t)`, hence by `le_renewalCountNat_iff` to `t < arrival T (m(t))`, which
   after centering by `m(t) * μ` and scaling by `σ * √(m(t))` becomes
   `-(arrival T (m(t)) - m(t) * μ) / (σ * √(m(t))) < (m(t) * μ - t) / (σ * √(m(t)))`.
2. **Rounding asymptotics** (`tendsto_natFloor_add_one_div_add_mul_sqrt_atTop`,
   `tendsto_rounding_sub_div_sqrt_atTop`): as `t → ∞`, `m(t) → ∞`, `m(t) / (t / μ) → 1`, and the
   rounding remainder `m(t) - u(t) ∈ (0, 1]` becomes negligible when divided by `√(m(t))`, so the
   threshold `(m(t) * μ - t) / (σ * √(m(t)))` converges to `x`.
3. **Comparison with the scalar i.i.d. central limit theorem**: applying Mathlib's
   `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum` to the standardized negated
   increments `-(T k - μ) / σ` and sandwiching the threshold between points `z < x < y` via
   continuity of the standard Gaussian cumulative distribution function yields pointwise CDF
   convergence (`tendsto_cdf_renewalCountNat_sub_div`), from which weak convergence follows by
   `MeasureTheory.TendstoInDistribution.of_tendsto_cdf`.

Both the `ℝ≥0` real-time limit (with both `P[T 0]` and `(∫⁻ T 0 ∂P).toReal` formulations), the
limit along any `t_i → ∞` (in particular any sequence `t_n → ∞`), and the `ℝ` real-time limit are
provided. Zero waiting times are permitted.

## Main statements

* `TauCeti.Probability.integral_coe_pos_of_variance_ne_zero`,
  `TauCeti.Probability.lintegral_coe_lt_top_of_variance_ne_zero`,
  `TauCeti.Probability.lintegral_coe_pos_of_variance_ne_zero`,
  `TauCeti.Probability.toReal_lintegral_coe_eq_integral_of_variance_ne_zero` — under nonzero
  variance, a nonnegative random variable has finite, strictly positive extended mean equal to its
  real expectation.
* `TauCeti.Probability.renewalCountNat_sub_div_le_iff` — pathwise inversion of the standardized
  count sublevel event into a standardized arrival-time event.
* `TauCeti.Probability.tendsto_rounding_sub_div_sqrt_atTop` — asymptotic limit `x` of the rounded
  threshold `(m(s) * μ - s) / (σ * √(m(s)))`.
* `TauCeti.Probability.tendsto_cdf_renewalCountNat_sub_div` — pointwise convergence of the CDFs of
  the standardized renewal counts to `cdf (gaussianReal 0 1)`.
* `TauCeti.Probability.tendstoInDistribution_renewalCountNat_sub_div` — **the renewal central limit
  theorem** along `atTop : Filter ℝ≥0`, together with its extended-mean form
  `tendstoInDistribution_renewalCountNat_sub_div_toReal_lintegral`, its general filter/sequential
  form `tendstoInDistribution_renewalCountNat_sub_div_of_tendsto`, and its real-axis form
  `tendstoInDistribution_renewalCountNat_toNNReal_sub_div`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI, §5, Theorem 5.
* Vincent Tassion, *Applied Stochastic Processes*, lecture notes, ETH Zürich, 2025, Chapter 5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

/-! ### Almost-everywhere measurability and moments under positive variance -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- If every increment is almost-everywhere measurable, so is the natural-valued renewal count at
every time `t`. -/
@[fun_prop]
theorem aemeasurable_renewalCountNat {T : ℕ → Ω → ℝ≥0} (hT : ∀ n, AEMeasurable (T n) P)
    (t : ℝ≥0) : AEMeasurable (renewalCountNat T t) P := by
  set T' : ℕ → Ω → ℝ≥0 := fun n ↦ (hT n).mk (T n)
  have hT' (n : ℕ) : Measurable (T' n) := (hT n).measurable_mk
  refine (measurable_renewalCountNat hT' t).aemeasurable.congr ?_
  filter_upwards [ae_all_iff.2 fun n ↦ (hT n).ae_eq_mk] with ω hω
  have harr (n : ℕ) : arrival T' n ω = arrival T n ω := by
    rw [arrival_def, arrival_def]
    exact Finset.sum_congr rfl fun i _ ↦ (hω i).symm
  have hrc : renewalCount T' t ω = renewalCount T t ω := by
    simp only [renewalCount_def, harr]
  have hfn : (fun n ↦ arrival T' n ω) = fun n ↦ arrival T n ω := funext harr
  rw [renewalCountNat_def, renewalCountNat_def, hfn, hrc]

private lemma integrable_coe_of_variance_ne_zero [IsFiniteMeasure P] {X : Ω → ℝ≥0}
    (hX : AEMeasurable X P) (hvar : Var[fun ω ↦ (X ω : ℝ); P] ≠ 0) :
    Integrable (fun ω ↦ (X ω : ℝ)) P :=
  memLp_one_iff_integrable.1 <|
    (memLp_two_of_variance_ne_zero
      (measurable_coe_nnreal_real.comp_aemeasurable hX).aestronglyMeasurable hvar).mono_exponent
      one_le_two

/-- A nonnegative random variable on a finite measure space with nonzero variance has strictly
positive real expectation. -/
theorem integral_coe_pos_of_variance_ne_zero [IsFiniteMeasure P] {X : Ω → ℝ≥0}
    (hX : AEMeasurable X P) (hvar : Var[fun ω ↦ (X ω : ℝ); P] ≠ 0) :
    0 < ∫ ω, (X ω : ℝ) ∂P := by
  have hint := integrable_coe_of_variance_ne_zero hX hvar
  refine lt_of_le_of_ne (integral_nonneg fun ω ↦ (X ω).coe_nonneg) fun heq ↦ hvar ?_
  have hz : (fun ω ↦ (X ω : ℝ)) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω ↦ (X ω).coe_nonneg) hint).1 heq.symm
  rw [variance_congr hz, variance_zero]

/-- A nonnegative random variable on a finite measure space with nonzero variance has finite
extended mean. -/
theorem lintegral_coe_lt_top_of_variance_ne_zero [IsFiniteMeasure P] {X : Ω → ℝ≥0}
    (hX : AEMeasurable X P) (hvar : Var[fun ω ↦ (X ω : ℝ); P] ≠ 0) :
    ∫⁻ ω, (X ω : ℝ≥0∞) ∂P < ⊤ := by
  rw [lintegral_coe_eq_integral X (integrable_coe_of_variance_ne_zero hX hvar)]
  exact ENNReal.ofReal_lt_top

/-- A nonnegative random variable on a finite measure space with nonzero variance has strictly
positive extended mean. -/
theorem lintegral_coe_pos_of_variance_ne_zero [IsFiniteMeasure P] {X : Ω → ℝ≥0}
    (hX : AEMeasurable X P) (hvar : Var[fun ω ↦ (X ω : ℝ); P] ≠ 0) :
    0 < ∫⁻ ω, (X ω : ℝ≥0∞) ∂P := by
  rw [lintegral_coe_eq_integral X (integrable_coe_of_variance_ne_zero hX hvar), ENNReal.ofReal_pos]
  exact integral_coe_pos_of_variance_ne_zero hX hvar

/-- Under nonzero variance, the real part of the extended mean of a nonnegative random variable
equals its Bochner expectation. -/
theorem toReal_lintegral_coe_eq_integral_of_variance_ne_zero [IsFiniteMeasure P] {X : Ω → ℝ≥0}
    (hX : AEMeasurable X P) (hvar : Var[fun ω ↦ (X ω : ℝ); P] ≠ 0) :
    (∫⁻ ω, (X ω : ℝ≥0∞) ∂P).toReal = ∫ ω, (X ω : ℝ) ∂P := by
  rw [lintegral_coe_eq_integral X (integrable_coe_of_variance_ne_zero hX hvar),
    ENNReal.toReal_ofReal (integral_nonneg fun ω ↦ (X ω).coe_nonneg)]

/-- On a probability space, a nonnegative random variable with nonzero variance is not almost
surely zero. -/
theorem measure_eq_zero_lt_one_of_variance_ne_zero [IsProbabilityMeasure P] {X : Ω → ℝ≥0}
    (hX : AEMeasurable X P) (hvar : Var[fun ω ↦ (X ω : ℝ); P] ≠ 0) :
    P {ω | X ω = 0} < 1 := by
  refine lt_of_le_of_ne prob_le_one fun hfull ↦ ?_
  have hnull : NullMeasurableSet {ω | X ω = 0} P :=
    hX.nullMeasurable (measurableSet_singleton (0 : ℝ≥0))
  have hae : ∀ᵐ ω ∂P, X ω = 0 := (ae_mem_iff_measure_eq hnull).2 (hfull.trans measure_univ.symm)
  have hint0 : ∫ ω, (X ω : ℝ) ∂P = ∫ _ : Ω, (0 : ℝ) ∂P :=
    integral_congr_ae (hae.mono fun ω hω ↦ by simp [hω])
  rw [integral_zero] at hint0
  exact (integral_coe_pos_of_variance_ne_zero hX hvar).ne' hint0

end Moments

/-! ### Pathwise inversion and rounding asymptotics -/

section InversionAndRounding

/-- **Pathwise inversion for the standardized renewal count.** On a nonexplosive path, once `t > 0`
and `u = t / μ + x * σ * √(t / μ ^ 3) ≥ 0`, the standardized count at time `t` is at most `x` if
and only if the standardized negated `m`-th arrival time (with `m = ⌊u⌋₊ + 1`) lies strictly below
the rounded threshold `(m * μ - t) / (σ * √m)`. -/
theorem renewalCountNat_sub_div_le_iff {Ω : Type*} {T : ℕ → Ω → ℝ≥0} {ω : Ω}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop) {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ)
    (x : ℝ) {t : ℝ≥0} (ht : 0 < t) (hu : 0 ≤ (t : ℝ) / μ + x * σ * √((t : ℝ) / μ ^ 3)) :
    let m : ℕ := ⌊(t : ℝ) / μ + x * σ * √((t : ℝ) / μ ^ 3)⌋₊ + 1
    ((renewalCountNat T t ω : ℝ) - (t : ℝ) / μ) / (σ * √((t : ℝ) / μ ^ 3)) ≤ x ↔
      -((arrival T m ω : ℝ) - (m : ℝ) * μ) / (σ * √(m : ℝ)) <
        ((m : ℝ) * μ - (t : ℝ)) / (σ * √(m : ℝ)) := by
  intro m
  have htR : (0 : ℝ) < t := ht
  have hden_t : 0 < σ * √((t : ℝ) / μ ^ 3) := by positivity
  have hm_pos : (0 : ℝ) < m := by positivity
  have hden_m : 0 < σ * √(m : ℝ) := by positivity
  calc
    ((renewalCountNat T t ω : ℝ) - (t : ℝ) / μ) / (σ * √((t : ℝ) / μ ^ 3)) ≤ x
      ↔ (renewalCountNat T t ω : ℝ) ≤ (t : ℝ) / μ + x * σ * √((t : ℝ) / μ ^ 3) := by
        rw [div_le_iff₀ hden_t, sub_le_iff_le_add', mul_assoc]
    _ ↔ renewalCountNat T t ω ≤ ⌊(t : ℝ) / μ + x * σ * √((t : ℝ) / μ ^ 3)⌋₊ :=
        (Nat.le_floor_iff hu).symm
    _ ↔ ¬ (m ≤ renewalCountNat T t ω) := by
        dsimp only [m]
        omega
    _ ↔ (t : ℝ) < (arrival T m ω : ℝ) := by
        rw [le_renewalCountNat_iff hω, not_le, ← NNReal.coe_lt_coe]
    _ ↔ -((arrival T m ω : ℝ) - (m : ℝ) * μ) < (m : ℝ) * μ - (t : ℝ) := by
        constructor <;> intro h <;> linarith
    _ ↔ -((arrival T m ω : ℝ) - (m : ℝ) * μ) / (σ * √(m : ℝ)) <
          ((m : ℝ) * μ - (t : ℝ)) / (σ * √(m : ℝ)) :=
        (div_lt_div_iff_of_pos_right hden_m).symm

private lemma sqrt_div_cube_eq {μ s : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) :
    √(s / μ ^ 3) = √(s / μ) / μ := by
  have hdiv : s / μ ^ 3 = (s / μ) / μ ^ 2 := by ring
  rw [hdiv, Real.sqrt_div (div_nonneg hs hμ.le), Real.sqrt_sq hμ.le]

private lemma tendsto_target_atTop {μ σ : ℝ} (hμ : 0 < μ) (x : ℝ) :
    Tendsto (fun s : ℝ ↦ s / μ + x * σ * √(s / μ ^ 3)) atTop atTop := by
  have hw : Tendsto (fun s : ℝ ↦ √(s / μ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const hμ)
  have hprod : Tendsto (fun s : ℝ ↦ √(s / μ) * (√(s / μ) + x * σ / μ)) atTop atTop :=
    hw.atTop_mul_atTop₀ (tendsto_atTop_add_const_right atTop (x * σ / μ) hw)
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  rw [sqrt_div_cube_eq hμ hs, mul_add, Real.mul_self_sqrt (div_nonneg hs hμ.le)]
  ring

/-- The integer arrival index `⌊s / μ + x * σ * √(s / μ ^ 3)⌋₊ + 1` in the renewal inversion tends
to infinity as `s → ∞`. -/
theorem tendsto_natFloor_add_one_div_add_mul_sqrt_atTop {μ σ : ℝ} (hμ : 0 < μ) (x : ℝ) :
    Tendsto (fun s : ℝ ↦ ⌊s / μ + x * σ * √(s / μ ^ 3)⌋₊ + 1) atTop atTop := by
  rw [← tendsto_natCast_atTop_iff (R := ℝ)]
  refine tendsto_atTop_mono (f := fun s : ℝ ↦ s / μ + x * σ * √(s / μ ^ 3))
    (fun s ↦ ?_) (tendsto_target_atTop (σ := σ) hμ x)
  push_cast
  exact (Nat.lt_floor_add_one (s / μ + x * σ * √(s / μ ^ 3))).le

private lemma tendsto_sqrt_div_sqrt_index_one {μ σ : ℝ} (hμ : 0 < μ) (x : ℝ) :
    Tendsto (fun s : ℝ ↦
      √(s / μ) / √((⌊s / μ + x * σ * √(s / μ ^ 3)⌋₊ + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
  set u : ℝ → ℝ := fun s ↦ s / μ + x * σ * √(s / μ ^ 3)
  set m : ℝ → ℕ := fun s ↦ ⌊u s⌋₊ + 1
  have hw : Tendsto (fun s : ℝ ↦ √(s / μ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const hμ)
  have hinv_w : Tendsto (fun s : ℝ ↦ (√(s / μ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hw
  have hinv_s : Tendsto (fun s : ℝ ↦ (s / μ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_id.atTop_div_const hμ)
  -- First show `m s / (s / μ) → 1` by sandwiching `m s` between `u s` and `u s + 1`.
  have hu_ratio : Tendsto (fun s : ℝ ↦ u s / (s / μ)) atTop (𝓝 1) := by
    have hlim :
        Tendsto (fun s : ℝ ↦ 1 + x * σ / μ * (√(s / μ))⁻¹) atTop (𝓝 (1 + x * σ / μ * 0)) :=
      tendsto_const_nhds.add (hinv_w.const_mul _)
    rw [mul_zero, add_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hw_ne : √(s / μ) ≠ 0 := (Real.sqrt_pos.2 (div_pos hs hμ)).ne'
    have hdiv_w : √(s / μ) / (s / μ) = (√(s / μ))⁻¹ := by
      nth_rw 2 [← Real.mul_self_sqrt (div_pos hs hμ).le]
      rw [div_mul_eq_div_div, div_self hw_ne, one_div]
    have hmul_assoc :
        x * σ * (√(s / μ) / μ) / (s / μ) = x * σ / μ * (√(s / μ) / (s / μ)) := by ring
    dsimp only [u]
    rw [add_div, div_self (div_pos hs hμ).ne', sqrt_div_cube_eq hμ hs.le, hmul_assoc, hdiv_w]
  have hm_ratio : Tendsto (fun s : ℝ ↦ (m s : ℝ) / (s / μ)) atTop (𝓝 1) := by
    have hupper : Tendsto (fun s : ℝ ↦ u s / (s / μ) + (s / μ)⁻¹) atTop (𝓝 1) := by
      simpa using hu_ratio.add hinv_s
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hu_ratio hupper ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      refine div_le_div_of_nonneg_right ?_ (div_pos hs hμ).le
      dsimp only [m]
      push_cast
      exact (Nat.lt_floor_add_one (u s)).le
    · filter_upwards [eventually_gt_atTop (0 : ℝ),
        (tendsto_target_atTop (σ := σ) hμ x).eventually_ge_atTop 0] with s hs hu0
      rw [← one_div, ← add_div]
      refine div_le_div_of_nonneg_right ?_ (div_pos hs hμ).le
      dsimp only [m]
      push_cast
      linarith [Nat.floor_le hu0]
  -- Invert and take square roots to pass from `m s / (s / μ) → 1` to `√(s / μ) / √(m s) → 1`.
  have hinv_ratio : Tendsto (fun s : ℝ ↦ ((m s : ℝ) / (s / μ))⁻¹) atTop (𝓝 1) := by
    simpa using hm_ratio.inv₀ one_ne_zero
  have hsqrt : Tendsto (fun s : ℝ ↦ √(((m s : ℝ) / (s / μ))⁻¹)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sqrt_one] using
      (Real.continuous_sqrt.tendsto 1).comp hinv_ratio
  refine hsqrt.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  rw [inv_div, Real.sqrt_div (div_pos hs hμ).le]

/-- **Rounding estimate for the renewal central limit theorem.** For `μ > 0`, `σ > 0`, and `x : ℝ`,
setting `m(s) = ⌊s / μ + x * σ * √(s / μ ^ 3)⌋₊ + 1`, the standardized threshold
`(m(s) * μ - s) / (σ * √(m(s)))` converges to `x` as `s → ∞`. -/
theorem tendsto_rounding_sub_div_sqrt_atTop {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (x : ℝ) :
    Tendsto (fun s : ℝ ↦
      (((⌊s / μ + x * σ * √(s / μ ^ 3)⌋₊ + 1 : ℕ) : ℝ) * μ - s) /
        (σ * √((⌊s / μ + x * σ * √(s / μ ^ 3)⌋₊ + 1 : ℕ) : ℝ)))
      atTop (𝓝 x) := by
  set u : ℝ → ℝ := fun s ↦ s / μ + x * σ * √(s / μ ^ 3)
  set m : ℝ → ℕ := fun s ↦ ⌊u s⌋₊ + 1
  -- The fractional overshoot `(m s - u s) * μ / (σ * √(m s))` is bounded by `μ / (σ * √(m s)) → 0`.
  have hm_top : Tendsto (fun s : ℝ ↦ (m s : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_natFloor_add_one_div_add_mul_sqrt_atTop (σ := σ) hμ x)
  have hrem_upper : Tendsto (fun s : ℝ ↦ μ / (σ * √(m s : ℝ))) atTop (𝓝 0) := by
    have hinv : Tendsto (fun s : ℝ ↦ μ / σ * (√(m s : ℝ))⁻¹) atTop (𝓝 (μ / σ * 0)) :=
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hm_top)).const_mul (μ / σ)
    rw [mul_zero] at hinv
    exact hinv.congr fun s ↦ by ring
  have hrem : Tendsto (fun s : ℝ ↦ ((m s : ℝ) - u s) * μ / (σ * √(m s : ℝ))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrem_upper ?_ ?_
    · filter_upwards with s
      have hlt : u s < (m s : ℝ) := by
        dsimp only [m]
        push_cast
        exact Nat.lt_floor_add_one (u s)
      have hsub : 0 ≤ (m s : ℝ) - u s := sub_nonneg.2 hlt.le
      positivity
    · filter_upwards [(tendsto_target_atTop (σ := σ) hμ x).eventually_ge_atTop 0] with s hu0
      have h1 : (m s : ℝ) - u s ≤ 1 := by
        dsimp only [m]
        push_cast
        linarith [Nat.floor_le hu0]
      have hnum : ((m s : ℝ) - u s) * μ ≤ μ := by nlinarith
      exact div_le_div_of_nonneg_right hnum (by positivity)
  have hratio1 : Tendsto (fun s : ℝ ↦ √(s / μ) / √(m s : ℝ)) atTop (𝓝 1) :=
    tendsto_sqrt_div_sqrt_index_one (σ := σ) hμ x
  have hmain : Tendsto (fun s : ℝ ↦
      x * (√(s / μ) / √(m s : ℝ)) + ((m s : ℝ) - u s) * μ / (σ * √(m s : ℝ))) atTop (𝓝 x) := by
    simpa using (hratio1.const_mul x).add hrem
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  have hm0 : √(m s : ℝ) ≠ 0 := by positivity
  have hu_eq : u s * μ = s + x * σ * √(s / μ) := by
    dsimp only [u]
    rw [sqrt_div_cube_eq hμ hs]
    field_simp [hμ.ne']
  calc
    x * (√(s / μ) / √(m s : ℝ)) + ((m s : ℝ) - u s) * μ / (σ * √(m s : ℝ))
      = (x * σ * √(s / μ) + ((m s : ℝ) * μ - u s * μ)) / (σ * √(m s : ℝ)) := by
        field_simp [hσ.ne', hm0]
    _ = ((m s : ℝ) * μ - s) / (σ * √(m s : ℝ)) := by
        rw [hu_eq]
        ring

end InversionAndRounding

/-! ### The renewal central limit theorem -/

section RenewalCLT

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {T : ℕ → Ω → ℝ≥0} {Z : Ω' → ℝ}

/-- Standardized negated arrival times satisfy the scalar central limit theorem with standard
Gaussian limit. -/
private theorem tendstoInDistribution_neg_arrival_sub_div
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hvar : Var[fun ω ↦ (T 0 ω : ℝ); P] ≠ 0) :
    let μ := P[fun ω ↦ (T 0 ω : ℝ)]
    let σ := √Var[fun ω ↦ (T 0 ω : ℝ); P]
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ -((arrival T n ω : ℝ) - (n : ℝ) * μ) / (σ * √(n : ℝ)))
      atTop (id : ℝ → ℝ) (fun _ ↦ P) (gaussianReal 0 1) := by
  intro μ σ
  have hσ : σ ≠ 0 := Real.sqrt_ne_zero'.2 ((variance_nonneg _ _).lt_of_ne' hvar)
  have mT0 : AEMeasurable (fun ω ↦ (T 0 ω : ℝ)) P :=
    measurable_coe_nnreal_real.comp_aemeasurable (hid 0).aemeasurable_fst
  have intT0 : Integrable (fun ω ↦ (T 0 ω : ℝ)) P :=
    integrable_coe_of_variance_ne_zero (hid 0).aemeasurable_fst hvar
  let Y : ℕ → Ω → ℝ := fun k ω ↦ -((T k ω : ℝ) - μ) / σ
  have hlaw : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    ⟨measurable_id.aemeasurable, Measure.map_id⟩
  have hY0 : P[Y 0] = 0 := by
    simp only [Y, neg_div]
    rw [integral_neg, integral_div, integral_sub intT0 (integrable_const μ)]
    simp [μ]
  have hY1 : P[Y 0 ^ 2] = 1 := by
    have hsq : Y 0 ^ 2 = fun ω ↦ ((T 0 ω : ℝ) - μ) ^ 2 / σ ^ 2 := by
      ext ω
      simp only [Pi.pow_apply, Y, div_pow]
      ring
    rw [hsq, integral_div, ← variance_eq_integral mT0,
      Real.sq_sqrt (variance_nonneg _ _), div_self hvar]
  have hYi : iIndepFun Y P :=
    hindep.comp (fun _ (x : ℝ≥0) ↦ -((x : ℝ) - μ) / σ) (by fun_prop)
  have hYd : ∀ n, IdentDistrib (Y n) (Y 0) P P :=
    fun n ↦ (hid n).comp (u := fun (x : ℝ≥0) ↦ -((x : ℝ) - μ) / σ) (by fun_prop)
  refine (tendstoInDistribution_inv_sqrt_mul_sum hlaw hY0 hY1 hYi hYd).congr (fun n ↦ .of_forall ?_)
    EventuallyEq.rfl
  intro ω
  simp only [Y, arrival_def, NNReal.coe_sum]
  rw [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

private lemma ae_tendsto_arrival_atTop_of_variance_ne_zero
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hvar : Var[fun ω ↦ (T 0 ω : ℝ); P] ≠ 0) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ arrival T n ω) atTop atTop := by
  let T' : ℕ → Ω → ℝ≥0 := fun n ↦ (hid n).aemeasurable_fst.mk (T n)
  have hT'_ae (n : ℕ) : T n =ᵐ[P] T' n := (hid n).aemeasurable_fst.ae_eq_mk
  have hT'_meas : ∀ n, Measurable (T' n) := fun n ↦ (hid n).aemeasurable_fst.measurable_mk
  have hindep' : iIndepFun T' P := by
    refine (iIndepFun_iff_measure_inter_preimage_eq_mul).2 fun S s hs ↦ ?_
    have heq (i : ℕ) (hi : i ∈ S) : T' i ⁻¹' s i =ᵐ[P] T i ⁻¹' s i :=
      (hT'_ae i).symm.preimage (s i)
    rw [measure_congr (EventuallyEqSet.countable_iInter fun i ↦
      EventuallyEqSet.countable_iInter fun hi ↦ heq i hi),
      hindep.measure_inter_preimage_eq_mul S hs]
    exact Finset.prod_congr rfl fun i hi ↦ measure_congr (heq i hi).symm
  have hid' (n : ℕ) : IdentDistrib (T' n) (T' 0) P P :=
    ((IdentDistrib.of_ae_eq (hT'_meas n).aemeasurable (hT'_ae n).symm).trans (hid n)).trans
      (IdentDistrib.of_ae_eq (hid 0).aemeasurable_fst (hT'_ae 0))
  have hzero' : P {ω | T' 0 ω = 0} < 1 := by
    have hset : {ω | T' 0 ω = 0} =ᵐ[P] {ω | T 0 ω = 0} :=
      (hT'_ae 0).symm.mono fun ω hω ↦ by simp [hω]
    rw [measure_congr hset]
    exact measure_eq_zero_lt_one_of_variance_ne_zero (hid 0).aemeasurable_fst hvar
  filter_upwards [ae_tendsto_arrival_atTop hT'_meas hindep' hid' hzero',
    ae_all_iff.2 hT'_ae] with ω hω hEq
  simpa [arrival_def, hEq] using hω

/-- Sandwiching a family of sublevel probabilities `{R t ≤ x}` via an almost-sure event equivalence
`R t ω ≤ x ↔ W t ω < α t` with a threshold `α t → x` when the CDFs of `W t` converge pointwise to a
continuous limiting CDF `Φ`. -/
private lemma tendsto_cdf_of_eventually_ae_le_iff_lt {ι : Type*} {l : Filter ι}
    {R W : ι → Ω → ℝ} {α : ι → ℝ} {Φ : ℝ → ℝ} {x : ℝ}
    (hR : ∀ i, AEMeasurable (R i) P) (hW : ∀ i, AEMeasurable (W i) P)
    (hΦ : ContinuousAt Φ x) (hα : Tendsto α l (𝓝 x))
    (hW_cdf : ∀ y, Tendsto (fun i ↦ cdf (P.map (W i)) y) l (𝓝 (Φ y)))
    (hinv : ∀ᶠ i in l, ∀ᵐ ω ∂P, R i ω ≤ x ↔ W i ω < α i) :
    Tendsto (fun i ↦ cdf (P.map (R i)) x) l (𝓝 (Φ x)) := by
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · -- Lower bound: pick `z < x` with `a < Φ z`, then `W i ≤ z` and `z < α i` force `R i ≤ x`.
    obtain ⟨δ, hδ, hz⟩ := Metric.continuousAt_iff.1 hΦ (Φ x - a) (sub_pos.2 ha)
    set z : ℝ := x - δ / 2
    have hzx : z < x := sub_lt_self x (half_pos hδ)
    have haΦz : a < Φ z := by
      have hsub_z : z - x = -(δ / 2) := by ring
      have hdz : dist z x < δ := by
        rw [Real.dist_eq, hsub_z, abs_neg, abs_of_pos (half_pos hδ)]
        exact half_lt_self hδ
      have hdist := hz hdz
      rw [Real.dist_eq] at hdist
      linarith [(abs_lt.1 hdist).1]
    filter_upwards [hinv, (tendsto_order.1 hα).1 z hzx,
      (tendsto_order.1 (hW_cdf z)).1 a haΦz] with i hi hαz hW_gt
    refine hW_gt.trans_le ?_
    rw [Measure.cdf_map_of_aemeasurable P (hW i) z, Measure.cdf_map_of_aemeasurable P (hR i) x]
    refine ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae ?_)
    filter_upwards [hi] with ω hω hWz
    exact hω.2 (lt_of_le_of_lt hWz hαz)
  · -- Upper bound: pick `y > x` with `Φ y < b`, then `R i ≤ x` and `α i < y` force `W i ≤ y`.
    obtain ⟨δ, hδ, hy⟩ := Metric.continuousAt_iff.1 hΦ (b - Φ x) (sub_pos.2 hb)
    set y : ℝ := x + δ / 2
    have hxy : x < y := lt_add_of_pos_right x (half_pos hδ)
    have hΦyb : Φ y < b := by
      have hsub_y : y - x = δ / 2 := by ring
      have hdy : dist y x < δ := by
        rw [Real.dist_eq, hsub_y, abs_of_pos (half_pos hδ)]
        exact half_lt_self hδ
      have hdist := hy hdy
      rw [Real.dist_eq] at hdist
      linarith [(abs_lt.1 hdist).2]
    filter_upwards [hinv, (tendsto_order.1 hα).2 y hxy,
      (tendsto_order.1 (hW_cdf y)).2 b hΦyb] with i hi hαy hW_lt
    refine lt_of_le_of_lt ?_ hW_lt
    rw [Measure.cdf_map_of_aemeasurable P (hR i) x, Measure.cdf_map_of_aemeasurable P (hW i) y]
    refine ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae ?_)
    filter_upwards [hi] with ω hω hRx
    exact (hω.1 hRx).le.trans hαy.le

/-- **Pointwise CDF convergence in the renewal central limit theorem.** For i.i.d. nonnegative
increments with nonzero variance, the cumulative distribution function of the standardized renewal
count at `x` converges to `cdf (gaussianReal 0 1) x` as `t → ∞` in `ℝ≥0`. -/
theorem tendsto_cdf_renewalCountNat_sub_div
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hvar : Var[fun ω ↦ (T 0 ω : ℝ); P] ≠ 0) (x : ℝ) :
    let μ := P[fun ω ↦ (T 0 ω : ℝ)]
    let σ := √Var[fun ω ↦ (T 0 ω : ℝ); P]
    Tendsto
      (fun t : ℝ≥0 ↦
        cdf (P.map fun ω ↦
          ((renewalCountNat T t ω : ℝ) - (t : ℝ) / μ) / (σ * √((t : ℝ) / μ ^ 3))) x)
      atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  intro μ σ
  have hμ : 0 < μ := integral_coe_pos_of_variance_ne_zero (hid 0).aemeasurable_fst hvar
  have hσ : 0 < σ := Real.sqrt_pos.2 ((variance_nonneg _ _).lt_of_ne' hvar)
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have : NullSingletonClass ((gaussianReal 0 1).map (id : ℝ → ℝ)) := by rwa [Measure.map_id]
  set R : ℝ≥0 → Ω → ℝ := fun t ω ↦
    ((renewalCountNat T t ω : ℝ) - (t : ℝ) / μ) / (σ * √((t : ℝ) / μ ^ 3))
  set W : ℕ → Ω → ℝ := fun n ω ↦ -((arrival T n ω : ℝ) - (n : ℝ) * μ) / (σ * √(n : ℝ))
  set u : ℝ≥0 → ℝ := fun t ↦ (t : ℝ) / μ + x * σ * √((t : ℝ) / μ ^ 3)
  set m : ℝ≥0 → ℕ := fun t ↦ ⌊u t⌋₊ + 1
  have hR_meas (t : ℝ≥0) : AEMeasurable (R t) P := by
    have hN := aemeasurable_renewalCountNat (fun n ↦ (hid n).aemeasurable_fst) t
    fun_prop
  have hW_meas (n : ℕ) : AEMeasurable (W n) P := by
    have hA : AEMeasurable (arrival T n) P := by
      simp only [funext (arrival_def T n)]
      exact Finset.aemeasurable_fun_sum _ fun k _ ↦ (hid k).aemeasurable_fst
    fun_prop
  have hcoe_top : Tendsto (fun t : ℝ≥0 ↦ (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.2 tendsto_id
  have hu_top : Tendsto u atTop atTop := (tendsto_target_atTop (σ := σ) hμ x).comp hcoe_top
  have hm_top : Tendsto m atTop atTop :=
    (tendsto_natFloor_add_one_div_add_mul_sqrt_atTop (σ := σ) hμ x).comp hcoe_top
  have hW_clt := tendstoInDistribution_neg_arrival_sub_div hindep hid hvar
  refine tendsto_cdf_of_eventually_ae_le_iff_lt hR_meas (fun t ↦ hW_meas (m t))
    (Measure.continuous_cdf_of_noAtoms (gaussianReal 0 1)).continuousAt
    ((tendsto_rounding_sub_div_sqrt_atTop hμ hσ x).comp hcoe_top)
    (fun y ↦ by
      have h := hW_clt.tendsto_cdf y
      rw [Measure.map_id] at h
      exact h.comp hm_top) ?_
  have hnonexp := ae_tendsto_arrival_atTop_of_variance_ne_zero hindep hid hvar
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0), hu_top.eventually_ge_atTop 0] with t ht hu0
  filter_upwards [hnonexp] with ω hω
  exact renewalCountNat_sub_div_le_iff hω hμ hσ x ht hu0

/-- **The renewal central limit theorem.** Let `T 0, T 1, …` be independent, identically distributed
nonnegative waiting times with nonzero variance `σ² = Var[T 0; P]` and expectation `μ = P[T 0]`. As
`t → ∞` in `ℝ≥0`, the standardized renewal count `((N_t : ℝ) - t / μ) / (σ * √(t / μ ^ 3))`
converges in distribution to any standard normal random variable `Z`. -/
theorem tendstoInDistribution_renewalCountNat_sub_div
    (hZ : HasLaw Z (gaussianReal 0 1) P')
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hvar : Var[fun ω ↦ (T 0 ω : ℝ); P] ≠ 0) :
    TendstoInDistribution
      (fun (t : ℝ≥0) ω ↦
        ((renewalCountNat T t ω : ℝ) - (t : ℝ) / P[fun ω ↦ (T 0 ω : ℝ)]) /
          (√Var[fun ω ↦ (T 0 ω : ℝ); P] * √((t : ℝ) / P[fun ω ↦ (T 0 ω : ℝ)] ^ 3)))
      atTop Z (fun _ ↦ P) P' := by
  refine TendstoInDistribution.of_tendsto_cdf
    (fun t ↦ by
      have hN := aemeasurable_renewalCountNat (fun n ↦ (hid n).aemeasurable_fst) t
      fun_prop)
    hZ.aemeasurable fun x ↦ ?_
  rw [hZ.map_eq]
  exact tendsto_cdf_renewalCountNat_sub_div hindep hid hvar x

/-- **The renewal central limit theorem (extended-mean formulation).** Same limit as
`tendstoInDistribution_renewalCountNat_sub_div`, written in terms of the extended mean
`(∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P).toReal` of the waiting-time distribution. -/
theorem tendstoInDistribution_renewalCountNat_sub_div_toReal_lintegral
    (hZ : HasLaw Z (gaussianReal 0 1) P')
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hvar : Var[fun ω ↦ (T 0 ω : ℝ); P] ≠ 0) :
    TendstoInDistribution
      (fun (t : ℝ≥0) ω ↦
        ((renewalCountNat T t ω : ℝ) - (t : ℝ) / (∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P).toReal) /
          (√Var[fun ω ↦ (T 0 ω : ℝ); P] *
            √((t : ℝ) / (∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P).toReal ^ 3)))
      atTop Z (fun _ ↦ P) P' := by
  rw [toReal_lintegral_coe_eq_integral_of_variance_ne_zero (hid 0).aemeasurable_fst hvar]
  exact tendstoInDistribution_renewalCountNat_sub_div hZ hindep hid hvar

/-- **The renewal central limit theorem along any time family tending to infinity.** In particular,
this applies to every sequence `t : ℕ → ℝ≥0` with `Tendsto t atTop atTop`. -/
theorem tendstoInDistribution_renewalCountNat_sub_div_of_tendsto
    {ι : Type*} {l : Filter ι} {t : ι → ℝ≥0} (ht : Tendsto t l atTop)
    (hZ : HasLaw Z (gaussianReal 0 1) P')
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hvar : Var[fun ω ↦ (T 0 ω : ℝ); P] ≠ 0) :
    TendstoInDistribution
      (fun i ω ↦
        ((renewalCountNat T (t i) ω : ℝ) - (t i : ℝ) / P[fun ω ↦ (T 0 ω : ℝ)]) /
          (√Var[fun ω ↦ (T 0 ω : ℝ); P] * √((t i : ℝ) / P[fun ω ↦ (T 0 ω : ℝ)] ^ 3)))
      l Z (fun _ ↦ P) P' :=
  (tendstoInDistribution_renewalCountNat_sub_div hZ hindep hid hvar).comp_tendsto ht

/-- **The renewal central limit theorem on the real time axis.** As `t → ∞` in `ℝ`, the
standardized renewal count at `t.toNNReal` converges in distribution to a standard normal law. -/
theorem tendstoInDistribution_renewalCountNat_toNNReal_sub_div
    (hZ : HasLaw Z (gaussianReal 0 1) P')
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hvar : Var[fun ω ↦ (T 0 ω : ℝ); P] ≠ 0) :
    TendstoInDistribution
      (fun (t : ℝ) ω ↦
        ((renewalCountNat T t.toNNReal ω : ℝ) - t / P[fun ω ↦ (T 0 ω : ℝ)]) /
          (√Var[fun ω ↦ (T 0 ω : ℝ); P] * √(t / P[fun ω ↦ (T 0 ω : ℝ)] ^ 3)))
      atTop Z (fun _ ↦ P) P' := by
  refine ((tendstoInDistribution_renewalCountNat_sub_div hZ hindep hid hvar).comp_tendsto
    Real.tendsto_toNNReal_atTop).congr'
    (fun t ↦ by
      have hN := aemeasurable_renewalCountNat (fun n ↦ (hid n).aemeasurable_fst) t.toNNReal
      fun_prop)
    ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact .of_forall fun ω ↦ by simp [Real.coe_toNNReal t ht]

end RenewalCLT

end TauCeti.Probability

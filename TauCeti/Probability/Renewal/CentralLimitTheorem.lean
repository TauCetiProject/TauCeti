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
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cdf
import TauCeti.Probability.Moments.Variance

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
   `tendsto_natFloor_add_one_mul_sub_div_sqrt_atTop`): as `t → ∞`, `m(t) → ∞`,
   `m(t) / (t / μ) → 1`, and the rounding remainder `m(t) - u(t) ∈ (0, 1]` becomes negligible when
   divided by `√(m(t))`, so the threshold `(m(t) * μ - t) / (σ * √(m(t)))` converges to `x`.
3. **Comparison with the scalar i.i.d. central limit theorem**: applying Mathlib's
   `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum` to the standardized negated
   increments `-(T k - μ) / σ` and sandwiching the threshold via
   `MeasureTheory.tendsto_cdf_of_eventually_ae_le_iff_lt` and continuity of the standard Gaussian
   cumulative distribution function yields pointwise CDF convergence
   (`tendsto_cdf_renewalCountNat_sub_div`), from which weak convergence follows by
   `MeasureTheory.TendstoInDistribution.of_tendsto_cdf`.

Both the `ℝ≥0` real-time limit (with both `P[T 0]` and `(∫⁻ T 0 ∂P).toReal` formulations) and the
`ℝ` real-time limit are provided; precomposing with
`MeasureTheory.TendstoInDistribution.comp_tendsto` specializes them along any time family `t_i → ∞`
(in particular any sequence `t_n → ∞`). Zero waiting times are permitted.

## Main statements

* `TauCeti.Probability.renewalCountNat_sub_div_le_iff` — pathwise inversion of the standardized
  count sublevel event into a standardized arrival-time event.
* `TauCeti.Probability.tendsto_natFloor_add_one_div_add_mul_sqrt_atTop`,
  `TauCeti.Probability.tendsto_natFloor_add_one_mul_sub_div_sqrt_atTop` — divergence of the
  arrival index `m(s) = ⌊s / μ + x * σ * √(s / μ ^ 3)⌋₊ + 1` and convergence of the threshold
  `(m(s) * μ - s) / (σ * √(m(s)))` to `x`.
* `TauCeti.Probability.tendsto_cdf_renewalCountNat_sub_div` — pointwise convergence of the CDFs of
  the standardized renewal counts to `cdf (gaussianReal 0 1)`.
* `TauCeti.Probability.tendstoInDistribution_renewalCountNat_sub_div` — **the renewal central limit
  theorem** along `atTop : Filter ℝ≥0`, together with its extended-mean form
  `tendstoInDistribution_renewalCountNat_sub_div_toReal_lintegral` and its real-axis form
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
theorem tendsto_natFloor_add_one_mul_sub_div_sqrt_atTop {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ)
    (x : ℝ) :
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
    integrable_of_variance_ne_zero mT0.aestronglyMeasurable hvar
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
    have hA := aemeasurable_arrival (fun k ↦ (hid k).aemeasurable_fst) n
    fun_prop
  have hcoe_top : Tendsto (fun t : ℝ≥0 ↦ (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.2 tendsto_id
  have hu_top : Tendsto u atTop atTop := (tendsto_target_atTop (σ := σ) hμ x).comp hcoe_top
  have hm_top : Tendsto m atTop atTop :=
    (tendsto_natFloor_add_one_div_add_mul_sqrt_atTop (σ := σ) hμ x).comp hcoe_top
  have hW_clt := tendstoInDistribution_neg_arrival_sub_div hindep hid hvar
  refine tendsto_cdf_of_eventually_ae_le_iff_lt hR_meas (fun t ↦ hW_meas (m t))
    (Measure.continuous_cdf_of_noAtoms (gaussianReal 0 1)).continuousAt
    ((tendsto_natFloor_add_one_mul_sub_div_sqrt_atTop hμ hσ x).comp hcoe_top)
    (fun y ↦ by
      have h := hW_clt.tendsto_cdf y
      rw [Measure.map_id] at h
      exact h.comp hm_top) ?_
  have hzero : P {ω | T 0 ω = 0} < 1 := by
    simpa only [Function.comp_apply, NNReal.coe_eq_zero] using
      measure_setOf_eq_zero_lt_one_of_variance_ne_zero
        (measurable_coe_nnreal_real.comp_aemeasurable (hid 0).aemeasurable_fst) hvar
  have hnonexp := ae_tendsto_arrival_atTop hindep hid hzero
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0), hu_top.eventually_ge_atTop 0] with t ht hu0
  filter_upwards [hnonexp] with ω hω
  exact renewalCountNat_sub_div_le_iff hω hμ hσ x ht hu0

/-- **The renewal central limit theorem.** Let `T 0, T 1, …` be independent, identically distributed
nonnegative waiting times with nonzero variance `σ² = Var[T 0; P]` and expectation `μ = P[T 0]`. As
`t → ∞` in `ℝ≥0`, the standardized renewal count `((N_t : ℝ) - t / μ) / (σ * √(t / μ ^ 3))`
converges in distribution to any standard normal random variable `Z`. Precomposing with
`MeasureTheory.TendstoInDistribution.comp_tendsto` gives convergence along any time family (in
particular any sequence) tending to `atTop`. -/
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
  rw [TauCeti.MeasureTheory.toReal_lintegral_coe_eq_integral (hid 0).aemeasurable_fst]
  exact tendstoInDistribution_renewalCountNat_sub_div hZ hindep hid hvar

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

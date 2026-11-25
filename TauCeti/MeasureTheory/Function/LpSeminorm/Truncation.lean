/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Truncated second moments

For a real square-integrable function `X` and a level `ε`, the truncated square
`X ^ 2 𝟙{ε ≤ |X|}` is integrable (`MeasureTheory.MemLp.integrable_indicator_sq`), and on a
probability space the second moment splits as `E[X²] ≤ ε² + E[X²; ε ≤ |X|]`
(`MeasureTheory.MemLp.integral_sq_le_sq_add_integral_indicator`). The truncated second moment is
the quantity in the Lindeberg condition of the central limit theorem, and the split is how that
condition controls each individual variance. Only almost-everywhere measurability is used, through
`Integrable.indicator₀`.

For functions in `Lᵖ`, with finite positive `p` and values in a seminormed group, cutting off
values above increasing real norm levels makes the integral of the `p`-th power of the error
norm tend to zero. This supplies bounded approximations without requiring the underlying measure
to be finite. For `p = 2` this says that the discarded second absolute moment
`E[‖X‖²; R < ‖X‖]` tends to zero as the cutoff `R` tends to infinity
(`MeasureTheory.MemLp.tendsto_integral_indicator_norm_sq`). The cut-off function is bounded by
the level itself (`TauCeti.norm_indicator_setOf_norm_le_le`), and is measurable when the original
function is (`Measurable.indicator_setOf_norm_le`).

The integral of a norm cutoff also tends to the original integral for any integrable function
(`MeasureTheory.Integrable.tendsto_integral_ite_norm_le`). For a function of integral zero with
a finite absolute moment of order `k + 1`, the integral of its cutoff at a level `r > 0` has norm
at most that moment divided by `r ^ k`, for an arbitrary measure
(`MeasureTheory.MemLp.norm_integral_indicator_setOf_norm_le_le_of_integral_eq_zero`). Hence
weights that are small compared with `r ^ k` still send it to zero, with no sign condition on
the weights or cutoffs
(`MeasureTheory.MemLp.tendsto_mul_norm_integral_indicator_setOf_norm_le_nhds_zero`).
-/

public section

open Set Filter
open scoped ENNReal Topology NNReal

namespace TauCeti

/-- Keeping a function only where its norm is at most `R ≥ 0` gives values of norm at most `R`. -/
theorem norm_indicator_setOf_norm_le_le {α E : Type*} [SeminormedAddGroup E] (f : α → E)
    {R : ℝ} (hR : 0 ≤ R) (a : α) : ‖{x | ‖f x‖ ≤ R}.indicator f a‖ ≤ R := by
  by_cases h : ‖f a‖ ≤ R <;> simp [indicator, h, hR]

end TauCeti

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- The truncated square `X ^ 2 𝟙{ε ≤ |X|}` of a square-integrable function is integrable. -/
theorem MemLp.integrable_indicator_sq (hX : MemLp X 2 P) (ε : ℝ) :
    Integrable ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) P :=
  hX.integrable_sq.indicator₀
    (nullMeasurableSet_le aemeasurable_const
      (continuous_abs.measurable.comp_aemeasurable hX.aestronglyMeasurable.aemeasurable))

/-- Splitting the second moment at level `ε`: `E[X²] ≤ ε² + E[X²; ε ≤ |X|]`. -/
theorem MemLp.integral_sq_le_sq_add_integral_indicator [IsProbabilityMeasure P]
    (hX : MemLp X 2 P) (ε : ℝ) :
    ∫ ω, X ω ^ 2 ∂P ≤ ε ^ 2 + ∫ ω, ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) ω ∂P := by
  have h := hX.integrable_indicator_sq ε
  calc ∫ ω, X ω ^ 2 ∂P
      ≤ ∫ ω, (ε ^ 2 + ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) ω) ∂P := by
        refine integral_mono hX.integrable_sq ((integrable_const _).add h) fun ω ↦ ?_
        by_cases hω : ε ≤ |X ω|
        · rw [indicator_of_mem (s := {ω | ε ≤ |X ω|}) hω]
          linarith [sq_nonneg ε]
        · rw [indicator_of_notMem (s := {ω | ε ≤ |X ω|}) hω, add_zero,
            ← sq_abs (X ω)]
          have := abs_nonneg (X ω)
          nlinarith [not_le.mp hω]
    _ = ε ^ 2 + ∫ ω, ({ω | ε ≤ |X ω|}.indicator fun ω ↦ X ω ^ 2) ω ∂P := by
        rw [integral_add (integrable_const _) h]
        simp

/-- Cutting off an almost-everywhere strongly measurable function at a real norm level
preserves almost-everywhere strong measurability. -/
theorem AEStronglyMeasurable.ite_norm_le
    {E : Type*} [SeminormedAddCommGroup E] {f : Ω → E}
    (hf : AEStronglyMeasurable f P) (R : ℝ) :
    AEStronglyMeasurable (fun x ↦ if ‖f x‖ ≤ R then f x else 0) P := by
  exact (hf.indicator₀ (hf.norm.nullMeasurableSet_le aestronglyMeasurable_const)).congr
    (Filter.Eventually.of_forall fun x ↦ Set.indicator_apply _ _ x)

/-- Keeping a measurable function only where its norm is at most a real level `R` gives a
measurable function. -/
theorem _root_.Measurable.indicator_setOf_norm_le
    {E : Type*} [SeminormedAddGroup E] [MeasurableSpace E] [OpensMeasurableSpace E] {f : Ω → E}
    (hf : Measurable f) (R : ℝ) :
    Measurable ({x | ‖f x‖ ≤ R}.indicator f) :=
  hf.indicator (measurableSet_le (continuous_norm.measurable.comp hf) measurable_const)

/-- The integrals of the norm cutoffs of an integrable function converge to its integral
as the cutoff radius tends to infinity. -/
theorem Integrable.tendsto_integral_ite_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Ω → E} (hf : Integrable f P) :
    Filter.Tendsto (fun R : ℝ ↦ ∫ x, (if ‖f x‖ ≤ R then f x else 0) ∂P) Filter.atTop
      (𝓝 (∫ x, f x ∂P)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖)
    (.of_forall fun R ↦ hf.aestronglyMeasurable.ite_norm_le R)
    (.of_forall fun R ↦ .of_forall fun x ↦ ?_) hf.norm (.of_forall fun x ↦ ?_)
  · split_ifs <;> simp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ‖f x‖] with R hR
    simp [hR]

/-- Cutting off an `Lᵖ` function at a real norm level preserves `Lᵖ` membership,
including for infinite measures and arbitrary exponents. -/
theorem MemLp.ite_norm_le
    {E : Type*} [SeminormedAddCommGroup E] {p : ℝ≥0∞} {f : Ω → E}
    (hf : MemLp f p P) (R : ℝ) :
    MemLp (fun x ↦ if ‖f x‖ ≤ R then f x else 0) p P := by
  apply hf.of_le_eNorm (hf.aestronglyMeasurable.ite_norm_le R)
  exact Filter.Eventually.of_forall fun x ↦ by split_ifs <;> simp

/-- Cutting off an `Lᵖ` function above increasing real norm levels gives errors whose
`p`-th norm-power integrals tend to zero, for finite positive `p`. No finiteness assumption
on the measure is needed. -/
theorem MemLp.tendsto_lintegral_eNorm_ite_sub_rpow
    {E : Type*} [SeminormedAddCommGroup E] {p : ℝ≥0∞} {f : Ω → E}
    (hf : MemLp f p P) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    Filter.Tendsto (fun R : ℝ ↦ ∫⁻ x,
      ‖(if ‖f x‖ ≤ R then f x else 0) - f x‖ₑ ^ p.toReal ∂P) Filter.atTop (nhds 0) := by
  have hp_pos := ENNReal.toReal_pos hp0 hp
  have hmeas (R : ℝ) : AEStronglyMeasurable
      (fun x ↦ (if ‖f x‖ ≤ R then f x else 0) - f x) P :=
    (hf.aestronglyMeasurable.ite_norm_le R).sub hf.aestronglyMeasurable
  have hdom (R : ℝ) (x : Ω) :
      ‖(if ‖f x‖ ≤ R then f x else 0) - f x‖ₑ ^ p.toReal ≤ ‖f x‖ₑ ^ p.toReal := by
    split_ifs <;> simp [ENNReal.zero_rpow_of_pos hp_pos]
  have hfinite : ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂P < ∞ :=
    lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp0 hp hf.eLpNorm_lt_top
  have hlim (x : Ω) : Filter.Tendsto
      (fun R : ℝ ↦ ‖(if ‖f x‖ ≤ R then f x else 0) - f x‖ₑ ^ p.toReal)
        Filter.atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop ‖f x‖] with R hR
    simp [hR, ENNReal.zero_rpow_of_pos hp_pos]
  simpa using tendsto_lintegral_filter_of_dominated_convergence' (fun x ↦ ‖f x‖ₑ ^ p.toReal)
    (Filter.Eventually.of_forall fun R ↦ (hmeas R).eNorm.pow_const p.toReal)
    (Filter.Eventually.of_forall fun R ↦ Filter.Eventually.of_forall (hdom R))
    hfinite.ne (Filter.Eventually.of_forall hlim)

/-- The Bochner integral of the `p`-th power of the norm error from a norm cutoff
converges to zero for finite positive `p`, on an arbitrary measure space. -/
theorem MemLp.tendsto_integral_norm_ite_sub_rpow
    {E : Type*} [SeminormedAddCommGroup E] {p : ℝ≥0∞} {f : Ω → E}
    (hf : MemLp f p P) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    Filter.Tendsto (fun R : ℝ ↦ ∫ x,
      ‖(if ‖f x‖ ≤ R then f x else 0) - f x‖ ^ p.toReal ∂P) Filter.atTop (nhds 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (hf.tendsto_lintegral_eNorm_ite_sub_rpow hp0 hp)
  simp only [Function.comp_def, ENNReal.toReal_zero] at h
  convert h using 1
  ext R
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _) ?_]
  · congr 1
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg, ofReal_norm]
  · exact (Real.continuous_rpow_const ENNReal.toReal_nonneg).comp_aestronglyMeasurable
      ((hf.aestronglyMeasurable.ite_norm_le R).sub hf.aestronglyMeasurable).norm

/-- The discarded second moment tends to zero for a square-integrable variable. -/
theorem MemLp.tendsto_integral_indicator_norm_sq {E : Type*} [SeminormedAddCommGroup E]
    {X : Ω → E} (hX : MemLp X 2 P) :
    Tendsto (fun R : ℝ≥0 ↦
      ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂P)
      atTop (𝓝 0) := by
  refine ((hX.tendsto_integral_norm_ite_sub_rpow two_ne_zero ENNReal.ofNat_ne_top).comp
    (NNReal.tendsto_coe_atTop.mpr tendsto_id)).congr fun R ↦
      integral_congr_ae (.of_forall fun ω ↦ ?_)
  by_cases h : ‖X ω‖ ≤ R <;> simp [h, not_lt.mpr, not_le.mp]

/-- For a centered variable, the norm of its truncated mean is bounded by the absolute
moment of order `k+1` divided by the `k`-th power of the cutoff. The measure may be infinite.
If the original variable is nonintegrable, the retained part is nonintegrable as well,
and its Bochner integral is zero by convention. -/
theorem MemLp.norm_integral_indicator_setOf_norm_le_le_of_integral_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Ω → E}
    {k : ℕ} (hf : MemLp f (↑(k + 1 : ℕ)) P)
    (hmean : ∫ ω, f ω ∂P = 0) {r : ℝ} (hr : 0 < r) :
    ‖∫ ω, {ω' | ‖f ω'‖ ≤ r}.indicator f ω ∂P‖ ≤
      (∫ ω, ‖f ω‖ ^ (k + 1) ∂P) / r ^ k := by
  let S := {ω | r < ‖f ω‖}
  have hS : NullMeasurableSet S P :=
    nullMeasurableSet_lt aemeasurable_const hf.aestronglyMeasurable.norm.aemeasurable
  have hdom := (hf.integrable_norm_pow (Nat.succ_ne_zero k)).div_const (r ^ k)
  have hbound : ∀ᵐ ω ∂P, ‖S.indicator f ω‖ ≤ ‖f ω‖ ^ (k + 1) / r ^ k := by
    refine .of_forall fun ω ↦ ?_
    by_cases hω : ω ∈ S
    · rw [indicator_of_mem hω, le_div_iff₀ (pow_pos hr _), pow_succ, mul_comm]
      simp only [S, Set.mem_ofPred_eq] at hω
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hω.le _) (norm_nonneg _)
    · rw [indicator_of_notMem hω, norm_zero]
      positivity
  have hcomp : Sᶜ = {ω | ‖f ω‖ ≤ r} := by ext ω; simp [S]
  rw [← hcomp]
  by_cases hint : Integrable f P
  · have hsplit : (∫ ω, Sᶜ.indicator f ω ∂P) = -(∫ ω, S.indicator f ω ∂P) := by
      rw [integral_indicator₀ hS.compl, integral_indicator₀ hS,
        setIntegral_compl₀ hS hint, hmean, zero_sub]
    rw [hsplit, norm_neg, ← integral_div]
    exact norm_integral_le_of_norm_le hdom hbound
  · have htail := hdom.mono' (hf.aestronglyMeasurable.indicator₀ hS) hbound
    have hretained : ¬ Integrable (Sᶜ.indicator f) P := by
      intro h
      exact hint (by simpa only [indicator_self_add_compl] using htail.add h)
    rw [integral_undef hretained, norm_zero]
    exact div_nonneg (integral_nonneg fun _ ↦ by positivity) (pow_nonneg hr.le _)

/-- The weighted truncated mean tends to zero when the weight divided by the
cutoff to the power `k` tends to zero and the centered variable has moment `k + 1`. The cutoffs
and weights are arbitrary real families: a nonpositive cutoff keeps only zero values. -/
theorem MemLp.tendsto_mul_norm_integral_indicator_setOf_norm_le_nhds_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Ω → E}
    {k : ℕ} (hf : MemLp f (↑(k + 1 : ℕ)) P)
    (hmean : ∫ ω, f ω ∂P = 0)
    {ι : Type*} {l : Filter ι} {R w : ι → ℝ}
    (hlim : Tendsto (fun i ↦ w i / R i ^ k) l (𝓝 0)) :
    Tendsto (fun i ↦ w i * ‖∫ ω, {ω' | ‖f ω'‖ ≤ R i}.indicator f ω ∂P‖) l (𝓝 0) := by
  let C := ∫ ω, ‖f ω‖ ^ (k + 1) ∂P
  have hC : 0 ≤ C := integral_nonneg fun _ ↦ by positivity
  refine squeeze_zero_norm (fun i ↦ ?_)
    (by simpa only [abs_zero, mul_zero] using hlim.abs.const_mul C)
  rw [norm_mul, Real.norm_eq_abs, norm_norm]
  rcases le_or_gt (R i) 0 with hR | hR
  · -- At a nonpositive cutoff only zero values are kept, so the truncated mean vanishes.
    have h0 : {ω' | ‖f ω'‖ ≤ R i}.indicator f = 0 := by
      ext ω
      by_cases hω : ‖f ω‖ ≤ R i
      · rw [indicator_of_mem hω, Pi.zero_apply, ← norm_le_zero_iff]
        exact hω.trans hR
      · rw [indicator_of_notMem hω, Pi.zero_apply]
    rw [h0, Pi.zero_def, integral_zero, norm_zero, mul_zero]
    exact mul_nonneg hC (abs_nonneg _)
  · calc
      _ ≤ |w i| * (C / R i ^ k) := mul_le_mul_of_nonneg_left
          (hf.norm_integral_indicator_setOf_norm_le_le_of_integral_eq_zero hmean hR)
          (abs_nonneg _)
      _ = C * |w i / R i ^ k| := by rw [abs_div, abs_of_pos (pow_pos hR k)]; ring

end MeasureTheory

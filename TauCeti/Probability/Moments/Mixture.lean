/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Integral.Bind
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance
import TauCeti.MeasureTheory.Integral.Average

/-!
# Means and covariances of mixtures

The integral against a mixture of an observable integrable under the mixture is the integral of
its component means against the mixing measure. The covariance of a mixture is the integral of the
component covariances against the mixing measure plus the covariance of the component means under
the mixing measure; taking the same observable twice gives the law of total variance.

Throughout, the component family need only be almost everywhere measurable. Component means are
the component Bochner integrals; they are genuine averages only where the component is a
probability measure, and they are `0` by convention for observables that are not integrable under
the component or that take values in an incomplete space. With no assumption on the mixing measure,
if almost every component has mass at most a constant `c`, then for `1 ≤ p` the `Lᵖ` seminorm of
the component means is at most `c ^ (1 - 1 / p)` times the `Lᵖ` seminorm of the observable under
the mixture, so an observable in `Lᵖ` of the mixture has its component means in `Lᵖ` of the mixing
measure. In particular, for square-integrable observables the component means are
square-integrable and the component covariances are integrable. The laws of total covariance and
variance need almost every component to be a probability measure and the mixing measure to be
finite, but not of mass one: Mathlib's `covariance` and `variance` are defined for every measure
and center by raw integrals, not by normalized averages, and the identities hold in that sense for
every finite mixing measure. They fail for some infinite mixing measures. The covariance formula
applies to any pair of real observables that are square-integrable under the mixture, including
coordinates of a vector-valued law. The extended variance identity on the product of a finite
first measure and a probability second measure needs no integrability, only almost everywhere
strong measurability with respect to the product measure: for such an observable that is not
square-integrable, both sides are infinite. The extended variances, under an s-finite measure on
the second coordinate, of the sections of a function that is almost everywhere strongly measurable
on a product are almost everywhere measurable in the first coordinate.

The integration steps use Mathlib's kernel-composition theory through
`TauCeti.MeasureTheory.Integral.Bind`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {K : α → Measure β}

/-- `eLpNorm_integral_bind_le` for an observable that is almost everywhere strongly measurable
with respect to the mixture. -/
private theorem eLpNorm_integral_bind_le_of_aestronglyMeasurable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {X : β → E} {p : ℝ≥0∞} (hp : 1 ≤ p) {c : ℝ≥0}
    (hK : AEMeasurable K μ) (hmass : ∀ᵐ a ∂μ, K a Set.univ ≤ c)
    (hX : AEStronglyMeasurable X (μ.bind K)) :
    eLpNorm (fun a ↦ ∫ x, X x ∂K a) p μ ≤
      (c : ℝ≥0∞) ^ (1 - p.toReal⁻¹) * eLpNorm X p (μ.bind K) := by
  have hmean := Measure.aestronglyMeasurable_integral_bind hK hX
  rcases eq_or_ne p ∞ with rfl | hp_top
  · -- An essential bound of `X` under the mixture bounds almost every component mean, up to the
    -- mass of the component.
    rw [eLpNorm_exponent_top hmean, eLpNorm_exponent_top hX, ENNReal.toReal_top, inv_zero,
      sub_zero, ENNReal.rpow_one]
    refine eLpNormEssSup_le_of_ae_eNorm_bound ?_
    filter_upwards [hmass, Measure.ae_ae_of_ae_bind hK (ae_le_eLpNormEssSup (f := X))]
      with a hca ha
    calc ‖∫ x, X x ∂K a‖ₑ ≤ ∫⁻ x, ‖X x‖ₑ ∂K a := eNorm_integral_le_lintegral_eNorm _
      _ ≤ ∫⁻ _, eLpNormEssSup X (μ.bind K) ∂K a := lintegral_mono_ae ha
      _ = eLpNormEssSup X (μ.bind K) * K a Set.univ := lintegral_const _
      _ ≤ c * eLpNormEssSup X (μ.bind K) := by
          rw [mul_comm]
          exact mul_le_mul' hca le_rfl
  · -- Jensen's inequality under each component, integrated against the mixing measure.
    have hr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
    have hr0 : p.toReal ≠ 0 := (zero_lt_one.trans_le hr).ne'
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
    have hcr : (c : ℝ≥0∞) ^ (p.toReal - 1) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hr) ENNReal.coe_ne_top
    have hfac : (c : ℝ≥0∞) ^ (1 - p.toReal⁻¹) =
        ((c : ℝ≥0∞) ^ (p.toReal - 1)) ^ (1 / p.toReal) := by
      rw [← ENNReal.rpow_mul]
      congr 1
      field_simp
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hmean,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hX,
      Measure.lintegral_bind hK (hX.eNorm.pow_const _), hfac,
      ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← lintegral_const_mul' _ _ hcr]
    gcongr ?_ ^ _
    refine lintegral_mono_ae ?_
    filter_upwards [hmass] with a hca
    exact (enorm_integral_rpow_le_measure_univ_rpow_mul _ hr).trans
      (mul_le_mul' (ENNReal.rpow_le_rpow hca (sub_nonneg.2 hr)) le_rfl)

/-- If almost every component has mass at most `c`, then for `1 ≤ p` the `Lᵖ` seminorm of the
component Bochner integrals of an observable is at most `c ^ (1 - 1 / p)` times its `Lᵖ` seminorm
under the mixture. For `p = ∞` the factor is `c`. No measurability of the observable is needed:
the `Lᵖ` seminorm of a function that is not almost everywhere strongly measurable is `∞`. -/
theorem eLpNorm_integral_bind_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : β → E} {p : ℝ≥0∞} (hp : 1 ≤ p) {c : ℝ≥0} (hK : AEMeasurable K μ)
    (hmass : ∀ᵐ a ∂μ, K a Set.univ ≤ c) :
    eLpNorm (fun a ↦ ∫ x, X x ∂K a) p μ ≤
      (c : ℝ≥0∞) ^ (1 - p.toReal⁻¹) * eLpNorm X p (μ.bind K) := by
  by_cases hX : AEStronglyMeasurable X (μ.bind K)
  · exact eLpNorm_integral_bind_le_of_aestronglyMeasurable hp hK hmass hX
  rw [eLpNorm_of_not_aestronglyMeasurable hX]
  rcases eq_or_ne ((c : ℝ≥0∞) ^ (1 - p.toReal⁻¹)) 0 with h0 | h0
  · -- Then `c = 0`, so almost every component and component mean vanishes.
    have hc0 : (c : ℝ≥0∞) = 0 := by
      rcases ENNReal.rpow_eq_zero_iff.mp h0 with h | h
      · exact h.1
      · exact absurd h.1 ENNReal.coe_ne_top
    have hzero : (fun a ↦ ∫ x, X x ∂K a) =ᵐ[μ] 0 := by
      filter_upwards [hmass] with a ha
      have hKa : K a = 0 := Measure.measure_univ_eq_zero.mp (nonpos_iff_eq_zero.mp (hc0 ▸ ha))
      rw [hKa, integral_zero_measure, Pi.zero_apply]
    rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
    exact zero_le
  · rw [ENNReal.mul_top h0]
    exact le_top

/-- If almost every component has mass at most `c`, then for `1 ≤ p` the component Bochner
integrals of an observable in `Lᵖ` of the mixture, with values in a real normed space, are in `Lᵖ`
of the mixing measure. -/
theorem memLp_integral_bind {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : β → E}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {c : ℝ≥0} (hK : AEMeasurable K μ)
    (hmass : ∀ᵐ a ∂μ, K a Set.univ ≤ c) (hX : MemLp X p (μ.bind K)) :
    MemLp (fun a ↦ ∫ x, X x ∂K a) p μ := by
  have hexp : 0 ≤ 1 - p.toReal⁻¹ := by
    rcases eq_or_ne p ∞ with rfl | hp_top
    · simp
    · exact sub_nonneg.2 (inv_le_one_of_one_le₀ (by simpa using ENNReal.toReal_mono hp_top hp))
  exact (eLpNorm_integral_bind_le hp hK hmass).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hexp ENNReal.coe_ne_top) hX.eLpNorm_lt_top)

/-- Mathlib's covariance under a finite measure, expanded in terms of its total mass. For a
probability measure this is `covariance_eq_sub`. -/
private theorem covariance_eq_integral_mul_add {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsFiniteMeasure ν] {X Y : Ω → ℝ} (hX : MemLp X 2 ν) (hY : MemLp Y 2 ν) :
    covariance X Y ν = ν[X * Y] + (ν.real Set.univ - 2) * (ν[X] * ν[Y]) := by
  have hXY : Integrable (fun ω ↦ X ω * Y ω) ν := hX.integrable_mul hY
  have hXc : Integrable (fun ω ↦ X ω * ν[Y]) ν := (hX.integrable one_le_two).mul_const _
  have hcY : Integrable (fun ω ↦ ν[X] * Y ω) ν := (hY.integrable one_le_two).const_mul _
  have hc : Integrable (fun _ ↦ ν[X] * ν[Y]) ν := integrable_const _
  have hl : Integrable (fun ω ↦ X ω * Y ω - X ω * ν[Y]) ν := hXY.sub hXc
  have hr : Integrable (fun ω ↦ ν[X] * Y ω - ν[X] * ν[Y]) ν := hcY.sub hc
  simp_rw [covariance, sub_mul, mul_sub]
  rw [integral_sub hl hr, integral_sub hXY hXc, integral_sub hcY hc]
  simp_rw [integral_mul_const, integral_const_mul, integral_const, smul_eq_mul]
  simp only [Pi.mul_apply]
  ring

variable {X Y : β → ℝ}

/-- If almost every component is a finite measure, then almost every component covariance is the
component integral of the product plus the component mass minus `2`, times the product of the
component integrals. -/
private theorem covariance_ae_eq_bind (hK : AEMeasurable K μ)
    (hfin : ∀ᵐ a ∂μ, IsFiniteMeasure (K a))
    (hX : MemLp X 2 (μ.bind K)) (hY : MemLp Y 2 (μ.bind K)) :
    (fun a ↦ covariance X Y (K a)) =ᵐ[μ] fun a ↦ (∫ x, X x * Y x ∂K a) +
      ((K a).real Set.univ - 2) * ((∫ x, X x ∂K a) * ∫ x, Y x ∂K a) := by
  obtain ⟨hXae, _⟩ := (Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX
  obtain ⟨hYae, _⟩ := (Measure.memLp_two_bind_iff hK hY.aestronglyMeasurable).mp hY
  filter_upwards [hfin, hXae, hYae] with a hfa hXa hYa
  exact covariance_eq_integral_mul_add hXa hYa

/-- If almost every component has mass at most `c`, then the component covariances of two
square-integrable observables are integrable under the mixing law. -/
theorem integrable_covariance_bind {c : ℝ≥0} (hK : AEMeasurable K μ)
    (hmass : ∀ᵐ a ∂μ, K a Set.univ ≤ c)
    (hX : MemLp X 2 (μ.bind K)) (hY : MemLp Y 2 (μ.bind K)) :
    Integrable (fun a ↦ covariance X Y (K a)) μ := by
  have hprod := Measure.integrable_integral_bind hK (hX.integrable_mul hY)
  have hmeans := (memLp_integral_bind one_le_two hK hmass hX).integrable_mul
    (memLp_integral_bind one_le_two hK hmass hY)
  -- The component masses minus `2` are almost everywhere measurable and bounded.
  have hm : AEStronglyMeasurable (fun a ↦ (K a).real Set.univ - 2) μ :=
    (((Measure.measurable_coe MeasurableSet.univ).comp_aemeasurable hK).ennreal_toReal.sub_const
      2).aestronglyMeasurable
  have hbdd : ∀ᵐ a ∂μ, ‖(K a).real Set.univ - 2‖ ≤ c + 2 := by
    filter_upwards [hmass] with a ha
    have hle : (K a).real Set.univ ≤ c := by
      simpa only [measureReal_def, ENNReal.coe_toReal] using
        ENNReal.toReal_mono ENNReal.coe_ne_top ha
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [measureReal_nonneg (μ := K a) (s := Set.univ), c.coe_nonneg]
  simp only [Pi.mul_apply] at hprod hmeans
  exact (hprod.add (hmeans.bdd_mul hm hbdd)).congr (covariance_ae_eq_bind hK
    (hmass.mono fun _ ha ↦ ⟨ha.trans_lt ENNReal.coe_lt_top⟩) hX hY).symm

/-- The extended variances, under an s-finite measure, of the sections in the second coordinate
of a measurable function on a product form a measurable function of the first coordinate. -/
theorem measurable_evariance_prod_right {π : Measure β} [SFinite π] {F : α × β → ℝ}
    (hF : Measurable F) : Measurable fun a => evariance (fun w => F (a, w)) π := by
  have hm : StronglyMeasurable fun a => ∫ w, F (a, w) ∂π :=
    hF.stronglyMeasurable.integral_prod_right'
  exact Measurable.lintegral_prod_right' (f := fun p : α × β => ‖F p - ∫ w, F (p.1, w) ∂π‖ₑ ^ 2)
    ((hF.sub (hm.measurable.comp measurable_fst)).eNorm.pow_const 2)

/-- The extended variances, under an s-finite measure, of the sections in the second coordinate
of a function that is almost everywhere strongly measurable on a product form an almost everywhere
measurable function of the first coordinate. -/
theorem aemeasurable_evariance_prod_right {π : Measure β} [SFinite π] {F : α × β → ℝ}
    (hF : AEStronglyMeasurable F (μ.prod π)) :
    AEMeasurable (fun a => evariance (fun w => F (a, w)) π) μ := by
  refine (measurable_evariance_prod_right (π := π)
    hF.stronglyMeasurable_mk.measurable).aemeasurable.congr ?_
  filter_upwards [Measure.ae_ae_of_ae_prod hF.ae_eq_mk] with a ha
  exact (evariance_congr ha).symm

variable [IsFiniteMeasure μ]

/-- **Law of total covariance**: the covariance of a mixture over a finite mixing measure is the
integral of the component covariances against the mixing measure plus the covariance of the
component means under the mixing measure. Both covariances are Mathlib's, centered by raw
integrals. -/
theorem covariance_bind (hK : AEMeasurable K μ)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a))
    (hX : MemLp X 2 (μ.bind K)) (hY : MemLp Y 2 (μ.bind K)) :
    covariance X Y (μ.bind K) =
      (∫ a, covariance X Y (K a) ∂μ) +
        covariance (fun a ↦ ∫ x, X x ∂K a) (fun a ↦ ∫ x, Y x ∂K a) μ := by
  -- The mixture has the same total mass as the mixing measure.
  have htot : μ.bind K Set.univ = μ Set.univ := by
    rw [Measure.bind_apply MeasurableSet.univ hK,
      lintegral_congr_ae (hprob.mono fun a ha ↦ measure_univ), lintegral_one]
  have : IsFiniteMeasure (μ.bind K) := ⟨htot ▸ measure_lt_top μ _⟩
  have hreal : (μ.bind K).real Set.univ = μ.real Set.univ := by
    simpa only [measureReal_def] using congrArg ENNReal.toReal htot
  have hmass : ∀ᵐ a ∂μ, K a Set.univ ≤ (1 : ℝ≥0) := hprob.mono fun _ _ ↦ by simp
  have hmX := memLp_integral_bind one_le_two hK hmass hX
  have hmY := memLp_integral_bind one_le_two hK hmass hY
  -- Almost every component covariance is the component mean of the product minus the product of
  -- the component means.
  have hcov : (fun a ↦ covariance X Y (K a)) =ᵐ[μ]
      fun a ↦ (∫ x, X x * Y x ∂K a) - (∫ x, X x ∂K a) * ∫ x, Y x ∂K a := by
    filter_upwards [covariance_ae_eq_bind hK (hprob.mono fun _ _ ↦ inferInstance) hX hY, hprob]
      with a ha _
    rw [ha, probReal_univ]
    ring
  have hprod := Measure.integrable_integral_bind hK (hX.integrable_mul hY)
  have hmeans : Integrable (fun a ↦ (∫ x, X x ∂K a) * ∫ x, Y x ∂K a) μ :=
    hmX.integrable_mul hmY
  rw [covariance_eq_integral_mul_add hX hY, covariance_eq_integral_mul_add hmX hmY, hreal,
    integral_congr_ae hcov]
  simp only [Pi.mul_apply] at hprod hmeans ⊢
  have hXY : (∫ x, X x * Y x ∂μ.bind K) = ∫ a, ∫ x, X x * Y x ∂K a ∂μ :=
    Measure.integral_bind hK (hX.integrable_mul hY)
  rw [integral_sub hprod hmeans, hXY,
    Measure.integral_bind hK (hX.integrable one_le_two),
    Measure.integral_bind hK (hY.integrable one_le_two)]
  ring

/-- **Law of total variance**: the variance of a mixture over a finite mixing measure is the
integral of the component variances against the mixing measure plus the variance of the component
means under the mixing measure. Both variances are Mathlib's, centered by raw integrals. -/
theorem variance_bind (hK : AEMeasurable K μ)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a)) (hX : MemLp X 2 (μ.bind K)) :
    variance X (μ.bind K) = (∫ a, variance X (K a) ∂μ) +
      variance (fun a ↦ ∫ x, X x ∂K a) μ := by
  obtain ⟨hXae, _⟩ := (Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX
  rw [← covariance_self hX.aestronglyMeasurable.aemeasurable, covariance_bind hK hprob hX hX,
    covariance_self (memLp_integral_bind one_le_two (c := 1) hK
      (hprob.mono fun _ _ ↦ by simp) hX).aestronglyMeasurable.aemeasurable]
  congr 1
  exact integral_congr_ae
    (hXae.mono fun a ha ↦ covariance_self ha.aestronglyMeasurable.aemeasurable)

variable {π : Measure β} [IsProbabilityMeasure π] {F : α × β → ℝ}

/-- If an observable is almost everywhere strongly measurable on the product of a finite measure
and a probability measure, and both terms of the law of total variance on the product are finite,
then the observable is square-integrable. -/
private theorem memLp_prod_of_evariance_ne_top (hF : AEStronglyMeasurable F (μ.prod π))
    (hslice : ∫⁻ a, evariance (fun w => F (a, w)) π ∂μ ≠ ∞)
    (hmean : evariance (fun a => ∫ w, F (a, w) ∂π) μ ≠ ∞) : MemLp F 2 (μ.prod π) := by
  have hvm := aemeasurable_evariance_prod_right hF
  have hsl : ∀ᵐ a ∂μ, MemLp (fun w => F (a, w)) 2 π := by
    filter_upwards [ae_lt_top' hvm hslice, hF.prodMk_left] with a ha hma
    exact (evariance_lt_top_iff_memLp hma).mp ha
  have hmL := (evariance_lt_top_iff_memLp hF.integral_prod_right').mp hmean.lt_top
  have hvar : Integrable (fun a => variance (fun w => F (a, w)) π) μ :=
    integrable_toReal_of_lintegral_ne_top hvm hslice
  -- Each section's second moment is its variance plus its squared mean.
  rw [memLp_two_iff_integrable_sq hF, integrable_prod_iff (f := fun p ↦ F p ^ 2) (hF.pow 2)]
  refine ⟨hsl.mono fun a ha => ha.integrable_sq, (hvar.add hmL.integrable_sq).congr ?_⟩
  filter_upwards [hsl] with a ha
  simp only [Pi.add_apply, Real.norm_of_nonneg (sq_nonneg _), variance_eq_sub ha, Pi.pow_apply,
    sub_add_cancel]

/-- The law of total variance on the product of a finite measure and a probability measure: the
extended variance of `F` is the integral against the first factor of the variances in the second
coordinate plus the variance of the average over the second coordinate. The observable `F` need
only be almost everywhere strongly measurable with respect to the product measure; when it is not
square-integrable, both sides are infinite. -/
theorem evariance_prod_eq (hF : AEStronglyMeasurable F (μ.prod π)) :
    evariance F (μ.prod π) = ∫⁻ a, evariance (fun w => F (a, w)) π ∂μ +
      evariance (fun a => ∫ w, F (a, w) ∂π) μ := by
  by_cases hL : MemLp F 2 (μ.prod π)
  swap
  · rw [evariance_eq_top hF hL, eq_comm, ENNReal.add_eq_top]
    by_contra h
    exact hL (memLp_prod_of_evariance_ne_top hF (h ∘ .inl) (h ∘ .inr))
  let K : α → Measure (α × β) := fun a => π.map (Prod.mk a)
  have hK : AEMeasurable K μ := Measurable.map_prodMk_left.aemeasurable
  have hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a) :=
    .of_forall fun _ => inferInstance
  have hmass : ∀ᵐ a ∂μ, K a Set.univ ≤ (1 : ℝ≥0) := hprob.mono fun _ _ ↦ by simp
  have hbind : μ.bind K = μ.prod π := (Measure.prod_eq_of_sfinite μ π).symm
  have hX : MemLp F 2 (μ.bind K) := hbind ▸ hL
  have hae := ((Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX).1
  have hslice : ∀ᵐ a ∂μ, variance F (K a) = variance (fun w => F (a, w)) π ∧
      ∫ x, F x ∂K a = ∫ w, F (a, w) ∂π ∧ MemLp (fun w => F (a, w)) 2 π := by
    filter_upwards [hae] with a ha
    have hmp : AEMeasurable (Prod.mk a) π := measurable_prodMk_left.aemeasurable
    exact ⟨variance_map ha.aestronglyMeasurable.aemeasurable hmp,
      integral_map hmp ha.aestronglyMeasurable, ha.comp_of_map hmp⟩
  have hmean : MemLp (fun a => ∫ w, F (a, w) ∂π) 2 μ :=
    (memLp_integral_bind one_le_two hK hmass hX).ae_eq (hslice.mono fun a ha => ha.2.1)
  have hvarint : Integrable (fun a => variance (fun w => F (a, w)) π) μ := by
    refine (integrable_covariance_bind hK hmass hX hX).congr ?_
    filter_upwards [hae, hslice] with a ha hs
    rw [covariance_self ha.aestronglyMeasurable.aemeasurable, hs.1]
  have hlint : ∫⁻ a, evariance (fun w => F (a, w)) π ∂μ =
      ENNReal.ofReal (∫ a, variance (fun w => F (a, w)) π ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hvarint
      (Filter.Eventually.of_forall fun a => variance_nonneg _ _)]
    refine lintegral_congr_ae ?_
    filter_upwards [hslice] with a ha
    exact (ofReal_variance ha.2.2).symm
  have hvar := variance_bind hK hprob hX
  rw [hbind] at hvar
  rw [hlint, ← ofReal_variance hmean, ← ofReal_variance hL,
    ← ENNReal.ofReal_add (integral_nonneg fun a => variance_nonneg _ _) (variance_nonneg _ _),
    hvar, integral_congr_ae (hslice.mono fun a ha => ha.1),
    variance_congr (hslice.mono fun a ha => ha.2.1)]

end TauCeti.Probability

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} [IsFiniteMeasure μ] {X Y : β → ℝ}

/-- The law of total covariance for the composition of a finite measure and a Markov kernel. -/
theorem covariance_comp (κ : Kernel α β) [IsMarkovKernel κ]
    (hX : MemLp X 2 (κ ∘ₘ μ)) (hY : MemLp Y 2 (κ ∘ₘ μ)) :
    covariance X Y (κ ∘ₘ μ) = (∫ a, covariance X Y (κ a) ∂μ) +
      covariance (fun a ↦ ∫ x, X x ∂κ a) (fun a ↦ ∫ x, Y x ∂κ a) μ := by
  exact TauCeti.Probability.covariance_bind κ.aemeasurable
    (Filter.Eventually.of_forall fun _ ↦ inferInstance) hX hY

/-- The law of total variance for the composition of a finite measure and a Markov kernel. -/
theorem variance_comp (κ : Kernel α β) [IsMarkovKernel κ]
    (hX : MemLp X 2 (κ ∘ₘ μ)) :
    variance X (κ ∘ₘ μ) = (∫ a, variance X (κ a) ∂μ) +
      variance (fun a ↦ ∫ x, X x ∂κ a) μ := by
  exact TauCeti.Probability.variance_bind κ.aemeasurable
    (Filter.Eventually.of_forall fun _ ↦ inferInstance) hX

end ProbabilityTheory.Kernel

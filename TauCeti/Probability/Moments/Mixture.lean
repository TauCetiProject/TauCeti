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
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow

/-!
# Means and covariances of mixtures

The integral against a mixture of an observable integrable under the mixture is the integral of
its component means against the mixing measure. The covariance of a mixture is the integral of the
component covariances against the mixing measure plus the covariance of the component means under
the mixing measure; taking the same observable twice gives the law of total variance.

Throughout, the component family need only be almost everywhere measurable, and the components
need be probability measures only almost everywhere, so component means are genuine averages.
With no assumption on the mixing measure, an observable in `Lᵖ` of the mixture, for `1 ≤ p`, has
its component means in `Lᵖ` of the mixing measure. In particular, for square-integrable
observables the component means are square-integrable and the component covariances are
integrable. The laws of total covariance and variance need the mixing measure to be finite, but
not of mass one: Mathlib's `covariance` and `variance` are defined for every measure and center by
raw integrals, not by normalized averages, and the identities hold in that sense for every finite
mixing measure. They fail for some infinite mixing measures. The covariance formula applies to any
pair of real observables that are square-integrable under the mixture, including coordinates of a
vector-valued law. The extended variance identity on a product needs no integrability, only
almost everywhere strong measurability with respect to the product measure: for such an
observable that is not square-integrable, both sides are infinite. The extended variances of the
sections of such an observable are almost everywhere measurable in the remaining coordinate.

The integration steps use Mathlib's kernel-composition theory through
`TauCeti.MeasureTheory.Integral.Bind`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {K : α → Measure β}

/-- Component means of an observable in `Lᵖ` of the mixture, for `1 ≤ p` and with values in a
real normed space, are in `Lᵖ` of the mixing measure, even when the components are probability
measures only almost everywhere. -/
theorem memLp_integral_bind {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X : β → E}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hK : AEMeasurable K μ)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a)) (hX : MemLp X p (μ.bind K)) :
    MemLp (fun a ↦ ∫ x, X x ∂K a) p μ := by
  have hmean := Measure.aestronglyMeasurable_integral_bind hK hX.aestronglyMeasurable
  refine lt_of_le_of_lt ?_ hX.eLpNorm_lt_top
  rcases eq_or_ne p ∞ with rfl | hp_top
  · -- An essential bound of `X` under the mixture bounds almost every component mean.
    rw [eLpNorm_exponent_top hmean, eLpNorm_exponent_top hX.aestronglyMeasurable]
    refine eLpNormEssSup_le_of_ae_eNorm_bound ?_
    filter_upwards [hprob, Measure.ae_ae_of_ae_bind hK (ae_le_eLpNormEssSup (f := X))] with a hpa ha
    calc ‖∫ x, X x ∂K a‖ₑ ≤ ∫⁻ x, ‖X x‖ₑ ∂K a := eNorm_integral_le_lintegral_eNorm _
      _ ≤ ∫⁻ _, eLpNormEssSup X (μ.bind K) ∂K a := lintegral_mono_ae ha
      _ = eLpNormEssSup X (μ.bind K) := by simp
  · -- Jensen's inequality under each component, integrated against the mixing measure.
    have hr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp_top hp
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hmean,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hX.aestronglyMeasurable,
      Measure.lintegral_bind hK (hX.aestronglyMeasurable.eNorm.pow_const _)]
    gcongr ?_ ^ _
    refine lintegral_mono_ae ?_
    filter_upwards [hprob] with a hpa
    calc ‖∫ x, X x ∂K a‖ₑ ^ p.toReal ≤ (∫⁻ x, ‖X x‖ₑ ∂K a) ^ p.toReal := by
          gcongr
          exact eNorm_integral_le_lintegral_eNorm _
      _ ≤ ∫⁻ x, ‖X x‖ₑ ^ p.toReal ∂K a := by
          simpa using rpow_lintegral_le_measure_univ_rpow_mul (μ := K a)
            (u := fun x ↦ ‖X x‖ₑ) hr

variable {X Y : β → ℝ}

/-- Almost every component covariance is the component mean of the product minus the product of
the component means. -/
private theorem covariance_ae_eq_bind (hK : AEMeasurable K μ)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a))
    (hX : MemLp X 2 (μ.bind K)) (hY : MemLp Y 2 (μ.bind K)) :
    (fun a ↦ covariance X Y (K a)) =ᵐ[μ]
      fun a ↦ (∫ x, X x * Y x ∂K a) - (∫ x, X x ∂K a) * ∫ x, Y x ∂K a := by
  obtain ⟨hXae, _⟩ := (Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX
  obtain ⟨hYae, _⟩ := (Measure.memLp_two_bind_iff hK hY.aestronglyMeasurable).mp hY
  filter_upwards [hprob, hXae, hYae] with a hpa hXa hYa
  exact covariance_eq_sub hXa hYa

/-- The component covariances of two square-integrable observables are integrable under the
mixing law. -/
theorem integrable_covariance_bind (hK : AEMeasurable K μ)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a))
    (hX : MemLp X 2 (μ.bind K)) (hY : MemLp Y 2 (μ.bind K)) :
    Integrable (fun a ↦ covariance X Y (K a)) μ := by
  have hprod := Measure.integrable_integral_bind hK (hX.integrable_mul hY)
  have hmeans := (memLp_integral_bind one_le_two hK hprob hX).integrable_mul
    (memLp_integral_bind one_le_two hK hprob hY)
  simp only [Pi.mul_apply] at hprod hmeans
  exact (hprod.sub hmeans).congr (covariance_ae_eq_bind hK hprob hX hY).symm

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

/-- The extended variances of the sections in the second coordinate of a measurable function on
a product form a measurable function of the first coordinate. -/
theorem measurable_evariance_prod_right {π : Measure β} [SFinite π] {F : α × β → ℝ}
    (hF : Measurable F) : Measurable fun a => evariance (fun w => F (a, w)) π := by
  have hm : StronglyMeasurable fun a => ∫ w, F (a, w) ∂π :=
    hF.stronglyMeasurable.integral_prod_right'
  exact Measurable.lintegral_prod_right' (f := fun p : α × β => ‖F p - ∫ w, F (p.1, w) ∂π‖ₑ ^ 2)
    ((hF.sub (hm.measurable.comp measurable_fst)).eNorm.pow_const 2)

/-- The extended variances of the sections in the second coordinate of a function that is almost
everywhere strongly measurable on a product form an almost everywhere measurable function of the
first coordinate. -/
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
  have hmass : μ.bind K Set.univ = μ Set.univ := by
    rw [Measure.bind_apply MeasurableSet.univ hK,
      lintegral_congr_ae (hprob.mono fun a ha ↦ measure_univ), lintegral_one]
  have : IsFiniteMeasure (μ.bind K) := ⟨hmass ▸ measure_lt_top μ _⟩
  have hreal : (μ.bind K).real Set.univ = μ.real Set.univ := by
    simpa only [measureReal_def] using congrArg ENNReal.toReal hmass
  have hmX := memLp_integral_bind one_le_two hK hprob hX
  have hmY := memLp_integral_bind one_le_two hK hprob hY
  have hprod := Measure.integrable_integral_bind hK (hX.integrable_mul hY)
  have hmeans : Integrable (fun a ↦ (∫ x, X x ∂K a) * ∫ x, Y x ∂K a) μ :=
    hmX.integrable_mul hmY
  rw [covariance_eq_integral_mul_add hX hY, covariance_eq_integral_mul_add hmX hmY, hreal,
    integral_congr_ae (covariance_ae_eq_bind hK hprob hX hY)]
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
    covariance_self
      (memLp_integral_bind one_le_two hK hprob hX).aestronglyMeasurable.aemeasurable]
  congr 1
  exact integral_congr_ae
    (hXae.mono fun a ha ↦ covariance_self ha.aestronglyMeasurable.aemeasurable)

variable {π : Measure β} [IsProbabilityMeasure π] {F : α × β → ℝ}

/-- If both terms of the law of total variance on a product are finite, then the observable is
square-integrable. -/
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
    (memLp_integral_bind one_le_two hK hprob hX).ae_eq (hslice.mono fun a ha => ha.2.1)
  have hvarint : Integrable (fun a => variance (fun w => F (a, w)) π) μ := by
    refine (integrable_covariance_bind hK hprob hX hX).congr ?_
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

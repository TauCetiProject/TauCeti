/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Integral.Bind
public import Mathlib.Probability.Moments.Variance
import TauCeti.Probability.Moments.Covariance

/-!
# Means and covariances of mixtures

The integral against a mixture of an observable integrable under the mixture is the integral of
its component means against the mixing measure. The covariance of a mixture is the integral of the
component covariances against the mixing measure plus the covariance of the component means under
the mixing measure; taking the same observable twice gives the law of total variance.

Throughout, the component family need only be almost everywhere measurable. Component means are the
component Bochner integrals; they are genuine averages only where the component is a probability
measure, and they are `0` by convention for observables that are not integrable under the component
or that take values in an incomplete space. The `Lᵖ` bounds on the component means are
`MeasureTheory.Measure.eLpNorm_integral_bind_le` and `MeasureTheory.Measure.memLp_integral_bind`.
If almost every component has mass at most a constant, then for real observables in `Lᵖ` and
`L^q` of the mixture with conjugate exponents `p` and `q` the component covariances are
integrable; no assumption on the mixing measure is needed for this. The laws of total
covariance and variance need almost every component to be a probability measure and the mixing
measure to be finite, but not of mass one: Mathlib's `covariance` and `variance` are defined for
every measure and center by raw integrals, not by normalized averages, and the identities hold in
that sense for every finite mixing measure. They fail for some infinite mixing measures. The
covariance formula applies to any pair of real observables in `Lᵖ` and `L^q` of the mixture with
conjugate exponents, for instance two square-integrable observables, such as coordinates of a
vector-valued law, or an integrable observable and an essentially bounded one.

The integration steps use Mathlib's kernel-composition theory through
`TauCeti.MeasureTheory.Integral.Bind`. The extended-variance identity on a product of measures,
which is the law of total variance for the mixture of the sections, is in
`TauCeti.Probability.Moments.Variance`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {K : α → Measure β}

variable {X Y : β → ℝ} {p q : ℝ≥0∞} [p.HolderConjugate q]

/-- If almost every component is a finite measure, then for real observables in `Lᵖ` and `L^q` of
the mixture with conjugate exponents `p` and `q`, almost every component covariance is the
component integral of the product plus the component mass minus `2`, times the product of the
component integrals. -/
private theorem covariance_ae_eq_bind (hK : AEMeasurable K μ)
    (hfin : ∀ᵐ a ∂μ, IsFiniteMeasure (K a))
    (hX : MemLp X p (μ.bind K)) (hY : MemLp Y q (μ.bind K)) :
    (fun a ↦ covariance X Y (K a)) =ᵐ[μ] fun a ↦ (∫ x, X x * Y x ∂K a) +
      ((K a).real Set.univ - 2) * ((∫ x, X x ∂K a) * ∫ x, Y x ∂K a) := by
  filter_upwards [hfin, Measure.ae_memLp_bind hK hX, Measure.ae_memLp_bind hK hY]
    with a hfa hXa hYa
  exact covariance_eq_integral_mul_add (hXa.integrable (ENNReal.HolderConjugate.one_le p q))
    (hYa.integrable (ENNReal.HolderConjugate.one_le q p)) (hXa.integrable_mul hYa)

/-- If almost every component has mass at most `c`, then for real observables in `Lᵖ` and `L^q`
of the mixture with conjugate exponents `p` and `q`, the component covariances are integrable
under the mixing measure. -/
theorem integrable_covariance_bind {c : ℝ≥0} (hK : AEMeasurable K μ)
    (hmass : ∀ᵐ a ∂μ, K a Set.univ ≤ c)
    (hX : MemLp X p (μ.bind K)) (hY : MemLp Y q (μ.bind K)) :
    Integrable (fun a ↦ covariance X Y (K a)) μ := by
  have hprod := Measure.integrable_integral_bind hK (hX.integrable_mul hY)
  have hmeans := (Measure.memLp_integral_bind (ENNReal.HolderConjugate.one_le p q) hK hmass
    hX).integrable_mul
    (Measure.memLp_integral_bind (ENNReal.HolderConjugate.one_le q p) hK hmass hY)
  -- The component masses minus `2` are almost everywhere measurable and bounded.
  have hm : AEStronglyMeasurable (fun a ↦ (K a).real Set.univ - 2) μ := by
    simpa only [measureReal_def, Function.comp_apply] using
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

variable [IsFiniteMeasure μ]

/-- **Law of total covariance**: for real observables in `Lᵖ` and `L^q` of the mixture with
conjugate exponents `p` and `q`, for instance two square-integrable observables, if the mixing
measure is finite and almost every component is a probability measure, then the covariance of the
mixture is the integral of the component covariances against the mixing measure plus the
covariance of the component means under the mixing measure. Both covariances are Mathlib's,
centered by raw integrals. -/
theorem covariance_bind (hK : AEMeasurable K μ)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a))
    (hX : MemLp X p (μ.bind K)) (hY : MemLp Y q (μ.bind K)) :
    covariance X Y (μ.bind K) =
      (∫ a, covariance X Y (K a) ∂μ) +
        covariance (fun a ↦ ∫ x, X x ∂K a) (fun a ↦ ∫ x, Y x ∂K a) μ := by
  have hp := ENNReal.HolderConjugate.one_le p q
  have hq := ENNReal.HolderConjugate.one_le q p
  -- The mixture has the same total mass as the mixing measure.
  have htot : μ.bind K Set.univ = μ Set.univ := by
    rw [Measure.bind_apply MeasurableSet.univ hK,
      lintegral_congr_ae (hprob.mono fun a ha ↦ measure_univ), lintegral_one]
  have : IsFiniteMeasure (μ.bind K) := ⟨htot ▸ measure_lt_top μ _⟩
  have hreal : (μ.bind K).real Set.univ = μ.real Set.univ := by
    simpa only [measureReal_def] using congrArg ENNReal.toReal htot
  have hmass : ∀ᵐ a ∂μ, K a Set.univ ≤ (1 : ℝ≥0) := hprob.mono fun _ _ ↦ by simp
  have hmX := Measure.memLp_integral_bind hp hK hmass hX
  have hmY := Measure.memLp_integral_bind hq hK hmass hY
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
  rw [covariance_eq_integral_mul_add (hX.integrable hp) (hY.integrable hq) (hX.integrable_mul hY),
    covariance_eq_integral_mul_add (hmX.integrable hp) (hmY.integrable hq) hmeans, hreal,
    integral_congr_ae hcov]
  simp only [Pi.mul_apply] at hprod hmeans ⊢
  have hXY : (∫ x, X x * Y x ∂μ.bind K) = ∫ a, ∫ x, X x * Y x ∂K a ∂μ :=
    Measure.integral_bind hK (hX.integrable_mul hY)
  rw [integral_sub hprod hmeans, hXY, Measure.integral_bind hK (hX.integrable hp),
    Measure.integral_bind hK (hY.integrable hq)]
  ring

/-- **Law of total variance**: for a real observable that is square-integrable under the mixture,
if the mixing measure is finite and almost every component is a probability measure, then the
variance of the mixture is the integral of the component variances against the mixing measure plus
the variance of the component means under the mixing measure. Both variances are Mathlib's,
centered by raw integrals. -/
theorem variance_bind (hK : AEMeasurable K μ)
    (hprob : ∀ᵐ a ∂μ, IsProbabilityMeasure (K a)) (hX : MemLp X 2 (μ.bind K)) :
    variance X (μ.bind K) = (∫ a, variance X (K a) ∂μ) +
      variance (fun a ↦ ∫ x, X x ∂K a) μ := by
  obtain ⟨hXae, _⟩ := (Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX
  rw [← covariance_self hX.aestronglyMeasurable.aemeasurable, covariance_bind hK hprob hX hX,
    covariance_self (Measure.memLp_integral_bind one_le_two (c := 1) hK
      (hprob.mono fun _ _ ↦ by simp) hX).aestronglyMeasurable.aemeasurable]
  congr 1
  exact integral_congr_ae
    (hXae.mono fun a ha ↦ covariance_self ha.aestronglyMeasurable.aemeasurable)

end TauCeti.Probability

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} [IsFiniteMeasure μ] {X Y : β → ℝ}

/-- The law of total covariance for the composition of a finite measure and a Markov kernel, for
real observables in `Lᵖ` and `L^q` of the composition with conjugate exponents `p` and `q`, for
instance two square-integrable observables. -/
theorem covariance_comp (κ : Kernel α β) [IsMarkovKernel κ] {p q : ℝ≥0∞} [p.HolderConjugate q]
    (hX : MemLp X p (κ ∘ₘ μ)) (hY : MemLp Y q (κ ∘ₘ μ)) :
    covariance X Y (κ ∘ₘ μ) = (∫ a, covariance X Y (κ a) ∂μ) +
      covariance (fun a ↦ ∫ x, X x ∂κ a) (fun a ↦ ∫ x, Y x ∂κ a) μ := by
  exact TauCeti.Probability.covariance_bind κ.aemeasurable
    (Filter.Eventually.of_forall fun _ ↦ inferInstance) hX hY

/-- The law of total variance for the composition of a finite measure and a Markov kernel, for a
real observable that is square-integrable under the composition. -/
theorem variance_comp (κ : Kernel α β) [IsMarkovKernel κ]
    (hX : MemLp X 2 (κ ∘ₘ μ)) :
    variance X (κ ∘ₘ μ) = (∫ a, variance X (κ a) ∂μ) +
      variance (fun a ↦ ∫ x, X x ∂κ a) μ := by
  exact TauCeti.Probability.variance_bind κ.aemeasurable
    (Filter.Eventually.of_forall fun _ ↦ inferInstance) hX

end ProbabilityTheory.Kernel

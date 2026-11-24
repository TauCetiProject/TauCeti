/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.Variance
public import TauCeti.MeasureTheory.Function.L2Space.MeanZero
public import TauCeti.MeasureTheory.Function.Lp.Norm
public import TauCeti.MeasureTheory.Integral.Lebesgue.SetOfEqZero
public import TauCeti.Probability.Moments.Mixture
import TauCeti.MeasureTheory.Function.L2Space.Basic
import TauCeti.MeasureTheory.Function.Lp.Const
import TauCeti.MeasureTheory.Function.Lp.Iterated
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Probability.Moments.Covariance

/-!
# The mean squared distance between two independent copies and nonzero-variance bounds

Let `f` be a square-integrable function, with values in a real Hilbert space, on a finite measure
space `(α, μ)`. Then

`∫∫ ‖f x - f y‖² dμ(x) dμ(y) = 2 (μ(α) ∫ ‖f‖² dμ - ‖∫ f dμ‖²)`.

For a probability measure the right-hand side is twice the variance `∫ ‖f‖² dμ - ‖∫ f dμ‖²` of
`f`, the trace of its covariance: the mean squared distance between two independent samples of `f`
is twice its variance. Expanding `‖u - v‖² = ‖u‖² + ‖v‖² - 2 ⟪u, v⟫`, the cross term integrates
to `‖∫ f dμ‖²` because the two coordinates are integrated separately.

This identity is what turns the strong-convexity remainder of an interaction energy along a
transport plan, an integral over pairs of transported pairs, into the variance of the
displacement.

The file also records two consequences of nonzero variance `Var[X; μ] ≠ 0` on a finite measure
space: strict positivity of the integral (expectation on a probability space) of an almost
everywhere strongly measurable, almost everywhere nonnegative real function, and nondegeneracy
`μ {ω | X ω = 0} < μ univ` of a real-valued function. For a family of square-integrable real
functions on finite measure spaces, the deviation of each from its own integral (its mean when the
measure is a probability measure) tends to zero in measure when the variances tend to zero
(Chebyshev), and almost everywhere on a fixed finite measure space when the variances are summable
(Borel--Cantelli); the integrals themselves may vary and need not converge.

## Main statements

* `MeasureTheory.MemLp.integrable_norm_sub_sq_prod`: for `f ∈ L²(μ)` and a finite measure `μ`,
  the function `(x, y) ↦ ‖f x - f y‖²` is integrable for `μ ⊗ μ`.
* `TauCeti.integral_norm_sub_sq_prod`: the identity above.
* `MeasureTheory.MeasurePreserving.evariance_fun_comp`: the variance is invariant under
  composition with a measure-preserving measurable embedding.
* `ProbabilityTheory.variance_eq_norm_sub_const_sq`: for `f ∈ L²(μ)` on a finite measure space,
  `Var[f; μ] = ‖f - ∫ f dμ‖²`.
* `MeasureTheory.Measure.norm_starProjection_meanZeroL2_sq_eq_variance`: on a probability space,
  the squared `L²` norm of the projection onto `L²₀(P)` equals the variance.
* `ProbabilityTheory.tendsto_variance_of_tendsto_eLpNorm_sub`: variance is continuous under
  L² convergence on a finite measure space.
* `TauCeti.variance_eq_integral_sq_add`: the variance of a square-integrable function under a
  finite measure of mass `m` is `∫ X² + (m - 2) (∫ X)²`.
* `TauCeti.integral_eq_zero_of_evariance_ne_top` and `TauCeti.lintegral_enorm_sq_le_evariance`:
  under a measure of infinite mass, a function of finite extended variance has integral `0`, and
  the lower integral of `‖X‖ₑ ^ 2` is at most the extended variance of `X`.
* `TauCeti.memLp_two_of_evariance_ne_top`: under any measure, an almost everywhere strongly
  measurable function of finite extended variance is square-integrable.
* `TauCeti.Probability.evariance_prod_eq`: the law of total variance on the product of a finite
  measure and a probability measure, for any almost everywhere strongly measurable function.
* `TauCeti.Probability.lintegral_enorm_sq_prod_le_lintegral_evariance`: if the second factor of a
  product has infinite mass, the second moment of any function on the product is at most the lower
  integral of the extended variances of its sections in the second coordinate.
* `TauCeti.Probability.memLp_two_prod_of_lintegral_evariance_ne_top`: an almost everywhere strongly
  measurable function on a product of two s-finite measures is square-integrable if the lower
  integrals of the extended variances of its sections in both coordinates are finite.
* `TauCeti.Probability.memLp_two_prod_of_evariance_ne_top`: an almost everywhere strongly measurable
  function on the product of any measure and an s-finite measure is square-integrable if the lower
  integral of the extended variances of its sections in the second coordinate is finite and the
  extended variance of their integrals is finite.
* `MeasureTheory.Integrable.evariance_integral_prod_le`: for a function integrable on the product
  of two s-finite measures, the extended variance of its integral over the second factor is at
  most the mass of that factor times the lower integral of the extended variances of its sections
  in the first coordinate.
* `TauCeti.Probability.evariance_prod_le`: the two-factor Efron–Stein bound for a function that is
  almost everywhere strongly measurable on the product of an s-finite measure and a probability
  measure.
* `TauCeti.Probability.variance_weighted_coordinate_sum`,
  `TauCeti.Probability.variance_weighted_coordinate_sum_of_covariance_eq_zero` and
  `TauCeti.Probability.measure_weighted_coordinate_sum_sub_integral_ge`: variance and Chebyshev
  bounds for weighted sums of square-integrable variables that are pairwise independent or
  pairwise uncorrelated.
* `TauCeti.Probability.tendsto_measure_abs_sub_integral_ge_of_tendsto_variance`: vanishing
  variances imply that the deviations of square-integrable functions from their own integrals
  (their means when each measure is a probability measure) tend to zero in measure, including on
  varying finite measure spaces.
* `TauCeti.Probability.ae_tendsto_sub_integral_of_summable_variance`: on a finite measure space,
  summable variances imply that the deviations of square-integrable functions from their own
  integrals (their means when the measure is a probability measure) tend to zero almost everywhere.
* `MeasureTheory.AEStronglyMeasurable.integral_pos_of_nonneg_ae_of_variance_ne_zero`: on a finite
  measure space, an almost everywhere strongly measurable, almost everywhere nonnegative real
  function with nonzero variance has strictly positive integral.
* `TauCeti.measure_setOf_eq_zero_lt_measure_univ_of_variance_ne_zero`: on a finite measure space,
  a real-valued function with nonzero variance satisfies `μ {ω | X ω = 0} < μ univ`.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace ProbabilityTheory

/-- For `f ∈ L²(μ)` on a finite measure space, the variance of `f` equals
`‖f - Lp.const 2 μ (∫ x, f x ∂μ)‖ ^ 2`. -/
theorem variance_eq_norm_sub_const_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (f : Lp ℝ 2 μ) :
    variance (f : α → ℝ) μ = ‖f - Lp.const 2 μ (∫ x, f x ∂μ)‖ ^ 2 := by
  rw [variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable,
    ← Lp.integral_norm_sq_eq_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub_const f (∫ x, f x ∂μ)] with x hx
  rw [hx, Real.norm_eq_abs, sq_abs]

/-- On a probability space, the squared `L²` norm of the projection onto `L²₀(P)` is the
variance. -/
theorem _root_.MeasureTheory.Measure.norm_starProjection_meanZeroL2_sq_eq_variance
    {X : Type*} [MeasurableSpace X] {P : Measure X} [IsProbabilityMeasure P] (f : Lp ℝ 2 P) :
    ‖(MeasureTheory.Measure.meanZeroL2 P ℝ).starProjection f‖ ^ 2 = variance (f : X → ℝ) P := by
  rw [MeasureTheory.Measure.starProjection_meanZeroL2, variance_eq_norm_sub_const_sq]

/-- The variance is continuous under L² convergence on a finite measure space. -/
theorem tendsto_variance_of_tendsto_eLpNorm_sub {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} {g : ι → α → ℝ} {l : Filter ι}
    (hf : MemLp f 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (ht : Tendsto (fun i ↦ eLpNorm (g i - f) 2 μ) l (𝓝 0)) :
    Tendsto (fun i ↦ variance (g i) μ) l (𝓝 (variance f μ)) := by
  have hLp : Tendsto (fun i ↦ (hg i).toLp (g i)) l (𝓝 (hf.toLp f)) := by
    rw [tendsto_iff_edist_tendsto_0]
    simpa only [Lp.edist_toLp_toLp] using ht
  have hmean_eq (u : α → ℝ) (hu : MemLp u 2 μ) :
      inner ℝ (Lp.const 2 μ (1 : ℝ)) (hu.toLp u) = ∫ x, u x ∂μ := by
    rw [L2.inner_const_one]
    exact integral_congr_ae hu.coeFn_toLp
  have hmeanLp : Tendsto (fun i ↦ inner ℝ (Lp.const 2 μ (1 : ℝ)) ((hg i).toLp (g i))) l
      (𝓝 (inner ℝ (Lp.const 2 μ (1 : ℝ)) (hf.toLp f))) :=
    tendsto_const_nhds.inner hLp
  have hmean : Tendsto (fun i ↦ ∫ x, g i x ∂μ) l (𝓝 (∫ x, f x ∂μ)) := by
    simpa only [hmean_eq] using hmeanLp
  have hconst : Tendsto (fun i ↦ Lp.const 2 μ (∫ x, g i x ∂μ)) l
      (𝓝 (Lp.const 2 μ (∫ x, f x ∂μ))) := by
    simpa only [Function.comp_def, Lp.constL_apply] using
      ((Lp.constL 2 μ ℝ : ℝ →L[ℝ] Lp ℝ 2 μ).continuous.tendsto _).comp hmean
  have hvar (u : α → ℝ) (hu : MemLp u 2 μ) :
      variance u μ = ‖hu.toLp u - Lp.const 2 μ (∫ x, u x ∂μ)‖ ^ 2 := by
    rw [← variance_congr hu.coeFn_toLp, variance_eq_norm_sub_const_sq,
      integral_congr_ae hu.coeFn_toLp]
  simpa only [← hvar] using (hLp.sub hconst).norm.pow 2

end ProbabilityTheory

namespace MeasureTheory.MemLp

variable {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]

/-- For a square-integrable function `f` on a finite measure space, `(x, y) ↦ ‖f x - f y‖²` is
integrable for the product of the measure with itself. -/
theorem integrable_norm_sub_sq_prod [IsFiniteMeasure μ] {f : α → E} (hf : MemLp f 2 μ) :
    Integrable (fun z : α × α ↦ ‖f z.1 - f z.2‖ ^ 2) (μ.prod μ) :=
  (memLp_two_iff_integrable_sq_norm
    ((hf.comp_fst μ).sub (hf.comp_snd μ)).aestronglyMeasurable).1
    ((hf.comp_fst μ).sub (hf.comp_snd μ))

end MeasureTheory.MemLp

namespace MeasureTheory

section Centering

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

/-- Centering a square-integrable variable with values in a real inner product space subtracts
the squared norm of its mean from its second absolute moment. -/
theorem MemLp.integral_norm_sub_integral_sq [IsProbabilityMeasure μ] {f : α → E}
    (hf : MemLp f 2 μ) :
    ∫ x, ‖f x - ∫ y, f y ∂μ‖ ^ 2 ∂μ =
      (∫ x, ‖f x‖ ^ 2 ∂μ) - ‖∫ x, f x ∂μ‖ ^ 2 := by
  by_cases hE : CompleteSpace E
  swap
  · simp only [integral_of_not_completeSpace hE, sub_zero, norm_zero]
    ring
  -- The orthogonal splitting of the square oscillation about `0` over the whole space.
  have h := TauCeti.setIntegral_norm_sub_sq_eq_setIntegral_norm_sub_setAverage_sq_add
    (s := univ) (c := 0) (measure_ne_top μ univ) (hf.integrable one_le_two).integrableOn
    (by simpa only [sub_zero] using
      ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf).integrableOn)
  simp only [Measure.restrict_univ, sub_zero, average_eq_integral, probReal_univ, one_mul] at h
  linarith

end Centering

end MeasureTheory

namespace TauCeti

section InnerProductSpace

variable {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The mean squared distance between two independent copies.** For a square-integrable function
`f` with values in a real Hilbert space and a finite measure `μ`,
`∫∫ ‖f x - f y‖² dμ(x) dμ(y) = 2 (μ(α) ∫ ‖f‖² dμ - ‖∫ f dμ‖²)`. For a probability measure this is
twice the variance of `f`. -/
theorem integral_norm_sub_sq_prod [IsFiniteMeasure μ] {f : α → E} (hf : MemLp f 2 μ) :
    ∫ z, ‖f z.1 - f z.2‖ ^ 2 ∂μ.prod μ =
      2 * (μ.real univ * ∫ x, ‖f x‖ ^ 2 ∂μ - ‖∫ x, f x ∂μ‖ ^ 2) := by
  have hf₁ : Integrable f μ := hf.integrable one_le_two
  have hsq : Integrable (fun x ↦ ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hinner : Integrable (fun z : α × α ↦ ⟪f z.1, f z.2⟫) (μ.prod μ) :=
    (hf₁.norm.mul_prod hf₁.norm).mono' (hf₁.1.comp_fst.inner hf₁.1.comp_snd)
      (.of_forall fun z ↦ by simpa using abs_real_inner_le_norm (f z.1) (f z.2))
  -- The cross term integrates to the squared norm of the mean.
  have hcross : ∫ z, ⟪f z.1, f z.2⟫ ∂μ.prod μ = ‖∫ x, f x ∂μ‖ ^ 2 := by
    have h (x : α) : ∫ y, ⟪f x, f y⟫ ∂μ = ⟪∫ y, f y ∂μ, f x⟫ := by
      rw [integral_inner hf₁, real_inner_comm]
    rw [integral_prod _ hinner]
    simp only [h]
    rw [integral_inner hf₁, real_inner_self_eq_norm_sq]
  have hexp : (fun z : α × α ↦ ‖f z.1 - f z.2‖ ^ 2) =
      fun z ↦ (‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2) - 2 * ⟪f z.1, f z.2⟫ := by
    ext z
    rw [norm_sub_sq_real]
    ring
  have hsum : Integrable (fun z : α × α ↦ ‖f z.1‖ ^ 2 + ‖f z.2‖ ^ 2) (μ.prod μ) :=
    (hsq.comp_fst μ).add (hsq.comp_snd μ)
  rw [hexp, integral_sub hsum (hinner.const_mul 2),
    integral_add (hsq.comp_fst μ) (hsq.comp_snd μ), integral_const_mul, hcross,
    integral_fun_fst (fun x ↦ ‖f x‖ ^ 2), integral_fun_snd (fun x ↦ ‖f x‖ ^ 2)]
  ring

end InnerProductSpace

/-- Mathlib's variance of a square-integrable observable under a finite measure, expanded in terms
of the total mass: it is the integral of the square plus the mass minus `2`, times the square of
the integral. For a probability measure this is `variance_eq_sub`. -/
theorem variance_eq_integral_sq_add {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsFiniteMeasure ν] {X : Ω → ℝ} (hX : MemLp X 2 ν) :
    variance X ν = ν[X ^ 2] + (ν.real Set.univ - 2) * ν[X] ^ 2 := by
  have hi := hX.integrable one_le_two
  rw [← covariance_self hX.aestronglyMeasurable.aemeasurable,
    covariance_eq_integral_mul_add hi hi (hX.integrable_mul hX), sq, sq]

section EVarianceNeTop

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- Under a measure of infinite total mass, an observable of finite extended variance has integral
`0`. Otherwise the observable would be integrable with a nonzero integral `m`, and by Markov's and
Chebyshev's inequalities the sets where `|X| ≥ |m| / 2` and where `|X - m| ≥ |m| / 2` would have
finite measure, although they cover the space. -/
theorem integral_eq_zero_of_evariance_ne_top (hμ : μ Set.univ = ∞) (hX : evariance X μ ≠ ∞) :
    μ[X] = 0 := by
  by_contra hm
  have hint : Integrable X μ := by
    by_contra h
    exact hm (integral_undef h)
  obtain ⟨c, hcval⟩ : ∃ c : ℝ≥0, (c : ℝ) = |μ[X]| / 2 := ⟨⟨_, by positivity⟩, rfl⟩
  have hc : (0 : ℝ) < c := hcval ▸ half_pos (abs_pos.mpr hm)
  have hcover : Set.univ ⊆ {ω | (c : ℝ) ≤ ‖X ω‖} ∪ {ω | (c : ℝ) ≤ |X ω - μ[X]|} := by
    intro ω _
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, Real.norm_eq_abs, hcval] at h
    have := abs_sub (X ω) (X ω - μ[X])
    rw [sub_sub_cancel] at this
    linarith [h.1, h.2]
  refine hμ.not_lt ((measure_mono hcover).trans_lt ((measure_union_le _ _).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hint.measure_norm_ge_lt_top hc, ?_⟩)))
  exact (meas_ge_le_evariance_div_sq hint.aestronglyMeasurable (NNReal.coe_pos.mp hc).ne').trans_lt
    (ENNReal.div_lt_top hX (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr (NNReal.coe_pos.mp hc).ne')))

/-- Under a measure of infinite total mass, the second moment `∫⁻ ‖X‖ₑ ^ 2` of any observable is
at most its extended variance: when the latter is finite, the integral of `X` vanishes. -/
theorem lintegral_enorm_sq_le_evariance (hμ : μ Set.univ = ∞) :
    ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ ≤ evariance X μ := by
  by_cases hX : evariance X μ = ∞
  · exact hX ▸ le_top
  · simp only [evariance, integral_eq_zero_of_evariance_ne_top hμ hX, sub_zero, le_rfl]

/-- An almost everywhere strongly measurable observable of finite extended variance is
square-integrable, under any measure. For a finite measure this is Mathlib's
`evariance_lt_top_iff_memLp`; under a measure of infinite mass the integral of the observable
vanishes, so its extended variance is its second moment. -/
theorem memLp_two_of_evariance_ne_top (hXm : AEStronglyMeasurable X μ)
    (hX : evariance X μ ≠ ∞) : MemLp X 2 μ := by
  by_cases hμ : μ Set.univ = ∞
  · exact hXm.memLp_two_iff_lintegral_enorm_sq_lt_top.mpr
      ((lintegral_enorm_sq_le_evariance hμ).trans_lt hX.lt_top)
  · have : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr hμ⟩
    exact (evariance_lt_top_iff_memLp hXm).mp hX.lt_top

end EVarianceNeTop

section VarianceNeZero

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- An almost everywhere strongly measurable, almost everywhere nonnegative real function on a
finite measure space with nonzero variance has strictly positive integral (expectation when `μ`
is a probability measure). -/
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_pos_of_nonneg_ae_of_variance_ne_zero
    [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) (h0 : 0 ≤ᵐ[μ] X) (hvar : Var[X; μ] ≠ 0) :
    0 < ∫ ω, X ω ∂μ := by
  have hint := (memLp_two_of_variance_ne_zero hX hvar).integrable one_le_two
  refine (integral_nonneg_of_ae h0).lt_of_ne fun heq ↦ hvar ?_
  rw [variance_congr ((integral_eq_zero_iff_of_nonneg_ae h0 hint).1 heq.symm), variance_zero]

/-- On a finite measure space, a real-valued random variable with nonzero variance is not almost
everywhere zero: the set where it vanishes has measure strictly less than the whole space. -/
theorem measure_setOf_eq_zero_lt_measure_univ_of_variance_ne_zero [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hvar : Var[X; μ] ≠ 0) :
    μ {ω | X ω = 0} < μ univ := by
  refine (measure_mono (subset_univ _)).lt_of_ne fun hfull ↦ hvar ?_
  by_cases hX : AEMeasurable X μ
  · have hnull : NullMeasurableSet {ω | X ω = 0} μ :=
      hX.nullMeasurable (measurableSet_singleton (0 : ℝ))
    have hae : X =ᵐ[μ] 0 := (ae_mem_iff_measure_eq hnull).2 hfull
    rw [variance_congr hae, variance_zero]
  · have hint : ∫ ω, X ω ∂μ = 0 := integral_non_aestronglyMeasurable fun h ↦ hX h.aemeasurable
    -- Without a measurable version of `X` the mean is `0`, so the integrand of the variance
    -- vanishes on `{X = 0}`, a set of full outer measure; hence the variance is `0`.
    have hev : evariance X μ = 0 := by
      rw [evariance]
      refine lintegral_eq_zero_of_measure_setOf_eq_zero_eq_measure_univ ?_
      refine le_antisymm (measure_mono (subset_univ _)) ?_
      rw [← hfull]
      refine measure_mono fun ω h0 ↦ ?_
      simp only [Set.mem_ofPred_eq] at h0 ⊢
      simp [h0, hint]
    simp [variance, hev]

end VarianceNeZero

end TauCeti

namespace MeasureTheory.MeasurePreserving

open ProbabilityTheory
open scoped ENNReal

/-- The variance is invariant under composition with a measure-preserving measurable embedding. -/
theorem evariance_fun_comp {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {e : Ω → Ω'} (he : MeasurePreserving e μ ν)
    (hem : MeasurableEmbedding e) (f : Ω' → ℝ) :
    ProbabilityTheory.evariance (fun x => f (e x)) μ = ProbabilityTheory.evariance f ν := by
  rw [evariance, evariance, he.integral_comp hem f]
  exact he.lintegral_comp_emb hem fun y => ‖f y - ∫ y', f y' ∂ν‖ₑ ^ 2

end MeasureTheory.MeasurePreserving

namespace TauCeti.Probability

/-- The variance of a weighted sum of pairwise independent square-integrable variables. -/
theorem variance_weighted_coordinate_sum {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ι → Ω → ℝ} {s : Finset ι} (a : ι → ℝ) (hX : ∀ i ∈ s, MemLp (X i) 2 P)
    (hindep : (s : Set ι).Pairwise fun i j ↦ IndepFun (X i) (X j) P) :
    Var[fun ω ↦ ∑ i ∈ s, a i * X i ω; P] = ∑ i ∈ s, a i ^ 2 * Var[X i; P] := by
  have h := IndepFun.variance_sum (X := fun i ω ↦ a i * X i ω)
    (fun i hi ↦ (hX i hi).const_mul (a i))
    fun i hi j hj hij ↦ (hindep hi hj hij).comp (by fun_prop) (by fun_prop)
  simpa only [Finset.sum_fn, variance_const_mul] using h

/-- The variance of a weighted sum of pairwise uncorrelated square-integrable variables on a
finite measure space. -/
theorem variance_weighted_coordinate_sum_of_covariance_eq_zero {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : ι → Ω → ℝ} {s : Finset ι} (a : ι → ℝ)
    (hX : ∀ i ∈ s, MemLp (X i) 2 P)
    (hcov : (s : Set ι).Pairwise fun i j ↦ cov[X i, X j; P] = 0) :
    Var[fun ω ↦ ∑ i ∈ s, a i * X i ω; P] = ∑ i ∈ s, a i ^ 2 * Var[X i; P] := by
  rw [variance_fun_sum' fun i hi ↦ (hX i hi).const_mul (a i)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.sum_eq_single_of_mem i hi fun j hj hji ↦ by
      rw [covariance_const_mul_left, covariance_const_mul_right, hcov hi hj hji.symm, mul_zero,
        mul_zero],
    covariance_self ((hX i hi).const_mul (a i)).aemeasurable, variance_const_mul]

/-- Chebyshev's bound for a weighted sum of pairwise uncorrelated square-integrable variables on a
finite measure space. -/
theorem measure_weighted_coordinate_sum_sub_integral_ge {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : ι → Ω → ℝ} {s : Finset ι} (a : ι → ℝ)
    (hX : ∀ i ∈ s, MemLp (X i) 2 P)
    (hcov : (s : Set ι).Pairwise fun i j ↦ cov[X i, X j; P] = 0) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(∑ i ∈ s, a i * X i ω) - ∫ ω, ∑ i ∈ s, a i * X i ω ∂P|} ≤
      ENNReal.ofReal ((∑ i ∈ s, a i ^ 2 * Var[X i; P]) / ε ^ 2) := by
  have h := meas_ge_le_variance_div_sq
    (memLp_finsetSum s fun i hi ↦ (hX i hi).const_mul (a i)) hε
  rwa [variance_weighted_coordinate_sum_of_covariance_eq_zero a hX hcov] at h

/-- **Chebyshev convergence in measure from vanishing variances.** If square-integrable real-valued
functions on possibly varying finite measure spaces have variances tending to zero along a filter,
then their deviations from their own integrals (their means when each measure is a probability
measure) converge to zero in measure. -/
theorem tendsto_measure_abs_sub_integral_ge_of_tendsto_variance {ι : Type*} {l : Filter ι}
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsFiniteMeasure (P i)]
    {X : (i : ι) → Ω i → ℝ} (hX : ∀ i, MemLp (X i) 2 (P i))
    (hvar : Tendsto (fun i ↦ Var[X i; P i]) l (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun i ↦ P i {ω | ε ≤ |X i ω - ∫ ω', X i ω' ∂P i|}) l (𝓝 0) := by
  have hreal : Tendsto (fun i ↦ Var[X i; P i] / ε ^ 2) l (𝓝 0) := by
    simpa only [zero_div] using hvar.div_const (ε ^ 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal)
    (fun _ ↦ bot_le) (fun i ↦ meas_ge_le_variance_div_sq (hX i) hε)

/-- **Borel--Cantelli almost-everywhere convergence from summable variances.** On a finite measure
space, if a sequence of square-integrable real-valued functions has summable variances, then its
deviations from its own integrals (its means when `P` is a probability measure) converge almost
everywhere to zero. -/
theorem ae_tendsto_sub_integral_of_summable_variance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hvar : Summable fun n ↦ Var[X n; P]) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω - ∫ ω', X n ω' ∂P) atTop (𝓝 0) := by
  refine TauCeti.MeasureTheory.ae_tendsto_of_tsum_dist_ge_ne_top (g := 0) fun ε hε ↦ ?_
  refine ne_top_of_le_ne_top (hvar.div_const (ε ^ 2)).tsum_ofReal_ne_top
    (tsum_le_tsum fun n ↦ ?_)
  simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using meas_ge_le_variance_div_sq (hX n) hε

section ProdSections

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {ν : Measure α} {π : Measure β}
  {F : α × β → ℝ}

/-- The extended variances, under an s-finite measure, of the sections in the second coordinate
of a measurable function on a product form a measurable function of the first coordinate. -/
theorem measurable_evariance_prod_right [SFinite π] (hF : Measurable F) :
    Measurable fun a => evariance (fun w => F (a, w)) π := by
  have hm : StronglyMeasurable fun a => ∫ w, F (a, w) ∂π :=
    hF.stronglyMeasurable.integral_prod_right'
  simpa only [evariance] using
    Measurable.lintegral_prod_right' (f := fun p : α × β => ‖F p - ∫ w, F (p.1, w) ∂π‖ₑ ^ 2)
      ((hF.sub (hm.measurable.comp measurable_fst)).eNorm.pow_const 2)

/-- The extended variances, under an s-finite measure, of the sections in the second coordinate
of a function that is almost everywhere strongly measurable on a product form an almost everywhere
measurable function of the first coordinate. -/
theorem aemeasurable_evariance_prod_right [SFinite π] (hF : AEStronglyMeasurable F (ν.prod π)) :
    AEMeasurable (fun a => evariance (fun w => F (a, w)) π) ν := by
  refine (measurable_evariance_prod_right (π := π)
    hF.stronglyMeasurable_mk.measurable).aemeasurable.congr ?_
  filter_upwards [Measure.ae_ae_of_ae_prod hF.ae_eq_mk] with a ha
  exact (evariance_congr ha).symm

/-- If the second factor has infinite mass, then the second moment `∫⁻ ‖F‖ₑ ^ 2` of any function
on the product is at most the lower integral of the extended variances of its sections in the
second coordinate: by Tonelli's inequality and `lintegral_enorm_sq_le_evariance`. -/
theorem lintegral_enorm_sq_prod_le_lintegral_evariance (hπ : π Set.univ = ∞) :
    ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(ν.prod π) ≤ ∫⁻ a, evariance (fun w => F (a, w)) π ∂ν :=
  (lintegral_prod_le _).trans (lintegral_mono fun _ => lintegral_enorm_sq_le_evariance hπ)

/-- If a function is almost everywhere strongly measurable on the product with an s-finite
measure, and the lower integral of the extended variances of its sections in the second coordinate
is finite, then almost every such section is square-integrable. -/
theorem ae_memLp_two_prod_right_of_lintegral_evariance_ne_top [SFinite π]
    (hF : AEStronglyMeasurable F (ν.prod π))
    (h : ∫⁻ a, evariance (fun w => F (a, w)) π ∂ν ≠ ∞) :
    ∀ᵐ a ∂ν, MemLp (fun w => F (a, w)) 2 π := by
  filter_upwards [ae_lt_top' (aemeasurable_evariance_prod_right hF) h, hF.prodMk_left]
    with a ha hma
  exact memLp_two_of_evariance_ne_top hma ha.ne

/-- If `F` is almost everywhere strongly measurable on the product of two s-finite measures, and
the lower integrals of the extended variances of its sections in either coordinate are both finite,
then `F` is square-integrable. -/
theorem memLp_two_prod_of_lintegral_evariance_ne_top [SFinite ν] [SFinite π]
    (hF : AEStronglyMeasurable F (ν.prod π))
    (h₁ : ∫⁻ a, evariance (fun w => F (a, w)) π ∂ν ≠ ∞)
    (h₂ : ∫⁻ w, evariance (fun a => F (a, w)) ν ∂π ≠ ∞) : MemLp F 2 (ν.prod π) := by
  rcases eq_or_ne (ν Set.univ) ∞ with hν | hν
  · -- Under a first factor of infinite mass, the section extended variances in the first
    -- coordinate bound the second moment of `F`.
    refine hF.memLp_two_iff_lintegral_enorm_sq_lt_top.mpr ?_
    rw [← lintegral_prod_swap]
    exact (lintegral_enorm_sq_prod_le_lintegral_evariance hν).trans_lt h₂.lt_top
  have : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.mpr hν⟩
  rcases eq_zero_or_neZero ν with rfl | hν
  · simp
  -- Centering each section in the first coordinate gives a square-integrable function.
  have hm : AEStronglyMeasurable (fun w => ∫ a, F (a, w) ∂ν) π :=
    hF.prod_swap.integral_prod_right'
  have hGm : AEStronglyMeasurable (fun p : α × β => F p - ∫ a, F (a, p.2) ∂ν) (ν.prod π) :=
    hF.sub hm.comp_snd
  have hGL : MemLp (fun p : α × β => F p - ∫ a, F (a, p.2) ∂ν) 2 (ν.prod π) := by
    refine hGm.memLp_two_iff_lintegral_enorm_sq_lt_top.mpr ?_
    rw [lintegral_prod_symm _ (hGm.eNorm.pow_const 2)]
    simpa only [evariance] using h₂.lt_top
  -- Almost every section in the second coordinate is square-integrable, both before and after
  -- centering in the first coordinate, so the centering function is square-integrable.
  obtain ⟨a, ha, hsec⟩ := ((ae_memLp_two_prod_right_of_lintegral_evariance_ne_top hF h₁).and
    hGL.ae_memLp_prod_right).exists
  have hmL : MemLp (fun w => ∫ a, F (a, w) ∂ν) 2 π := by
    convert ha.sub hsec using 1
    ext w
    simp
  convert hGL.add (hmL.comp_snd ν) using 1
  ext p
  simp

/-- If an observable is almost everywhere strongly measurable on the product of any measure and an
s-finite measure, the lower integral of the extended variances of its sections in the second
coordinate is finite, and the extended variance of the integrals of those sections is finite, then
the observable is square-integrable. -/
theorem memLp_two_prod_of_evariance_ne_top [SFinite π]
    (hF : AEStronglyMeasurable F (ν.prod π))
    (hslice : ∫⁻ a, evariance (fun w => F (a, w)) π ∂ν ≠ ∞)
    (hmean : evariance (fun a => ∫ w, F (a, w) ∂π) ν ≠ ∞) : MemLp F 2 (ν.prod π) := by
  rcases eq_or_ne (π Set.univ) ∞ with hπ | hπ
  · -- Under a second factor of infinite mass, the section extended variances in the second
    -- coordinate bound the second moment of `F`.
    exact hF.memLp_two_iff_lintegral_enorm_sq_lt_top.mpr
      ((lintegral_enorm_sq_prod_le_lintegral_evariance hπ).trans_lt hslice.lt_top)
  have : IsFiniteMeasure π := ⟨lt_top_iff_ne_top.mpr hπ⟩
  have hsl := ae_memLp_two_prod_right_of_lintegral_evariance_ne_top hF hslice
  have hmL := memLp_two_of_evariance_ne_top hF.integral_prod_right' hmean
  have hvar : Integrable (fun a => variance (fun w => F (a, w)) π) ν := by
    simpa only [variance] using
      integrable_toReal_of_lintegral_ne_top (aemeasurable_evariance_prod_right hF) hslice
  -- Each section's second moment is its variance minus `(mass - 2)` times its squared integral.
  rw [memLp_two_iff_integrable_sq hF, integrable_prod_iff (f := fun p ↦ F p ^ 2) (hF.pow 2)]
  refine ⟨hsl.mono fun a ha => ha.integrable_sq,
    (hvar.sub (hmL.integrable_sq.const_mul (π.real Set.univ - 2))).congr ?_⟩
  filter_upwards [hsl] with a ha
  simp only [Pi.sub_apply, variance_eq_integral_sq_add ha, Real.norm_of_nonneg (sq_nonneg _),
    Pi.pow_apply]
  ring

/-- The law of total variance on the product of a finite measure and a probability measure: the
extended variance of `F` is the lower integral against the first factor of the extended variances
of its sections in the second coordinate plus the extended variance, under the first factor, of
its averages over the second coordinate. The observable `F` need only be almost everywhere strongly
measurable with respect to the product measure; when it is not square-integrable, both sides are
infinite. -/
theorem evariance_prod_eq [IsFiniteMeasure ν] [IsProbabilityMeasure π]
    (hF : AEStronglyMeasurable F (ν.prod π)) :
    evariance F (ν.prod π) = ∫⁻ a, evariance (fun w => F (a, w)) π ∂ν +
      evariance (fun a => ∫ w, F (a, w) ∂π) ν := by
  by_cases hL : MemLp F 2 (ν.prod π)
  swap
  · rw [evariance_eq_top hF hL, eq_comm, ENNReal.add_eq_top]
    by_contra h
    exact hL (memLp_two_prod_of_evariance_ne_top hF (h ∘ .inl) (h ∘ .inr))
  let K : α → Measure (α × β) := fun a => π.map (Prod.mk a)
  have hK : AEMeasurable K ν := Measurable.map_prodMk_left.aemeasurable
  have hprob : ∀ᵐ a ∂ν, IsProbabilityMeasure (K a) :=
    .of_forall fun _ => inferInstance
  have hmass : ∀ᵐ a ∂ν, K a Set.univ ≤ (1 : ℝ≥0) := hprob.mono fun _ _ ↦ by simp
  have hbind : ν.bind K = ν.prod π := (Measure.prod_eq_of_sfinite ν π).symm
  have hX : MemLp F 2 (ν.bind K) := hbind ▸ hL
  have hae := ((Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX).1
  have hslice : ∀ᵐ a ∂ν, variance F (K a) = variance (fun w => F (a, w)) π ∧
      ∫ x, F x ∂K a = ∫ w, F (a, w) ∂π ∧ MemLp (fun w => F (a, w)) 2 π := by
    filter_upwards [hae] with a ha
    have hmp : AEMeasurable (Prod.mk a) π := measurable_prodMk_left.aemeasurable
    exact ⟨variance_map ha.aestronglyMeasurable.aemeasurable hmp,
      integral_map hmp ha.aestronglyMeasurable, ha.comp_of_map hmp⟩
  have hmean : MemLp (fun a => ∫ w, F (a, w) ∂π) 2 ν :=
    (Measure.memLp_integral_bind one_le_two hK hmass hX).ae_eq (hslice.mono fun a ha => ha.2.1)
  have hvarint : Integrable (fun a => variance (fun w => F (a, w)) π) ν := by
    refine (integrable_covariance_bind hK hmass hX hX).congr ?_
    filter_upwards [hae, hslice] with a ha hs
    rw [covariance_self ha.aestronglyMeasurable.aemeasurable, hs.1]
  have hlint : ∫⁻ a, evariance (fun w => F (a, w)) π ∂ν =
      ENNReal.ofReal (∫ a, variance (fun w => F (a, w)) π ∂ν) := by
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

end ProdSections

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {ν : Measure α} {π : Measure β}
  [SFinite ν] [SFinite π] {F : α × β → ℝ}

/-- Jensen's inequality for the variance of an integral: for `F` integrable on the product of two
s-finite measures, the extended variance of its integral over the second coordinate is at most the
mass of the second factor times the lower integral over the second coordinate of the extended
variances of its sections in the first coordinate. For a probability measure on the second factor
this bounds the extended variance of the average by the lower integral of the extended variances of
the sections. The proof applies Minkowski's integral inequality in `L²` to the sections centered in
the first coordinate. -/
theorem _root_.MeasureTheory.Integrable.evariance_integral_prod_le
    (hint : Integrable F (ν.prod π)) :
    evariance (fun a => ∫ w, F (a, w) ∂π) ν ≤
      π Set.univ * ∫⁻ w, evariance (fun a => F (a, w)) ν ∂π := by
  -- Center each section in the first coordinate.
  set G : α → β → ℝ := fun a w => F (a, w) - ∫ a', F (a', w) ∂ν with hG_def
  have hmint : Integrable (fun w => ∫ a, F (a, w) ∂ν) π := hint.integral_prod_right
  have hG : AEStronglyMeasurable (Function.uncurry G) (ν.prod π) := hint.1.sub hmint.1.comp_snd
  -- The integrals of the centered sections over the second coordinate are the centered integrals.
  have hc : ∀ᵐ a ∂ν, (∫ w, F (a, w) ∂π) - ∫ a', ∫ w, F (a', w) ∂π ∂ν = ∫ w, G a w ∂π := by
    filter_upwards [hint.prod_right_ae] with a ha
    rw [hG_def, integral_sub ha hmint, ← integral_prod_symm _ hint, integral_prod _ hint]
  -- The squared `L²(ν)` seminorms of the centered sections are their extended variances.
  have hsec : ∀ᵐ w ∂π, eLpNorm (fun a => G a w) 2 ν ^ 2 = evariance (fun a => F (a, w)) ν := by
    filter_upwards [hG.prod_swap.prodMk_left] with w hw
    rw [eLpNorm_two_sq_eq_lintegral (f := fun a => G a w) hw, evariance]
  have hJ := rpow_lintegral_le_measure_univ_rpow_mul (μ := π)
    (u := fun w => eLpNorm (fun a => G a w) 2 ν) one_le_two
  rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at hJ
  simp only [ENNReal.rpow_two] at hJ
  calc evariance (fun a => ∫ w, F (a, w) ∂π) ν
      = eLpNorm (fun a => ∫ w, G a w ∂π) 2 ν ^ 2 := by
        rw [evariance,
          eLpNorm_two_sq_eq_lintegral (f := fun a => ∫ w, G a w ∂π) hG.integral_prod_right']
        exact lintegral_congr_ae (hc.mono fun a ha => by simp only [ha])
    _ ≤ (∫⁻ w, eLpNorm (fun a => G a w) 2 ν ∂π) ^ 2 := by
        gcongr
        exact eLpNorm_integral_le_lintegral_eLpNorm_of_ne_top hG one_le_two ENNReal.ofNat_ne_top
    _ ≤ π Set.univ * ∫⁻ w, eLpNorm (fun a => G a w) 2 ν ^ 2 ∂π := hJ
    _ = π Set.univ * ∫⁻ w, evariance (fun a => F (a, w)) ν ∂π := by
        rw [lintegral_congr_ae hsec]

omit [SFinite π] in
/-- The two-factor Efron--Stein inequality on the product of an s-finite measure and a probability
measure. The function `F` need only be almost everywhere strongly measurable with respect to the
product measure; when it is not square-integrable, both sides are infinite. -/
theorem evariance_prod_le [IsProbabilityMeasure π] (hF : AEStronglyMeasurable F (ν.prod π)) :
    evariance F (ν.prod π) ≤ ∫⁻ a, evariance (fun w => F (a, w)) π ∂ν +
      ∫⁻ w, evariance (fun a => F (a, w)) ν ∂π := by
  rcases eq_or_ne (ν Set.univ) ∞ with hν | hν
  · -- Under a first factor of infinite mass, almost every section in the first coordinate has
    -- integral zero, hence so does `F`, and the section extended variances in the first
    -- coordinate bound the second moment of `F`.
    rcases eq_or_ne (∫⁻ w, evariance (fun a => F (a, w)) ν ∂π) ∞ with h₂ | h₂
    · simp only [h₂, add_top, le_top]
    have hae : ∀ᵐ w ∂π, ∫ a, F (a, w) ∂ν = 0 := by
      filter_upwards [ae_lt_top' (aemeasurable_evariance_prod_right hF.prod_swap) h₂] with w hw
      exact integral_eq_zero_of_evariance_ne_top hν hw.ne
    have hmean : ∫ p, F p ∂(ν.prod π) = 0 := by
      by_cases hint : Integrable F (ν.prod π)
      · rw [integral_prod_symm _ hint, integral_congr_ae hae, integral_zero]
      · exact integral_undef hint
    calc evariance F (ν.prod π) = ∫⁻ p, ‖F p‖ₑ ^ 2 ∂(ν.prod π) := by
          simp only [evariance, hmean, sub_zero]
      _ = ∫⁻ p, ‖F p.swap‖ₑ ^ 2 ∂(π.prod ν) := (lintegral_prod_swap _).symm
      _ ≤ ∫⁻ w, evariance (fun a => F (a, w)) ν ∂π :=
          lintegral_enorm_sq_prod_le_lintegral_evariance hν
      _ ≤ _ := le_add_self
  have : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.mpr hν⟩
  by_cases hL : MemLp F 2 (ν.prod π)
  · rw [evariance_prod_eq hF]
    gcongr
    simpa only [measure_univ, one_mul] using (hL.integrable one_le_two).evariance_integral_prod_le
  rw [evariance_eq_top hF hL, top_le_iff, ENNReal.add_eq_top]
  by_contra h
  exact hL (memLp_two_prod_of_lintegral_evariance_ne_top hF (h ∘ .inl) (h ∘ .inr))

/-- The variance of `f` in coordinate `i`, with the other coordinates frozen at `x`, is a
measurable function of `x`. -/
theorem measurable_evariance_update {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) (i : ι) [SFinite (μ i)]
    {f : (∀ i, α i) → ℝ} (hf : Measurable f) :
    Measurable fun x => evariance (fun y => f (Function.update x i y)) (μ i) :=
  measurable_evariance_prod_right (π := μ i)
    (F := fun p : (∀ i, α i) × α i => f (Function.update p.1 i p.2)) (hf.comp measurable_update')

end TauCeti.Probability

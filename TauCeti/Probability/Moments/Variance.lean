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
public import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
public import TauCeti.MeasureTheory.Function.Lp.Norm
public import TauCeti.MeasureTheory.Integral.Lebesgue.SetOfEqZero
public import TauCeti.Probability.Moments.Mixture
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli

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

The file also records the elementary bound of the mean of a real function by the square root of
its second moment (the nonnegativity of its variance), together with two consequences of nonzero
variance `Var[X; μ] ≠ 0` on a finite measure space: strict positivity of the expectation of an
almost everywhere strongly measurable, almost everywhere nonnegative real random variable, and
nondegeneracy `μ {ω | X ω = 0} < μ univ` of a real-valued random variable, as well as Chebyshev
convergence in probability from vanishing variances and Borel--Cantelli almost-sure convergence to
the mean from summable variances.

## Main statements

* `MeasureTheory.MemLp.integrable_norm_sub_sq_prod`: for `f ∈ L²(μ)` and a finite measure `μ`,
  the function `(x, y) ↦ ‖f x - f y‖²` is integrable for `μ ⊗ μ`.
* `TauCeti.integral_norm_sub_sq_prod`: the identity above.
* `MeasureTheory.integral_le_sqrt_integral_sq`: on a probability space, the mean of a real
  square-integrable function is at most the square root of its second moment, which is the
  nonnegativity of its variance.
* `MeasureTheory.MemLp.integral_norm_pow_le_sqrt_integral_norm_pow_two_mul`: on a probability
  space, the `k`-th absolute moment of a function in `L^(2k)` is at most the square root of its
  `2k`-th absolute moment.
* `MeasureTheory.MeasurePreserving.evariance_fun_comp`: the variance is invariant under
  composition with a measure-preserving measurable embedding.
* `ProbabilityTheory.tendsto_variance_of_tendsto_eLpNorm_sub`: variance is continuous under
  L² convergence on a finite measure space.
* `TauCeti.Probability.evariance_integral_prod_le` and
  `TauCeti.Probability.evariance_prod_le`: product-variance bounds for averages and products.
* `TauCeti.Probability.variance_weighted_coordinate_sum`,
  `TauCeti.Probability.variance_weighted_coordinate_sum_of_covariance_eq_zero` and
  `TauCeti.Probability.measure_weighted_coordinate_sum_sub_mean_ge`: variance and Chebyshev
  bounds for weighted sums of pairwise independent or pairwise uncorrelated variables.
* `TauCeti.Probability.tendsto_measure_abs_sub_integral_ge_of_tendsto_variance`: vanishing
  variances imply convergence in measure to the mean, including on varying finite measure spaces.
* `TauCeti.Probability.ae_tendsto_sub_integral_of_summable_variance`: summable variances imply
  almost-everywhere convergence to the mean on a finite measure space.
* `TauCeti.integral_pos_of_nonneg_ae_of_variance_ne_zero`: on a finite measure space, an almost
  everywhere strongly measurable, almost everywhere nonnegative real random variable with nonzero
  variance has strictly positive expectation.
* `TauCeti.measure_setOf_eq_zero_lt_measure_univ_of_variance_ne_zero`: on a finite measure space,
  a real-valued random variable with nonzero variance satisfies `μ {ω | X ω = 0} < μ univ`.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal RealInnerProductSpace Topology

namespace ProbabilityTheory

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
    rw [← indicatorConstLp_univ, L2.inner_indicatorConstLp_one, setIntegral_univ]
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
    rw [variance_eq_integral hu.aemeasurable, ← Lp.integral_norm_sq_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (hu.toLp u) (Lp.const 2 μ (∫ x, u x ∂μ)),
      hu.coeFn_toLp, Lp.coeFn_const 2 μ (∫ x, u x ∂μ)] with x hx hu hc
    simp only [hx, Pi.sub_apply, hu, hc, Function.const_apply, Real.norm_eq_abs, sq_abs]
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

/-- On a probability space, the mean of a square-integrable function is at most the square root of
its second moment. -/
theorem integral_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {g : Ω → ℝ} (hg : MemLp g 2 μ) :
    ∫ x, g x ∂μ ≤ √(∫ x, g x ^ 2 ∂μ) := by
  apply Real.le_sqrt_of_sq_le
  have h := ProbabilityTheory.variance_nonneg g μ
  rw [ProbabilityTheory.variance_eq_sub hg] at h
  simpa only [Pi.pow_apply, sub_nonneg] using h

/-- On a probability space, the `k`-th absolute moment of a function in `L^(2k)` is at most the
square root of its `2k`-th absolute moment. -/
theorem MemLp.integral_norm_pow_le_sqrt_integral_norm_pow_two_mul
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → E} {k : ℕ} (hf : MemLp f (2 * k : ℕ) μ) :
    ∫ x, ‖f x‖ ^ k ∂μ ≤ √(∫ x, ‖f x‖ ^ (2 * k) ∂μ) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hk0 : (k : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hmem : MemLp (fun x ↦ ‖f x‖ ^ k) 2 μ := by
    have h := hf.norm_rpow_div (k : ℕ)
    rw [Nat.cast_mul, Nat.cast_ofNat,
      ENNReal.mul_div_cancel_right hk0 (ENNReal.natCast_ne_top _)] at h
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast] using h
  simpa only [← pow_mul, mul_comm k 2] using integral_le_sqrt_integral_sq hmem

section Centering

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Centering a Hilbert-space-valued square-integrable variable subtracts the squared norm
of its mean from its second absolute moment. -/
theorem MemLp.integral_norm_sub_integral_sq [IsProbabilityMeasure μ] {f : α → E}
    (hf : MemLp f 2 μ) :
    ∫ x, ‖f x - ∫ y, f y ∂μ‖ ^ 2 ∂μ =
      (∫ x, ‖f x‖ ^ 2 ∂μ) - ‖∫ x, f x ∂μ‖ ^ 2 := by
  have hi := hf.integrable one_le_two
  have hs := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hc : Integrable (fun x ↦ 2 * ⟪(∫ y, f y ∂μ), f x⟫) μ :=
    (hi.const_inner _).const_mul 2
  -- The cross term integrates to twice the squared norm of the mean.
  have hcross : ∫ x, 2 * ⟪(∫ y, f y ∂μ), f x⟫ ∂μ = 2 * ‖∫ x, f x ∂μ‖ ^ 2 := by
    rw [integral_const_mul, integral_inner hi, real_inner_self_eq_norm_sq]
  simp_rw [norm_sub_sq_real, real_inner_comm (∫ y, f y ∂μ)]
  rw [integral_add (f := fun x ↦ ‖f x‖ ^ 2 - 2 * ⟪(∫ y, f y ∂μ), f x⟫)
      (g := fun _ ↦ ‖∫ y, f y ∂μ‖ ^ 2) (hs.sub hc) (integrable_const _),
    integral_sub hs hc, hcross]
  simp only [integral_const, probReal_univ, one_smul]
  ring

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

section VarianceNeZero

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- An almost everywhere strongly measurable, almost everywhere nonnegative real random variable
on a finite measure space with nonzero variance has strictly positive expectation. -/
theorem integral_pos_of_nonneg_ae_of_variance_ne_zero [IsFiniteMeasure μ] {X : Ω → ℝ}
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

/-- Chebyshev's bound for a weighted sum of pairwise uncorrelated variables on a finite measure
space. -/
theorem measure_weighted_coordinate_sum_sub_mean_ge {Ω ι : Type*} [MeasurableSpace Ω]
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
then their deviations from their expectations converge to zero in measure. -/
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
fluctuations around its expectations converge almost everywhere to zero. -/
theorem ae_tendsto_sub_integral_of_summable_variance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hvar : Summable fun n ↦ Var[X n; P]) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω - ∫ ω', X n ω' ∂P) atTop (𝓝 0) := by
  refine TauCeti.MeasureTheory.ae_tendsto_of_tsum_dist_ge_ne_top (g := 0) fun ε hε ↦ ?_
  refine ne_top_of_le_ne_top (hvar.div_const (ε ^ 2)).tsum_ofReal_ne_top
    (tsum_le_tsum fun n ↦ ?_)
  simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using meas_ge_le_variance_div_sq (hX n) hε

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {ν : Measure α} {π : Measure β}
  [SFinite ν] [IsProbabilityMeasure π] {F : α × β → ℝ}

/-- Jensen's inequality for the extended variance of an average: for `F` integrable on the
product of an s-finite measure `ν` and a probability measure `π`, the extended variance (with
respect to `ν`) of the average of `F` over the second coordinate against `π` is at most the
`π`-average over the second coordinate of the extended variances of the first-coordinate
sections. -/
theorem evariance_integral_prod_le (hint : Integrable F (ν.prod π)) :
    evariance (fun a => ∫ w, F (a, w) ∂π) ν ≤
      ∫⁻ w, evariance (fun a => F (a, w)) ν ∂π := by
  have hmint : Integrable (fun w => ∫ a, F (a, w) ∂ν) π := hint.integral_prod_right
  have hm_eq : ∫ w, ∫ a, F (a, w) ∂ν ∂π = ∫ a, ∫ w, F (a, w) ∂π ∂ν :=
    (integral_integral_swap (f := fun a w => F (a, w)) hint).symm
  have hae : ∀ᵐ a ∂ν, ‖(∫ w, F (a, w) ∂π) - ∫ a', ∫ w, F (a', w) ∂π ∂ν‖ₑ ^ 2 ≤
      ∫⁻ w, ‖F (a, w) - ∫ a', F (a', w) ∂ν‖ₑ ^ 2 ∂π := by
    filter_upwards [hint.prod_right_ae] with a ha
    have hsub : (∫ w, F (a, w) ∂π) - ∫ a', ∫ w, F (a', w) ∂π ∂ν =
        ∫ w, (F (a, w) - ∫ a', F (a', w) ∂ν) ∂π := by
      rw [integral_sub ha hmint, hm_eq]
    rw [hsub]
    calc ‖∫ w, (F (a, w) - ∫ a', F (a', w) ∂ν) ∂π‖ₑ ^ 2
        ≤ (∫⁻ w, ‖F (a, w) - ∫ a', F (a', w) ∂ν‖ₑ ∂π) ^ 2 := by
          gcongr
          exact eNorm_integral_le_lintegral_eNorm _
      _ ≤ _ := by
          simpa [ENNReal.rpow_two] using rpow_lintegral_le_measure_univ_rpow_mul
            (μ := π) (u := fun w => ‖F (a, w) - ∫ a', F (a', w) ∂ν‖ₑ)
            one_le_two
  calc evariance (fun a => ∫ w, F (a, w) ∂π) ν
      ≤ ∫⁻ a, ∫⁻ w, ‖F (a, w) - ∫ a', F (a', w) ∂ν‖ₑ ^ 2 ∂π ∂ν := lintegral_mono_ae hae
    _ = ∫⁻ w, ∫⁻ a, ‖F (a, w) - ∫ a', F (a', w) ∂ν‖ₑ ^ 2 ∂ν ∂π :=
        lintegral_lintegral_swap
          ((hint.1.sub hmint.aestronglyMeasurable.comp_snd).eNorm.pow_const 2)
    _ = ∫⁻ w, evariance (fun a => F (a, w)) ν ∂π := rfl

omit [SFinite ν] in
/-- The two-factor Efron--Stein inequality. -/
theorem evariance_prod_le [IsProbabilityMeasure ν] (hL : MemLp F 2 (ν.prod π)) :
    evariance F (ν.prod π) ≤ ∫⁻ a, evariance (fun w => F (a, w)) π ∂ν +
      ∫⁻ w, evariance (fun a => F (a, w)) ν ∂π := by
  rw [evariance_prod_eq hL]
  gcongr
  exact evariance_integral_prod_le (hL.integrable one_le_two)

/-- The variance of `f` in coordinate `i`, with the other coordinates frozen at `x`, is a
measurable function of `x`. -/
theorem measurable_evariance_update {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) (i : ι) [SFinite (μ i)]
    {f : (∀ i, α i) → ℝ} (hf : Measurable f) :
    Measurable fun x => evariance (fun y => f (Function.update x i y)) (μ i) := by
  have hu : Measurable fun p : (∀ i, α i) × α i => f (Function.update p.1 i p.2) :=
    hf.comp measurable_update'
  have hm : StronglyMeasurable fun x => ∫ y, f (Function.update x i y) ∂μ i :=
    hu.stronglyMeasurable.integral_prod_right'
  exact Measurable.lintegral_prod_right'
    (f := fun p : (∀ i, α i) × α i =>
      ‖f (Function.update p.1 i p.2) - ∫ y, f (Function.update p.1 i y) ∂μ i‖ₑ ^ 2)
    ((hu.sub (hm.measurable.comp measurable_fst)).eNorm.pow_const 2)

end TauCeti.Probability

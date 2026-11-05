/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.Variance

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
variance `Var[X; μ] ≠ 0`: strict positivity of the expectation of an `ℝ≥0`-valued random variable
on a finite measure space, and nondegeneracy `μ {ω | X ω = 0} < 1` of a real-valued random
variable on a probability space.

## Main statements

* `MeasureTheory.MemLp.integrable_norm_sub_sq_prod`: for `f ∈ L²(μ)` and a finite measure `μ`,
  the function `(x, y) ↦ ‖f x - f y‖²` is integrable for `μ ⊗ μ`.
* `TauCeti.integral_norm_sub_sq_prod`: the identity above.
* `MeasureTheory.integral_le_sqrt_integral_sq`: on a probability space, the mean of a real
  square-integrable function is at most the square root of its second moment, which is the
  nonnegativity of its variance.
* `TauCeti.integral_coe_pos_of_variance_ne_zero`: on a finite measure space, an `ℝ≥0`-valued
  random variable with nonzero variance has strictly positive expectation.
* `TauCeti.measure_setOf_eq_zero_lt_one_of_variance_ne_zero`: on a probability space, a
  real-valued random variable with nonzero variance satisfies `μ {ω | X ω = 0} < 1`.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal RealInnerProductSpace

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

/-- A nonnegative random variable on a finite measure space with nonzero variance has strictly
positive real expectation. -/
theorem integral_coe_pos_of_variance_ne_zero [IsFiniteMeasure μ] {X : Ω → ℝ≥0}
    (hX : AEMeasurable X μ) (hvar : Var[fun ω ↦ (X ω : ℝ); μ] ≠ 0) :
    0 < ∫ ω, (X ω : ℝ) ∂μ := by
  have hint := (memLp_two_of_variance_ne_zero
    (measurable_coe_nnreal_real.comp_aemeasurable hX).aestronglyMeasurable hvar).integrable
    one_le_two
  refine lt_of_le_of_ne (integral_nonneg fun ω ↦ (X ω).coe_nonneg) fun heq ↦ hvar ?_
  have hz : (fun ω ↦ (X ω : ℝ)) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω ↦ (X ω).coe_nonneg) hint).1 heq.symm
  rw [variance_congr hz, variance_zero]

/-- On a probability space, a real-valued random variable with nonzero variance is not almost
surely zero. -/
theorem measure_setOf_eq_zero_lt_one_of_variance_ne_zero [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (hvar : Var[X; μ] ≠ 0) :
    μ {ω | X ω = 0} < 1 := by
  refine lt_of_le_of_ne prob_le_one fun hfull ↦ hvar ?_
  have hnull : NullMeasurableSet {ω | X ω = 0} μ :=
    hX.nullMeasurable (measurableSet_singleton (0 : ℝ))
  have hae : X =ᵐ[μ] 0 := (ae_mem_iff_measure_eq hnull).2 (hfull.trans measure_univ.symm)
  rw [variance_congr hae, variance_zero]

end VarianceNeZero

end TauCeti

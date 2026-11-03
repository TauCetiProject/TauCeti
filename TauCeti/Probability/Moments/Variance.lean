/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.Variance
public import TauCeti.MeasureTheory.Function.Lp.Iterated
public import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
public import TauCeti.Probability.Moments.Mixture

/-!
# The mean squared distance between two independent copies

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
its second moment, which is the nonnegativity of its variance.

## Main statements

* `MeasureTheory.MemLp.integrable_norm_sub_sq_prod`: for `f ∈ L²(μ)` and a finite measure `μ`,
  the function `(x, y) ↦ ‖f x - f y‖²` is integrable for `μ ⊗ μ`.
* `TauCeti.integral_norm_sub_sq_prod`: the identity above.
* `MeasureTheory.integral_le_sqrt_integral_sq`: on a probability space, the mean of a real
  square-integrable function is at most the square root of its second moment, which is the
  nonnegativity of its variance.
* `TauCeti.Probability.evariance_comp_measurePreserving`: the variance is invariant under a
  measure-preserving measurable embedding.
* `TauCeti.Probability.evariance_prod_eq`: the law of total variance on a product of two
  probability spaces.
* `TauCeti.Probability.evariance_prod_le`: the two-factor Efron--Stein inequality.
* `TauCeti.Probability.evariance_integral_prod_le`: Jensen's inequality for the variance of an
  average over one factor of a product.
* `TauCeti.Probability.measurable_evariance_update`: measurability of the variance in one
  coordinate with the others frozen.
-/

public section

open MeasureTheory Set
open scoped RealInnerProductSpace

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

end TauCeti

namespace TauCeti.Probability

open ProbabilityTheory
open scoped ENNReal

/-- The variance is invariant under composition with a measure-preserving measurable embedding. -/
theorem evariance_comp_measurePreserving {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {e : Ω → Ω'} (he : MeasurePreserving e μ ν)
    (hem : MeasurableEmbedding e) (f : Ω' → ℝ) :
    evariance (fun x => f (e x)) μ = evariance f ν := by
  rw [evariance, evariance, he.integral_comp hem f]
  exact he.lintegral_comp_emb hem fun y => ‖f y - ∫ y', f y' ∂ν‖ₑ ^ 2
section Prod

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {ν : Measure α} {π : Measure β}
  [IsProbabilityMeasure ν] [IsProbabilityMeasure π] {F : α × β → ℝ}

/-- The law of total variance on a product of probability spaces: the variance of a square
integrable `F` splits into the average of the variances in the second coordinate and the variance
of the average over the second coordinate. -/
theorem evariance_prod_eq (hL : MemLp F 2 (ν.prod π)) :
    evariance F (ν.prod π) = ∫⁻ a, evariance (fun w => F (a, w)) π ∂ν +
      evariance (fun a => ∫ w, F (a, w) ∂π) ν := by
  let K : α → Measure (α × β) := fun a => π.map (Prod.mk a)
  have hK : Measurable K := Measurable.map_prodMk_left
  have hprob : ∀ᵐ a ∂ν, IsProbabilityMeasure (K a) :=
    .of_forall fun _ => inferInstance
  have hbind : ν.bind K = ν.prod π := (Measure.prod_eq_of_sfinite ν π).symm
  have hX : MemLp F 2 (ν.bind K) := hbind ▸ hL
  have hslice : ∀ᵐ a ∂ν, variance F (K a) = variance (fun w => F (a, w)) π ∧
      ∫ x, F x ∂K a = ∫ w, F (a, w) ∂π ∧ MemLp (fun w => F (a, w)) 2 π := by
    filter_upwards [(Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX |>.1,
      hL.ae_memLp_prod_right] with a ha hsl
    have hm : AEMeasurable F (K a) := ha.aestronglyMeasurable.aemeasurable
    have hmp : AEMeasurable (Prod.mk a) π := measurable_prodMk_left.aemeasurable
    exact ⟨variance_map hm hmp, integral_map hmp ha.aestronglyMeasurable, hsl⟩
  have hmean : MemLp (fun a => ∫ w, F (a, w) ∂π) 2 ν :=
    (memLp_integral_bind hK hprob hX).ae_eq (hslice.mono fun a ha => ha.2.1)
  have hvarint : Integrable (fun a => variance (fun w => F (a, w)) π) ν := by
    refine (integrable_covariance_bind hK hprob hX hX).congr ?_
    filter_upwards [(Measure.memLp_two_bind_iff hK hX.aestronglyMeasurable).mp hX |>.1,
      hslice] with a ha hs
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
/-- Jensen's inequality for the variance of an average: the variance of the average over the
second coordinate is at most the average over the second coordinate of the variances in the first
coordinate. -/
theorem evariance_integral_prod_le (hF : Measurable F) (hint : Integrable F (ν.prod π)) :
    evariance (fun a => ∫ w, F (a, w) ∂π) ν ≤
      ∫⁻ w, evariance (fun a => F (a, w)) ν ∂π := by
  have hmm : StronglyMeasurable (fun w => ∫ a, F (a, w) ∂ν) :=
    (hF.comp measurable_swap).stronglyMeasurable.integral_prod_right'
  have hmint : Integrable (fun w => ∫ a, F (a, w) ∂ν) π := hint.integral_prod_right
  have hm_eq : ∫ w, ∫ a, F (a, w) ∂ν ∂π = ∫ a, ∫ w, F (a, w) ∂π ∂ν := by
    rw [← integral_prod_symm _ hint, integral_prod _ hint]
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
          exact enorm_integral_le_lintegral_enorm _
      _ ≤ _ := by
          simpa [ENNReal.rpow_two] using rpow_lintegral_le_measure_univ_rpow_mul
            (μ := π) (u := fun w => ‖F (a, w) - ∫ a', F (a', w) ∂ν‖ₑ)
            (((hF.comp measurable_prodMk_left).sub hmm.measurable).enorm.aemeasurable)
            one_le_two
  calc evariance (fun a => ∫ w, F (a, w) ∂π) ν
      ≤ ∫⁻ a, ∫⁻ w, ‖F (a, w) - ∫ a', F (a', w) ∂ν‖ₑ ^ 2 ∂π ∂ν := lintegral_mono_ae hae
    _ = ∫⁻ w, ∫⁻ a, ‖F (a, w) - ∫ a', F (a', w) ∂ν‖ₑ ^ 2 ∂ν ∂π :=
        lintegral_lintegral_swap
          ((hF.sub (hmm.measurable.comp measurable_snd)).enorm.pow_const 2).aemeasurable
    _ = ∫⁻ w, evariance (fun a => F (a, w)) ν ∂π := rfl

/-- The two-factor Efron--Stein inequality. -/
theorem evariance_prod_le (hF : Measurable F) (hL : MemLp F 2 (ν.prod π)) :
    evariance F (ν.prod π) ≤ ∫⁻ a, evariance (fun w => F (a, w)) π ∂ν +
      ∫⁻ w, evariance (fun a => F (a, w)) ν ∂π := by
  rw [evariance_prod_eq hL]
  gcongr
  exact evariance_integral_prod_le hF (hL.integrable one_le_two)

end Prod

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
    ((hu.sub (hm.measurable.comp measurable_fst)).enorm.pow_const 2)

end TauCeti.Probability

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Statistics.Experiments.Density
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Calculus.FDeriv.Measurable
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Fisher information and the information inequality

For a family of real densities `f θ` in a real parameter `θ`, the **score** is
`likelihoodScore f θ x = ∂/∂θ log f(θ, x)` and the **Fisher information** of the family of laws
`P θ` is its second moment `fisherInformation P f θ = ∫ (likelihoodScore f θ)² dP θ`, which is
nonnegative. Where `f θ x ≠ 0` and `t ↦ f t x` is differentiable at `θ`, the score is
`∂_θ f(θ, x) / f(θ, x)`.

For a vector score `s : ι → X → ℝ` the information matrix `(∫ sᵢ sⱼ dP)ᵢⱼ` is the Gram matrix of
the `sᵢ` in `L²(P)`, hence positive semidefinite, when every `sᵢ` is square integrable.
Without square integrability this fails: for the density `2 (1 + x)⁻³` on `x ≥ 0` and
`s = (1, x)`, the junk value `0` of the integral of the nonintegrable `x²` gives the matrix
`[[1, 1], [1, 0]]`.

The **information inequality** holds for a regular model, one whose densities are
differentiable in the parameter almost everywhere and whose integrals `∫ f t dμ` and
`∫ W f t dμ` may be differentiated under the integral sign at `θ`: if the score and `W` are
square integrable (in particular, if the Fisher information is positive), then
`(d/dθ ∫ W dP θ)² ≤ Var[W; P θ] · fisherInformation P f θ`.
The first identity makes the score centred, the second makes `d/dθ ∫ W dP θ` the integral of
`W` times the score, and the Cauchy–Schwarz inequality concludes. The densities may vanish: the
score is the true score `∂_θ f / f` almost everywhere for `P θ`, and where `f θ` vanishes so does
`∂_θ f`, as the densities are nonnegative.

## Main definitions

* `TauCeti.likelihoodScore f θ x`: the score `∂/∂θ log f(θ, x)`.
* `TauCeti.fisherInformation P f θ`: the Fisher information `∫ (likelihoodScore f θ)² dP θ`.
* `TauCeti.fisherInformationMatrix s P`: the information matrix `(∫ sᵢ sⱼ dP)ᵢⱼ` of a vector
  score.

## Main results

* `TauCeti.likelihoodScore_eq_deriv_div`: the score is `∂_θ f / f`.
* `TauCeti.fisherInformation_nonneg`: the Fisher information is nonnegative.
* `TauCeti.posSemidef_fisherInformationMatrix`: the information matrix of a square-integrable
  vector score is positive semidefinite.
* `TauCeti.integral_likelihoodScore_eq_zero`: the score of a regular model has mean `0`.
* `TauCeti.integral_mul_likelihoodScore_eq_deriv`: `∫ W · score dP θ = d/dθ ∫ W dP θ`.
* `TauCeti.sq_deriv_le_variance_mul_fisherInformation_of_memLp`: the information inequality for
  a square-integrable score.
* `TauCeti.sq_deriv_le_variance_mul_fisherInformation`: the information inequality for positive
  Fisher information.

## References

* M. J. Schervish, *Theory of Statistics*, Springer (1995), Theorem 5.13.
* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002),
  Theorem 7.3.9.

The definitions are adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Inference/Model.lean`; the information inequality follows the Cauchy–Schwarz argument of
`CKSD/Inference/Estimation.lean`, with its regularity identities derived here.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {X : Type*} [MeasurableSpace X]

/-- The **score** `∂/∂θ log f(θ, x)` of a likelihood `f` in a real parameter `θ`. -/
noncomputable def likelihoodScore (f : ℝ → X → ℝ) (θ : ℝ) (x : X) : ℝ :=
  deriv (fun t ↦ Real.log (f t x)) θ

omit [MeasurableSpace X] in
/-- The defining formula of `likelihoodScore`. -/
theorem likelihoodScore_def (f : ℝ → X → ℝ) (θ : ℝ) (x : X) :
    likelihoodScore f θ x = deriv (fun t ↦ Real.log (f t x)) θ := (rfl)

omit [MeasurableSpace X] in
/-- Where the likelihood is nonzero and differentiable in the parameter, the score is
`∂_θ f(θ, x) / f(θ, x)`. -/
theorem likelihoodScore_eq_deriv_div {f : ℝ → X → ℝ} {θ : ℝ} {x : X}
    (hd : DifferentiableAt ℝ (fun t ↦ f t x) θ) (hf : f θ x ≠ 0) :
    likelihoodScore f θ x = deriv (fun t ↦ f t x) θ / f θ x :=
  deriv.log hd hf

/-- The **Fisher information** `∫ (∂/∂θ log f(θ, x))² dP θ(x)` of a real-parameter family of
laws `P θ` with likelihood `f`, the second moment of the score. -/
noncomputable def fisherInformation (P : ℝ → Measure X) (f : ℝ → X → ℝ) (θ : ℝ) : ℝ :=
  ∫ x, likelihoodScore f θ x ^ 2 ∂P θ

/-- The defining formula of `fisherInformation`. -/
theorem fisherInformation_def (P : ℝ → Measure X) (f : ℝ → X → ℝ) (θ : ℝ) :
    fisherInformation P f θ = ∫ x, likelihoodScore f θ x ^ 2 ∂P θ := (rfl)

/-- The Fisher information is nonnegative. -/
theorem fisherInformation_nonneg (P : ℝ → Measure X) (f : ℝ → X → ℝ) (θ : ℝ) :
    0 ≤ fisherInformation P f θ :=
  integral_nonneg fun _ ↦ sq_nonneg _

/-- The **information matrix** `(∫ sᵢ sⱼ dP)ᵢⱼ` of a vector score `s`. -/
noncomputable def fisherInformationMatrix {ι : Type*} (s : ι → X → ℝ) (P : Measure X) :
    Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ ∫ x, s i x * s j x ∂P

/-- The entries of the information matrix. -/
@[simp]
theorem fisherInformationMatrix_apply {ι : Type*} (s : ι → X → ℝ) (P : Measure X) (i j : ι) :
    fisherInformationMatrix s P i j = ∫ x, s i x * s j x ∂P := (rfl)

/-- The information matrix of a square-integrable vector score is the Gram matrix of its
components in `L²(P)`. -/
theorem fisherInformationMatrix_eq_gram {ι : Type*} {s : ι → X → ℝ} {P : Measure X}
    (hs : ∀ i, MemLp (s i) 2 P) :
    fisherInformationMatrix s P = Matrix.gram ℝ fun i ↦ (hs i).toLp (s i) := by
  ext i j
  rw [fisherInformationMatrix_apply, Matrix.gram_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(hs i).coeFn_toLp, (hs j).coeFn_toLp] with x hi hj
  rw [hi, hj, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
    mul_comm]

/-- The information matrix of a square-integrable vector score is positive semidefinite. -/
theorem posSemidef_fisherInformationMatrix {ι : Type*} {s : ι → X → ℝ}
    {P : Measure X} (hs : ∀ i, MemLp (s i) 2 P) : (fisherInformationMatrix s P).PosSemidef := by
  rw [fisherInformationMatrix_eq_gram hs]
  exact Matrix.posSemidef_gram ℝ _

variable {P : ℝ → Measure X} {μ : Measure X} {f : ℝ → X → ℝ} {θ : ℝ}

/-- Under densities `f t` of `P t` that are `μ`-almost everywhere differentiable in the parameter
at `θ`, the score is `P θ`-almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_likelihoodScore (hf : ∀ t, HasDensity (P t) μ (f t))
    (hd : ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun t ↦ f t x) θ) :
    AEStronglyMeasurable (likelihoodScore f θ) (P θ) := by
  refine aestronglyMeasurable_deriv_of_ae_differentiableAt
    (fun t ↦ (hf t).measurable.log.aestronglyMeasurable) ?_
  filter_upwards [(hf θ).absolutelyContinuous.ae_le hd, (hf θ).ae_pos] with x hdx hx
  exact hdx.log hx.ne'

/-- The score of a model with nonzero Fisher information is square integrable. -/
theorem memLp_likelihoodScore (hf : ∀ t, HasDensity (P t) μ (f t))
    (hd : ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun t ↦ f t x) θ) (hI : fisherInformation P f θ ≠ 0) :
    MemLp (likelihoodScore f θ) 2 (P θ) :=
  (memLp_two_iff_integrable_sq (aestronglyMeasurable_likelihoodScore hf hd)).2
    (Integrable.of_integral_ne_zero hI)

/-- Where a density vanishes, its derivative in the parameter vanishes, `μ`-almost everywhere:
the densities `f (θ ± 1 / (n + 1))` are almost everywhere nonnegative, so the difference
quotients are nonnegative from the right and nonpositive from the left. -/
private theorem ae_deriv_eq_zero_of_eq_zero (hf : ∀ t, HasDensity (P t) μ (f t))
    (hd : ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun t ↦ f t x) θ) :
    ∀ᵐ x ∂μ, f θ x = 0 → deriv (fun t ↦ f t x) θ = 0 := by
  have hnn : ∀ᵐ x ∂μ, ∀ n : ℕ,
      0 ≤ f (θ + 1 / ((n : ℝ) + 1)) x ∧ 0 ≤ f (θ + -(1 / ((n : ℝ) + 1))) x :=
    ae_all_iff.2 fun n ↦ (hf _).ae_nonneg.and (hf _).ae_nonneg
  have hseq : Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhdsWithin 0 {0}ᶜ) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall fun n ↦ by simp [Nat.cast_add_one_ne_zero]⟩
  have hseq' : Filter.Tendsto (fun n : ℕ ↦ -(1 / ((n : ℝ) + 1))) Filter.atTop
      (nhdsWithin 0 {0}ᶜ) :=
    tendsto_nhdsWithin_iff.2 ⟨neg_zero (G := ℝ) ▸ tendsto_one_div_add_atTop_nhds_zero_nat.neg,
      Filter.Eventually.of_forall fun n ↦ by simp [Nat.cast_add_one_ne_zero]⟩
  filter_upwards [hd, hnn] with x hdx hx h0
  have hlim := hasDerivAt_iff_tendsto_slope_zero.1 hdx.hasDerivAt
  refine le_antisymm (le_of_tendsto (hlim.comp hseq') (Filter.Eventually.of_forall fun n ↦ ?_))
    (ge_of_tendsto (hlim.comp hseq) (Filter.Eventually.of_forall fun n ↦ ?_))
  · have hn := (hx n).2
    simp only [Function.comp_apply, h0, sub_zero, smul_eq_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (by rw [inv_neg, one_div, inv_inv]; linarith) hn
  · have hn := (hx n).1
    simp only [Function.comp_apply, h0, sub_zero, smul_eq_mul]
    positivity

/-- The density times the score is the derivative of the density in the parameter,
`μ`-almost everywhere. -/
private theorem ae_mul_likelihoodScore_eq_deriv (hf : ∀ t, HasDensity (P t) μ (f t))
    (hd : ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun t ↦ f t x) θ) :
    ∀ᵐ x ∂μ, f θ x * likelihoodScore f θ x = deriv (fun t ↦ f t x) θ := by
  filter_upwards [hd, ae_deriv_eq_zero_of_eq_zero hf hd] with x hdx h0
  by_cases hx : f θ x = 0
  · rw [hx, zero_mul, h0 hx]
  · rw [likelihoodScore_eq_deriv_div hdx hx, mul_div_cancel₀ _ hx]

/-- **The score has mean zero** when `∫ f t dμ` may be differentiated under the integral sign at
`θ`. No integrability of the score is needed. -/
theorem integral_likelihoodScore_eq_zero [∀ t, IsProbabilityMeasure (P t)]
    (hf : ∀ t, HasDensity (P t) μ (f t)) (hd : ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun t ↦ f t x) θ)
    (h1 : HasDerivAt (fun t ↦ ∫ x, f t x ∂μ) (∫ x, deriv (fun t ↦ f t x) θ ∂μ) θ) :
    ∫ x, likelihoodScore f θ x ∂P θ = 0 := by
  have hconst : (fun t ↦ ∫ x, f t x ∂μ) = fun _ ↦ 1 := funext fun t ↦ (hf t).integral_eq_one
  rw [hconst] at h1
  simp_rw [(hf θ).integral_eq, smul_eq_mul]
  rw [integral_congr_ae (ae_mul_likelihoodScore_eq_deriv hf hd)]
  exact h1.unique (hasDerivAt_const θ 1)

/-- When `∫ W f t dμ` may be differentiated under the integral sign at `θ`, the derivative of the
mean of `W` is the integral of `W` times the score. -/
theorem integral_mul_likelihoodScore_eq_deriv (hf : ∀ t, HasDensity (P t) μ (f t))
    (hd : ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun t ↦ f t x) θ) {W : X → ℝ}
    (hW' : HasDerivAt (fun t ↦ ∫ x, W x * f t x ∂μ) (∫ x, W x * deriv (fun t ↦ f t x) θ ∂μ) θ) :
    ∫ x, W x * likelihoodScore f θ x ∂P θ = deriv (fun t ↦ ∫ x, W x ∂P t) θ := by
  have hmean : (fun t ↦ ∫ x, W x ∂P t) = fun t ↦ ∫ x, W x * f t x ∂μ :=
    funext fun t ↦ by simp_rw [(hf t).integral_eq, smul_eq_mul, mul_comm]
  rw [hmean, hW'.deriv, (hf θ).integral_eq]
  refine integral_congr_ae ?_
  filter_upwards [ae_mul_likelihoodScore_eq_deriv hf hd] with x hx
  rw [smul_eq_mul, ← hx]
  ring

/-- **The information inequality** for a regular real-parameter model with a square-integrable
score: the densities are almost everywhere differentiable in the parameter at `θ`, and the
integrals `∫ f t dμ` and `∫ W f t dμ` are differentiated under the integral sign at `θ`. For a
square-integrable `W`, `(d/dθ ∫ W dP θ)² ≤ Var[W; P θ] · fisherInformation P f θ`. The Fisher
information may be zero, as for a model that does not depend on the parameter. -/
theorem sq_deriv_le_variance_mul_fisherInformation_of_memLp [∀ t, IsProbabilityMeasure (P t)]
    (hf : ∀ t, HasDensity (P t) μ (f t)) {W : X → ℝ} (hW : MemLp W 2 (P θ))
    (hd : ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun t ↦ f t x) θ)
    (h1 : HasDerivAt (fun t ↦ ∫ x, f t x ∂μ) (∫ x, deriv (fun t ↦ f t x) θ ∂μ) θ)
    (hW' : HasDerivAt (fun t ↦ ∫ x, W x * f t x ∂μ) (∫ x, W x * deriv (fun t ↦ f t x) θ ∂μ) θ)
    (hs : MemLp (likelihoodScore f θ) 2 (P θ)) :
    deriv (fun t ↦ ∫ x, W x ∂P t) θ ^ 2 ≤ Var[W; P θ] * fisherInformation P f θ := by
  have hWc : MemLp (fun x ↦ W x - ∫ y, W y ∂P θ) 2 (P θ) := hW.sub (memLp_const _)
  have hcross : ∫ x, (W x - ∫ y, W y ∂P θ) * likelihoodScore f θ x ∂P θ =
      deriv (fun t ↦ ∫ x, W x ∂P t) θ := by
    simp_rw [sub_mul]
    have hWs : Integrable (fun x ↦ W x * likelihoodScore f θ x) (P θ) := hW.integrable_mul hs
    rw [integral_sub hWs ((hs.integrable one_le_two).const_mul _),
      integral_const_mul, integral_likelihoodScore_eq_zero hf hd h1, mul_zero, sub_zero,
      integral_mul_likelihoodScore_eq_deriv hf hd hW']
  rw [← hcross, variance_eq_integral hW.aemeasurable, fisherInformation_def]
  exact sq_integral_mul_le_integral_sq_mul_integral_sq hWc hs

/-- **The information inequality** for a regular real-parameter model: the densities are
almost everywhere differentiable in the parameter at `θ`, and the integrals
`∫ f t dμ` and `∫ W f t dμ` are differentiated under the integral sign at `θ`. For a
square-integrable `W` and positive Fisher information,
`(d/dθ ∫ W dP θ)² ≤ Var[W; P θ] · fisherInformation P f θ`. Positive information makes the score
square integrable (`TauCeti.memLp_likelihoodScore`); see
`TauCeti.sq_deriv_le_variance_mul_fisherInformation_of_memLp` for the form under square
integrability of the score. -/
theorem sq_deriv_le_variance_mul_fisherInformation [∀ t, IsProbabilityMeasure (P t)]
    (hf : ∀ t, HasDensity (P t) μ (f t)) {W : X → ℝ} (hW : MemLp W 2 (P θ))
    (hd : ∀ᵐ x ∂μ, DifferentiableAt ℝ (fun t ↦ f t x) θ)
    (h1 : HasDerivAt (fun t ↦ ∫ x, f t x ∂μ) (∫ x, deriv (fun t ↦ f t x) θ ∂μ) θ)
    (hW' : HasDerivAt (fun t ↦ ∫ x, W x * f t x ∂μ) (∫ x, W x * deriv (fun t ↦ f t x) θ ∂μ) θ)
    (hI : 0 < fisherInformation P f θ) :
    deriv (fun t ↦ ∫ x, W x ∂P t) θ ^ 2 ≤ Var[W; P θ] * fisherInformation P f θ :=
  sq_deriv_le_variance_mul_fisherInformation_of_memLp hf hW hd h1 hW'
    (memLp_likelihoodScore hf hd hI.ne')

end TauCeti

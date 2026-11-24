/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# The Fourier integral of an integrable function

On a finite-dimensional real inner-product space, the Fourier transform `𝓕 f` of an integrable
`f` with values in a complex normed space is continuous, and so is the inverse transform `𝓕⁻ f`.
These are Mathlib's `VectorFourier.fourierIntegral_continuous` specialized to the inner-product
pairing and its negation, packaged so that consumers do not repeat the pairing-continuity bridge
at every call site.

This file also records the elementary algebraic and `L¹` properties of the Fourier integral of a
function: it is homogeneous for every function and additive on integrable functions, it is
bounded from `L¹` to `L^∞` with norm at most one, and `L¹` convergence of integrable functions
makes their Fourier integrals converge uniformly. For a family of functions depending on a real
parameter, the inverse Fourier integral can be differentiated in the parameter under the integral
sign under the usual domination hypothesis.

## Main declarations

* `MeasureTheory.Integrable.continuous_fourier`: `𝓕 f` is continuous for integrable `f`.
* `MeasureTheory.Integrable.continuous_fourierInv`: `𝓕⁻ f` is continuous for integrable `f`.
* `Real.fourier_const_smul`, `Real.fourier_neg`: `𝓕 (c • f) = c • 𝓕 f` and `𝓕 (-f) = -𝓕 f`;
  `Real.fourierInv_const_smul`: `𝓕⁻ (c • f) = c • 𝓕⁻ f`.
* `MeasureTheory.Integrable.fourier_add`, `MeasureTheory.Integrable.fourier_sub`: the Fourier
  integral is additive on integrable functions; `MeasureTheory.Integrable.fourierInv_add`: so is
  the inverse Fourier integral.
* `MeasureTheory.Integrable.fourierChar_smul`: an integrable function times a measurable phase
  `𝐞 (φ ξ)` is integrable.
* `TauCeti.eLpNorm_fourier_top_le`: `‖𝓕 f‖_∞ ≤ ‖f‖₁`.
* `MeasureTheory.Integrable.tendstoUniformly_fourier`: if integrable `gᵢ` tend to an integrable
  `f` in `L¹`, then `𝓕 gᵢ` tends to `𝓕 f` uniformly.
* `Real.hasDerivAt_fourierInv_of_dominated_loc_of_deriv_le`: differentiation in a real parameter
  under the inverse Fourier integral, for integrands whose parameter derivatives are dominated by
  an integrable function near the base point.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform

namespace MeasureTheory.Integrable

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

/-- The Fourier transform of an integrable function is continuous. This is Mathlib's
`VectorFourier.fourierIntegral_continuous` specialized to the inner-product pairing. -/
theorem continuous_fourier (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

/-- The inverse Fourier transform of an integrable function is continuous. This is Mathlib's
`VectorFourier.fourierIntegral_continuous` specialized to the negated inner-product pairing. -/
theorem continuous_fourierInv (hf : Integrable f) : Continuous (𝓕⁻ f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (-innerSL ℝ).continuous₂ hf

end MeasureTheory.Integrable

namespace Real

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Fourier integral of a function is homogeneous: `𝓕 (c • f) = c • 𝓕 f`. On functions, `𝓕`
is by definition `VectorFourier.fourierIntegral` for the pairing `innerₗ V`
(`Real.instFourierTransform`), so this is Mathlib's `VectorFourier.fourierIntegral_const_smul`. -/
@[simp]
theorem fourier_const_smul (c : ℂ) (f : V → E) : 𝓕 (c • f) = c • 𝓕 f :=
  VectorFourier.fourierIntegral_const_smul _ _ _ _ _

/-- The inverse Fourier integral of a function is homogeneous: `𝓕⁻ (c • f) = c • 𝓕⁻ f`. On
functions, `𝓕⁻` is by definition `VectorFourier.fourierIntegral` for the pairing `-innerₗ V`
(`Real.instFourierTransformInv`), so this is again Mathlib's
`VectorFourier.fourierIntegral_const_smul`. -/
@[simp]
theorem fourierInv_const_smul (c : ℂ) (f : V → E) : 𝓕⁻ (c • f) = c • 𝓕⁻ f :=
  VectorFourier.fourierIntegral_const_smul _ _ _ _ _

/-- The Fourier integral of `-f` is `-𝓕 f`. -/
@[simp]
theorem fourier_neg (f : V → E) : 𝓕 (-f) = -𝓕 f := by
  simpa only [neg_one_smul] using fourier_const_smul (-1) f

end Real

namespace MeasureTheory.Integrable

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : V → E}

/-- The Fourier integral is additive on integrable functions. -/
theorem fourier_add (hf : Integrable f) (hg : Integrable g) : 𝓕 (f + g) = 𝓕 f + 𝓕 g :=
  VectorFourier.fourierIntegral_add (L := innerₗ V) Real.continuous_fourierChar continuous_inner
    hf hg

/-- The inverse Fourier integral is additive on integrable functions. -/
theorem fourierInv_add (hf : Integrable f) (hg : Integrable g) : 𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g :=
  VectorFourier.fourierIntegral_add (L := -innerₗ V) Real.continuous_fourierChar
    continuous_inner.neg hf hg

/-- An integrable function times a measurable phase `𝐞 (φ x)` is integrable, since the phase has
norm one. -/
theorem fourierChar_smul {α : Type*} [MeasurableSpace α] {μ : Measure α} {a : α → E}
    {φ : α → ℝ} (ha : Integrable a μ) (hφ : AEMeasurable φ μ) :
    Integrable (fun x ↦ 𝐞 (φ x) • a x) μ :=
  ha.mono ((Real.continuous_fourierChar.comp_aestronglyMeasurable
    hφ.aestronglyMeasurable).smul ha.aestronglyMeasurable) (ae_of_all _ fun x ↦ by simp)

/-- The Fourier integral of a difference of integrable functions is the difference of their
Fourier integrals. -/
theorem fourier_sub (hf : Integrable f) (hg : Integrable g) : 𝓕 (f - g) = 𝓕 f - 𝓕 g := by
  rw [sub_eq_add_neg, hf.fourier_add hg.neg, Real.fourier_neg, ← sub_eq_add_neg]

/-- If integrable functions `gᵢ` tend to an integrable function `f` in `L¹`, then their Fourier
integrals tend to `𝓕 f` uniformly, since `‖𝓕 gᵢ - 𝓕 f‖_∞ ≤ ‖gᵢ - f‖₁`. -/
theorem tendstoUniformly_fourier {ι : Type*} {l : Filter ι} {g : ι → V → E} (hf : Integrable f)
    (hg : ∀ i, Integrable (g i)) (h : Tendsto (fun i => eLpNorm (g i - f) 1 volume) l (𝓝 0)) :
    TendstoUniformly (fun i => 𝓕 (g i)) (𝓕 f) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).eventually
    (gt_mem_nhds (by simpa using hε))] with i hi ξ
  rw [dist_eq_norm', ← Pi.sub_apply (𝓕 (g i)), ← (hg i).fourier_sub hf]
  refine (Real.norm_fourier_le_integral_norm _ _).trans_lt ?_
  rwa [integral_norm_eq_lintegral_eNorm ((hg i).1.sub hf.1),
    ← eLpNorm_one_eq_lintegral_eNorm ((hg i).1.sub hf.1)]

end MeasureTheory.Integrable

namespace TauCeti

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Fourier integral is bounded from `L¹` to `L^∞` with norm at most one:
`‖𝓕 f‖_∞ ≤ ‖f‖₁`. No integrability is assumed; for a function outside `L¹` the bound is trivial. -/
theorem eLpNorm_fourier_top_le (f : V → E) : eLpNorm (𝓕 f) ∞ volume ≤ eLpNorm f 1 volume := by
  by_cases hf : Integrable f
  · rw [eLpNorm_exponent_top hf.continuous_fourier.aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_eNorm hf.aestronglyMeasurable]
    refine eLpNormEssSup_le_of_ae_eNorm_bound (ae_of_all _ fun ξ => ?_)
    rw [Real.fourier_eq]
    refine (eNorm_integral_le_lintegral_eNorm _).trans_eq ?_
    simp only [Circle.eNorm_smul]
  · have h : eLpNorm f 1 volume = ∞ := by
      by_contra h
      exact hf (memLp_one_iff_integrable.1 (memLp_iff.2 (lt_top_iff_ne_top.2 h)))
    rw [h]
    exact le_top

end TauCeti

namespace Real

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Differentiation under the inverse Fourier integral.** If `G s` is integrable at `s = t`,
a.e. strongly measurable for `s` near `t`, and differentiable in `s` with derivatives `G' s`
dominated near `t` by an integrable function, then `s ↦ 𝓕⁻ (G s) x` has derivative
`𝓕⁻ (G' t) x` at `t`. This is `hasDerivAt_integral_of_dominated_loc_of_deriv_le` for the
integrands `𝐞 ⟪ξ, x⟫ • G s ξ`, which have the same norms. -/
theorem hasDerivAt_fourierInv_of_dominated_loc_of_deriv_le {G G' : ℝ → V → E} {b : V → ℝ}
    {t : ℝ} {S : Set ℝ} (hS : S ∈ 𝓝 t) (hG : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (G s))
    (hGt : Integrable (G t)) (hG' : AEStronglyMeasurable (G' t))
    (hbd : ∀ᵐ ξ, ∀ s ∈ S, ‖G' s ξ‖ ≤ b ξ) (hb : Integrable b)
    (hd : ∀ᵐ ξ, ∀ s ∈ S, HasDerivAt (G · ξ) (G' s ξ) s) (x : V) :
    HasDerivAt (fun s ↦ 𝓕⁻ (G s) x) (𝓕⁻ (G' t) x) t := by
  have hc : Continuous fun ξ : V ↦ 𝐞 (inner ℝ ξ x) :=
    continuous_fourierChar.comp (continuous_id.inner continuous_const)
  simp only [fourierInv_eq]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun s ξ ↦ 𝐞 (inner ℝ ξ x) • G' s ξ) hS
    (hG.mono fun s hs ↦ hc.aestronglyMeasurable.smul hs)
    (hGt.mono (hc.aestronglyMeasurable.smul hGt.1) (ae_of_all _ fun ξ ↦ by simp))
    (hc.aestronglyMeasurable.smul hG') ?_ hb
    (hd.mono fun ξ hξ s hs ↦ (hξ s hs).const_smul _)).2
  filter_upwards [hbd] with ξ hξ s hs
  rw [Circle.norm_smul]
  exact hξ s hs

end Real

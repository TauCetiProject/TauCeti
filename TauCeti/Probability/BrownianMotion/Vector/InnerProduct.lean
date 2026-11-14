/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Vector.Basic

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess
import TauCeti.Probability.Distributions.Gaussian.IsGaussianProcess

/-!
# Vector Brownian motion on real inner-product spaces

This file defines basis-free centered pre-Brownian and Brownian motion in a real inner-product space
`E`, proves their equivalence with `IsPreBrownianVector` / `IsBrownianVector` in every finite
orthonormal basis, establishes Gaussian laws of directional projections and vector increments,
proves invariance under linear isometric equivalences, and derives noncentered translations `ξ + W`.

## Main definitions

* `TauCeti.Probability.IsPreBrownian`: centered `E`-valued Gaussian process `W : ℝ≥0 → Ω → E` with
  `cov[⟪u, W s⟫, ⟪v, W t⟫; P] = min s t * ⟪u, v⟫`.
* `TauCeti.Probability.IsBrownian`: `IsPreBrownian` with almost-sure path continuity.

## Main results

* `TauCeti.Probability.isPreBrownian_iff_isPreBrownianVector`,
  `TauCeti.Probability.isBrownian_iff_isBrownianVector`: finite orthonormal-basis dictionary.
* `TauCeti.Probability.IsPreBrownian.hasLaw_inner_eval`,
  `TauCeti.Probability.IsPreBrownian.isPreBrownianReal_norm_inv_mul_inner`: directional projections.
* `TauCeti.Probability.isPreBrownian_comp_linearIsometryEquiv_iff`: `E ≃ₗᵢ[ℝ] F` invariance.
* `TauCeti.Probability.IsPreBrownian.hasLaw_sub_of_le`,
  `TauCeti.Probability.IsPreBrownian.hasIndepIncrements`,
  `ProbabilityTheory.HasIndepIncrements.isPreBrownian_of_hasLaw`: standard Gaussian increment laws
  and independent-increment characterization.
* `TauCeti.Probability.IsPreBrownian.indepFun_add_left_increments`: noncentered Brownian motion
  `ξ + W` started at an independent random vector `ξ`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.1.
* P. Mörters, Y. Peres, *Brownian Motion*, Cambridge University Press, 2010, Chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal RealInnerProductSpace

namespace TauCeti.Probability

variable {ι Ω E F : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section Defs

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

/-- `W : ℝ≥0 → Ω → E` is a **vector pre-Brownian motion** in a real inner-product space `E` under
`P` if it is a centered `E`-valued Gaussian process whose inner-product projections satisfy
`cov[⟪u, W s⟫, ⟪v, W t⟫; P] = min s t * ⟪u, v⟫` for all `s, t : ℝ≥0` and `u, v : E`. -/
structure IsPreBrownian (W : ℝ≥0 → Ω → E) (P : Measure Ω := by volume_tac) : Prop where
  /-- `W` is an `E`-valued Gaussian process under `P`. -/
  isGaussianProcess : IsGaussianProcess W P
  /-- Every directional projection `⟪u, W t⟫` has mean zero. -/
  integral_inner (t : ℝ≥0) (u : E) : ∫ ω, ⟪u, W t ω⟫ ∂P = 0
  /-- Directional projections have covariance `min s t * ⟪u, v⟫`. -/
  covariance_inner (s t : ℝ≥0) (u v : E) :
    cov[fun ω ↦ ⟪u, W s ω⟫, fun ω ↦ ⟪v, W t ω⟫; P] = min (s : ℝ) t * ⟪u, v⟫

/-- `W : ℝ≥0 → Ω → E` is a **vector Brownian motion** in `E` under `P` if it is a vector
pre-Brownian motion with almost-surely continuous sample paths. -/
structure IsBrownian (W : ℝ≥0 → Ω → E) (P : Measure Ω := by volume_tac) : Prop
    extends IsPreBrownian W P where
  /-- Almost every sample path `t ↦ W t ω` is continuous in `E`. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous (W · ω)

namespace IsPreBrownian

variable {W W' : ℝ≥0 → Ω → E}

/-- A vector pre-Brownian motion can only exist under a probability measure. -/
theorem isProbabilityMeasure (hW : IsPreBrownian W P) : IsProbabilityMeasure P :=
  hW.isGaussianProcess.isProbabilityMeasure

/-- Every time marginal of a vector pre-Brownian motion is a.e. measurable. -/
theorem aemeasurable (hW : IsPreBrownian W P) (t : ℝ≥0) : AEMeasurable (W t) P :=
  hW.isGaussianProcess.aemeasurable t

/-- Fixed-time almost-everywhere modifications preserve `IsPreBrownian`. -/
theorem congr (hW : IsPreBrownian W P) (h : ∀ t, W t =ᵐ[P] W' t) : IsPreBrownian W' P where
  isGaussianProcess := hW.isGaussianProcess.congr h
  integral_inner t u := by
    rw [← hW.integral_inner t u]
    exact integral_congr_ae ((h t).symm.mono fun _ hω ↦ by dsimp only; rw [hω])
  covariance_inner s t u v := by
    have hm (w : E) (r : ℝ≥0) : P[fun ω ↦ ⟪w, W' r ω⟫] = P[fun ω ↦ ⟪w, W r ω⟫] :=
      integral_congr_ae ((h r).symm.mono fun _ hω ↦ by dsimp only; rw [hω])
    rw [← hW.covariance_inner s t u v, covariance, covariance]
    refine integral_congr_ae ?_
    filter_upwards [h s, h t] with ω hs ht using by simp [hs, ht, hm]

/-- Indistinguishable modifications preserve `IsPreBrownian`. -/
theorem congr_indistinguishable (hW : IsPreBrownian W P) (h : W ≡ᵐ[P] W') : IsPreBrownian W' P :=
  hW.congr fun t ↦ h.mono fun _ hω ↦ hω t

end IsPreBrownian

namespace IsBrownian

variable {W W' : ℝ≥0 → Ω → E}

/-- Indistinguishable modifications preserve `IsBrownian`. -/
theorem congr_indistinguishable (hW : IsBrownian W P) (h : W ≡ᵐ[P] W') : IsBrownian W' P :=
  ⟨hW.toIsPreBrownian.congr_indistinguishable h,
    hW.ae_continuous.mp (h.mono fun _ hω hc ↦ by simpa [funext hω] using hc)⟩

end IsBrownian

end Defs

section Basic

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {W : ℝ≥0 → Ω → E}

namespace IsPreBrownian

/-- Every time marginal `W t` of a vector pre-Brownian motion has a Gaussian law on `E`. -/
theorem hasGaussianLaw_eval (hW : IsPreBrownian W P) (t : ℝ≥0) : HasGaussianLaw (W t) P :=
  hW.isGaussianProcess.hasGaussianLaw_eval t

/-- On a complete separable inner-product space, every time marginal `W t` belongs to `L²(P)`. -/
theorem memLp_two_eval [SecondCountableTopology E] [CompleteSpace E]
    (hW : IsPreBrownian W P) (t : ℝ≥0) : MemLp (W t) 2 P :=
  (hW.hasGaussianLaw_eval t).memLp_two

/-- On a complete separable inner-product space, every time marginal `W t` is Bochner integrable. -/
theorem integrable_eval [SecondCountableTopology E] [CompleteSpace E]
    (hW : IsPreBrownian W P) (t : ℝ≥0) : Integrable (W t) P :=
  (hW.hasGaussianLaw_eval t).integrable

/-- Every scalar inner-product marginal `ω ↦ ⟪u, W t ω⟫` has a real Gaussian law. -/
theorem hasGaussianLaw_inner_eval (hW : IsPreBrownian W P) (u : E) (t : ℝ≥0) :
    HasGaussianLaw (fun ω ↦ ⟪u, W t ω⟫) P :=
  (hW.hasGaussianLaw_eval t).map (innerSL ℝ u)

/-- Every scalar inner-product marginal `ω ↦ ⟪u, W t ω⟫` belongs to `L²(P)`. -/
theorem memLp_two_inner_eval (hW : IsPreBrownian W P) (u : E) (t : ℝ≥0) :
    MemLp (fun ω ↦ ⟪u, W t ω⟫) 2 P :=
  (hW.hasGaussianLaw_inner_eval u t).memLp_two

/-- On a complete separable inner-product space, every `W t` has Bochner integral `0`. -/
@[simp]
theorem integral_eval [SecondCountableTopology E] [CompleteSpace E]
    (hW : IsPreBrownian W P) (t : ℝ≥0) : ∫ ω, W t ω ∂P = 0 :=
  ext_inner_left ℝ fun u ↦ by
    simpa [innerSL_apply_apply] using
      ((innerSL ℝ u).integral_comp_comm (hW.integrable_eval t)).symm.trans (hW.integral_inner t u)

/-- On `[Subsingleton E]`, every process on a probability space is a vector pre-Brownian motion. -/
theorem of_subsingleton [Subsingleton E] [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → E) :
    IsPreBrownian W P :=
  ⟨⟨fun _ ↦ .of_subsingleton⟩, fun _ _ ↦ by simp [Subsingleton.elim _ (0 : E)],
    fun _ _ u _ ↦ by simp [Subsingleton.elim u 0]⟩

/-- Variance of a directional projection `⟪u, W t⟫` equals `‖u‖ ^ 2 * t`. -/
theorem variance_inner_eval (hW : IsPreBrownian W P) (u : E) (t : ℝ≥0) :
    Var[fun ω ↦ ⟪u, W t ω⟫; P] = ‖u‖ ^ 2 * (t : ℝ) := by
  have := hW.isProbabilityMeasure
  rw [← covariance_self (hW.hasGaussianLaw_inner_eval u t).aemeasurable,
    hW.covariance_inner, min_self, real_inner_self_eq_norm_sq, mul_comm]

/-- For every `u : E`, `⟪u, W t⟫` has Gaussian law `gaussianReal 0 (‖u‖₊ ^ 2 * t)`. -/
theorem hasLaw_inner_eval (hW : IsPreBrownian W P) (u : E) (t : ℝ≥0) :
    HasLaw (fun ω ↦ ⟪u, W t ω⟫) (gaussianReal 0 (‖u‖₊ ^ 2 * t)) P :=
  ⟨(hW.hasGaussianLaw_inner_eval u t).aemeasurable, by
    rw [(hW.hasGaussianLaw_inner_eval u t).map_eq_gaussianReal, hW.integral_inner,
      hW.variance_inner_eval]
    exact congrArg (gaussianReal 0) (NNReal.coe_injective <| by
      simp [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg _) t.coe_nonneg)])⟩

end IsPreBrownian

/-- Constructor for `IsPreBrownian` from Bochner mean zero `∀ t, ∫ ω, W t ω ∂P = 0`. -/
theorem isPreBrownian_of_integral_eval [SecondCountableTopology E] [CompleteSpace E]
    (hG : IsGaussianProcess W P) (hmean : ∀ t, ∫ ω, W t ω ∂P = 0)
    (hcov : ∀ s t (u v : E),
      cov[fun ω ↦ ⟪u, W s ω⟫, fun ω ↦ ⟪v, W t ω⟫; P] = min (s : ℝ) t * ⟪u, v⟫) :
    IsPreBrownian W P :=
  ⟨hG, fun t u ↦ by
    simpa [hmean t] using (innerSL ℝ u).integral_comp_comm (hG.hasGaussianLaw_eval t).integrable,
    hcov⟩

/-- Characterization of `IsPreBrownian` on a complete separable space via Bochner mean zero. -/
theorem isPreBrownian_iff_of_completeSpace [SecondCountableTopology E] [CompleteSpace E] :
    IsPreBrownian W P ↔
      IsGaussianProcess W P ∧ (∀ t, ∫ ω, W t ω ∂P = 0) ∧
        ∀ s t (u v : E),
          cov[fun ω ↦ ⟪u, W s ω⟫, fun ω ↦ ⟪v, W t ω⟫; P] = min (s : ℝ) t * ⟪u, v⟫ :=
  ⟨fun h ↦ ⟨h.isGaussianProcess, h.integral_eval, h.covariance_inner⟩,
    fun ⟨hG, hm, hc⟩ ↦ isPreBrownian_of_integral_eval hG hm hc⟩

/-- On `[Subsingleton E]`, every process on a probability space is a vector Brownian motion. -/
theorem IsBrownian.of_subsingleton [Subsingleton E] [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → E) : IsBrownian W P :=
  ⟨.of_subsingleton W, ae_of_all _ fun ω ↦ Subsingleton.elim (W · ω) (fun _ ↦ 0) ▸ continuous_const⟩

/-- On `E = ℝ`, `IsPreBrownian` agrees with `ProbabilityTheory.IsPreBrownianReal`. -/
@[simp]
theorem isPreBrownian_real_iff {W : ℝ≥0 → Ω → ℝ} :
    IsPreBrownian W P ↔ IsPreBrownianReal W P where
  mp hW := hW.isGaussianProcess.isPreBrownianReal_of_covariance hW.integral_eval fun s t hst ↦ by
    simpa [min_eq_left (NNReal.coe_le_coe.mpr hst)] using hW.covariance_inner s t 1 1
  mpr hW := isPreBrownian_of_integral_eval hW.isGaussianProcess hW.integral_eval fun s t u v ↦ by
    have := hW.isGaussianProcess.isProbabilityMeasure
    simp only [RCLike.inner_apply, conj_trivial]
    simp_rw [mul_comm (W _ _) _]
    rw [covariance_const_mul_left, covariance_const_mul_right, hW.covariance_eval]
    push_cast; ring

/-- On `E = ℝ`, `IsBrownian` agrees with `ProbabilityTheory.IsBrownianReal`. -/
@[simp]
theorem isBrownian_real_iff {W : ℝ≥0 → Ω → ℝ} : IsBrownian W P ↔ IsBrownianReal W P :=
  ⟨fun hW ↦ ⟨isPreBrownian_real_iff.mp hW.toIsPreBrownian, hW.ae_continuous⟩,
    fun hW ↦ ⟨isPreBrownian_real_iff.mpr hW.toIsPreBrownianReal, hW.cont⟩⟩

end Basic

section Transformations

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {W : ℝ≥0 → Ω → E}

namespace IsPreBrownian

/-- For nonzero `u : E`, `‖u‖⁻¹ * ⟪u, W t⟫` is a scalar pre-Brownian motion. -/
theorem isPreBrownianReal_norm_inv_mul_inner (hW : IsPreBrownian W P) {u : E} (hu : u ≠ 0) :
    IsPreBrownianReal (fun t ω ↦ ‖u‖⁻¹ * ⟪u, W t ω⟫) P := by
  have := hW.isProbabilityMeasure
  have hG : IsGaussianProcess (fun t ω ↦ ‖u‖⁻¹ * ⟪u, W t ω⟫) P :=
    hW.isGaussianProcess.comp_left fun _ ↦ ‖u‖⁻¹ • innerSL ℝ u
  refine hG.isPreBrownianReal_of_covariance
    (fun t ↦ by rw [integral_const_mul, hW.integral_inner, mul_zero]) fun s t hst ↦ ?_
  have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  rw [covariance_const_mul_left, covariance_const_mul_right, hW.covariance_inner,
    min_eq_left (NNReal.coe_le_coe.mpr hst), real_inner_self_eq_norm_sq]
  field_simp

/-- Projecting onto a unit vector `u` (`‖u‖ = 1`) produces a scalar pre-Brownian motion. -/
theorem isPreBrownianReal_inner_of_norm_eq_one (hW : IsPreBrownian W P) {u : E} (hu : ‖u‖ = 1) :
    IsPreBrownianReal (fun t ω ↦ ⟪u, W t ω⟫) P := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  simpa [hu] using hW.isPreBrownianReal_norm_inv_mul_inner hu0

/-- Applying a linear isometric equivalence `f : E ≃ₗᵢ[ℝ] F` preserves `IsPreBrownian`. -/
theorem comp_linearIsometryEquiv [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (hW : IsPreBrownian W P) (f : E ≃ₗᵢ[ℝ] F) :
    IsPreBrownian (fun t ω ↦ f (W t ω)) P where
  isGaussianProcess :=
    hW.isGaussianProcess.comp_left fun _ ↦ f.toContinuousLinearEquiv.toContinuousLinearMap
  integral_inner t u := by
    have hflip (x : E) : ⟪u, f x⟫ = ⟪f.symm u, x⟫ := by
      rw [real_inner_comm, f.inner_map_eq_flip, real_inner_comm]
    simp_rw [hflip]; exact hW.integral_inner t (f.symm u)
  covariance_inner s t u v := by
    have hflip (y : F) (x : E) : ⟪y, f x⟫ = ⟪f.symm y, x⟫ := by
      rw [real_inner_comm, f.inner_map_eq_flip, real_inner_comm]
    simp_rw [hflip]; rw [hW.covariance_inner, f.symm.inner_map_map]

/-- Negation preserves `IsPreBrownian`. -/
theorem neg (hW : IsPreBrownian W P) : IsPreBrownian (-W) P :=
  hW.comp_linearIsometryEquiv (.neg ℝ)

/-- Brownian diffusive scaling `(√c)⁻¹ • W (c * t)` (`c ≠ 0`) preserves `IsPreBrownian`. -/
theorem smul (hW : IsPreBrownian W P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsPreBrownian (fun t ω ↦ (√(c : ℝ))⁻¹ • W (c * t) ω) P where
  isGaussianProcess := (hW.isGaussianProcess.comp_right (c * ·)).smul fun _ ↦ (√(c : ℝ))⁻¹
  integral_inner t u := by
    simp_rw [real_inner_smul_right, integral_const_mul, hW.integral_inner, mul_zero]
  covariance_inner s t u v := by
    have := hW.isProbabilityMeasure
    have hc_pos : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
    simp_rw [real_inner_smul_right]
    rw [covariance_const_mul_left, covariance_const_mul_right, hW.covariance_inner]
    push_cast
    rw [← mul_min_of_nonneg _ _ hc_pos.le]
    have hsq : (√(c : ℝ))⁻¹ * ((√(c : ℝ))⁻¹ * ((c : ℝ) * min (s : ℝ) t * ⟪u, v⟫)) =
        ((√(c : ℝ)) ^ 2)⁻¹ * (c : ℝ) * (min (s : ℝ) t * ⟪u, v⟫) := by ring
    rw [hsq, Real.sq_sqrt hc_pos.le, inv_mul_cancel₀ hc_pos.ne', one_mul]

omit [SecondCountableTopology E] in
private theorem covariance_inner_sub (hW : IsPreBrownian W P) (s₁ s₂ t₁ t₂ : ℝ≥0) (u v : E) :
    cov[fun ω ↦ ⟪u, W s₂ ω - W s₁ ω⟫, fun ω ↦ ⟪v, W t₂ ω - W t₁ ω⟫; P] =
      (min (s₂ : ℝ) t₂ - min (s₂ : ℝ) t₁ - (min (s₁ : ℝ) t₂ - min (s₁ : ℝ) t₁)) * ⟪u, v⟫ := by
  have := hW.isProbabilityMeasure
  have hsub (w : E) (a b : ℝ≥0) : (fun ω ↦ ⟪w, W b ω - W a ω⟫) =
      (fun ω ↦ ⟪w, W b ω⟫) - fun ω ↦ ⟪w, W a ω⟫ := by ext ω; simp [inner_sub_right]
  rw [hsub u s₁ s₂, hsub v t₁ t₂, covariance_sub_left (hW.memLp_two_inner_eval u s₂)
      (hW.memLp_two_inner_eval u s₁) ((hW.memLp_two_inner_eval v t₂).sub
        (hW.memLp_two_inner_eval v t₁)),
    covariance_sub_right (hW.memLp_two_inner_eval u s₂)
      (hW.memLp_two_inner_eval v t₂) (hW.memLp_two_inner_eval v t₁),
    covariance_sub_right (hW.memLp_two_inner_eval u s₁)
      (hW.memLp_two_inner_eval v t₂) (hW.memLp_two_inner_eval v t₁)]
  simp only [hW.covariance_inner]; ring

/-- Deterministic time shift `W (t₀ + t) - W t₀` preserves `IsPreBrownian`. -/
theorem shift (hW : IsPreBrownian W P) (t₀ : ℝ≥0) :
    IsPreBrownian (fun t ω ↦ W (t₀ + t) ω - W t₀ ω) P where
  isGaussianProcess := hW.isGaussianProcess.shift t₀
  integral_inner t u := by
    simp_rw [inner_sub_right]
    rw [integral_sub (hW.hasGaussianLaw_inner_eval u (t₀ + t)).integrable
      (hW.hasGaussianLaw_inner_eval u t₀).integrable, hW.integral_inner, hW.integral_inner,
      sub_zero]
  covariance_inner s t u v := by
    rw [hW.covariance_inner_sub]
    push_cast
    rw [← add_min, min_eq_right (le_add_of_nonneg_right s.coe_nonneg),
      min_eq_left (le_add_of_nonneg_right t.coe_nonneg), min_self]; ring

/-- For `s ≤ t`, `⟪u, W t - W s⟫` has Gaussian law `gaussianReal 0 (‖u‖₊ ^ 2 * (t - s))`. -/
theorem hasLaw_inner_sub_of_le (hW : IsPreBrownian W P) (u : E) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ ⟪u, W t ω - W s ω⟫) (gaussianReal 0 (‖u‖₊ ^ 2 * (t - s))) P := by
  simpa only [add_tsub_cancel_of_le hst] using (hW.shift s).hasLaw_inner_eval u (t - s)

/-- Weak Markov independence: `t ↦ W (t₀ + t) - W t₀` is independent of `(W u)_{u ≤ t₀}`. -/
theorem indepFun_shift [CompleteSpace E] (hW : IsPreBrownian W P) (t₀ : ℝ≥0) :
    IndepFun (fun ω t ↦ W (t₀ + t) ω - W t₀ ω) (fun ω (u : Set.Iic t₀) ↦ W u ω) P := by
  have := hW.isProbabilityMeasure
  refine IsGaussianProcess.indepFun_of_covariance_inner
    (hW.isGaussianProcess.of_isGaussianProcess fun
      | .inl t => ⟨{t₀, t₀ + t}, { toFun z := z ⟨t₀ + t, by simp⟩ - z ⟨t₀, by simp⟩
                                   map_add' _ _ := by simp; abel
                                   map_smul' _ _ := by simp; module }, by simp⟩
      | .inr ⟨u, _⟩ => ⟨{u}, { toFun z := z ⟨u, by simp⟩, map_add' _ _ := rfl
                               map_smul' _ _ := rfl }, by simp⟩)
    (fun t ↦ (hW.aemeasurable (t₀ + t)).sub (hW.aemeasurable t₀))
    (fun u ↦ hW.aemeasurable u.1) fun t ⟨u, hu⟩ x y ↦ ?_
  have hsub : (fun ω ↦ ⟪x, W (t₀ + t) ω - W t₀ ω⟫) =
      (fun ω ↦ ⟪x, W (t₀ + t) ω⟫) - fun ω ↦ ⟪x, W t₀ ω⟫ := by ext ω; simp [inner_sub_right]
  have hu1 : (u : ℝ) ≤ ((t₀ + t : ℝ≥0) : ℝ) := by
    push_cast; linarith [NNReal.coe_le_coe.mpr hu, t.coe_nonneg]
  rw [hsub, covariance_sub_left (hW.memLp_two_inner_eval x (t₀ + t))
    (hW.memLp_two_inner_eval x t₀) (hW.memLp_two_inner_eval y u),
    hW.covariance_inner, hW.covariance_inner, min_eq_right hu1,
    min_eq_right (NNReal.coe_le_coe.mpr hu), sub_self]

/-- Every vector pre-Brownian motion on a complete separable space has independent increments. -/
theorem hasIndepIncrements [CompleteSpace E] (hW : IsPreBrownian W P) :
    HasIndepIncrements W P := by
  have := hW.isProbabilityMeasure
  intro n t ht
  refine HasGaussianLaw.iIndepFun_of_covariance_inner hW.isGaussianProcess.hasGaussianLaw_increments
    fun i j hij x y ↦ ?_
  have hcov_lt ⦃a b : Fin n⦄ (hab : a < b) (u v : E) :
      cov[fun ω ↦ ⟪u, W (t a.succ) ω - W (t a.castSucc) ω⟫,
        fun ω ↦ ⟪v, W (t b.succ) ω - W (t b.castSucc) ω⟫; P] = 0 := by
    have h1 : (t a.castSucc : ℝ) ≤ t a.succ := NNReal.coe_le_coe.mpr (ht a.castSucc_le_succ)
    have h2 : (t a.succ : ℝ) ≤ t b.castSucc :=
      NNReal.coe_le_coe.mpr (ht (Fin.succ_le_castSucc_iff.mpr hab))
    have h3 : (t b.castSucc : ℝ) ≤ t b.succ := NNReal.coe_le_coe.mpr (ht b.castSucc_le_succ)
    rw [hW.covariance_inner_sub, min_eq_left (h1.trans (h2.trans h3)), min_eq_left (h1.trans h2),
      min_eq_left (h2.trans h3), min_eq_left h2]; ring
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact hcov_lt hlt x y
  · exact absurd rfl hij
  · exact (covariance_comm ..).trans (hcov_lt hgt y x)

end IsPreBrownian

/-- Linear isometric equivalences preserve and reflect `IsPreBrownian`. -/
theorem isPreBrownian_comp_linearIsometryEquiv_iff [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (f : E ≃ₗᵢ[ℝ] F) :
    IsPreBrownian (fun t ω ↦ f (W t ω)) P ↔ IsPreBrownian W P :=
  ⟨fun h ↦ by simpa using h.comp_linearIsometryEquiv f.symm, fun h ↦ h.comp_linearIsometryEquiv f⟩

namespace IsBrownian

/-- Normalized inner product `‖u‖⁻¹ * ⟪u, W t ω⟫` (`u ≠ 0`) is a scalar Brownian motion. -/
theorem isBrownianReal_norm_inv_mul_inner (hW : IsBrownian W P) {u : E} (hu : u ≠ 0) :
    IsBrownianReal (fun t ω ↦ ‖u‖⁻¹ * ⟪u, W t ω⟫) P :=
  ⟨hW.toIsPreBrownian.isPreBrownianReal_norm_inv_mul_inner hu,
    hW.ae_continuous.mono fun _ _ ↦ by fun_prop⟩

/-- Inner product `⟪u, W t ω⟫` against a unit vector (`‖u‖ = 1`) is a scalar Brownian motion. -/
theorem isBrownianReal_inner_of_norm_eq_one (hW : IsBrownian W P) {u : E} (hu : ‖u‖ = 1) :
    IsBrownianReal (fun t ω ↦ ⟪u, W t ω⟫) P :=
  ⟨hW.toIsPreBrownian.isPreBrownianReal_inner_of_norm_eq_one hu,
    hW.ae_continuous.mono fun _ _ ↦ by fun_prop⟩

/-- Linear isometric equivalences preserve `IsBrownian`. -/
theorem comp_linearIsometryEquiv [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (hW : IsBrownian W P) (f : E ≃ₗᵢ[ℝ] F) : IsBrownian (fun t ω ↦ f (W t ω)) P :=
  ⟨hW.toIsPreBrownian.comp_linearIsometryEquiv f, hW.ae_continuous.mono fun _ ↦ f.continuous.comp⟩

/-- Negating a vector Brownian motion preserves `IsBrownian`. -/
theorem neg (hW : IsBrownian W P) : IsBrownian (-W) P :=
  hW.comp_linearIsometryEquiv (.neg ℝ)

/-- Brownian diffusive scaling `(√c)⁻¹ • W (c * t)` (`c ≠ 0`) preserves `IsBrownian`. -/
theorem smul (hW : IsBrownian W P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownian (fun t ω ↦ (√(c : ℝ))⁻¹ • W (c * t) ω) P :=
  ⟨hW.toIsPreBrownian.smul hc, hW.ae_continuous.mono fun _ _ ↦ by fun_prop⟩

/-- Deterministic time shift `W (t₀ + t) - W t₀` preserves `IsBrownian`. -/
theorem shift (hW : IsBrownian W P) (t₀ : ℝ≥0) :
    IsBrownian (fun t ω ↦ W (t₀ + t) ω - W t₀ ω) P :=
  ⟨hW.toIsPreBrownian.shift t₀, hW.ae_continuous.mono fun _ _ ↦ by fun_prop⟩

end IsBrownian

/-- Linear isometric equivalences preserve and reflect `IsBrownian`. -/
theorem isBrownian_comp_linearIsometryEquiv_iff [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (f : E ≃ₗᵢ[ℝ] F) :
    IsBrownian (fun t ω ↦ f (W t ω)) P ↔ IsBrownian W P :=
  ⟨fun h ↦ by simpa using h.comp_linearIsometryEquiv f.symm, fun h ↦ h.comp_linearIsometryEquiv f⟩

end Transformations

section OrthonormalBasis

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Projecting `IsPreBrownian` onto a finite orthonormal basis `b` yields `IsPreBrownianVector`. -/
theorem IsPreBrownian.isPreBrownianVector_inner [Fintype ι] {W : ℝ≥0 → Ω → E}
    (hW : IsPreBrownian W P) (b : OrthonormalBasis ι ℝ E) :
    IsPreBrownianVector (fun i t ω ↦ ⟪b i, W t ω⟫) P := by
  classical
  have := b.repr.symm.finiteDimensional
  refine isPreBrownianVector_of_isGaussianProcess
    (hW.isGaussianProcess.of_isGaussianProcess fun ⟨i, t⟩ ↦ ⟨{t},
      { toFun z := ⟪b i, z ⟨t, by simp⟩⟫, map_add' _ _ := by simp [inner_add_right]
        map_smul' _ _ := by simp [inner_smul_right] }, fun _ ↦ rfl⟩)
    (fun i t ↦ hW.integral_inner t (b i)) fun i j s t ↦ ?_
  rw [hW.covariance_inner, orthonormal_iff_ite.mp b.orthonormal i j]; split_ifs <;> simp

/-- Projecting `IsBrownian` onto a finite orthonormal basis `b` yields `IsBrownianVector`. -/
theorem IsBrownian.isBrownianVector_inner [Fintype ι] {W : ℝ≥0 → Ω → E}
    (hW : IsBrownian W P) (b : OrthonormalBasis ι ℝ E) :
    IsBrownianVector (fun i t ω ↦ ⟪b i, W t ω⟫) P :=
  ⟨hW.toIsPreBrownian.isPreBrownianVector_inner b,
    fun i ↦ hW.ae_continuous.mono fun _ ↦ (innerSL ℝ (b i)).continuous.comp⟩

/-- Expanding `IsPreBrownianVector` along a finite orthonormal basis `b` yields `IsPreBrownian`. -/
theorem IsPreBrownianVector.isPreBrownian_sum_smul [Fintype ι] {B : ι → ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianVector B P) (b : OrthonormalBasis ι ℝ E) :
    IsPreBrownian (fun t ω ↦ ∑ i, B i t ω • b i) P := by
  classical
  have := b.repr.symm.finiteDimensional
  have := hB.isProbabilityMeasure
  refine isPreBrownian_of_integral_eval
    (hB.isGaussianProcess.sum_smul univ fun _ i ↦ b i)
    (fun t ↦ by
      rw [integral_finsetSum _ fun i _ ↦
        ((hB.memLp_two_eval i t).integrable one_le_two).smul_const _]
      simp [integral_smul_const, hB.integral_eval])
    fun s t u v ↦ ?_
  have hexp (w : E) (r : ℝ≥0) : (fun ω ↦ ⟪w, ∑ i, B i r ω • b i⟫) =
      ∑ i : ι, fun ω ↦ ⟪w, b i⟫ * B i r ω := by ext ω; simp [inner_sum, inner_smul_right, mul_comm]
  have hentry (i j : ι) : cov[fun ω ↦ ⟪u, b i⟫ * B i s ω, fun ω ↦ ⟪v, b j⟫ * B j t ω; P] =
      ⟪u, b i⟫ * ⟪v, b j⟫ * if i = j then (min s t : ℝ) else 0 := by
    rw [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_fun_eval]; ring
  rw [hexp u s, hexp v t, covariance_sum_sum (fun i ↦ (hB.memLp_two_eval i s).const_mul _)
    (fun j ↦ (hB.memLp_two_eval j t).const_mul _)]
  simp only [hentry, mul_ite, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte, ← sum_mul]
  simp_rw [real_inner_comm (b _) v]
  rw [b.sum_inner_mul_inner u v, mul_comm]

/-- Expanding `IsBrownianVector` along a finite orthonormal basis `b` yields `IsBrownian`. -/
theorem IsBrownianVector.isBrownian_sum_smul [Fintype ι] {B : ι → ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianVector B P) (b : OrthonormalBasis ι ℝ E) :
    IsBrownian (fun t ω ↦ ∑ i, B i t ω • b i) P :=
  ⟨hB.toIsPreBrownianVector.isPreBrownian_sum_smul b,
    (ae_all_iff.mpr hB.ae_continuous).mono fun _ _ ↦ by fun_prop⟩

/-- `IsPreBrownian W P` iff its coordinates in a finite orthonormal basis `b` satisfy
`IsPreBrownianVector`. -/
theorem isPreBrownian_iff_isPreBrownianVector [Fintype ι] {W : ℝ≥0 → Ω → E}
    (b : OrthonormalBasis ι ℝ E) :
    IsPreBrownian W P ↔ IsPreBrownianVector (fun i t ω ↦ ⟪b i, W t ω⟫) P :=
  ⟨fun hW ↦ hW.isPreBrownianVector_inner b,
    fun hB ↦ by simpa only [b.sum_repr'] using hB.isPreBrownian_sum_smul b⟩

/-- `IsBrownian W P` iff its coordinates in a finite orthonormal basis `b` satisfy
`IsBrownianVector`. -/
theorem isBrownian_iff_isBrownianVector [Fintype ι] {W : ℝ≥0 → Ω → E}
    (b : OrthonormalBasis ι ℝ E) :
    IsBrownian W P ↔ IsBrownianVector (fun i t ω ↦ ⟪b i, W t ω⟫) P :=
  ⟨fun hW ↦ hW.isBrownianVector_inner b,
    fun hB ↦ by simpa only [b.sum_repr'] using hB.isBrownian_sum_smul b⟩

/-- Product construction of `IsPreBrownian` along a finite orthonormal basis `b`. -/
theorem _root_.ProbabilityTheory.IsPreBrownianReal.isPreBrownian_sum_smul_pi
    [Fintype ι] {Ω₀ : ι → Type*} [∀ i, MeasurableSpace (Ω₀ i)]
    {P₀ : ∀ i, Measure (Ω₀ i)} {B₀ : ∀ i, ℝ≥0 → Ω₀ i → ℝ}
    (hB₀ : ∀ i, IsPreBrownianReal (B₀ i) (P₀ i)) (b : OrthonormalBasis ι ℝ E) :
    IsPreBrownian (fun t (ω : ∀ j, Ω₀ j) ↦ ∑ i, B₀ i t (ω i) • b i) (Measure.pi P₀) :=
  (IsPreBrownianReal.isPreBrownianVector_pi hB₀).isPreBrownian_sum_smul b

/-- Product construction of `IsBrownian` along a finite orthonormal basis `b`. -/
theorem _root_.ProbabilityTheory.IsBrownianReal.isBrownian_sum_smul_pi
    [Fintype ι] {Ω₀ : ι → Type*} [∀ i, MeasurableSpace (Ω₀ i)]
    {P₀ : ∀ i, Measure (Ω₀ i)} {B₀ : ∀ i, ℝ≥0 → Ω₀ i → ℝ}
    (hB₀ : ∀ i, IsBrownianReal (B₀ i) (P₀ i)) (b : OrthonormalBasis ι ℝ E) :
    IsBrownian (fun t (ω : ∀ j, Ω₀ j) ↦ ∑ i, B₀ i t (ω i) • b i) (Measure.pi P₀) :=
  (IsBrownianReal.isBrownianVector_pi hB₀).isBrownian_sum_smul b

end OrthonormalBasis

section FiniteDimensional

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : ℝ≥0 → Ω → E}

namespace IsPreBrownian

/-- A vector pre-Brownian motion vanishes almost surely at `t = 0`. -/
theorem eval_zero_ae_eq_zero (hW : IsPreBrownian W P) : W 0 =ᵐ[P] 0 := by
  let b := stdOrthonormalBasis ℝ E
  filter_upwards [ae_all_iff.mpr fun i ↦
    ((hW.isPreBrownianVector_inner b).isPreBrownianReal i).eval_zero_ae_eq_zero] with ω hω
  rw [Pi.zero_apply, ← b.sum_repr' (W 0 ω)]; simp [hω]

/-- For `s ≤ t`, `W t - W s` has law `(stdGaussian E).map (fun x ↦ √(t - s) • x)`. -/
theorem hasLaw_sub_of_le (hW : IsPreBrownian W P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (W t - W s) ((stdGaussian E).map (fun x : E ↦ √((t - s : ℝ≥0) : ℝ) • x)) P := by
  let b := stdOrthonormalBasis ℝ E
  have hsum : W t - W s = (fun (z : Fin (Module.finrank ℝ E) → ℝ) ↦ ∑ i, z i • b i) ∘
      fun ω i ↦ ⟪b i, W t ω⟫ - ⟪b i, W s ω⟫ := by
    ext ω; simp_rw [Pi.sub_apply, Function.comp_apply, ← inner_sub_right]
    exact (b.sum_repr' (W t ω - W s ω)).symm
  have hmeas : Measurable (fun (z : Fin (Module.finrank ℝ E) → ℝ) ↦ ∑ i, z i • b i) := by fun_prop
  have hscale : (fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 (t - s)) =
      fun _ ↦ (gaussianReal 0 1).map (fun r : ℝ ↦ √((t - s : ℝ≥0) : ℝ) * r) := by
    ext _; rw [gaussianReal_map_const_mul]; simp [Real.sq_sqrt (NNReal.coe_nonneg _)]
  rw [hsum]
  refine (HasLaw.mk hmeas.aemeasurable ?_).fun_comp
    ((hW.isPreBrownianVector_inner b).hasLaw_sub_pi hst)
  rw [hscale, ← Measure.pi_map_pi fun _ ↦ by fun_prop, Measure.map_map hmeas (by fun_prop),
    stdGaussian_eq_map_pi_orthonormalBasis b, Measure.map_map (by fun_prop) hmeas]
  congr 1; ext z; simp [smul_sum, smul_smul]

/-- At any time `t : ℝ≥0`, `W t` has law `(stdGaussian E).map (fun x ↦ √t • x)`. -/
theorem hasLaw_eval (hW : IsPreBrownian W P) (t : ℝ≥0) :
    HasLaw (W t) ((stdGaussian E).map (fun x : E ↦ √(t : ℝ) • x)) P :=
  (tsub_zero t ▸ hW.hasLaw_sub_of_le (zero_le (a := t))).congr
    (hW.eval_zero_ae_eq_zero.mono fun _ hω ↦ by simp [hω])

/-- At `t = 1`, a vector pre-Brownian motion has law `stdGaussian E`. -/
theorem hasLaw_eval_one (hW : IsPreBrownian W P) : HasLaw (W 1) (stdGaussian E) P := by
  simpa using hW.hasLaw_eval 1

/-! ### Noncentered variant started at an arbitrary or independent initial vector -/

/-- Adding `ξ : Ω → E` to `W` yields initial value `ξ` almost surely at `t = 0`. -/
theorem add_left_eval_zero_ae_eq (hW : IsPreBrownian W P) (ξ : Ω → E) :
    (fun ω ↦ ξ ω + W 0 ω) =ᵐ[P] ξ :=
  hW.eval_zero_ae_eq_zero.mono fun _ hω ↦ by simp [hω]

/-- For any `ξ : Ω → E` and `s ≤ t`, `(ξ + W t) - (ξ + W s)` has law
`(stdGaussian E).map (fun x ↦ √(t - s) • x)`. -/
theorem hasLaw_add_left_sub_of_le (hW : IsPreBrownian W P) (ξ : Ω → E)
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ (ξ ω + W t ω) - (ξ ω + W s ω))
      ((stdGaussian E).map (fun x : E ↦ √((t - s : ℝ≥0) : ℝ) • x)) P := by
  simpa only [add_sub_add_left_eq_sub, Pi.sub_def] using hW.hasLaw_sub_of_le hst

/-- For any `ξ : Ω → E`, `ξ + W` retains independent increments. -/
theorem hasIndepIncrements_add_left (hW : IsPreBrownian W P) (ξ : Ω → E) :
    HasIndepIncrements (fun t ω ↦ ξ ω + W t ω) P := fun n t ht ↦ by
  simpa only [add_sub_add_left_eq_sub] using hW.hasIndepIncrements n t ht

/-- If `ξ` is independent of `W`, then `X 0 = ξ + W 0` is independent of `t ↦ X t - X 0`. -/
theorem indepFun_add_left_increments (hW : IsPreBrownian W P) {ξ : Ω → E}
    (hξ : IndepFun ξ (fun ω t ↦ W t ω) P) :
    IndepFun (fun ω ↦ ξ ω + W 0 ω) (fun ω t ↦ (ξ ω + W t ω) - (ξ ω + W 0 ω)) P :=
  hξ.congr (hW.add_left_eval_zero_ae_eq ξ).symm
    (hW.eval_zero_ae_eq_zero.mono fun _ hω ↦ by ext t; simp [hω])

end IsPreBrownian

private theorem covariance_inner_of_hasLaw_smul_stdGaussian {Y : Ω → E} {s : ℝ≥0}
    (hY : HasLaw Y ((stdGaussian E).map (fun x : E ↦ √(s : ℝ) • x)) P) (u v : E) :
    cov[fun ω ↦ ⟪u, Y ω⟫, fun ω ↦ ⟪v, Y ω⟫; P] = (s : ℝ) * ⟪u, v⟫ := by
  have := hY.isProbabilityMeasure
  have h1 := (covariance_map (innerSL ℝ u).continuous.aestronglyMeasurable
    (innerSL ℝ v).continuous.aestronglyMeasurable hY.aemeasurable).symm
  have h2 := covariance_map (μ := stdGaussian E) (innerSL ℝ u).continuous.aestronglyMeasurable
    (innerSL ℝ v).continuous.aestronglyMeasurable (measurable_id.const_smul (√(s : ℝ))).aemeasurable
  have hcov : cov[fun ω ↦ ⟪u, Y ω⟫, fun ω ↦ ⟪v, Y ω⟫; P] =
      cov[fun x : E ↦ ⟪u, √(s : ℝ) • x⟫, fun x : E ↦ ⟪v, √(s : ℝ) • x⟫; stdGaussian E] := by
    simpa [Function.comp_def, hY.map_eq] using h1.trans (hY.map_eq ▸ h2)
  rw [hcov]
  simp_rw [real_inner_smul_right]
  rw [covariance_const_mul_left, covariance_const_mul_right,
    ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
    innerSL_apply_apply, ← mul_assoc, ← sq, Real.sq_sqrt s.coe_nonneg]

/-- An `E`-valued process with independent increments and marginals `(stdGaussian E).map (√t • ·)`
is a vector pre-Brownian motion. -/
theorem _root_.ProbabilityTheory.HasIndepIncrements.isPreBrownian_of_hasLaw {X : ℝ≥0 → Ω → E}
    (hlaw : ∀ t, HasLaw (X t) ((stdGaussian E).map (fun x : E ↦ √(t : ℝ) • x)) P)
    (hincr : HasIndepIncrements X P) : IsPreBrownian X P := by
  have := (hlaw 0).isProbabilityMeasure
  have hgauss (t : ℝ≥0) : HasGaussianLaw (X t) P :=
    ⟨(hlaw t).aemeasurable, (hlaw t).map_eq ▸
      ((IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map
        (√(t : ℝ) • ContinuousLinearMap.id ℝ E)).isGaussian_map⟩
  have h0 : ∀ᵐ ω ∂P, X 0 ω = 0 := HasLaw.ae_eq_of_dirac (by simpa using hlaw 0)
  have hG : IsGaussianProcess X P := hincr.isGaussianProcess hgauss h0
  refine isPreBrownian_of_integral_eval hG
    (fun t ↦ by
      rw [(hlaw t).integral_eq, integral_map (φ := fun x : E ↦ √(t : ℝ) • x) (by fun_prop)
        (f := fun x : E ↦ x) measurable_id.aestronglyMeasurable, integral_smul,
        integral_id_stdGaussian, smul_zero])
    fun s t u v ↦ ?_
  have hle ⦃a b : ℝ≥0⦄ (hab : a ≤ b) (x y : E) :
      cov[fun ω ↦ ⟪x, X a ω⟫, fun ω ↦ ⟪y, X b ω⟫; P] = (a : ℝ) * ⟪x, y⟫ := by
    have hind : IndepFun (fun ω ↦ ⟪x, X a ω⟫) (fun ω ↦ ⟪y, X b ω - X a ω⟫) P :=
      (hincr.indepFun_eval_sub zero_le hab h0).comp (by fun_prop) (by fun_prop)
    have hax : MemLp (fun ω ↦ ⟪x, X a ω⟫) 2 P := ((hgauss a).map (innerSL ℝ x)).memLp_two
    have hay : MemLp (fun ω ↦ ⟪y, X a ω⟫) 2 P := ((hgauss a).map (innerSL ℝ y)).memLp_two
    have hdiff : MemLp (fun ω ↦ ⟪y, X b ω - X a ω⟫) 2 P :=
      ((hG.hasGaussianLaw_fun_sub (s := b) (t := a)).map (innerSL ℝ y)).memLp_two
    have hsplit : (fun ω ↦ ⟪y, X b ω⟫) = (fun ω ↦ ⟪y, X b ω - X a ω⟫) + fun ω ↦ ⟪y, X a ω⟫ := by
      ext ω; simp [inner_sub_right]
    rw [hsplit, covariance_add_right hax hdiff hay, hind.covariance_eq_zero hax hdiff, zero_add,
      covariance_inner_of_hasLaw_smul_stdGaussian (hlaw a) x y]
  rcases le_total s t with hst | hts
  · rw [min_eq_left (NNReal.coe_le_coe.mpr hst), hle hst u v]
  · rw [min_eq_right (NNReal.coe_le_coe.mpr hts), covariance_comm, hle hts v u, real_inner_comm]

/-- Unconditional witness of `IsPreBrownian` on any finite-dimensional real inner-product space. -/
theorem isPreBrownian_sum_smul_pi_gaussianLimit :
    IsPreBrownian
      (fun t (ω : Fin (Module.finrank ℝ E) → ℝ≥0 → ℝ) ↦ ∑ i, ω i t • stdOrthonormalBasis ℝ E i)
      (Measure.pi fun _ : Fin (Module.finrank ℝ E) ↦ gaussianLimit) :=
  isPreBrownianVector_eval_pi_gaussianLimit.isPreBrownian_sum_smul (stdOrthonormalBasis ℝ E)

end FiniteDimensional

end TauCeti.Probability

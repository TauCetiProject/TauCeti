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

This file defines basis-free centered pre-Brownian and Brownian motion taking values in a real
inner-product space `E`, proves their equivalence with coordinate vector Brownian motion
`TauCeti.Probability.IsPreBrownianVector` / `TauCeti.Probability.IsBrownianVector` in every finite
orthonormal basis, establishes covariance and Gaussian laws of directional projections and vector
increments, proves invariance under linear isometric equivalences, and derives the noncentered
variant `ξ + W` started at a deterministic or independent random initial vector.

## Main definitions

* `TauCeti.Probability.IsPreBrownian`: a centered `E`-valued Gaussian process `W : ℝ≥0 → Ω → E`
  with inner-product covariance `cov[⟪u, W s⟫, ⟪v, W t⟫; P] = min s t * ⟪u, v⟫`.
* `TauCeti.Probability.IsBrownian`: `IsPreBrownian` together with almost-sure path continuity.

## Main results

* `TauCeti.Probability.isPreBrownian_iff_isPreBrownianVector` and
  `TauCeti.Probability.isBrownian_iff_isBrownianVector`: equivalence with mutually independent
  scalar `(Pre)Brownian` coordinates in any finite orthonormal basis `b : OrthonormalBasis ι ℝ E`.
* `TauCeti.Probability.IsPreBrownian.hasLaw_inner_eval` and
  `TauCeti.Probability.IsPreBrownian.isPreBrownianReal_norm_inv_mul_inner`: Gaussian law and unit
  normalization of arbitrary directional projections `⟪u, W t⟫`.
* `TauCeti.Probability.IsPreBrownian.comp_linearIsometryEquiv` and
  `TauCeti.Probability.isPreBrownian_comp_linearIsometryEquiv_iff`: invariance under linear
  isometric equivalences `E ≃ₗᵢ[ℝ] F`.
* `TauCeti.Probability.IsPreBrownian.hasLaw_sub_of_le`,
  `TauCeti.Probability.IsPreBrownian.hasIndepIncrements`, and
  `TauCeti.Probability.HasIndepIncrements.isPreBrownian_of_hasLaw`: standard Gaussian increment laws
  `(stdGaussian E).map (√(t - s) • ·)` and independent-increment characterization.
* `TauCeti.Probability.IsPreBrownian.add_left_eval_zero_ae_eq`,
  `TauCeti.Probability.IsPreBrownian.hasLaw_add_left_sub_of_le`, and
  `TauCeti.Probability.IsPreBrownian.indepFun_add_left_increments`: noncentered Brownian motion
  `ξ + W` started at an arbitrary or independent initial random vector `ξ`.

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
    refine integral_congr_ae ?_
    filter_upwards [h t] with ω hω using by rw [hω]
  covariance_inner s t u v := by
    rw [← hW.covariance_inner s t u v, covariance, covariance]
    have hmean_s : P[fun ω ↦ ⟪u, W' s ω⟫] = P[fun ω ↦ ⟪u, W s ω⟫] := by
      refine integral_congr_ae ?_
      filter_upwards [h s] with ω hω using by rw [hω]
    have hmean_t : P[fun ω ↦ ⟪v, W' t ω⟫] = P[fun ω ↦ ⟪v, W t ω⟫] := by
      refine integral_congr_ae ?_
      filter_upwards [h t] with ω hω using by rw [hω]
    refine integral_congr_ae ?_
    filter_upwards [h s, h t] with ω hs ht
    simp [hs, ht, hmean_s, hmean_t]

/-- Indistinguishable modifications preserve `IsPreBrownian`. -/
theorem congr_indistinguishable (hW : IsPreBrownian W P) (h : W ≡ᵐ[P] W') :
    IsPreBrownian W' P :=
  hW.congr fun t ↦ by filter_upwards [h] with ω hω using hω t

end IsPreBrownian

namespace IsBrownian

variable {W W' : ℝ≥0 → Ω → E}

/-- Indistinguishable modifications preserve `IsBrownian`. -/
theorem congr_indistinguishable (hW : IsBrownian W P) (h : W ≡ᵐ[P] W') :
    IsBrownian W' P where
  toIsPreBrownian := hW.toIsPreBrownian.congr_indistinguishable h
  ae_continuous := by
    filter_upwards [hW.ae_continuous, h] with ω hcont hω
    simpa [funext hω] using hcont

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

/-- On a complete separable inner-product space (in particular any finite-dimensional one), every
value `W t` has Bochner integral `0`. -/
@[simp]
theorem integral_eval [SecondCountableTopology E] [CompleteSpace E]
    (hW : IsPreBrownian W P) (t : ℝ≥0) :
    ∫ ω, W t ω ∂P = 0 := by
  refine ext_inner_left ℝ fun u ↦ ?_
  have hcomm := (innerSL ℝ u).integral_comp_comm (hW.integrable_eval t)
  simpa [innerSL_apply_apply] using hcomm.symm.trans (hW.integral_inner t u)

/-- On a zero-dimensional inner-product space (`Subsingleton E`), every process on a probability
space is a vector pre-Brownian motion. -/
theorem of_subsingleton [Subsingleton E] [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → E) :
    IsPreBrownian W P where
  isGaussianProcess := ⟨fun _ ↦ .of_subsingleton⟩
  integral_inner _ _ := by simp [Subsingleton.elim _ (0 : E)]
  covariance_inner _ _ u _ := by simp [Subsingleton.elim u 0]

/-- Variance of a directional projection `⟪u, W t⟫` equals `‖u‖ ^ 2 * t`. -/
theorem variance_inner_eval (hW : IsPreBrownian W P) (u : E) (t : ℝ≥0) :
    Var[fun ω ↦ ⟪u, W t ω⟫; P] = ‖u‖ ^ 2 * (t : ℝ) := by
  have := hW.isProbabilityMeasure
  rw [← covariance_self (hW.hasGaussianLaw_inner_eval u t).aemeasurable,
    hW.covariance_inner, min_self, real_inner_self_eq_norm_sq, mul_comm]

/-- For every vector `u : E` (including `u = 0`), the projection `⟪u, W t⟫` has Gaussian law
`gaussianReal 0 (‖u‖₊ ^ 2 * t)`. -/
theorem hasLaw_inner_eval (hW : IsPreBrownian W P) (u : E) (t : ℝ≥0) :
    HasLaw (fun ω ↦ ⟪u, W t ω⟫) (gaussianReal 0 (‖u‖₊ ^ 2 * t)) P where
  aemeasurable := (hW.hasGaussianLaw_inner_eval u t).aemeasurable
  map_eq := by
    rw [(hW.hasGaussianLaw_inner_eval u t).map_eq_gaussianReal, hW.integral_inner,
      hW.variance_inner_eval]
    congr 1
    apply NNReal.coe_injective
    simp [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg _) t.coe_nonneg)]

end IsPreBrownian

/-- Constructor for `IsPreBrownian` on a complete separable inner-product space from Bochner mean
zero `∀ t, ∫ ω, W t ω ∂P = 0`. -/
theorem isPreBrownian_of_integral_eval [SecondCountableTopology E] [CompleteSpace E]
    (hG : IsGaussianProcess W P) (hmean : ∀ t, ∫ ω, W t ω ∂P = 0)
    (hcov : ∀ s t (u v : E),
      cov[fun ω ↦ ⟪u, W s ω⟫, fun ω ↦ ⟪v, W t ω⟫; P] = min (s : ℝ) t * ⟪u, v⟫) :
    IsPreBrownian W P where
  isGaussianProcess := hG
  integral_inner t u := by
    simpa [hmean t] using (innerSL ℝ u).integral_comp_comm (hG.hasGaussianLaw_eval t).integrable
  covariance_inner := hcov

/-- Characterization of `IsPreBrownian` on a complete separable inner-product space via Bochner
mean zero. -/
theorem isPreBrownian_iff_of_completeSpace [SecondCountableTopology E] [CompleteSpace E] :
    IsPreBrownian W P ↔
      IsGaussianProcess W P ∧ (∀ t, ∫ ω, W t ω ∂P = 0) ∧
        ∀ s t (u v : E),
          cov[fun ω ↦ ⟪u, W s ω⟫, fun ω ↦ ⟪v, W t ω⟫; P] = min (s : ℝ) t * ⟪u, v⟫ :=
  ⟨fun h ↦ ⟨h.isGaussianProcess, h.integral_eval, h.covariance_inner⟩,
    fun ⟨hG, hm, hc⟩ ↦ isPreBrownian_of_integral_eval hG hm hc⟩

/-- On a zero-dimensional inner-product space (`Subsingleton E`), every process on a probability
space is a vector Brownian motion. -/
theorem IsBrownian.of_subsingleton [Subsingleton E] [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → E) : IsBrownian W P where
  toIsPreBrownian := .of_subsingleton W
  ae_continuous := ae_of_all _ fun ω ↦
    Subsingleton.elim (W · ω) (fun _ ↦ 0) ▸ continuous_const

/-- On `E = ℝ`, `IsPreBrownian` agrees with Mathlib's `ProbabilityTheory.IsPreBrownianReal`. -/
@[simp]
theorem isPreBrownian_real_iff {W : ℝ≥0 → Ω → ℝ} :
    IsPreBrownian W P ↔ IsPreBrownianReal W P where
  mp hW := hW.isGaussianProcess.isPreBrownianReal_of_covariance hW.integral_eval fun s t hst ↦ by
    have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
    simpa [min_eq_left hst'] using hW.covariance_inner s t 1 1
  mpr hW := isPreBrownian_of_integral_eval hW.isGaussianProcess hW.integral_eval fun s t u v ↦ by
    have := hW.isGaussianProcess.isProbabilityMeasure
    simp only [RCLike.inner_apply, conj_trivial]
    simp_rw [mul_comm (W _ _) _]
    rw [covariance_const_mul_left, covariance_const_mul_right, hW.covariance_eval]
    push_cast
    ring

/-- On `E = ℝ`, `IsBrownian` agrees with Mathlib's `ProbabilityTheory.IsBrownianReal`. -/
@[simp]
theorem isBrownian_real_iff {W : ℝ≥0 → Ω → ℝ} :
    IsBrownian W P ↔ IsBrownianReal W P where
  mp hW := ⟨isPreBrownian_real_iff.mp hW.toIsPreBrownian, hW.ae_continuous⟩
  mpr hW := ⟨isPreBrownian_real_iff.mpr hW.toIsPreBrownianReal, hW.cont⟩

end Basic

section Transformations

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {W : ℝ≥0 → Ω → E}

namespace IsPreBrownian

/-- For any nonzero direction `u : E`, normalizing `⟪u, W t⟫` by `‖u‖⁻¹` yields a scalar
pre-Brownian motion. -/
theorem isPreBrownianReal_norm_inv_mul_inner (hW : IsPreBrownian W P) {u : E} (hu : u ≠ 0) :
    IsPreBrownianReal (fun t ω ↦ ‖u‖⁻¹ * ⟪u, W t ω⟫) P := by
  have := hW.isProbabilityMeasure
  have hG : IsGaussianProcess (fun t ω ↦ ‖u‖⁻¹ * ⟪u, W t ω⟫) P :=
    hW.isGaussianProcess.comp_left fun _ ↦ ‖u‖⁻¹ • innerSL ℝ u
  refine hG.isPreBrownianReal_of_covariance (fun t ↦ ?_) fun s t hst ↦ ?_
  · rw [integral_const_mul, hW.integral_inner, mul_zero]
  · have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
    have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    rw [covariance_const_mul_left, covariance_const_mul_right, hW.covariance_inner,
      min_eq_left hst', real_inner_self_eq_norm_sq]
    field_simp

/-- Projecting onto a unit vector `u` (`‖u‖ = 1`) produces a scalar pre-Brownian motion. -/
theorem isPreBrownianReal_inner_of_norm_eq_one (hW : IsPreBrownian W P) {u : E} (hu : ‖u‖ = 1) :
    IsPreBrownianReal (fun t ω ↦ ⟪u, W t ω⟫) P := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  simpa [hu] using hW.isPreBrownianReal_norm_inv_mul_inner hu0

/-- For `s ≤ t` and any `u : E`, the directional increment `⟪u, W t - W s⟫` has Gaussian law
`gaussianReal 0 (‖u‖₊ ^ 2 * (t - s))`. -/
theorem hasLaw_inner_sub_of_le (hW : IsPreBrownian W P) (u : E) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ ⟪u, W t ω - W s ω⟫) (gaussianReal 0 (‖u‖₊ ^ 2 * (t - s))) P := by
  have := hW.isProbabilityMeasure
  have hG : HasGaussianLaw (fun ω ↦ ⟪u, W t ω - W s ω⟫) P :=
    hW.isGaussianProcess.hasGaussianLaw_sub.map (innerSL ℝ u)
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal]
  have hsub : (fun ω ↦ ⟪u, W t ω - W s ω⟫) = (fun ω ↦ ⟪u, W t ω⟫) - fun ω ↦ ⟪u, W s ω⟫ := by
    ext ω; simp [inner_sub_right]
  have hmean : P[fun ω ↦ ⟪u, W t ω - W s ω⟫] = 0 := by
    simp_rw [inner_sub_right]
    rw [integral_sub (hW.hasGaussianLaw_inner_eval u t).integrable
      (hW.hasGaussianLaw_inner_eval u s).integrable, hW.integral_inner, hW.integral_inner, sub_zero]
  have hvar : Var[fun ω ↦ ⟪u, W t ω - W s ω⟫; P] = ‖u‖ ^ 2 * ((t - s : ℝ≥0) : ℝ) := by
    have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
    rw [← covariance_self hG.aemeasurable, hsub,
      covariance_sub_left (hW.memLp_two_inner_eval u t) (hW.memLp_two_inner_eval u s)
        ((hW.memLp_two_inner_eval u t).sub (hW.memLp_two_inner_eval u s)),
      covariance_sub_right (hW.memLp_two_inner_eval u t) (hW.memLp_two_inner_eval u t)
        (hW.memLp_two_inner_eval u s),
      covariance_sub_right (hW.memLp_two_inner_eval u s) (hW.memLp_two_inner_eval u t)
        (hW.memLp_two_inner_eval u s),
      hW.covariance_inner, hW.covariance_inner, hW.covariance_inner, hW.covariance_inner,
      min_self, min_self, min_eq_right hst', min_eq_left hst', real_inner_self_eq_norm_sq,
      NNReal.coe_sub hst]
    ring
  rw [hmean, hvar]
  congr 1
  apply NNReal.coe_injective
  simp [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg _) (t - s).coe_nonneg)]

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
    simp_rw [hflip]
    exact hW.integral_inner t (f.symm u)
  covariance_inner s t u v := by
    have hflip (y : F) (x : E) : ⟪y, f x⟫ = ⟪f.symm y, x⟫ := by
      rw [real_inner_comm, f.inner_map_eq_flip, real_inner_comm]
    simp_rw [hflip]
    rw [hW.covariance_inner, f.symm.inner_map_map]

/-- Negation preserves `IsPreBrownian`. -/
theorem neg (hW : IsPreBrownian W P) : IsPreBrownian (-W) P where
  isGaussianProcess := hW.isGaussianProcess.comp_left fun _ ↦ -ContinuousLinearMap.id ℝ E
  integral_inner t u := by
    simp_rw [Pi.neg_apply, inner_neg_right, integral_neg, hW.integral_inner, neg_zero]
  covariance_inner s t u v := by
    have := hW.isProbabilityMeasure
    simp_rw [Pi.neg_apply, inner_neg_right]
    rw [covariance_fun_neg_left, covariance_fun_neg_right, neg_neg, hW.covariance_inner]

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
    have := hW.isProbabilityMeasure
    have hsub (w : E) (r : ℝ≥0) :
        (fun ω ↦ ⟪w, W (t₀ + r) ω - W t₀ ω⟫) =
          (fun ω ↦ ⟪w, W (t₀ + r) ω⟫) - fun ω ↦ ⟪w, W t₀ ω⟫ := by
      ext ω; simp [inner_sub_right]
    rw [hsub u s, hsub v t,
      covariance_sub_left (hW.memLp_two_inner_eval u (t₀ + s))
        (hW.memLp_two_inner_eval u t₀)
        ((hW.memLp_two_inner_eval v (t₀ + t)).sub (hW.memLp_two_inner_eval v t₀)),
      covariance_sub_right (hW.memLp_two_inner_eval u (t₀ + s))
        (hW.memLp_two_inner_eval v (t₀ + t)) (hW.memLp_two_inner_eval v t₀),
      covariance_sub_right (hW.memLp_two_inner_eval u t₀)
        (hW.memLp_two_inner_eval v (t₀ + t)) (hW.memLp_two_inner_eval v t₀),
      hW.covariance_inner, hW.covariance_inner, hW.covariance_inner, hW.covariance_inner]
    push_cast
    have hs : (t₀ : ℝ) ≤ (t₀ : ℝ) + s := le_add_of_nonneg_right s.coe_nonneg
    have ht : (t₀ : ℝ) ≤ (t₀ : ℝ) + t := le_add_of_nonneg_right t.coe_nonneg
    rw [← add_min, min_eq_right hs, min_eq_left ht, min_self]
    ring

/-- Weak Markov independence for vector pre-Brownian motion: for every `t₀ : ℝ≥0`, the shifted
process `t ↦ W (t₀ + t) - W t₀` is independent of the past path `(W u)_{u ≤ t₀}`. -/
theorem indepFun_shift [CompleteSpace E] (hW : IsPreBrownian W P) (t₀ : ℝ≥0) :
    IndepFun (fun ω t ↦ W (t₀ + t) ω - W t₀ ω) (fun ω (u : Set.Iic t₀) ↦ W u ω) P := by
  have := hW.isProbabilityMeasure
  refine IsGaussianProcess.indepFun_of_covariance_inner ?_
    (fun t ↦ (hW.aemeasurable (t₀ + t)).sub (hW.aemeasurable t₀))
    (fun u ↦ hW.aemeasurable u.1) fun t ⟨u, hu⟩ x y ↦ ?_
  · refine hW.isGaussianProcess.of_isGaussianProcess ?_
    rintro (t | ⟨u, _⟩)
    · exact ⟨{t₀, t₀ + t},
        { toFun z := z ⟨t₀ + t, by simp⟩ - z ⟨t₀, by simp⟩
          map_add' _ _ := by simp; abel
          map_smul' _ _ := by simp; module }, by simp⟩
    · exact ⟨{u},
        { toFun z := z ⟨u, by simp⟩
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }, by simp⟩
  · have hsub : (fun ω ↦ ⟪x, W (t₀ + t) ω - W t₀ ω⟫) =
        (fun ω ↦ ⟪x, W (t₀ + t) ω⟫) - fun ω ↦ ⟪x, W t₀ ω⟫ := by
      ext ω; simp [inner_sub_right]
    rw [hsub, covariance_sub_left (hW.memLp_two_inner_eval x (t₀ + t))
      (hW.memLp_two_inner_eval x t₀) (hW.memLp_two_inner_eval y u),
      hW.covariance_inner, hW.covariance_inner]
    have hu1 : (u : ℝ) ≤ ((t₀ + t : ℝ≥0) : ℝ) := by
      push_cast; linarith [NNReal.coe_le_coe.mpr hu, t.coe_nonneg]
    rw [min_eq_right hu1, min_eq_right (NNReal.coe_le_coe.mpr hu), sub_self]

/-- Every vector pre-Brownian motion on a complete separable inner-product space has independent
increments. -/
theorem hasIndepIncrements [CompleteSpace E] (hW : IsPreBrownian W P) :
    HasIndepIncrements W P := by
  have := hW.isProbabilityMeasure
  intro n t ht
  refine HasGaussianLaw.iIndepFun_of_covariance_inner hW.isGaussianProcess.hasGaussianLaw_increments
    fun i j hij x y ↦ ?_
  have hcov_lt : ∀ ⦃a b : Fin n⦄, a < b → ∀ (u v : E),
      cov[fun ω ↦ ⟪u, W (t a.succ) ω - W (t a.castSucc) ω⟫,
        fun ω ↦ ⟪v, W (t b.succ) ω - W (t b.castSucc) ω⟫; P] = 0 := by
    intro a b hab u v
    have h1 : (t a.castSucc : ℝ) ≤ t a.succ :=
      NNReal.coe_le_coe.mpr (ht a.castSucc_le_succ)
    have h2 : (t a.succ : ℝ) ≤ t b.castSucc :=
      NNReal.coe_le_coe.mpr (ht (Fin.succ_le_castSucc_iff.mpr hab))
    have h3 : (t b.castSucc : ℝ) ≤ t b.succ :=
      NNReal.coe_le_coe.mpr (ht b.castSucc_le_succ)
    have hsub (w : E) (k : Fin n) :
        (fun ω ↦ ⟪w, W (t k.succ) ω - W (t k.castSucc) ω⟫) =
          (fun ω ↦ ⟪w, W (t k.succ) ω⟫) - fun ω ↦ ⟪w, W (t k.castSucc) ω⟫ := by
      ext ω; simp [inner_sub_right]
    rw [hsub u a, hsub v b,
      covariance_sub_left (hW.memLp_two_inner_eval u _) (hW.memLp_two_inner_eval u _)
        ((hW.memLp_two_inner_eval v _).sub (hW.memLp_two_inner_eval v _)),
      covariance_sub_right (hW.memLp_two_inner_eval u _)
        (hW.memLp_two_inner_eval v _) (hW.memLp_two_inner_eval v _),
      covariance_sub_right (hW.memLp_two_inner_eval u _)
        (hW.memLp_two_inner_eval v _) (hW.memLp_two_inner_eval v _),
      hW.covariance_inner, hW.covariance_inner, hW.covariance_inner, hW.covariance_inner,
      min_eq_left (h1.trans (h2.trans h3)), min_eq_left (h1.trans h2),
      min_eq_left (h2.trans h3), min_eq_left h2]
    ring
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact hcov_lt hlt x y
  · exact absurd rfl hij
  · rw [covariance_comm]
    exact hcov_lt hgt y x

end IsPreBrownian

/-- Linear isometric equivalences preserve and reflect `IsPreBrownian`. -/
theorem isPreBrownian_comp_linearIsometryEquiv_iff [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (f : E ≃ₗᵢ[ℝ] F) :
    IsPreBrownian (fun t ω ↦ f (W t ω)) P ↔ IsPreBrownian W P where
  mp h := by simpa using h.comp_linearIsometryEquiv f.symm
  mpr h := h.comp_linearIsometryEquiv f

namespace IsBrownian

/-- Normalized inner product `‖u‖⁻¹ * ⟪u, W t ω⟫` against any nonzero `u : E` is a scalar
Brownian motion. -/
theorem isBrownianReal_norm_inv_mul_inner (hW : IsBrownian W P) {u : E} (hu : u ≠ 0) :
    IsBrownianReal (fun t ω ↦ ‖u‖⁻¹ * ⟪u, W t ω⟫) P where
  toIsPreBrownianReal := hW.toIsPreBrownian.isPreBrownianReal_norm_inv_mul_inner hu
  cont := by
    filter_upwards [hW.ae_continuous] with ω hω
    fun_prop

/-- Inner product `⟪u, W t ω⟫` against a unit vector `u : E` (`‖u‖ = 1`) is a scalar Brownian
motion. -/
theorem isBrownianReal_inner_of_norm_eq_one (hW : IsBrownian W P) {u : E} (hu : ‖u‖ = 1) :
    IsBrownianReal (fun t ω ↦ ⟪u, W t ω⟫) P where
  toIsPreBrownianReal := hW.toIsPreBrownian.isPreBrownianReal_inner_of_norm_eq_one hu
  cont := by
    filter_upwards [hW.ae_continuous] with ω hω
    fun_prop

/-- Linear isometric equivalences preserve `IsBrownian`. -/
theorem comp_linearIsometryEquiv [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (hW : IsBrownian W P) (f : E ≃ₗᵢ[ℝ] F) :
    IsBrownian (fun t ω ↦ f (W t ω)) P where
  toIsPreBrownian := hW.toIsPreBrownian.comp_linearIsometryEquiv f
  ae_continuous := by
    filter_upwards [hW.ae_continuous] with ω hω
    exact f.continuous.comp hω

/-- Negating a vector Brownian motion preserves `IsBrownian`. -/
theorem neg (hW : IsBrownian W P) : IsBrownian (-W) P where
  toIsPreBrownian := hW.toIsPreBrownian.neg
  ae_continuous := by
    filter_upwards [hW.ae_continuous] with ω hω
    simpa [← Pi.neg_def] using hω.neg

/-- Brownian diffusive scaling `(√c)⁻¹ • W (c * t)` (`c ≠ 0`) preserves `IsBrownian`. -/
theorem smul (hW : IsBrownian W P) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownian (fun t ω ↦ (√(c : ℝ))⁻¹ • W (c * t) ω) P where
  toIsPreBrownian := hW.toIsPreBrownian.smul hc
  ae_continuous := by
    filter_upwards [hW.ae_continuous] with ω hω
    fun_prop

/-- Deterministic time shift `W (t₀ + t) - W t₀` preserves `IsBrownian`. -/
theorem shift (hW : IsBrownian W P) (t₀ : ℝ≥0) :
    IsBrownian (fun t ω ↦ W (t₀ + t) ω - W t₀ ω) P where
  toIsPreBrownian := hW.toIsPreBrownian.shift t₀
  ae_continuous := by
    filter_upwards [hW.ae_continuous] with ω hω
    fun_prop

end IsBrownian

/-- Linear isometric equivalences preserve and reflect `IsBrownian`. -/
theorem isBrownian_comp_linearIsometryEquiv_iff [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (f : E ≃ₗᵢ[ℝ] F) :
    IsBrownian (fun t ω ↦ f (W t ω)) P ↔ IsBrownian W P where
  mp h := by simpa using h.comp_linearIsometryEquiv f.symm
  mpr h := h.comp_linearIsometryEquiv f

end Transformations

section OrthonormalBasis

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Projecting a vector pre-Brownian motion onto any finite orthonormal basis `b` yields a
coordinate vector pre-Brownian motion `IsPreBrownianVector`. -/
theorem IsPreBrownian.isPreBrownianVector_inner [Fintype ι] {W : ℝ≥0 → Ω → E}
    (hW : IsPreBrownian W P) (b : OrthonormalBasis ι ℝ E) :
    IsPreBrownianVector (fun i t ω ↦ ⟪b i, W t ω⟫) P := by
  classical
  have := b.repr.symm.finiteDimensional
  refine isPreBrownianVector_of_isGaussianProcess ?_
    (fun i t ↦ hW.integral_inner t (b i)) fun i j s t ↦ ?_
  · refine hW.isGaussianProcess.of_isGaussianProcess fun ⟨i, t⟩ ↦
      ⟨{t}, { toFun z := ⟪b i, z ⟨t, by simp⟩⟫
              map_add' _ _ := by simp [inner_add_right]
              map_smul' _ _ := by simp [inner_smul_right] }, fun _ ↦ rfl⟩
  · rw [hW.covariance_inner, orthonormal_iff_ite.mp b.orthonormal i j]
    split_ifs <;> simp

/-- Projecting a vector Brownian motion onto any finite orthonormal basis `b` yields a coordinate
vector Brownian motion `IsBrownianVector`. -/
theorem IsBrownian.isBrownianVector_inner [Fintype ι] {W : ℝ≥0 → Ω → E}
    (hW : IsBrownian W P) (b : OrthonormalBasis ι ℝ E) :
    IsBrownianVector (fun i t ω ↦ ⟪b i, W t ω⟫) P where
  toIsPreBrownianVector := hW.toIsPreBrownian.isPreBrownianVector_inner b
  ae_continuous i := by
    filter_upwards [hW.ae_continuous] with ω hω
    exact (innerSL ℝ (b i)).continuous.comp hω

/-- Expanding a coordinate vector pre-Brownian motion along any finite orthonormal basis `b` yields
a vector pre-Brownian motion in `E`. -/
theorem IsPreBrownianVector.isPreBrownian_sum_smul [Fintype ι] {B : ι → ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianVector B P) (b : OrthonormalBasis ι ℝ E) :
    IsPreBrownian (fun t ω ↦ ∑ i, B i t ω • b i) P := by
  classical
  have := b.repr.symm.finiteDimensional
  have := hB.isProbabilityMeasure
  refine isPreBrownian_of_integral_eval
    (hB.isGaussianProcess.sum_smul Finset.univ fun _ i ↦ b i) (fun t ↦ ?_) fun s t u v ↦ ?_
  · rw [integral_finsetSum _ fun i _ ↦
      ((hB.memLp_two_eval i t).integrable one_le_two).smul_const _]
    simp [integral_smul_const, hB.integral_eval]
  · have hexp (w : E) (r : ℝ≥0) :
        (fun ω ↦ ⟪w, ∑ i, B i r ω • b i⟫) = ∑ i : ι, fun ω ↦ ⟪w, b i⟫ * B i r ω := by
      ext ω
      simp [inner_sum, inner_smul_right, mul_comm]
    rw [hexp u s, hexp v t,
      covariance_sum_sum (fun i ↦ (hB.memLp_two_eval i s).const_mul _)
        (fun j ↦ (hB.memLp_two_eval j t).const_mul _)]
    have hentry (i j : ι) :
        cov[fun ω ↦ ⟪u, b i⟫ * B i s ω, fun ω ↦ ⟪v, b j⟫ * B j t ω; P] =
          ⟪u, b i⟫ * ⟪v, b j⟫ * if i = j then (min s t : ℝ) else 0 := by
      rw [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_fun_eval]
      ring
    simp only [hentry, mul_ite, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte, ← sum_mul]
    have hparseval : ∑ i : ι, ⟪u, b i⟫ * ⟪v, b i⟫ = ⟪u, v⟫ := by
      have hcomm : ∀ i : ι, ⟪v, b i⟫ = ⟪b i, v⟫ := fun i ↦ (real_inner_comm v (b i)).symm
      simp_rw [hcomm]
      exact b.sum_inner_mul_inner u v
    rw [hparseval, mul_comm]

/-- Expanding a coordinate vector Brownian motion along any finite orthonormal basis `b` yields a
vector Brownian motion in `E`. -/
theorem IsBrownianVector.isBrownian_sum_smul [Fintype ι] {B : ι → ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianVector B P) (b : OrthonormalBasis ι ℝ E) :
    IsBrownian (fun t ω ↦ ∑ i, B i t ω • b i) P where
  toIsPreBrownian := hB.toIsPreBrownianVector.isPreBrownian_sum_smul b
  ae_continuous := by
    filter_upwards [ae_all_iff.mpr hB.ae_continuous] with ω hω
    fun_prop

/-- Basis characterization of `IsPreBrownian`: an `E`-valued process `W` is a vector pre-Brownian
motion if and only if its coordinates `⟪b i, W⟫` in a finite orthonormal basis `b` form an
`IsPreBrownianVector`. -/
theorem isPreBrownian_iff_isPreBrownianVector [Fintype ι] {W : ℝ≥0 → Ω → E}
    (b : OrthonormalBasis ι ℝ E) :
    IsPreBrownian W P ↔ IsPreBrownianVector (fun i t ω ↦ ⟪b i, W t ω⟫) P where
  mp hW := hW.isPreBrownianVector_inner b
  mpr hB := by
    have h := hB.isPreBrownian_sum_smul b
    simp_rw [b.sum_repr'] at h
    exact h

/-- Basis characterization of `IsBrownian`: an `E`-valued process `W` is a vector Brownian motion
if and only if its coordinates `⟪b i, W⟫` in a finite orthonormal basis `b` form an
`IsBrownianVector`. -/
theorem isBrownian_iff_isBrownianVector [Fintype ι] {W : ℝ≥0 → Ω → E}
    (b : OrthonormalBasis ι ℝ E) :
    IsBrownian W P ↔ IsBrownianVector (fun i t ω ↦ ⟪b i, W t ω⟫) P where
  mp hW := hW.isBrownianVector_inner b
  mpr hB := by
    have h := hB.isBrownian_sum_smul b
    simp_rw [b.sum_repr'] at h
    exact h

/-- Product construction of an `E`-valued pre-Brownian motion from a finite family of scalar
pre-Brownian motions along an orthonormal basis `b : OrthonormalBasis ι ℝ E`. -/
theorem _root_.ProbabilityTheory.IsPreBrownianReal.isPreBrownian_sum_smul_pi
    [Fintype ι] {Ω₀ : ι → Type*} [∀ i, MeasurableSpace (Ω₀ i)]
    {P₀ : ∀ i, Measure (Ω₀ i)} {B₀ : ∀ i, ℝ≥0 → Ω₀ i → ℝ}
    (hB₀ : ∀ i, IsPreBrownianReal (B₀ i) (P₀ i)) (b : OrthonormalBasis ι ℝ E) :
    IsPreBrownian (fun t (ω : ∀ j, Ω₀ j) ↦ ∑ i, B₀ i t (ω i) • b i) (Measure.pi P₀) :=
  (IsPreBrownianReal.isPreBrownianVector_pi hB₀).isPreBrownian_sum_smul b

/-- Product construction of an `E`-valued Brownian motion from a finite family of scalar Brownian
motions along an orthonormal basis `b : OrthonormalBasis ι ℝ E`. -/
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
  have hcoord := fun i ↦ ((hW.isPreBrownianVector_inner b).isPreBrownianReal i).eval_zero_ae_eq_zero
  filter_upwards [ae_all_iff.mpr hcoord] with ω hω
  rw [Pi.zero_apply, ← b.sum_repr' (W 0 ω)]
  simp [hω]

/-- For `s ≤ t`, the vector increment `W t - W s` has law
`(stdGaussian E).map (fun x ↦ √(t - s) • x)`. -/
theorem hasLaw_sub_of_le (hW : IsPreBrownian W P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (W t - W s) ((stdGaussian E).map (fun x : E ↦ √((t - s : ℝ≥0) : ℝ) • x)) P := by
  let b := stdOrthonormalBasis ℝ E
  have hB := (hW.isPreBrownianVector_inner b).hasLaw_sub_pi hst
  have hsum : W t - W s = (fun (z : Fin (Module.finrank ℝ E) → ℝ) ↦ ∑ i, z i • b i) ∘
      fun ω i ↦ ⟪b i, W t ω⟫ - ⟪b i, W s ω⟫ := by
    ext ω
    simp_rw [Pi.sub_apply, Function.comp_apply, ← inner_sub_right]
    exact (b.sum_repr' (W t ω - W s ω)).symm
  have hmeas : Measurable (fun (z : Fin (Module.finrank ℝ E) → ℝ) ↦ ∑ i, z i • b i) := by
    fun_prop
  have hmap : (Measure.pi fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 (t - s)).map
      (fun z ↦ ∑ i, z i • b i) =
        (stdGaussian E).map (fun x : E ↦ √((t - s : ℝ≥0) : ℝ) • x) := by
    have hscale : (fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 (t - s)) =
        fun _ ↦ (gaussianReal 0 1).map (fun r : ℝ ↦ √((t - s : ℝ≥0) : ℝ) * r) := by
      ext _
      rw [gaussianReal_map_const_mul]
      simp [Real.sq_sqrt (NNReal.coe_nonneg _)]
    rw [hscale, ← Measure.pi_map_pi fun _ ↦ by fun_prop,
      Measure.map_map hmeas (by fun_prop), stdGaussian_eq_map_pi_orthonormalBasis b,
      Measure.map_map (by fun_prop) hmeas]
    congr 1
    ext z
    simp [smul_sum, smul_smul]
  rw [hsum]
  exact (HasLaw.mk hmeas.aemeasurable hmap).fun_comp hB

/-- At any time `t : ℝ≥0`, `W t` has law `(stdGaussian E).map (fun x ↦ √t • x)`. -/
theorem hasLaw_eval (hW : IsPreBrownian W P) (t : ℝ≥0) :
    HasLaw (W t) ((stdGaussian E).map (fun x : E ↦ √(t : ℝ) • x)) P := by
  refine (tsub_zero t ▸ hW.hasLaw_sub_of_le (zero_le (a := t))).congr ?_
  filter_upwards [hW.eval_zero_ae_eq_zero] with ω hω
  simp [hω]

/-- At `t = 1`, a vector pre-Brownian motion has law `stdGaussian E`. -/
theorem hasLaw_eval_one (hW : IsPreBrownian W P) : HasLaw (W 1) (stdGaussian E) P := by
  simpa using hW.hasLaw_eval 1

/-! ### Noncentered variant started at an arbitrary or independent initial vector -/

/-- Adding an initial random vector `ξ : Ω → E` to a centered vector pre-Brownian motion `W`
produces a process whose initial value at `t = 0` equals `ξ` almost surely. -/
theorem add_left_eval_zero_ae_eq (hW : IsPreBrownian W P) (ξ : Ω → E) :
    (fun ω ↦ ξ ω + W 0 ω) =ᵐ[P] ξ := by
  filter_upwards [hW.eval_zero_ae_eq_zero] with ω hω
  simp [hω]

/-- For any initial random vector `ξ : Ω → E` and `s ≤ t`, the increment of `ξ + W` over `[s, t]`
has the centered Gaussian law `(stdGaussian E).map (fun x ↦ √(t - s) • x)`. -/
theorem hasLaw_add_left_sub_of_le (hW : IsPreBrownian W P) (ξ : Ω → E)
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ (ξ ω + W t ω) - (ξ ω + W s ω))
      ((stdGaussian E).map (fun x : E ↦ √((t - s : ℝ≥0) : ℝ) • x)) P := by
  have hsub : (fun ω ↦ (ξ ω + W t ω) - (ξ ω + W s ω)) = W t - W s := by
    ext ω; simp [add_sub_add_left_eq_sub]
  simpa only [hsub] using hW.hasLaw_sub_of_le hst

/-- For any initial random vector `ξ : Ω → E`, the translated process `ξ + W` retains independent
increments. -/
theorem hasIndepIncrements_add_left (hW : IsPreBrownian W P) (ξ : Ω → E) :
    HasIndepIncrements (fun t ω ↦ ξ ω + W t ω) P := by
  intro n t ht
  simpa only [add_sub_add_left_eq_sub] using hW.hasIndepIncrements n t ht

/-- If an initial random vector `ξ : Ω → E` is independent of the path of `W`, then for
`X t ω := ξ ω + W t ω` the initial position `X 0` has the same a.s. value as `ξ` and is independent
of the entire increment process `t ↦ X t - X 0`. -/
theorem indepFun_add_left_increments (hW : IsPreBrownian W P) {ξ : Ω → E}
    (hξ : IndepFun ξ (fun ω t ↦ W t ω) P) :
    IndepFun (fun ω ↦ ξ ω + W 0 ω) (fun ω t ↦ (ξ ω + W t ω) - (ξ ω + W 0 ω)) P := by
  refine hξ.congr (hW.add_left_eval_zero_ae_eq ξ).symm ?_
  filter_upwards [hW.eval_zero_ae_eq_zero] with ω hω
  ext t
  simp [hω]

end IsPreBrownian

private theorem covariance_inner_of_hasLaw_smul_stdGaussian {Y : Ω → E} {s : ℝ≥0}
    (hY : HasLaw Y ((stdGaussian E).map (fun x : E ↦ √(s : ℝ) • x)) P) (u v : E) :
    cov[fun ω ↦ ⟪u, Y ω⟫, fun ω ↦ ⟪v, Y ω⟫; P] = (s : ℝ) * ⟪u, v⟫ := by
  have := hY.isProbabilityMeasure
  have hmap1 : cov[(innerSL ℝ u) ∘ Y, (innerSL ℝ v) ∘ Y; P] =
      cov[innerSL ℝ u, innerSL ℝ v; P.map Y] :=
    (covariance_map (innerSL ℝ u).continuous.aestronglyMeasurable
      (innerSL ℝ v).continuous.aestronglyMeasurable hY.aemeasurable).symm
  have hsmul : AEMeasurable (fun x : E ↦ √(s : ℝ) • x) (stdGaussian E) :=
    (measurable_id.const_smul _).aemeasurable
  have hmap2 : cov[innerSL ℝ u, innerSL ℝ v; (stdGaussian E).map (fun x : E ↦ √(s : ℝ) • x)] =
      cov[(innerSL ℝ u) ∘ (fun x : E ↦ √(s : ℝ) • x),
        (innerSL ℝ v) ∘ (fun x : E ↦ √(s : ℝ) • x); stdGaussian E] :=
    covariance_map (innerSL ℝ u).continuous.aestronglyMeasurable
      (innerSL ℝ v).continuous.aestronglyMeasurable hsmul
  have hcov : cov[fun ω ↦ ⟪u, Y ω⟫, fun ω ↦ ⟪v, Y ω⟫; P] =
      cov[fun x : E ↦ ⟪u, √(s : ℝ) • x⟫, fun x : E ↦ ⟪v, √(s : ℝ) • x⟫; stdGaussian E] := by
    simpa [Function.comp_def, hY.map_eq] using hmap1.trans (hY.map_eq ▸ hmap2)
  rw [hcov]
  simp_rw [real_inner_smul_right]
  rw [covariance_const_mul_left, covariance_const_mul_right,
    ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
    innerSL_apply_apply]
  have hsq : √(s : ℝ) * (√(s : ℝ) * ⟪u, v⟫) = (√(s : ℝ)) ^ 2 * ⟪u, v⟫ := by ring
  rw [hsq, Real.sq_sqrt s.coe_nonneg]

/-- An `E`-valued process `X` with independent increments such that `X t` has law
`(stdGaussian E).map (fun x ↦ √t • x)` for every `t : ℝ≥0` is a vector pre-Brownian motion. -/
theorem _root_.ProbabilityTheory.HasIndepIncrements.isPreBrownian_of_hasLaw {X : ℝ≥0 → Ω → E}
    (hlaw : ∀ t, HasLaw (X t) ((stdGaussian E).map (fun x : E ↦ √(t : ℝ) • x)) P)
    (hincr : HasIndepIncrements X P) :
    IsPreBrownian X P := by
  have := (hlaw 0).isProbabilityMeasure
  have hgauss (t : ℝ≥0) : HasGaussianLaw (X t) P := by
    have hL : HasGaussianLaw (fun x : E ↦ √(t : ℝ) • x) (stdGaussian E) :=
      (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map
        (√(t : ℝ) • ContinuousLinearMap.id ℝ E)
    exact ⟨(hlaw t).aemeasurable, by rw [(hlaw t).map_eq]; exact hL.isGaussian_map⟩
  have h0 : ∀ᵐ ω ∂P, X 0 ω = 0 := by
    apply HasLaw.ae_eq_of_dirac
    simpa using hlaw 0
  have hG : IsGaussianProcess X P := hincr.isGaussianProcess hgauss h0
  have hmean (t : ℝ≥0) : ∫ ω, X t ω ∂P = 0 := by
    rw [(hlaw t).integral_eq,
      integral_map (φ := fun x : E ↦ √(t : ℝ) • x) (by fun_prop) (f := fun x : E ↦ x)
        measurable_id.aestronglyMeasurable,
      integral_smul, integral_id_stdGaussian, smul_zero]
  refine isPreBrownian_of_integral_eval hG hmean fun s t u v ↦ ?_
  have hle : ∀ ⦃a b : ℝ≥0⦄, a ≤ b → ∀ (x y : E),
      cov[fun ω ↦ ⟪x, X a ω⟫, fun ω ↦ ⟪y, X b ω⟫; P] = (a : ℝ) * ⟪x, y⟫ := by
    intro a b hab x y
    have hind : IndepFun (fun ω ↦ ⟪x, X a ω⟫) (fun ω ↦ ⟪y, X b ω - X a ω⟫) P :=
      (hincr.indepFun_eval_sub zero_le hab h0).comp (by fun_prop) (by fun_prop)
    have hax : MemLp (fun ω ↦ ⟪x, X a ω⟫) 2 P := ((hgauss a).map (innerSL ℝ x)).memLp_two
    have hay : MemLp (fun ω ↦ ⟪y, X a ω⟫) 2 P := ((hgauss a).map (innerSL ℝ y)).memLp_two
    have hdiff : MemLp (fun ω ↦ ⟪y, X b ω - X a ω⟫) 2 P :=
      ((hG.hasGaussianLaw_fun_sub (s := b) (t := a)).map (innerSL ℝ y)).memLp_two
    have hsplit : (fun ω ↦ ⟪y, X b ω⟫) =
        (fun ω ↦ ⟪y, X b ω - X a ω⟫) + fun ω ↦ ⟪y, X a ω⟫ := by
      ext ω; simp [inner_sub_right]
    rw [hsplit, covariance_add_right hax hdiff hay,
      hind.covariance_eq_zero hax hdiff,
      zero_add, covariance_inner_of_hasLaw_smul_stdGaussian (hlaw a) x y]
  rcases le_total s t with hst | hts
  · rw [min_eq_left (NNReal.coe_le_coe.mpr hst)]
    exact hle hst u v
  · rw [min_eq_right (NNReal.coe_le_coe.mpr hts), covariance_comm, hle hts v u, real_inner_comm]

/-! ### Unconditional witness on any finite-dimensional real inner-product space -/

/-- Unconditional concrete witness of `IsPreBrownian` on any finite-dimensional real inner-product
space `E` (including `d = 0`), constructed by expanding independent Kolmogorov pre-Brownian
coordinates along `stdOrthonormalBasis ℝ E`. -/
theorem isPreBrownian_sum_smul_pi_gaussianLimit :
    IsPreBrownian
      (fun t (ω : Fin (Module.finrank ℝ E) → ℝ≥0 → ℝ) ↦ ∑ i, ω i t • stdOrthonormalBasis ℝ E i)
      (Measure.pi fun _ : Fin (Module.finrank ℝ E) ↦ gaussianLimit) :=
  isPreBrownianVector_eval_pi_gaussianLimit.isPreBrownian_sum_smul (stdOrthonormalBasis ℝ E)

end FiniteDimensional

end TauCeti.Probability

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Group.Convolution.Translation
import TauCeti.Probability.Distributions.Gaussian.Affine
import TauCeti.Probability.Distributions.Gaussian.Multivariate
import TauCeti.Probability.Distributions.Gaussian.Sum.Multivariate
import TauCeti.Probability.Kernel.Randomization

/-!
# The isotropic Gaussian Bayes update

Write `N(a, u)` for the isotropic Gaussian law `multivariateGaussian a (u • 1)` on
`EuclideanSpace ℝ ι`. Let `X ~ N(m, u)`, and observe `Y` with conditional law `N(c • X, v)`
given `X`. Then `Y ~ N(c • m, w)` with `w = c ^ 2 * u + v`, and given `Y = y` the law of `X` is

`N(m + (c * u / w) • (y - c • m), u * v / w)`.

This file states this conjugate-prior computation as an equality of joint laws of `(X, Y)`:
drawing `X` and then `Y`, or drawing `Y` from its marginal and then `X` from the posterior. It is
the step that identifies the posterior of a Gaussian noising kernel, as in the reverse
conditionals of denoising diffusion models. It is the isotropic case of the conditioning of
jointly Gaussian vectors in `TauCeti.Probability.Distributions.Gaussian.Conditional.Basic`; here
the two joint laws are compared directly through their characteristic functions.

The file also proves the composition law of these kernels: observing `N(c • x, v)` and then
`N(c' • y, v')` is observing `N((c' * c) • x, c' ^ 2 * v + v')`. This is the law of the
transitions between two noise levels of a Gaussian noising path.

It also computes the second moments of the displacement `Y - X`: the mean squared distance
from `x` to its observation, and the quadratic transport cost of the coupling
`μ₀ ⊗ₘ gaussianKernel c v` of a law and its Gaussian noising.

## Main definitions

* `TauCeti.Probability.gaussianKernel c v` — the Markov kernel `x ↦ N(c • x, v)`.

## Main results

* `TauCeti.Probability.gaussianKernel_apply` — `gaussianKernel c v x = N(c • x, v)`.
* `TauCeti.Probability.gaussianKernel_comp` — the composition law
  `gaussianKernel c' v' ∘ₖ gaussianKernel c v = gaussianKernel (c' * c) (c' ^ 2 * v + v')`.
* `TauCeti.Probability.compProd_gaussianKernel_eq_swap` — the Bayes update, as an equality of
  joint laws.
* `TauCeti.Probability.integral_norm_sub_sq_gaussianKernel` — the mean squared displacement of
  the Gaussian observation kernel, `∫ ‖x - y‖² ∂N(c • x, v) = (1 - c)² ‖x‖² + v d`.
* `TauCeti.Probability.eLpNorm_edist_compProd_gaussianKernel_sq` — the quadratic transport cost
  of the coupling `μ₀ ⊗ₘ gaussianKernel c v`, as an extended integral, with no moment assumption.

## References

* C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006, §2.3.3,
  equations (2.113)–(2.117).
* J. Ho, A. Jain and P. Abbeel, *Denoising diffusion probabilistic models*, NeurIPS 2020,
  equations (6) and (7).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gaussian observation kernel `x ↦ N(c • x, v)`: it rescales its input by `c` and adds
independent noise with law `N(0, v)`. -/
def gaussianKernel (c v : ℝ) : Kernel (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) :=
  (Kernel.id ×ₖ Kernel.const _ (multivariateGaussian 0 (v • 1))).map (fun p ↦ c • p.1 + p.2)

/-- The Gaussian observation kernel is the law of `c • x` plus independent noise `N(0, v)`. -/
theorem gaussianKernel_apply_eq_map (c v : ℝ) (x : EuclideanSpace ℝ ι) :
    gaussianKernel c v x = (multivariateGaussian 0 (v • 1)).map (fun e ↦ c • x + e) := by
  rw [gaussianKernel, Kernel.map_id_prod_const_apply _ _ (by fun_prop)]

/-- The Gaussian observation kernel at `x` is the isotropic Gaussian law `N(c • x, v)`. -/
@[simp]
theorem gaussianKernel_apply (c v : ℝ) (x : EuclideanSpace ℝ ι) :
    gaussianKernel c v x = multivariateGaussian (c • x) (v • 1) := by
  rw [gaussianKernel_apply_eq_map, multivariateGaussian, multivariateGaussian,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, zero_add]

instance (c v : ℝ) : IsMarkovKernel (gaussianKernel (ι := ι) c v) :=
  ⟨fun x ↦ by rw [gaussianKernel_apply]; infer_instance⟩

/-- **Composition of Gaussian observation kernels.** Observing `N(c • x, v)` and then
`N(c' • y, v')` is observing `N((c' * c) • x, c' ^ 2 * v + v')`: the first noise is rescaled by
`c'` and the two independent noises add. Neither variance may be negative, since a negative
variance parameter gives a point mass. -/
theorem gaussianKernel_comp {c v c' v' : ℝ} (hv : 0 ≤ v) (hv' : 0 ≤ v') :
    gaussianKernel (ι := ι) c' v' ∘ₖ gaussianKernel c v =
      gaussianKernel (c' * c) (c' ^ 2 * v + v') := by
  ext1 x
  -- The second step adds the independent noise `N(0, v')` to the rescaled first step.
  have hbind : (gaussianKernel c v x).bind (gaussianKernel c' v') =
      (gaussianKernel c v x).map (fun y ↦ c' • y) ∗ multivariateGaussian 0 (v' • 1) := by
    rw [← Measure.bind_map_add_eq_conv _ _ (by fun_prop)]
    congr 1
    funext y
    exact gaussianKernel_apply_eq_map c' v' y
  have hS : (v • (1 : Matrix ι ι ℝ)).PosSemidef := Matrix.PosSemidef.one.smul hv
  have hmap : (gaussianKernel c v x).map (fun y ↦ c' • y) =
      multivariateGaussian (c' • c • x) (c' ^ 2 • v • (1 : Matrix ι ι ℝ)) := by
    simpa only [zero_add, gaussianKernel_apply] using
      map_add_smul_multivariateGaussian (c • x) hS 0 c'
  -- Gaussian convolution adds the means and the covariances.
  rw [Kernel.comp_apply, hbind, hmap, multivariateGaussian_conv_multivariateGaussian _ _
    (hS.smul (sq_nonneg c')) (Matrix.PosSemidef.one.smul hv'), gaussianKernel_apply, add_zero,
    smul_smul, smul_smul, ← add_smul]

/-- The two joint laws of the Bayes update, as affine images of products of isotropic Gaussians:
`(x, e) ↦ (x, c • x + e)` with `x ~ N(m, u)`, `e ~ N(0, v)`, and
`(y, f) ↦ (m + (c * u / w) • (y - c • m) + f, y)` with `y ~ N(c • m, w)`, `f ~ N(0, u * v / w)`.
They agree because their characteristic functions do. -/
private theorem map_prod_multivariateGaussian_eq (m : EuclideanSpace ℝ ι) {u v c w : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : c ^ 2 * u + v = w) (hw₀ : 0 < w) :
    ((multivariateGaussian m (u • 1)).prod (multivariateGaussian 0 (v • 1))).map
        (fun p ↦ (p.1, c • p.1 + p.2)) =
      ((multivariateGaussian (c • m) (w • 1)).prod
          (multivariateGaussian 0 ((u * v / w) • 1))).map
        (fun p ↦ (m + (c * u / w) • (p.1 - c • m) + p.2, p.1)) := by
  let fst := ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι)
  let snd := ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι)
  let z₀ : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι := (m - (c * u / w * c) • m, 0)
  have h₁ : (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ (p.1, c • p.1 + p.2)) =
      fst.prod (c • fst + snd) := by
    funext p
    simp [fst, snd]
  have h₂ : (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
      (m + (c * u / w) • (p.1 - c • m) + p.2, p.1)) =
      (· + z₀) ∘ ((c * u / w) • fst + snd).prod fst := by
    funext p
    ext1
    · simp [z₀, fst, snd, smul_sub, smul_smul]
      abel
    · simp [z₀, fst]
  rw [h₁, h₂, ← Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, charFunDual_map_add_const, charFunDual_map, charFunDual_prod,
    charFunDual_prod]
  set α := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm (L.comp (.inl ℝ _ _))
  set β := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm (L.comp (.inr ℝ _ _))
  have hL (x y : EuclideanSpace ℝ ι) : L (x, y) = ⟪α, x⟫ + ⟪β, y⟫ := by
    simp only [α, β, InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk,
      add_zero, zero_add]
  -- A functional given by an inner product with `z` has the characteristic function at `z`.
  have hcf (μ : Measure (EuclideanSpace ℝ ι)) (L' : StrongDual ℝ (EuclideanSpace ℝ ι))
      (z : EuclideanSpace ℝ ι) (hz : ∀ x, L' x = ⟪z, x⟫) : charFunDual μ L' = charFun μ z := by
    rw [← charFun_toDual_symm_eq_charFunDual, (LinearIsometryEquiv.symm_apply_eq _).mpr]
    ext x
    rw [hz, InnerProductSpace.toDual_apply_apply]
  rw [hcf _ _ (α + c • β) (fun x ↦ by simp [hL, inner_add_left,
      real_inner_smul_left, real_inner_smul_right, fst, snd]),
    hcf _ _ β (fun x ↦ by simp [hL, fst, snd]),
    hcf _ _ ((c * u / w) • α + β) (fun x ↦ by simp [hL, inner_add_left,
      real_inner_smul_left, real_inner_smul_right, fst, snd]),
    hcf _ _ α (fun x ↦ by simp [hL, fst, snd]),
    charFun_multivariateGaussian_smul_one _ hu, charFun_multivariateGaussian_smul_one _ hv,
    charFun_multivariateGaussian_smul_one _ hw₀.le,
    charFun_multivariateGaussian_smul_one _ (by positivity), hL]
  simp only [← Complex.exp_add]
  congr 1
  simp only [← Complex.ofReal_pow, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right, inner_zero_right,
    real_inner_comm α β]
  subst hw
  have hw' : ((c : ℂ) ^ 2 * u + v) ≠ 0 := by exact_mod_cast hw₀.ne'
  push_cast
  field_simp
  ring

/-- **The isotropic Gaussian Bayes update.** Let `X ~ N(m, u)`, let `Y` given `X` have law
`N(c • X, v)`, and let `w = c ^ 2 * u + v > 0`. Then the joint law of `(X, Y)` is also obtained by
drawing `Y ~ N(c • m, w)` and then `X` from the posterior law
`N(m + (c * u / w) • (Y - c • m), u * v / w)`. -/
theorem compProd_gaussianKernel_eq_swap (m : EuclideanSpace ℝ ι) {u v c w : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v) (hw : c ^ 2 * u + v = w) (hw₀ : 0 < w) :
    multivariateGaussian m (u • 1) ⊗ₘ gaussianKernel c v =
      (multivariateGaussian (c • m) (w • 1) ⊗ₘ
        (Kernel.id ×ₖ Kernel.const _ (multivariateGaussian 0 ((u * v / w) • 1))).map
          (fun p ↦ m + (c * u / w) • (p.1 - c • m) + p.2)).map Prod.swap := by
  rw [← Kernel.map_prod_eq_compProd_of_map (gaussianKernel c v) (multivariateGaussian 0 (v • 1))
      (fun x e ↦ c • x + e) (by fun_prop) fun x ↦ (gaussianKernel_apply_eq_map c v x).symm,
    ← Kernel.map_prod_eq_compProd_of_map _ (multivariateGaussian 0 ((u * v / w) • 1))
      (fun y f ↦ m + (c * u / w) • (y - c • m) + f) (by fun_prop) fun y ↦ ?_,
    Measure.map_map (by fun_prop) (by fun_prop)]
  · exact map_prod_multivariateGaussian_eq m hu hv hw hw₀
  · -- The posterior kernel at `y` is its noise law translated by the posterior mean.
    rw [Kernel.map_id_prod_const_apply _ _ (by fun_prop)]

/-- The mean squared displacement of the Gaussian observation kernel: a point `x` and its noisy
observation `y ~ N(c • x, v)` are at mean squared distance `(1 - c)² ‖x‖² + v d`, where `d` is the
dimension. -/
theorem integral_norm_sub_sq_gaussianKernel (c : ℝ) {v : ℝ} (hv : 0 ≤ v)
    (x : EuclideanSpace ℝ ι) :
    ∫ y, ‖x - y‖ ^ 2 ∂(gaussianKernel c v x) = (1 - c) ^ 2 * ‖x‖ ^ 2 + v * Fintype.card ι := by
  have hmean : c • x - x = (c - 1) • x := by rw [sub_smul, one_smul]
  simp_rw [norm_sub_rev x]
  rw [gaussianKernel_apply, integral_norm_sub_sq_eq_norm_integral_sub_sq_add_trace_covMatrix _
      IsGaussian.memLp_two_id, integral_id_multivariateGaussian, hmean,
    covMatrix_multivariateGaussian _ (Matrix.PosSemidef.one.smul hv)]
  simp only [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  ring

/-- **The quadratic cost of the noising coupling.** For a probability measure `μ₀`, the joint law
`μ₀ ⊗ₘ gaussianKernel c v` of a point and its Gaussian observation has squared `L²` transport cost
`(1 - c)² ∫ ‖x‖² ∂μ₀ + v d`, where `d` is the dimension. The second moment is an extended integral,
so no integrability is assumed and both sides may be infinite. -/
theorem eLpNorm_edist_compProd_gaussianKernel_sq (μ₀ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ₀] (c : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    eLpNorm (fun z ↦ edist z.1 z.2) 2 (μ₀ ⊗ₘ gaussianKernel c v) ^ 2 =
      ENNReal.ofReal ((1 - c) ^ 2) * ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ₀ +
        ENNReal.ofReal (v * Fintype.card ι) := by
  have hinner (x : EuclideanSpace ℝ ι) :
      ∫⁻ y, ‖x - y‖ₑ ^ 2 ∂(gaussianKernel c v x) =
        ENNReal.ofReal ((1 - c) ^ 2) * ‖x‖ₑ ^ 2 + ENNReal.ofReal (v * Fintype.card ι) := by
    have hint : Integrable (fun y ↦ ‖x - y‖ ^ 2) (gaussianKernel c v x) := by
      have hX : MemLp id 2 (gaussianKernel c v x) := by
        rw [gaussianKernel_apply]
        exact IsGaussian.memLp_two_id
      exact (memLp_two_iff_integrable_sq_norm (by fun_prop)).1 ((memLp_const x).sub hX)
    simp_rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ ↦ by positivity),
      integral_norm_sub_sq_gaussianKernel c hv x, ENNReal.ofReal_add (by positivity)
        (by positivity), ENNReal.ofReal_mul (by positivity)]
  rw [eLpNorm_two_sq_eq_lintegral (by fun_prop)]
  simp_rw [eNorm_eq_self]
  rw [Measure.lintegral_compProd (by fun_prop)]
  simp_rw [eDist_eq_eNorm_sub, hinner]
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const, measure_univ, mul_one]

end TauCeti.Probability

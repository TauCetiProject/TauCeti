/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Distributions.Gaussian.CharFun
import TauCeti.Probability.Distributions.Gaussian.Multivariate
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

## Main definitions

* `TauCeti.Probability.gaussianKernel c v` — the Markov kernel `x ↦ N(c • x, v)`.

## Main results

* `TauCeti.Probability.gaussianKernel_apply` — `gaussianKernel c v x = N(c • x, v)`.
* `TauCeti.Probability.compProd_gaussianKernel_eq_swap` — the Bayes update, as an equality of
  joint laws.

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

end TauCeti.Probability

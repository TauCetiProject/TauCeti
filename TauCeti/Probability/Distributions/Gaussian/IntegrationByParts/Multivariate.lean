/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def
public import TauCeti.Probability.Distributions.Gaussian.IntegrationByParts.Basic
public import TauCeti.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import TauCeti.Probability.Distributions.Gaussian.Independence

/-!
# Multivariate Gaussian integration by parts

If `X` is a Gaussian random vector, `L` a continuous linear functional and `f` a differentiable
test function, then
`𝔼[(L X - 𝔼[L X]) • f X] = 𝔼[f' X c]`,
where `c` is the covariance vector of `L`: the vector with `L' c = cov[L' X, L X]` for every
continuous linear functional `L'`. In coordinates this is the identity
`𝔼[(X k - 𝔼[X k]) • f X] = ∑ l, cov[X k, X l] • 𝔼[∂ₗ f X]`
of Anderson, Guionnet and Zeitouni, used to differentiate expectations of functions of
Gaussian matrices and, for a covariance `v • 1`, as Stein's identity in estimation theory.

The covariance may be singular. In the functional form the only integrability hypotheses are
those of the two sides; the coordinate forms assume integrability of the centered side and of
every partial derivative `∂ₗ f X`.

## Main results

* `ProbabilityTheory.HasGaussianLaw.integral_dual_sub_smul_eq_integral_fderiv`: integration by
  parts along a continuous linear functional, for a Gaussian random vector in a separable Banach
  space and a test function with values in a Banach space.
* `ProbabilityTheory.HasGaussianLaw.integral_repr_sub_smul_eq_sum_covariance_smul_integral_fderiv`:
  the coordinate form with respect to a finite basis.
* `ProbabilityTheory.HasGaussianLaw.integral_sub_smul_eq_sum_covariance_smul_integral_fderiv`:
  the coordinate form for a jointly Gaussian finite family of real random variables.
* `TauCeti.Probability.integral_sub_smul_eq_sum_smul_integral_fderiv_multivariateGaussian`:
  the coordinate form for `multivariateGaussian m S`.

## Implementation notes

When `L c ≠ 0`, put `u = (L c)⁻¹ • c`. Then `X = (X - L X • u) + L X • u`, and the two summands
are uncorrelated, hence independent since they are jointly Gaussian. Conditionally on the first
summand, the identity is the one-dimensional Gaussian integration by parts in the real variable
`L X`, and Fubini's theorem on the product law reassembles it. When `L c = 0` the variable `L X`
is almost surely constant and `c = 0`, so both sides vanish.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Lemma 2.4.5.
* C. Stein, *Estimation of the mean of a multivariate normal distribution*, Ann. Statist. 9
  (1981), Lemma 2.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory.HasGaussianLaw

variable {Ω E F : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {X : Ω → E}

/-- The nondegenerate case of `integral_dual_sub_smul_eq_integral_fderiv`. -/
private theorem integral_dual_sub_smul_eq_integral_fderiv_of_ne_zero [CompleteSpace E]
    [SecondCountableTopology E]
    (hX : HasGaussianLaw X P) (L : StrongDual ℝ E) {c : E}
    (hc : ∀ L' : StrongDual ℝ E, L' c = cov[fun ω ↦ L' (X ω), fun ω ↦ L (X ω); P])
    (hLc : L c ≠ 0) (f : E → F) (hf : Differentiable ℝ f)
    (hxf : Integrable (fun ω ↦ (L (X ω) - ∫ ω', L (X ω') ∂P) • f (X ω)) P)
    (hdf : Integrable (fun ω ↦ fderiv ℝ f (X ω) c) P) :
    ∫ ω, (L (X ω) - ∫ ω', L (X ω') ∂P) • f (X ω) ∂P = ∫ ω, fderiv ℝ f (X ω) c ∂P := by
  have := hX.isProbabilityMeasure
  set a := ∫ ω, L (X ω) ∂P
  set u : E := (L c)⁻¹ • c with hu
  have hcu : c = L c • u := by rw [hu, smul_smul, mul_inv_cancel₀ hLc, one_smul]
  -- The law of `L X` is `gaussianReal a v` with `v = L c`.
  set v : ℝ≥0 := Var[fun ω ↦ L (X ω); P].toNNReal
  have hv : (v : ℝ) = L c := by
    rw [Real.coe_toNNReal _ (variance_nonneg _ _), ← covariance_self (by fun_prop), ← hc]
  have hlaw : P.map (fun ω ↦ L (X ω)) = gaussianReal a v := (hX.map_fun L).map_eq_gaussianReal
  -- The joint law of the two independent summands of `X = (X - L X • u) + L X • u` is a product.
  set φ : Ω → E × ℝ := fun ω ↦ (X ω - L (X ω) • u, L (X ω))
  have hφ : AEMeasurable φ P := by fun_prop
  have hprod : P.map φ = (P.map fun ω ↦ X ω - L (X ω) • u).prod (gaussianReal a v) := by
    rw [← hlaw]
    exact (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).1
      (hX.indepFun_sub_smul_of_covariance L hc hLc)
  -- The test function along the line through `y` in direction `u`, and its derivative.
  set g : E → ℝ → F := fun y s ↦ f (y + s • u)
  have hg : Continuous (Function.uncurry g) := hf.continuous.comp (by fun_prop)
  have hderiv (y : E) (s : ℝ) : deriv (g y) s = fderiv ℝ f (y + s • u) u := by
    have h := ((hasDerivAt_id s).smul_const u).const_add y
    simpa [g, Function.comp_def] using ((hf _).hasFDerivAt.comp_hasDerivAt s h).deriv
  set H₁ : E × ℝ → F := fun p ↦ (p.2 - a) • g p.1 p.2
  set H₂ : E × ℝ → F := fun p ↦ L c • deriv (g p.1) p.2
  have hH₁ : AEStronglyMeasurable H₁ (P.map φ) :=
    ((continuous_snd.sub continuous_const).smul hg).aestronglyMeasurable
  have hH₂ : AEStronglyMeasurable H₂ (P.map φ) :=
    ((stronglyMeasurable_deriv_with_param hg).const_smul _).aestronglyMeasurable
  have hφ₁ (ω : Ω) : H₁ (φ ω) = (L (X ω) - a) • f (X ω) := by simp [H₁, g, φ]
  have hφ₂ (ω : Ω) : H₂ (φ ω) = fderiv ℝ f (X ω) c := by
    simp only [H₂, φ, hderiv, sub_add_cancel]
    rw [← map_smul, ← hcu]
  -- Transport both sides to the product law.
  have hi₁ : Integrable H₁ (P.map φ) := by
    rw [integrable_map_measure hH₁ hφ, Function.comp_def]
    simpa only [hφ₁] using hxf
  have hi₂ : Integrable H₂ (P.map φ) := by
    rw [integrable_map_measure hH₂ hφ, Function.comp_def]
    simpa only [hφ₂] using hdf
  simp only [← hφ₁, ← hφ₂]
  rw [← integral_map hφ hH₁, ← integral_map hφ hH₂, hprod]
  rw [hprod] at hi₁ hi₂
  rw [integral_smul, ← hv]
  exact TauCeti.Probability.integral_prod_gaussianReal_sub_smul_eq_smul_integral_deriv a v g
    (fun y s ↦ (hf _).comp s ((differentiableAt_id.smul_const u).const_add y)) hi₁
    ((integrable_smul_iff hLc _).1 hi₂)

/-- **Multivariate Gaussian integration by parts.** Let `X` be a Gaussian random vector, `L` a
continuous linear functional and `c` the covariance vector of `L`, characterized by
`L' c = cov[L' X, L X]` for every continuous linear functional `L'`. For a differentiable test
function `f` such that both sides are integrable,
`𝔼[(L X - 𝔼[L X]) • f X] = 𝔼[f' X c]`.
The covariance of `X` may be singular. -/
theorem integral_dual_sub_smul_eq_integral_fderiv [CompleteSpace E] [SecondCountableTopology E]
    (hX : HasGaussianLaw X P) (L : StrongDual ℝ E) {c : E}
    (hc : ∀ L' : StrongDual ℝ E, L' c = cov[fun ω ↦ L' (X ω), fun ω ↦ L (X ω); P])
    (f : E → F) (hf : Differentiable ℝ f)
    (hxf : Integrable (fun ω ↦ (L (X ω) - ∫ ω', L (X ω') ∂P) • f (X ω)) P)
    (hdf : Integrable (fun ω ↦ fderiv ℝ f (X ω) c) P) :
    ∫ ω, (L (X ω) - ∫ ω', L (X ω') ∂P) • f (X ω) ∂P = ∫ ω, fderiv ℝ f (X ω) c ∂P := by
  rcases ne_or_eq (L c) 0 with hLc | hLc
  · exact integral_dual_sub_smul_eq_integral_fderiv_of_ne_zero hX L hc hLc f hf hxf hdf
  -- If `L c = 0`, then `L X` is almost surely constant and `c = 0`.
  have := hX.isProbabilityMeasure
  have hvar : Var[fun ω ↦ L (X ω); P] = 0 := by
    rw [← covariance_self (by fun_prop), ← hc, hLc]
  have hae := ae_eq_integral_of_variance_eq_zero (hX.map_fun L).memLp_two hvar
  have hc0 : c = 0 := by
    refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun L' ↦ ?_
    rw [hc, covariance]
    refine integral_eq_zero_of_ae (hae.mono fun ω hω ↦ ?_)
    simp [hω]
  rw [hc0, integral_eq_zero_of_ae (hae.mono fun ω hω ↦ by simp [hω])]
  simp

/-- **Multivariate Gaussian integration by parts in a basis.** If `X` is a Gaussian random vector
and `b` a finite basis, then for a differentiable test function `f` such that
`(X k - 𝔼[X k]) • f X` and each `∂ₗ f X` are integrable,
`𝔼[(X k - 𝔼[X k]) • f X] = ∑ l, cov[X k, X l] • 𝔼[∂ₗ f X]`,
where `X k` is the `k`-th coordinate of `X` and `∂ₗ f` the derivative of `f` in the direction of
`b l`. The covariance may be singular. -/
theorem integral_repr_sub_smul_eq_sum_covariance_smul_integral_fderiv {ι : Type*} [Fintype ι]
    (hX : HasGaussianLaw X P) (b : Module.Basis ι ℝ E) (f : E → F) (hf : Differentiable ℝ f)
    (k : ι) (hxf : Integrable (fun ω ↦ (b.repr (X ω) k - ∫ ω', b.repr (X ω') k ∂P) • f (X ω)) P)
    (hdf : ∀ l, Integrable (fun ω ↦ fderiv ℝ f (X ω) (b l)) P) :
    ∫ ω, (b.repr (X ω) k - ∫ ω', b.repr (X ω') k ∂P) • f (X ω) ∂P =
      ∑ l, cov[fun ω ↦ b.repr (X ω) k, fun ω ↦ b.repr (X ω) l; P] •
        ∫ ω, fderiv ℝ f (X ω) (b l) ∂P := by
  have := hX.isProbabilityMeasure
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have : SecondCountableTopology E := inferInstance
  let C (l : ι) : StrongDual ℝ E := LinearMap.toContinuousLinearMap (b.coord l)
  have hC (l : ι) (x : E) : C l x = b.repr x l := by simp [C]
  have hmem (l : ι) : MemLp (fun ω ↦ b.repr (X ω) l) 2 P := (hX.map_fun (C l)).memLp_two
  set c : E := ∑ l, cov[fun ω ↦ b.repr (X ω) l, fun ω ↦ b.repr (X ω) k; P] • b l
  have hc (L' : StrongDual ℝ E) :
      L' c = cov[fun ω ↦ L' (X ω), fun ω ↦ C k (X ω); P] := by
    have hL' : (fun ω ↦ L' (X ω)) = fun ω ↦ ∑ l, b.repr (X ω) l * L' (b l) := by
      ext ω
      conv_lhs => rw [← b.sum_repr (X ω)]
      simp only [map_sum, map_smul, smul_eq_mul]
    simp only [hL', hC, c, map_sum, map_smul, smul_eq_mul]
    rw [covariance_fun_sum_left (fun l ↦ (hmem l).mul_const _) (hmem k)]
    simp only [covariance_mul_const_left]
  have hdc : Integrable (fun ω ↦ fderiv ℝ f (X ω) c) P := by
    simp only [c, map_sum, map_smul]
    exact integrable_finsetSum _ fun l _ ↦ (hdf l).smul _
  have h := integral_dual_sub_smul_eq_integral_fderiv hX (C k) hc f hf hxf hdc
  simp only [hC] at h
  rw [h]
  simp only [c, map_sum, map_smul]
  rw [integral_finsetSum]
  · simp [integral_smul, covariance_comm]
  · exact fun l _ ↦ (hdf l).smul _

/-- **Multivariate Gaussian integration by parts in coordinates.** If the finite family of real
random variables `X ω k` is jointly Gaussian, then for a differentiable test function `f` such
that `(X k - 𝔼[X k]) • f X` and each `∂ₗ f X` are integrable,
`𝔼[(X k - 𝔼[X k]) • f X] = ∑ l, cov[X k, X l] • 𝔼[∂ₗ f X]`.
The covariance may be singular. -/
theorem integral_sub_smul_eq_sum_covariance_smul_integral_fderiv {ι : Type*} [Fintype ι]
    [DecidableEq ι] {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P) (f : (ι → ℝ) → F)
    (hf : Differentiable ℝ f) (k : ι)
    (hxf : Integrable (fun ω ↦ (X ω k - ∫ ω', X ω' k ∂P) • f (X ω)) P)
    (hdf : ∀ l, Integrable (fun ω ↦ fderiv ℝ f (X ω) (Pi.single l 1)) P) :
    ∫ ω, (X ω k - ∫ ω', X ω' k ∂P) • f (X ω) ∂P =
      ∑ l, cov[fun ω ↦ X ω k, fun ω ↦ X ω l; P] •
        ∫ ω, fderiv ℝ f (X ω) (Pi.single l 1) ∂P := by
  simpa using hX.integral_repr_sub_smul_eq_sum_covariance_smul_integral_fderiv
    (Pi.basisFun ℝ ι) f hf k (by simpa using hxf) (by simpa using hdf)

end ProbabilityTheory.HasGaussianLaw

namespace TauCeti.Probability

/-- **Gaussian integration by parts for a multivariate Gaussian.** For a positive-semidefinite
covariance matrix `S` and a differentiable test function `f` such that `(x i - m i) • f x` and
every partial derivative `∂ⱼ f` are integrable under `N(m, S)`,
`∫ (x i - m i) • f x ∂N(m, S) = ∑ j, S i j • ∫ ∂ⱼ f x ∂N(m, S)`.
Under these hypotheses, for `S = v • 1` this gives Stein's identity
`𝔼[(X i - m i) • f X] = v • 𝔼[∂ᵢ f X]`. -/
theorem integral_sub_smul_eq_sum_smul_integral_fderiv_multivariateGaussian {ι F : Type*}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (f : EuclideanSpace ℝ ι → F) (hf : Differentiable ℝ f) (i : ι)
    (hxf : Integrable (fun x ↦ (x i - m i) • f x) (multivariateGaussian m S))
    (hdf : ∀ j, Integrable (fun x ↦ fderiv ℝ f x (EuclideanSpace.single j 1))
      (multivariateGaussian m S)) :
    ∫ x, (x i - m i) • f x ∂multivariateGaussian m S =
      ∑ j, S i j • ∫ x, fderiv ℝ f x (EuclideanSpace.single j 1) ∂multivariateGaussian m S := by
  have hX := IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian m S)
  have h := hX.integral_repr_sub_smul_eq_sum_covariance_smul_integral_fderiv
    (EuclideanSpace.basisFun ι ℝ).toBasis f hf i (by simpa using hxf) (by simpa using hdf)
  simpa [covariance_eval_multivariateGaussian hS] using h

end TauCeti.Probability

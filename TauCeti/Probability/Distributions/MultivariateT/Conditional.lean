/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Conditional.Basic
public import TauCeti.Probability.Distributions.MultivariateT.PDF
import TauCeti.Probability.Distributions.Gamma.Measurability
import TauCeti.Probability.Distributions.MultivariateT.Measurability

/-!
# Conditional multivariate t laws

Partition a multivariate t vector with location `m`, positive-semidefinite scale `S` and `ν > 0`
degrees of freedom into a retained block indexed by `ι` and an observed block indexed by `κ`. If
the observed scale block `S₂₂` is positive definite, the conditional law of the retained block
given the observed value `x₂` is again multivariate t. It has `ν + card κ` degrees of freedom, the
Gaussian regression mean `m₁ + S₁₂ S₂₂⁻¹ (x₂ - m₂)`, and scale

`((ν + q) / (ν + card κ)) • (S₁₁ - S₁₂ S₂₂⁻¹ S₂₁)`, where `q = ⟪x₂ - m₂, S₂₂⁻¹ (x₂ - m₂)⟫`.

Unlike the Gaussian case, the conditional scale depends on the observed value through `q`, and
the degrees of freedom grow with the number of observed coordinates. The retained scale block,
and hence the conditional scale, may be singular.

## Implementation notes

The proof uses the Gamma precision representation
`TauCeti.Probability.multivariateTMeasure_smul_eq_bind_gammaMeasure`: given a precision `τ`, the
vector is Gaussian with covariance `τ⁻¹ • S`, so the retained block given `x₂` is Gaussian with
the regression mean and covariance `τ⁻¹ • (S₁₁ - S₁₂ S₂₂⁻¹ S₂₁)`. Given `x₂` alone, the precision
has a Gamma law of shape `(ν + card κ) / 2` and rate `(ν + q) / 2`; mixing the Gaussian
conditional laws over it gives the multivariate t law above.

## Main definitions

* `EuclideanSpace.multivariateTCondKernel`: the conditional multivariate t Markov kernel.

## Main results

* `EuclideanSpace.map_snd_fst_multivariateTMeasure`: the joint law factors into the observed
  multivariate t marginal and the conditional kernel.
* `TauCeti.Probability.condDistrib_multivariateTMeasure`: the conditional-distribution formula.
* `EuclideanSpace.isMarkovKernel_multivariateTCondKernel`: valid parameters give a Markov kernel.

## References

* S. Kotz and S. Nadarajah, *Multivariate t Distributions and Their Applications*, Cambridge
  University Press, 2004, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal RealInnerProductSpace MatrixOrder

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The Gamma–Gaussian density identity behind the conditional law. On the positive half-line,
the Gamma density of the precision `τ` (shape and rate `ν / 2`) times the density of
`N(a, τ⁻¹ • R)` at `x` factors as the multivariate t density at `x` times the Gamma density of
shape `(ν + d) / 2` and rate `(ν + q) / 2` at `τ`, where `q` is the Mahalanobis form of `x - a`. -/
private theorem gammaPDFReal_mul_multivariateGaussianPDFReal (a : EuclideanSpace ℝ κ)
    {R : Matrix κ κ ℝ} (hR : R.PosDef) {ν : ℝ} (hν : 0 < ν) {τ : ℝ} (hτ : 0 < τ)
    (x : EuclideanSpace ℝ κ) :
    gammaPDFReal (ν / 2) (ν / 2) τ * multivariateGaussianPDFReal a (τ⁻¹ • R) x =
      multivariateTPDFReal a R ν x *
        gammaPDFReal ((ν + Fintype.card κ) / 2) ((ν + ⟪x - a, R⁻¹.toEuclideanLin (x - a)⟫) / 2)
          τ := by
  set q := ⟪x - a, R⁻¹.toEuclideanLin (x - a)⟫ with hq_def
  have hq : 0 ≤ q :=
    (Matrix.isPositive_toEuclideanLin_iff.mpr hR.inv.posSemidef).inner_nonneg_right (x - a)
  set d : ℝ := (Fintype.card κ : ℝ) with hd_def
  have hD := hR.det_pos
  have hinv : (τ⁻¹ • R)⁻¹ = τ • R⁻¹ := by
    simpa [Units.smul_def] using
      Matrix.inv_smul' R (Units.mk0 _ (inv_pos.mpr hτ).ne') hD.ne'.isUnit
  have hΓ : 0 < Real.Gamma (ν / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hΓ' : 0 < Real.Gamma ((ν + d) / 2) := Real.Gamma_pos_of_pos (by positivity)
  -- Collect the powers of `τ` and the exponentials on the left.
  have e1 : (τ⁻¹ ^ Fintype.card κ * R.det) ^ (-(1 : ℝ) / 2) =
      τ ^ (d / 2) * R.det ^ (-(1 : ℝ) / 2) := by
    rw [Real.mul_rpow (by positivity) hD.le, inv_pow, Real.inv_rpow (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul hτ.le, ← Real.rpow_neg (by positivity), ← hd_def]
    congr 2
    ring
  have e2 : τ ^ (ν / 2 - 1) * τ ^ (d / 2) = τ ^ ((ν + d) / 2 - 1) := by
    rw [← Real.rpow_add hτ]
    congr 1
    ring
  have e3 : exp (-(ν / 2 * τ)) * exp (-(τ * q) / 2) = exp (-((ν + q) / 2 * τ)) := by
    rw [← exp_add]
    congr 1
    ring
  -- Split the posterior rate as `(1 + q / ν) * (ν / 2)`, which cancels the t kernel.
  have e4 : ((ν + q) / 2) ^ ((ν + d) / 2) * (1 + q / ν) ^ (-((ν + d) / 2)) =
      (ν / 2) ^ (ν / 2) * (ν / 2) ^ (d / 2) := by
    have hsplit : (ν + q) / 2 = (1 + q / ν) * (ν / 2) := by field_simp
    rw [hsplit, Real.mul_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity),
      ← Real.rpow_add (by positivity : (0 : ℝ) < ν / 2), ← add_div]
    field_simp
  simp only [gammaPDFReal, hτ.le, ↓reduceIte]
  rw [multivariateGaussianPDFReal_def, multivariateTPDFReal_of_posDef a hν hR, hinv,
    Matrix.det_smul, e1, ← hq_def, ← hd_def]
  simp only [map_smul, LinearMap.smul_apply, inner_smul_right]
  calc (ν / 2) ^ (ν / 2) / Real.Gamma (ν / 2) * τ ^ (ν / 2 - 1) * exp (-(ν / 2 * τ)) *
        ((2 * π) ^ (-d / 2) * (τ ^ (d / 2) * R.det ^ (-(1 : ℝ) / 2)) * exp (-(τ * q) / 2))
      = (ν / 2) ^ (ν / 2) * (2 * π) ^ (-d / 2) * R.det ^ (-(1 : ℝ) / 2) / Real.Gamma (ν / 2) *
          (τ ^ (ν / 2 - 1) * τ ^ (d / 2)) * (exp (-(ν / 2 * τ)) * exp (-(τ * q) / 2)) := by
        ring
    _ = _ := by
        rw [e2, e3]
        -- Only the constant factors remain to be compared.
        have hc : (ν / 2) ^ (ν / 2) * (2 * π) ^ (-d / 2) * R.det ^ (-(1 : ℝ) / 2) /
              Real.Gamma (ν / 2) =
            Real.Gamma ((ν + d) / 2) / (Real.Gamma (ν / 2) * (ν * π) ^ (d / 2) * √R.det) *
              (1 + q / ν) ^ (-((ν + d) / 2)) *
              (((ν + q) / 2) ^ ((ν + d) / 2) / Real.Gamma ((ν + d) / 2)) := by
          have hre : Real.Gamma ((ν + d) / 2) /
                (Real.Gamma (ν / 2) * (ν * π) ^ (d / 2) * √R.det) *
                (1 + q / ν) ^ (-((ν + d) / 2)) *
                (((ν + q) / 2) ^ ((ν + d) / 2) / Real.Gamma ((ν + d) / 2)) =
              ((ν + q) / 2) ^ ((ν + d) / 2) * (1 + q / ν) ^ (-((ν + d) / 2)) /
                (Real.Gamma (ν / 2) * (ν * π) ^ (d / 2) * √R.det) := by
            field_simp
          rw [hre, e4]
          simp (disch := positivity) only [neg_div, Real.rpow_neg, Real.mul_rpow, Real.div_rpow,
            Real.sqrt_eq_rpow]
          field_simp
        rw [hc]
        ring

/-- **Gamma–Gaussian conjugacy.** Draw a precision `τ` from the Gamma law of shape and rate
`ν / 2` and then `x` from `N(a, τ⁻¹ • R)`. Equivalently, draw `x` from the multivariate t law
with location `a`, scale `R` and `ν` degrees of freedom, and then `τ` from the Gamma law of shape
`(ν + d) / 2` and rate `(ν + q) / 2`, where `q` is the Mahalanobis form of `x - a`. -/
private theorem lintegral_gammaMeasure_lintegral_multivariateGaussian (a : EuclideanSpace ℝ κ)
    {R : Matrix κ κ ℝ} (hR : R.PosDef) {ν : ℝ} (hν : 0 < ν)
    {F : ℝ × EuclideanSpace ℝ κ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ τ, ∫⁻ x, F (τ, x) ∂multivariateGaussian a (τ⁻¹ • R) ∂gammaMeasure (ν / 2) (ν / 2) =
      ∫⁻ x, ∫⁻ τ, F (τ, x) ∂gammaMeasure ((ν + Fintype.card κ) / 2)
          ((ν + ⟪x - a, R⁻¹.toEuclideanLin (x - a)⟫) / 2) ∂multivariateTMeasure a R ν := by
  let G : Kernel ℝ (EuclideanSpace ℝ κ) :=
    ⟨fun τ => multivariateGaussian a (τ⁻¹ • R), measurable_multivariateGaussian_inv_smul a R⟩
  have : IsMarkovKernel G := ⟨fun τ => inferInstanceAs (IsProbabilityMeasure
    (multivariateGaussian a (τ⁻¹ • R)))⟩
  have hGF : Measurable fun τ => ∫⁻ x, F (τ, x) ∂multivariateGaussian a (τ⁻¹ • R) :=
    hF.lintegral_kernel_prod_right' (κ := G)
  set s : ℝ := (ν + Fintype.card κ) / 2
  set r : EuclideanSpace ℝ κ → ℝ := fun x => (ν + ⟪x - a, R⁻¹.toEuclideanLin (x - a)⟫) / 2
    with hr_def
  have hr : Measurable r := by fun_prop
  -- The joint density of `(τ, x)` in its second factorization.
  let H : ℝ → EuclideanSpace ℝ κ → ℝ≥0∞ := fun τ x => multivariateTPDF a R ν x * gammaPDF s (r x) τ
  have hH : Measurable fun p : ℝ × EuclideanSpace ℝ κ => H p.1 p.2 :=
    ((measurable_multivariateTPDF a R ν).comp measurable_snd).mul
      (measurable_uncurry_gammaPDF.comp
        ((measurable_const.prodMk (hr.comp measurable_snd)).prodMk measurable_fst))
  calc ∫⁻ τ, ∫⁻ x, F (τ, x) ∂multivariateGaussian a (τ⁻¹ • R) ∂gammaMeasure (ν / 2) (ν / 2)
      = ∫⁻ τ, gammaPDF (ν / 2) (ν / 2) τ * ∫⁻ x, F (τ, x) ∂multivariateGaussian a (τ⁻¹ • R) :=
        lintegral_withDensity_eq_lintegral_mul _ (measurable_gammaPDF _ _) hGF
    _ = ∫⁻ τ, ∫⁻ x, H τ x * F (τ, x) := by
        refine lintegral_congr_ae ?_
        filter_upwards [Measure.ae_ne volume 0] with τ hτ0
        rcases hτ0.lt_or_gt with hτ | hτ
        · simp [H, gammaPDF_of_neg hτ]
        rw [multivariateGaussian_eq_withDensity (hR.smul (inv_pos.mpr hτ)),
          lintegral_withDensity_eq_lintegral_mul _ (measurable_multivariateGaussianPDF _ _)
            (g := fun x => F (τ, x)) (by fun_prop),
          ← lintegral_const_mul _ (by fun_prop)]
        refine lintegral_congr fun x => ?_
        simp only [Pi.mul_apply, H, gammaPDF, multivariateGaussianPDF_def,
          multivariateTPDF_eq_ofReal]
        rw [← mul_assoc, ← ENNReal.ofReal_mul (gammaPDFReal_nonneg (by positivity)
          (by positivity) τ), gammaPDFReal_mul_multivariateGaussianPDFReal a hR hν hτ x,
          ENNReal.ofReal_mul (multivariateTPDFReal_nonneg a R ν x)]
    _ = ∫⁻ x, ∫⁻ τ, H τ x * F (τ, x) := lintegral_lintegral_swap (hH.mul hF).aemeasurable
    _ = ∫⁻ x, multivariateTPDF a R ν x * ∫⁻ τ, F (τ, x) ∂gammaMeasure s (r x) := by
        refine lintegral_congr fun x => ?_
        rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ (measurable_gammaPDF _ _)
          (g := fun τ => F (τ, x)) (by fun_prop)]
        simp only [Pi.mul_apply]
        rw [← lintegral_const_mul _ (f := fun τ => gammaPDF s (r x) τ * F (τ, x))
          ((measurable_gammaPDF _ _).mul (by fun_prop))]
        simp only [H, mul_assoc]
    _ = _ := by
        -- The posterior Gamma laws form a Markov kernel, which gives the measurability needed
        -- to integrate against the multivariate t density.
        have hr_pos (x : EuclideanSpace ℝ κ) : 0 < r x := by
          have := (Matrix.isPositive_toEuclideanLin_iff.mpr hR.inv.posSemidef).inner_nonneg_right
            (x - a)
          simp only [hr_def]
          positivity
        let Γ : Kernel (EuclideanSpace ℝ κ) ℝ :=
          ⟨fun x => gammaMeasure s (r x), by fun_prop⟩
        have : IsMarkovKernel Γ := ⟨fun x => isProbabilityMeasure_gammaMeasure (by positivity)
          (hr_pos x)⟩
        have hΓF : Measurable fun x => ∫⁻ τ, F (τ, x) ∂gammaMeasure s
            ((ν + ⟪x - a, R⁻¹.toEuclideanLin (x - a)⟫) / 2) :=
          Measurable.lintegral_kernel_prod_right' (κ := Γ)
            (f := fun p : EuclideanSpace ℝ κ × ℝ => F (p.2, p.1)) (hF.comp measurable_swap)
        rw [multivariateTMeasure_eq_withDensity a hν hR,
          lintegral_withDensity_eq_lintegral_mul _ (measurable_multivariateTPDF a R ν) hΓF]
        -- The sides agree by `Pi.mul_apply` and the local abbreviations `s` and `r`.
        rfl

end TauCeti.Probability

namespace EuclideanSpace

open TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The conditional multivariate t kernel for the `ι`-block given the `κ`-block. At an observed
value `x₂` it is the multivariate t law with `ν + card κ` degrees of freedom, the Gaussian
regression mean `m.gaussianCondMean S x₂`, and scale
`((ν + q) / (ν + card κ)) • S.gaussianCondCov`, where
`q = ⟪x₂ - m₂, S₂₂⁻¹ (x₂ - m₂)⟫` is the Mahalanobis form of the observed deviation.
`TauCeti.Probability.condDistrib_multivariateTMeasure` identifies it with the conditional
distribution when the observed scale block `S₂₂` is positive definite. -/
noncomputable def multivariateTCondKernel (m : EuclideanSpace ℝ (ι ⊕ κ))
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (ν : ℝ) :
    Kernel (EuclideanSpace ℝ κ) (EuclideanSpace ℝ ι) where
  toFun x₂ := multivariateTMeasure (m.gaussianCondMean S x₂)
    (((ν + ⟪x₂ - (EuclideanSpace.sumEquivProd m).2, (S.submatrix Sum.inr Sum.inr)⁻¹.toEuclideanLin
        (x₂ - (EuclideanSpace.sumEquivProd m).2)⟫) / (ν + Fintype.card κ)) • S.gaussianCondCov)
    (ν + Fintype.card κ)
  measurable' := by
    have hmean : Measurable fun x₂ => m.gaussianCondMean S x₂ := by
      rw [funext fun x₂ => m.gaussianCondMean_def S x₂]
      fun_prop
    have hscale : Measurable fun x₂ : EuclideanSpace ℝ κ =>
        (((ν + ⟪x₂ - (EuclideanSpace.sumEquivProd m).2,
          (S.submatrix Sum.inr Sum.inr)⁻¹.toEuclideanLin
            (x₂ - (EuclideanSpace.sumEquivProd m).2)⟫) / (ν + Fintype.card κ)) •
          S.gaussianCondCov : ι → ι → ℝ) := by
      fun_prop
    -- `Matrix.of` is the identity on the underlying functions.
    exact measurable_multivariateTMeasure.comp (hmean.prodMk (hscale.prodMk measurable_const))

/-- The conditional multivariate t kernel evaluates to the multivariate t law with the
displayed location, scale and degrees of freedom. -/
@[simp]
theorem multivariateTCondKernel_apply (m : EuclideanSpace ℝ (ι ⊕ κ))
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (ν : ℝ) (x₂ : EuclideanSpace ℝ κ) :
    m.multivariateTCondKernel S ν x₂ =
      multivariateTMeasure (m.gaussianCondMean S x₂)
        (((ν + ⟪x₂ - (EuclideanSpace.sumEquivProd m).2,
          (S.submatrix Sum.inr Sum.inr)⁻¹.toEuclideanLin
            (x₂ - (EuclideanSpace.sumEquivProd m).2)⟫) / (ν + Fintype.card κ)) •
          S.gaussianCondCov)
        (ν + Fintype.card κ) :=
  (rfl)

/-- For positive degrees of freedom and a positive-semidefinite joint scale, the conditional
multivariate t kernel is a Markov kernel. -/
theorem isMarkovKernel_multivariateTCondKernel (m : EuclideanSpace ℝ (ι ⊕ κ))
    {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} {ν : ℝ} (hν : 0 < ν) (hS : S.PosSemidef) :
    IsMarkovKernel (m.multivariateTCondKernel S ν) where
  isProbabilityMeasure x₂ := by
    have hq := (Matrix.isPositive_toEuclideanLin_iff.mpr
      (hS.submatrix Sum.inr).inv).inner_nonneg_right (x₂ - (EuclideanSpace.sumEquivProd m).2)
    rw [multivariateTCondKernel_apply]
    exact isProbabilityMeasure_multivariateTMeasure _ (by positivity)
      (hS.gaussianCondCov.smul (by positivity))

end EuclideanSpace

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **The joint law of a multivariate t vector factors through the conditional t kernel.** If
the observed scale block `S₂₂` is positive definite, the joint law of the observed and retained
blocks is the multivariate t law of the observed block, with scale `S₂₂` and `ν` degrees of
freedom, composed with `m.multivariateTCondKernel S ν`. The joint coordinates are ordered as
observed, then retained. -/
theorem _root_.EuclideanSpace.map_snd_fst_multivariateTMeasure (m : EuclideanSpace ℝ (ι ⊕ κ))
    {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} {ν : ℝ} (hν : 0 < ν) (hS : S.PosSemidef)
    (hS₂₂ : (S.submatrix Sum.inr Sum.inr).PosDef) :
    (multivariateTMeasure m S ν).map
        (fun x => ((EuclideanSpace.sumEquivProd x).2, (EuclideanSpace.sumEquivProd x).1)) =
      multivariateTMeasure (EuclideanSpace.sumEquivProd m).2 (S.submatrix Sum.inr Sum.inr) ν ⊗ₘ
        m.multivariateTCondKernel S ν := by
  have := EuclideanSpace.isMarkovKernel_multivariateTCondKernel m hν hS
  have := isProbabilityMeasure_multivariateTMeasure (EuclideanSpace.sumEquivProd m).2 hν
    hS₂₂.posSemidef
  set m₂ := (EuclideanSpace.sumEquivProd m).2
  set mean := fun x₂ => m.gaussianCondMean S x₂
  set C := S.gaussianCondCov
  have hC : C.PosSemidef := hS.gaussianCondCov
  have hf : Measurable fun x : EuclideanSpace ℝ (ι ⊕ κ) =>
      ((EuclideanSpace.sumEquivProd x).2, (EuclideanSpace.sumEquivProd x).1) := by fun_prop
  -- The precision representation of the joint law.
  have hT : multivariateTMeasure m S ν =
      (gammaMeasure (ν / 2) (ν / 2)).bind fun τ => multivariateGaussian m (τ⁻¹ • S) := by
    simpa [div_self hν.ne'] using multivariateTMeasure_smul_eq_bind_gammaMeasure m hS hν hν
  -- Evaluate both sides on a measurable set `A`: condition the Gaussian components on `x₂` for
  -- each precision `τ`, swap the order of integration by Gamma–Gaussian conjugacy, and recognise
  -- the posterior Gamma mixture of Gaussian laws as the conditional multivariate t law.
  ext A hA
  -- Given the precision `τ`, the retained block given the observed block `x₂` is Gaussian with
  -- the same regression mean and covariance `τ⁻¹ • C`; this is jointly measurable in `(τ, x₂)`.
  let η : Kernel (ℝ × EuclideanSpace ℝ κ) (EuclideanSpace ℝ ι) :=
    ⟨fun p => multivariateGaussian (mean p.2) (p.1⁻¹ • C), by
      have hμ : Measurable mean := by
        simp only [mean]
        rw [funext fun x₂ => m.gaussianCondMean_def S x₂]
        fun_prop
      exact measurable_multivariateGaussian.comp
        ((hμ.comp measurable_snd).prodMk (by fun_prop))⟩
  have : IsMarkovKernel η := ⟨fun p => inferInstanceAs (IsProbabilityMeasure
    (multivariateGaussian (mean p.2) (p.1⁻¹ • C)))⟩
  have hF : Measurable fun p : ℝ × EuclideanSpace ℝ κ =>
      multivariateGaussian (mean p.2) (p.1⁻¹ • C) (Prod.mk p.2 ⁻¹' A) :=
    -- The section of `{q | (q.1.2, q.2) ∈ A}` at `p` is by definition the section of `A` at `p.2`.
    Kernel.measurable_kernel_prodMk_left (κ := η)
      (t := {q : (ℝ × EuclideanSpace ℝ κ) × EuclideanSpace ℝ ι | (q.1.2, q.2) ∈ A})
      (hA.preimage (by fun_prop))
  calc (multivariateTMeasure m S ν).map
        (fun x => ((EuclideanSpace.sumEquivProd x).2, (EuclideanSpace.sumEquivProd x).1)) A
      = ∫⁻ τ, ((multivariateGaussian m (τ⁻¹ • S)).map
          (fun x => ((EuclideanSpace.sumEquivProd x).2, (EuclideanSpace.sumEquivProd x).1))) A
            ∂gammaMeasure (ν / 2) (ν / 2) := by
        rw [Measure.map_apply hf hA, hT,
          Measure.bind_apply (hf hA) (measurable_multivariateGaussian_inv_smul m S).aemeasurable]
        refine lintegral_congr fun τ => ?_
        rw [Measure.map_apply hf hA]
    _ = ∫⁻ τ, ∫⁻ x₂, multivariateGaussian (mean x₂) (τ⁻¹ • C) (Prod.mk x₂ ⁻¹' A)
          ∂multivariateGaussian m₂ (τ⁻¹ • S.submatrix Sum.inr Sum.inr)
            ∂gammaMeasure (ν / 2) (ν / 2) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_pos_gammaMeasure (ν / 2) (ν / 2)] with τ hτ
        rw [EuclideanSpace.map_snd_fst_multivariateGaussian m (hS.smul (inv_pos.mpr hτ).le),
          Measure.compProd_apply hA]
        simp only [Matrix.submatrix_smul, Pi.smul_apply,
          EuclideanSpace.gaussianCondKernel_inv_smul m hS₂₂ hτ]
        -- The sides differ only by the local abbreviations `m₂`, `mean` and `C`.
        rfl
    _ = ∫⁻ x₂, ∫⁻ τ, multivariateGaussian (mean x₂) (τ⁻¹ • C) (Prod.mk x₂ ⁻¹' A)
          ∂gammaMeasure ((ν + Fintype.card κ) / 2)
            ((ν + ⟪x₂ - m₂, (S.submatrix Sum.inr Sum.inr)⁻¹.toEuclideanLin (x₂ - m₂)⟫) / 2)
          ∂multivariateTMeasure m₂ (S.submatrix Sum.inr Sum.inr) ν :=
        lintegral_gammaMeasure_lintegral_multivariateGaussian m₂ hS₂₂ hν hF
    _ = _ := by
        rw [Measure.compProd_apply hA]
        refine lintegral_congr fun x₂ => ?_
        have hq := (Matrix.isPositive_toEuclideanLin_iff.mpr hS₂₂.inv.posSemidef).inner_nonneg_right
          (x₂ - m₂)
        rw [EuclideanSpace.multivariateTCondKernel_apply,
          multivariateTMeasure_smul_eq_bind_gammaMeasure _ hC (by positivity) (by positivity),
          Measure.bind_apply (measurable_prodMk_left hA)
            (measurable_multivariateGaussian_inv_smul _ _).aemeasurable]

/-- **Conditional multivariate t laws.** For a multivariate t vector with location `m`,
positive-semidefinite scale `S` and `ν > 0` degrees of freedom whose observed scale block `S₂₂`
is positive definite, the regular conditional law of the retained block given the observed
block `x₂` is multivariate t with `ν + card κ` degrees of freedom, location
`m₁ + S₁₂ S₂₂⁻¹ (x₂ - m₂)` and scale `((ν + q) / (ν + card κ)) • (S₁₁ - S₁₂ S₂₂⁻¹ S₂₁)`, where
`q = ⟪x₂ - m₂, S₂₂⁻¹ (x₂ - m₂)⟫`. The retained scale block may be singular. -/
theorem condDistrib_multivariateTMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (X : Ω → EuclideanSpace ℝ (ι ⊕ κ)) (m : EuclideanSpace ℝ (ι ⊕ κ))
    {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} {ν : ℝ} (hX : HasLaw X (multivariateTMeasure m S ν) P)
    (hν : 0 < ν) (hS : S.PosSemidef) (hS₂₂ : (S.submatrix Sum.inr Sum.inr).PosDef) :
    condDistrib (fun ω => (EuclideanSpace.sumEquivProd (X ω)).1)
        (fun ω => (EuclideanSpace.sumEquivProd (X ω)).2) P =ᵐ[
      P.map (fun ω => (EuclideanSpace.sumEquivProd (X ω)).2)] m.multivariateTCondKernel S ν := by
  have := EuclideanSpace.isMarkovKernel_multivariateTCondKernel m hν hS
  have := isProbabilityMeasure_multivariateTMeasure (EuclideanSpace.sumEquivProd m).2 hν
    hS₂₂.posSemidef
  have hXm := hX.aemeasurable
  have hX₁ : AEMeasurable (fun ω => (EuclideanSpace.sumEquivProd (X ω)).1) P := by fun_prop
  have hX₂ : AEMeasurable (fun ω => (EuclideanSpace.sumEquivProd (X ω)).2) P := by fun_prop
  have hjoint : P.map (fun ω => ((EuclideanSpace.sumEquivProd (X ω)).2,
      (EuclideanSpace.sumEquivProd (X ω)).1)) =
      multivariateTMeasure (EuclideanSpace.sumEquivProd m).2 (S.submatrix Sum.inr Sum.inr) ν ⊗ₘ
        m.multivariateTCondKernel S ν := by
    rw [← EuclideanSpace.map_snd_fst_multivariateTMeasure m hν hS hS₂₂, ← hX.map_eq,
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) hXm]
    -- Match the compositional form produced by `map_map`.
    rfl
  refine condDistrib_ae_eq_of_measure_eq_compProd hX₂ hX₁ ?_
  rw [hjoint, ← Measure.fst_map_prodMk₀ hX₂ hX₁, hjoint, Measure.fst_compProd]

end TauCeti.Probability

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Conditional.Basic
public import TauCeti.Probability.Distributions.MultivariateT.PDF
import TauCeti.Probability.Distributions.Gamma.Measurability
import TauCeti.Probability.Distributions.Gaussian.Conditional.Measurability
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
has a Gamma law of shape `(ν + card κ) / 2` and rate `(ν + q) / 2`
(`TauCeti.Probability.lintegral_gammaMeasure_lintegral_multivariateGaussian`); mixing the
Gaussian conditional laws over it gives the multivariate t law above.

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
  have : Measurable mean :=
    EuclideanSpace.measurable_gaussianCondMean.comp
      ((measurable_const (a := (m, S))).prodMk measurable_id)
  have hF : Measurable fun p : ℝ × EuclideanSpace ℝ κ =>
      multivariateGaussian (mean p.2) (p.1⁻¹ • C) (Prod.mk p.2 ⁻¹' A) :=
    measurable_multivariateGaussian_prodMk_left_apply (g := Prod.snd) (this.comp measurable_snd)
      (by fun_prop) measurable_snd hA
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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Basic
public import TauCeti.Probability.Distributions.Wishart.Nonsingular
public import TauCeti.Probability.Distributions.ChiSquared
import TauCeti.Probability.Distributions.Gaussian.ChiSquared
import TauCeti.Probability.Distributions.Gamma.Basic
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Wishart laws in dimension one

In dimension one a Wishart law is a scaled chi-squared law. Read through the single-entry
identification `TauCeti.symmetricFinOneEquiv` of `1 × 1` symmetric matrices with the reals, both the
Gaussian-Gram Wishart law and the nonsingular Wishart density law of degree `n` and scale `S` are
the chi-squared law with `n` degrees of freedom, scaled by the variance `S 0 0`.

## Main results

* `TauCeti.Probability.map_symmetricFinOneEquiv_wishartGramMeasure` — the Gaussian-Gram law.
* `TauCeti.Probability.map_symmetricFinOneEquiv_nonsingularWishartMeasure` — the nonsingular law.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal RealInnerProductSpace Matrix MatrixOrder

namespace TauCeti.Probability

/-- **In dimension one the Gaussian-Gram Wishart law is a scaled chi-squared law.** Read through
the single-entry identification `TauCeti.symmetricFinOneEquiv` of `1 × 1` symmetric matrices with
the reals, the Gram law of degree `ν` and scale `S` is the chi-squared law with `ν` degrees of
freedom, scaled by the variance `S 0 0`. At `ν = 0` both sides are the point mass at zero.

In dimension one the hypothesis `0 ≤ S 0 0` is exactly positive semidefiniteness of the scale, so
nothing is assumed beyond the range on which the Gram law is the classical Wishart law. -/
theorem map_symmetricFinOneEquiv_wishartGramMeasure (ν : ℕ) {S : Matrix (Fin 1) (Fin 1) ℝ}
    (hS : 0 ≤ S 0 0) :
    (wishartGramMeasure ν S).map symmetricFinOneEquiv =
      (Probability.chiSquaredMeasure ν).map (S 0 0 * ·) := by
  have hposSemidef : S.PosSemidef := by
    have hdiag : S = Matrix.diagonal ![S 0 0] := by
      ext i j
      fin_cases i
      fin_cases j
      simp
    rw [hdiag, Matrix.posSemidef_diagonal_iff]
    simp [hS]
  have heval : (multivariateGaussian 0 S).map (fun x : EuclideanSpace ℝ (Fin 1) ↦ x 0) =
      gaussianReal 0 (S 0 0).toNNReal := by
    simpa using (measurePreserving_eval_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ (Fin 1))) hposSemidef (i := 0)).map_eq
  have hpi : (Measure.pi fun _ : Fin ν ↦ multivariateGaussian 0 S).map (fun X r ↦ X r 0) =
      Measure.pi fun _ : Fin ν ↦ gaussianReal 0 (S 0 0).toNNReal := by
    -- `Measure.pi_map_pi` asks for σ-finiteness of the pushed-forward factors.
    have : ∀ _ : Fin ν, SigmaFinite ((multivariateGaussian 0 S).map
        (fun x : EuclideanSpace ℝ (Fin 1) ↦ x 0)) := fun _ ↦ by rw [heval]; infer_instance
    rw [Measure.pi_map_pi fun _ ↦ (by fun_prop : AEMeasurable
      (fun x : EuclideanSpace ℝ (Fin 1) ↦ x 0) _)]
    simp only [heval]
  have hgram : (symmetricFinOneEquiv ∘ wishartGram : (Fin ν → EuclideanSpace ℝ (Fin 1)) → ℝ) =
      (fun y : Fin ν → ℝ ↦ ∑ r, y r ^ 2) ∘ (fun X r ↦ X r 0) := by
    funext X
    simp [coe_wishartGram, Matrix.sum_apply, Matrix.vecMulVec_apply, sq]
  rw [wishartGramMeasure_eq_map_pi, Measure.map_map symmetricFinOneEquiv.continuous.measurable
      measurable_wishartGram, hgram, ← Measure.map_map (by fun_prop) (by fun_prop), hpi,
    Probability.map_sum_sq_pi_gaussianReal, Fintype.card_fin, Real.coe_toNNReal _ hS]

/-- **In dimension one the nonsingular Wishart law is a scaled chi-squared law.** Read through
the single-entry identification `TauCeti.symmetricFinOneEquiv` of `1 × 1` symmetric matrices with
the reals, the Wishart law of degree `n` and scale `S` is the chi-squared law with `n` degrees of
freedom, scaled by the variance `S 0 0`.

In dimension one the hypotheses `0 < n` and `0 < S 0 0` are exactly the parameter range of the
density family, and neither can be dropped: at `n = 0`, or at a nonpositive variance with
`0 < n`, the Wishart law is zero while the right-hand side is a probability measure. -/
theorem map_symmetricFinOneEquiv_nonsingularWishartMeasure {n : ℝ} (hn : 0 < n)
    {S : Matrix (Fin 1) (Fin 1) ℝ} (hS : 0 < S 0 0) :
    (nonsingularWishartMeasure n S).map symmetricFinOneEquiv =
      (Probability.chiSquaredMeasure n).map (S 0 0 * ·) := by
  have hposDef : S.PosDef := (Matrix.posDef_fin_one_iff S).2 hS
  have hdet : S.det = S 0 0 := Matrix.det_fin_one S
  let e := symmetricFinOneEquiv.toHomeomorph.toMeasurableEquiv
  have he : (e : _ → ℝ) = symmetricFinOneEquiv := by
    rw [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph]
  rw [Probability.chiSquaredMeasure_eq_gammaMeasure hn,
    gammaMeasure_map_const_mul (by positivity) (by norm_num) hS,
    nonsingularWishartMeasure_of_posDef hposDef (by simpa using hn), ← he,
    MeasurableEquiv.map_withDensity, he, measurePreserving_symmetricFinOneEquiv.map_eq,
    ProbabilityTheory.gammaMeasure]
  -- Both sides are now densities against Lebesgue measure on `ℝ`: compare them off the origin,
  -- where the Wishart density vanishes but the gamma density need not.
  refine withDensity_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (μ := volume) (0 : ℝ))] with x hx
  set A := e.symm x
  have hA : ∀ i j, (A : Matrix (Fin 1) (Fin 1) ℝ) i j = x :=
    coe_symmetricFinOneEquiv_symm_apply x
  rcases (Set.mem_compl_singleton_iff.1 hx).lt_or_gt with hx | hx
  · have hnot : ¬ (A : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
      rw [Matrix.posDef_fin_one_iff, hA]
      exact hx.not_gt
    rw [nonsingularWishartPDF_of_not_posDef n S hnot, ProbabilityTheory.gammaPDF_of_neg hx]
  · have hApos : (A : Matrix (Fin 1) (Fin 1) ℝ).PosDef :=
      (Matrix.posDef_fin_one_iff _).2 (by rwa [hA])
    have htrace : Matrix.trace (S⁻¹ * (A : Matrix (Fin 1) (Fin 1) ℝ)) = x / S 0 0 := by
      simp [Matrix.trace, Matrix.mul_apply, hA, div_eq_inv_mul]
    rw [nonsingularWishartPDF_of_posDef n S hApos, ProbabilityTheory.gammaPDF_of_nonneg hx.le,
      Matrix.det_fin_one, hA, htrace, hdet, multivariateGamma_one,
      Real.div_rpow (by norm_num) hS.le, Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow]
    congr 1
    have h2 := (Real.rpow_pos_of_pos (two_pos : (0 : ℝ) < 2) (n / 2)).ne'
    have hσ := (Real.rpow_pos_of_pos hS (n / 2)).ne'
    have hΓ := (Real.Gamma_pos_of_pos (by positivity : 0 < n / 2)).ne'
    have hdetExponent : (n - ((1 : ℕ) : ℝ) - 1) / 2 = n / 2 - 1 := by
      push_cast
      ring
    have hnormalizerExponent : n * ((1 : ℕ) : ℝ) / 2 = n / 2 := by
      push_cast
      ring
    have hexponentialArgument : -(x / S 0 0) / 2 = -(1 / 2 / S 0 0 * x) := by
      ring
    rw [hdetExponent, hnormalizerExponent, hexponentialArgument]
    field_simp

end TauCeti.Probability

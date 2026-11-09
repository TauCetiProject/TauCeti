/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.Submatrix
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Analysis.Matrix.MeasurableSpace
import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Principal blocks of the independent-Beta correlation construction

The partial correlations used to construct a `p × p` LKJ correlation matrix of shape `η`
are centered symmetric Beta variables of shape `η + (p - j - 2) / 2`, where `j` is the
zero-based column. Selecting the leading `q × q` block retains exactly the corresponding
partial correlations. Their shapes are those of the `q`-dimensional construction with shape
`η + (p - q) / 2`.

This file proves that marginal identity directly for the product-measure Gram pushforwards.
It also proves the projection identity for arbitrary independent partial-correlation laws.
Neither identity needs a density representation of the resulting matrix measure.
Empty and singleton blocks are included.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {p q : ℕ}

/-- Leading principal blocks of a Gram matrix constructed from independent partial
correlations have the law obtained by selecting the same partial-correlation marginals. -/
theorem map_submatrix_partialCorrelationGram_pi (h : q ≤ p)
    (μ : strictLowerTriangle p → Measure ℝ) [∀ ij, IsProbabilityMeasure (μ ij)] :
    ((Measure.pi μ).map partialCorrelationGram).map
        (fun R ↦ R.submatrix (Fin.castLE h) (Fin.castLE h)) =
      (Measure.pi fun ij ↦ μ (strictLowerTriangle.castLE h ij)).map
        partialCorrelationGram := by
  have hm := (measurePreserving_pi_comp_embedding μ (strictLowerTriangle.castLE h)).map_eq
  rw [Measure.map_map (by fun_prop) continuous_partialCorrelationGram.measurable]
  simp only [Function.comp_def, partialCorrelationGram_submatrix_castLE]
  rw [← hm, Measure.map_map continuous_partialCorrelationGram.measurable (by fun_prop)]
  rfl

/-- A leading `q × q` block of the independent-Beta correlation construction in dimension `p`
has the same construction in dimension `q` with shape increased by `(p - q) / 2`.
Dimensions are cast to the reals before subtraction and division. -/
theorem map_submatrix_partialCorrelationGram_pi_betaMeasure (h : q ≤ p)
    {η : ℝ} (hη : 0 < η) :
    ((Measure.pi fun ij : strictLowerTriangle p ↦
        (betaMeasure (η + ((p : ℝ) - ij.1.2.val - 2) / 2)
          (η + ((p : ℝ) - ij.1.2.val - 2) / 2)).map (fun x ↦ -1 + 2 * x)).map
          partialCorrelationGram).map (fun R ↦ R.submatrix (Fin.castLE h) (Fin.castLE h)) =
      (Measure.pi fun ij : strictLowerTriangle q ↦
        (betaMeasure (η + ((p : ℝ) - q) / 2 + ((q : ℝ) - ij.1.2.val - 2) / 2)
          (η + ((p : ℝ) - q) / 2 + ((q : ℝ) - ij.1.2.val - 2) / 2)).map
            (fun x ↦ -1 + 2 * x)).map partialCorrelationGram := by
  have hshape (ij : strictLowerTriangle p) :
      0 < η + ((p : ℝ) - ij.1.2.val - 2) / 2 := by
    have hj : ij.1.2.val + 2 ≤ p := by
      have := ij.2
      have := ij.1.1.isLt
      omega
    have hj' : (ij.1.2.val : ℝ) + 2 ≤ p := by exact_mod_cast hj
    linarith
  let _ (ij : strictLowerTriangle p) :
      IsProbabilityMeasure (betaMeasure (η + ((p : ℝ) - ij.1.2.val - 2) / 2)
        (η + ((p : ℝ) - ij.1.2.val - 2) / 2)) :=
    isProbabilityMeasureBeta (hshape ij) (hshape ij)
  rw [map_submatrix_partialCorrelationGram_pi h]
  congr 2
  funext ij
  have hparam : η + ((p : ℝ) - (strictLowerTriangle.castLE h ij).1.2.val - 2) / 2 =
      η + ((p : ℝ) - q) / 2 + ((q : ℝ) - ij.1.2.val - 2) / 2 := by
    simp only [strictLowerTriangle.castLE_apply, Fin.val_castLE]
    ring
  rw [hparam]

end TauCeti.Probability

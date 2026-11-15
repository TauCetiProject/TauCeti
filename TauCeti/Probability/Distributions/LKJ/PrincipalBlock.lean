/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.PartialCorrelation.Submatrix
public import TauCeti.Probability.Distributions.LKJ.PartialCorrelation
public import TauCeti.Probability.Distributions.LKJ.Symmetry
import TauCeti.MeasureTheory.Constructions.Pi
import Mathlib.Logic.Equiv.Fintype

/-!
# Principal blocks of LKJ correlation matrices

The partial correlations used to construct a `p × p` LKJ correlation matrix of shape `η`
are centered symmetric Beta variables of shape `η + (p - j - 2) / 2`, where `j` is the
zero-based column. Selecting the leading `q × q` block retains exactly the corresponding
partial correlations. Their shapes are those of the `q`-dimensional construction with shape
`η + (p - q) / 2`.

This file proves that marginal identity directly for the product-measure Gram pushforwards.
It also proves the projection identity for arbitrary independent partial-correlation laws.
Neither identity needs a density representation of the resulting matrix measure.
Empty and singleton blocks are included.

For the density-defined LKJ law, every principal block of size `q` in dimension `p` has
LKJ shape `η + (p - q) / 2`. The leading-block identity for the independent-Beta construction
gives this marginal, and permutation invariance permits any injective selection of coordinates.
The block is bundled in the symmetric carrier using congruence by the selected rows of the
identity matrix. The law identity and its `HasLaw` corollary include empty and singleton blocks.

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

private theorem map_leadingBlock_lkjMeasure (h : q ≤ p) {η : ℝ} (hη : 0 < η) :
    (lkjMeasure p η).map
        (Matrix.symmetricCongruenceLinearMap
          ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE h) id)) =
      lkjMeasure q (η + ((p : ℝ) - q) / 2) := by
  have hη' : 0 < η + ((p : ℝ) - q) / 2 := by
    have : (q : ℝ) ≤ p := by exact_mod_cast h
    linarith
  have he : MeasurableEmbedding (Subtype.val :
      selfAdjoint.submodule ℝ (Matrix (Fin q) (Fin q) ℝ) → Matrix (Fin q) (Fin q) ℝ) :=
    MeasurableEmbedding.subtype_coe isClosed_setOfPred_isSelfAdjoint.measurableSet
  apply he.map_injective
  rw [Measure.map_map measurable_subtype_coe (by fun_prop), map_coe_lkjMeasure hη']
  have hshape {n : ℕ} (a : ℝ) (ij : strictLowerTriangle n) :
      lkjPartialCorrelationShape n a ij = a + ((n : ℝ) - ij.1.2.val - 2) / 2 := by
    have hj : ij.1.2.val + 2 ≤ n := by
      have := ij.2
      have := ij.1.1.isLt
      omega
    rw [lkjPartialCorrelationShape_def, Nat.cast_sub (by omega),
      Nat.cast_sub (by omega)]
    push_cast
    ring
  simp_rw [hshape]
  have hcoe := map_coe_lkjMeasure (p := p) hη
  simp_rw [hshape] at hcoe
  rw [← map_submatrix_partialCorrelationGram_pi_betaMeasure h hη, ← hcoe]
  rw [Measure.map_map (by fun_prop) measurable_subtype_coe]
  congr 1
  funext R
  simp [Matrix.transpose_submatrix,
    Matrix.submatrix_one_mul_mul_submatrix_one]

/-- Every principal `q × q` block of an LKJ matrix in dimension `p` has LKJ shape
`η + (p - q) / 2`. The selection may have any order, and empty and singleton blocks are
included. Congruence by the selected rows of the identity reads the principal submatrix. -/
theorem map_symmetricCongruenceLinearMap_submatrix_one_lkjMeasure
    (f : Fin q → Fin p) (hf : Function.Injective f) {η : ℝ} (hη : 0 < η) :
    (lkjMeasure p η).map
        (Matrix.symmetricCongruenceLinearMap
          ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix f id)) =
      lkjMeasure q (η + ((p : ℝ) - q) / 2) := by
  have h : q ≤ p := by simpa using Fintype.card_le_of_injective f hf
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (Fin.castLE h) f (Fin.castLE_injective h) hf
  calc
    _ = ((lkjMeasure p η).map (Matrix.symmetricCongruenceLinearMap (σ.permMatrix ℝ))).map
        (Matrix.symmetricCongruenceLinearMap
          ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix (Fin.castLE h) id)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext R
      apply Subtype.ext
      simp only [Function.comp_apply]
      rw [Matrix.coe_symmetricCongruenceLinearMap_apply,
        Matrix.coe_symmetricCongruenceLinearMap_apply]
      simp only [Matrix.transpose_submatrix, Matrix.transpose_one,
        Matrix.submatrix_one_mul_mul_submatrix_one]
      rw [Matrix.coe_symmetricCongruenceLinearMap_permMatrix_apply]
      ext i j
      simp [hσ]
    _ = _ := by
      rw [map_symmetricCongruenceLinearMap_permMatrix_lkjMeasure]
      exact map_leadingBlock_lkjMeasure h hη

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {p q : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A principal block of a random symmetric matrix with positive-shape LKJ law has the
lower-dimensional LKJ law with shape increased by half the number of omitted coordinates. -/
theorem principalBlock_lkjMeasure
    {R : Ω → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} {η : ℝ}
    (hR : HasLaw R (lkjMeasure p η) P) (hη : 0 < η)
    (f : Fin q → Fin p) (hf : Function.Injective f) :
    HasLaw (fun ω ↦ Matrix.symmetricCongruenceLinearMap
      ((1 : Matrix (Fin p) (Fin p) ℝ).submatrix f id) (R ω))
      (lkjMeasure q (η + ((p : ℝ) - q) / 2)) P := by
  exact (⟨(by fun_prop),
    map_symmetricCongruenceLinearMap_submatrix_one_lkjMeasure f hf hη⟩ :
      HasLaw _ _ (lkjMeasure p η)).fun_comp hR

end ProbabilityTheory.HasLaw

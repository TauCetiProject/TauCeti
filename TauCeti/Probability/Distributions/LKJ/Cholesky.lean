/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LKJ.PartialCorrelation
public import TauCeti.LinearAlgebra.Matrix.Cholesky.Topology
import TauCeti.Probability.Distributions.Beta.Symmetric

/-!
# The Cholesky-factor law of an LKJ matrix

The Cholesky factor of an LKJ correlation matrix is constructed from independent
centered symmetric Beta partial correlations. In zero-based column `j`, the Beta shape
is `η + (p - j - 2) / 2`. The map `partialCorrelationCholesky` turns these partial
correlations into the entire triangular factor, including its dependent diagonal entries.

Cholesky factorization is defined on the positive-definite cone. We therefore lift
`lkjMeasure` to that cone by `Measure.comap Subtype.val`, and prove that inclusion maps
the lift back to the original law. The factor-law identity describes a measure on raw
matrices, so it can be used directly for all the factor's entries. It also covers
dimensions zero and one, where the factor is the identity and the Beta family is empty.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {p : ℕ} {η : ℝ}

/-- The Cholesky factor of an LKJ matrix is the triangular construction from independent
centered symmetric Beta partial correlations. The diagonal entries are the residual products
in `partialCorrelationCholesky`, rather than additional independent variables. -/
theorem map_cholesky_comap_lkjMeasure (hη : 0 < η) :
    ((lkjMeasure p η).comap
        (Subtype.val : PosDefMatrix p → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))).map
        (fun A ↦ (cholesky A).1) =
      (Measure.pi fun ij : strictLowerTriangle p ↦
        (betaMeasure (lkjPartialCorrelationShape p η ij)
          (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)).map
        partialCorrelationCholesky := by
  let ν := Measure.pi fun ij : strictLowerTriangle p ↦
    (betaMeasure (lkjPartialCorrelationShape p η ij)
      (lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)
  let f := fun z : strictLowerTriangle p → ℝ ↦
    correlationMatrix p (correlationCoordinatesOfPartialCorrelation z)
  have hf : Measurable f := (measurableEmbedding_correlationMatrix p).measurable.comp
    continuous_correlationCoordinatesOfPartialCorrelation.measurable
  have hmap : ν.map f = lkjMeasure p η := by
    exact (Measure.map_map (measurableEmbedding_correlationMatrix p).measurable
      continuous_correlationCoordinatesOfPartialCorrelation.measurable).symm.trans
      (map_correlationMatrix_map_correlationCoordinatesOfPartialCorrelation_pi_betaMeasure hη)
  have hemb : MeasurableEmbedding
      (Subtype.val : PosDefMatrix p → selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
    MeasurableEmbedding.subtype_coe (measurableSet_posDefMatrix p)
  have hchol : Measurable (fun A : PosDefMatrix p ↦ (cholesky A).1) :=
    measurable_subtype_coe.comp measurable_cholesky
  ext s hs
  have hE := hemb.measurableSet_image.2 (hchol hs)
  rw [Measure.map_apply hchol hs, hemb.comap_apply, ← hmap, Measure.map_apply hf hE,
    Measure.map_apply continuous_partialCorrelationCholesky.measurable hs]
  apply measure_congr
  filter_upwards [ae_abs_lt_one_pi_centered_betaMeasure
    (lkjPartialCorrelationShape_pos hη)] with z hz
  have hpos : (f z : Matrix (Fin p) (Fin p) ℝ).PosDef :=
    mem_posDefCorrelationRegion.1 (mapsTo_correlationCoordinatesOfPartialCorrelation hz)
  have hfactor : (cholesky ⟨f z, hpos⟩).1 = partialCorrelationCholesky z := by
    exact (congrArg Subtype.val (eq_cholesky_of_mul_transpose_self_eq ⟨f z, hpos⟩
      ⟨partialCorrelationCholesky z, isLowerTriangular_partialCorrelationCholesky z,
        partialCorrelationCholesky_diag_pos hz⟩
      ((partialCorrelationGram_def z).symm.trans
        (coe_correlationMatrix_correlationCoordinatesOfPartialCorrelation
          (fun ij ↦ (hz ij).le)).symm))).symm
  apply propext
  constructor
  · rintro ⟨A, hAs, hA⟩
    have hAeq : A = ⟨f z, hpos⟩ := Subtype.ext hA
    simpa only [mem_preimage, hAeq, hfactor] using hAs
  · intro hzs
    exact ⟨⟨f z, hpos⟩, by simpa only [mem_preimage, hfactor] using hzs, rfl⟩

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

/-- A positive-definite random matrix with the lifted LKJ law has the Cholesky-factor law
constructed from independent centered symmetric Beta partial correlations. -/
theorem cholesky_lkjMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {p : ℕ} {η : ℝ} {A : Ω → TauCeti.PosDefMatrix p}
    (hA : HasLaw A ((TauCeti.Probability.lkjMeasure p η).comap Subtype.val) P) (hη : 0 < η) :
    HasLaw (fun ω ↦ (TauCeti.cholesky (A ω)).1)
      ((Measure.pi fun ij : TauCeti.strictLowerTriangle p ↦
        (betaMeasure (TauCeti.Probability.lkjPartialCorrelationShape p η ij)
          (TauCeti.Probability.lkjPartialCorrelationShape p η ij)).map (fun x ↦ -1 + 2 * x)).map
        TauCeti.partialCorrelationCholesky) P := by
  exact HasLaw.fun_comp (Y := fun B : TauCeti.PosDefMatrix p ↦ (TauCeti.cholesky B).1)
    ⟨(measurable_subtype_coe.comp TauCeti.measurable_cholesky).aemeasurable,
      TauCeti.Probability.map_cholesky_comap_lkjMeasure hη⟩ hA

end ProbabilityTheory.HasLaw

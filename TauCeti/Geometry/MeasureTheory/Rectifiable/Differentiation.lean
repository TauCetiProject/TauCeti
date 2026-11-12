/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.NormalGraph
public import TauCeti.MeasureTheory.Function.AreaFormula.Graph
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Tangential differentiation on Lipschitz normal graphs

A Lipschitz function on a Lipschitz normal graph is differentiable within that graph at
almost every point for normalized Hausdorff surface measure. The function need only be
Lipschitz on the graph, not in the ambient space. The same existence assertion holds on
arbitrary subsets of the parameter space, without measurability assumptions.

On the full graph, the restrictions of these within-derivatives to the classical tangent
plane are almost everywhere unique. The plane is the range of the linear graph of the
derivative of the graphing function. This provides tangential differentiation in graph
coordinates without choosing a derivative in the normal direction.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §3.3 (differentiation and integration on Lipschitz graphs).
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzOnWith

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {φ : E → ℝ} {f : WithLp 2 (ℝ × E) → F} {K L : ℝ≥0}

/-- Rademacher's theorem on a Lipschitz normal graph, restricted to an arbitrary parameter
set. Almost everywhere is with respect to normalized Hausdorff surface measure; neither
the parameter set nor its graph image is required to be measurable. -/
theorem ae_differentiableWithinAt_normalGraphEmbedding_image {s : Set E}
    (hf : LipschitzOnWith L f (TauCeti.normalGraphEmbedding φ '' s))
    (hφ : LipschitzWith K φ) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ TauCeti.normalGraphEmbedding φ '' s →
        DifferentiableWithinAt ℝ f (TauCeti.normalGraphEmbedding φ '' s) y := by
  have hp := hf.comp hφ.normalGraphEmbedding.lipschitzOnWith (mapsTo_image _ s)
  have hbad : volume {x | ¬(x ∈ s →
      DifferentiableWithinAt ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s x)} = 0 :=
    ae_iff.mp hp.ae_differentiableWithinAt_of_mem
  have hnull := (hφ.euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_zero_iff _).2 hbad
  have hgood : ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∉ TauCeti.normalGraphEmbedding φ '' {x | ¬(x ∈ s →
        DifferentiableWithinAt ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s x)} :=
    ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hnull)
  filter_upwards [hgood] with y hy hys
  obtain ⟨x, hx, rfl⟩ := hys
  have hd : DifferentiableWithinAt ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s x := by
    by_contra h
    exact hy ⟨x, fun hgood ↦ h (hgood hx), rfl⟩
  exact hd.hasFDerivWithinAt.of_comp_normalGraphEmbedding.differentiableWithinAt

/-- A Lipschitz function on a Lipschitz normal graph has almost everywhere a unique
continuous linear tangential derivative, represented by the restriction of any ambient
within-derivative. No ambient differentiability or choice of a normal derivative is assumed.
The tangent plane is computed from the almost everywhere derivative of `φ`. -/
theorem ae_existsUnique_restrict_normalGraph
    (hf : LipschitzOnWith L f (range (TauCeti.normalGraphEmbedding φ)))
    (hφ : LipschitzWith K φ) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ range (TauCeti.normalGraphEmbedding φ) →
        DifferentiableAt ℝ φ y.snd ∧
        ∃! D : (fderiv ℝ φ y.snd).normalGraphL.range →L[ℝ] F,
          ∃ M : WithLp 2 (ℝ × E) →L[ℝ] F,
            HasFDerivWithinAt f M (range (TauCeti.normalGraphEmbedding φ)) y ∧
            M.comp (fderiv ℝ φ y.snd).normalGraphL.range.subtypeL = D := by
  have hnull := (hφ.euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_zero_iff _).2
    (ae_iff.mp hφ.ae_differentiableAt)
  have hgood : ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∉ TauCeti.normalGraphEmbedding φ '' {x | ¬DifferentiableAt ℝ φ x} :=
    ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hnull)
  have hf' : LipschitzOnWith L f (TauCeti.normalGraphEmbedding φ '' univ) := by
    simpa only [image_univ] using hf
  have hdiff := hf'.ae_differentiableWithinAt_normalGraphEmbedding_image hφ
  simp only [image_univ] at hdiff
  filter_upwards [hgood, hdiff] with y hy hfy hyrange
  obtain ⟨x, rfl⟩ := hyrange
  have hφx : DifferentiableAt ℝ φ x := by
    by_contra h
    exact hy ⟨x, h, rfl⟩
  have hcomp := (hfy (mem_range_self x)).hasFDerivWithinAt.comp_hasFDerivAt x
    hφx.hasFDerivAt.normalGraphEmbedding (Filter.Eventually.of_forall mem_range_self)
  rw [TauCeti.normalGraphEmbedding_snd]
  exact ⟨hφx, hcomp.existsUnique_restrict_normalGraph hφx.hasFDerivAt⟩

end LipschitzOnWith

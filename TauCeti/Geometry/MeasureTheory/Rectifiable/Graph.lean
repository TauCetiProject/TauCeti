/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.TangentCone.Graph
public import TauCeti.Analysis.Calculus.FDeriv.NormalGraph
public import TauCeti.MeasureTheory.Function.AreaFormula.Graph
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Tangency and tangential differentiation on normal graphs

At every differentiability point of a normal graph, the classical tangent plane also satisfies
the measure-theoretic cone condition: the normalized Hausdorff measure of the graph outside
any cone about that plane, divided by the volume of a parameter ball, tends to zero.

In fact the part outside the cone is empty in a sufficiently small ball. Consequently this
comparison does not need local finiteness of surface measure or measurability of the parameter
set. The plane is explicitly the range of `A.normalGraphL`, where `A` is the derivative of the
graphing function. `HasFDerivAt.tangentConeAt_normalGraphEmbedding_image` identifies it with
the classical tangent cone over a neighborhood of the parameter. This is a comparison of cone
conditions, not a density-one theorem or a uniqueness theorem for approximate tangent planes.
The cone condition also holds for differentiability within an arbitrary parameter set.

A function Lipschitz on a Lipschitz normal graph is almost everywhere differentiable within
that graph. Its derivative on the tangent plane is unique and is explicitly identified with
the derivative of its pullback composed with the second projection. Derivative existence
holds over arbitrary parameter sets; the uniqueness and coordinate identities use unique
differentiability at the parameter point. No measurability of the parameter set or ambient
Lipschitz regularity of the function is required.

All surface measures here use the normalized convention `μHE[k]`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangent planes).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §3.1.2 (Rademacher's theorem) and §3.3.4 (surface measure on Lipschitz graphs).
-/

public section

open Filter Metric MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace HasFDerivWithinAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ} {A : E →L[ℝ] ℝ} {x : E}

/-- Differentiability within a parameter set makes the normal graph satisfy the cone condition
about the range of the derivative's linear graph. No surface-measure finiteness, measurability,
or membership of the base point in the parameter set is needed. This includes dimension zero. -/
theorem tendsto_euclideanHausdorffMeasure_normalGraphEmbedding_outside_cone_div
    {s : Set E} (hφ : HasFDerivWithinAt φ A s x) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun r =>
      μHE[Module.finrank ℝ E]
        {z ∈ TauCeti.normalGraphEmbedding φ '' s ∩
            closedBall (TauCeti.normalGraphEmbedding φ x) r |
          ε * dist z (TauCeti.normalGraphEmbedding φ x) <
            infDist (z - TauCeti.normalGraphEmbedding φ x)
              (LinearMap.range A.normalGraphL.toLinearMap : Set (WithLp 2 (ℝ × E)))} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨δ, hδ, hcone⟩ := hφ.exists_pos_forall_infDist_range_normalGraphL_le hε
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
  have hempty :
      {z ∈ TauCeti.normalGraphEmbedding φ '' s ∩
          closedBall (TauCeti.normalGraphEmbedding φ x) r |
        ε * dist z (TauCeti.normalGraphEmbedding φ x) <
          infDist (z - TauCeti.normalGraphEmbedding φ x)
            (LinearMap.range A.normalGraphL.toLinearMap : Set (WithLp 2 (ℝ × E)))} = ∅ := by
    apply eq_empty_of_forall_notMem
    intro z hz
    exact (not_lt_of_ge (hcone z hz.1.1
      ((mem_closedBall.mp hz.1.2).trans_lt hr))) hz.2
  rw [hempty, measure_empty, ENNReal.zero_div]

end HasFDerivWithinAt

/-- The classical tangent plane of a differentiable normal graph satisfies the approximate
tangent-plane cone condition. The parameter set is arbitrary, with no surface-measure
finiteness or measurability hypothesis. This includes dimension zero. -/
theorem HasFDerivAt.tendsto_euclideanHausdorffMeasure_normalGraphEmbedding_outside_cone_div
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ} {A : E →L[ℝ] ℝ} {x : E}
    (hφ : HasFDerivAt φ A x) (s : Set E) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun r =>
      μHE[Module.finrank ℝ E]
        {z ∈ TauCeti.normalGraphEmbedding φ '' s ∩
            closedBall (TauCeti.normalGraphEmbedding φ x) r |
          ε * dist z (TauCeti.normalGraphEmbedding φ x) <
            infDist (z - TauCeti.normalGraphEmbedding φ x)
              (LinearMap.range A.normalGraphL.toLinearMap : Set (WithLp 2 (ℝ × E)))} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r))
      (𝓝[>] 0) (𝓝 0) :=
  hφ.hasFDerivWithinAt.tendsto_euclideanHausdorffMeasure_normalGraphEmbedding_outside_cone_div hε

namespace LipschitzOnWith

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {φ : E → ℝ} {f : WithLp 2 (ℝ × E) → F} {K L : ℝ≥0}

/-- The pullback derivative provides a within-derivative almost everywhere on a Lipschitz
normal graph over an arbitrary parameter set, without a unique-differentiability hypothesis. -/
theorem ae_hasFDerivWithinAt_normalGraphEmbedding_image {s : Set E}
    (hf : LipschitzOnWith L f (TauCeti.normalGraphEmbedding φ '' s))
    (hφ : LipschitzOnWith K φ s) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ TauCeti.normalGraphEmbedding φ '' s →
        HasFDerivWithinAt f
          ((fderivWithin ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s y.snd).comp
            (WithLp.sndL 2 ℝ ℝ E)) (TauCeti.normalGraphEmbedding φ '' s) y := by
  apply (hφ.ae_normalGraphEmbedding_image_iff (μHE[Module.finrank ℝ E] : Measure E)).mpr
  have hp := hf.comp hφ.normalGraphEmbedding (mapsTo_image _ s)
  filter_upwards [hp.ae_differentiableWithinAt_of_mem
    (μ := (μHE[Module.finrank ℝ E] : Measure E))] with x hx hxs
  simpa only [TauCeti.normalGraphEmbedding_snd] using
    (hx hxs).hasFDerivWithinAt.of_comp_normalGraphEmbedding

/-- Rademacher's theorem on a Lipschitz normal graph over an arbitrary parameter set.
Almost everywhere refers to normalized Hausdorff surface measure. -/
theorem ae_differentiableWithinAt_normalGraphEmbedding_image {s : Set E}
    (hf : LipschitzOnWith L f (TauCeti.normalGraphEmbedding φ '' s))
    (hφ : LipschitzOnWith K φ s) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ TauCeti.normalGraphEmbedding φ '' s →
        DifferentiableWithinAt ℝ f (TauCeti.normalGraphEmbedding φ '' s) y := by
  filter_upwards [hf.ae_hasFDerivWithinAt_normalGraphEmbedding_image hφ] with y hy hys
  exact (hy hys).differentiableWithinAt

/-- Almost everywhere, every graph within-derivative pulls back to the parameter derivative
at points where the parameter set has unique derivatives. -/
theorem ae_comp_normalGraphL_eq_normalGraphEmbedding_image {s : Set E}
    (hf : LipschitzOnWith L f (TauCeti.normalGraphEmbedding φ '' s))
    (hφ : LipschitzOnWith K φ s) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ TauCeti.normalGraphEmbedding φ '' s → UniqueDiffWithinAt ℝ s y.snd →
        ∀ M : WithLp 2 (ℝ × E) →L[ℝ] F,
          HasFDerivWithinAt f M (TauCeti.normalGraphEmbedding φ '' s) y →
            M.comp (fderivWithin ℝ φ s y.snd).normalGraphL =
              fderivWithin ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s y.snd := by
  apply (hφ.ae_normalGraphEmbedding_image_iff (μHE[Module.finrank ℝ E] : Measure E)).mpr
  have hp := hf.comp hφ.normalGraphEmbedding (mapsTo_image _ s)
  filter_upwards [hφ.ae_differentiableWithinAt_of_mem
      (μ := (μHE[Module.finrank ℝ E] : Measure E)),
    hp.ae_differentiableWithinAt_of_mem
      (μ := (μHE[Module.finrank ℝ E] : Measure E))] with x hφx hpx hxs hs M hM
  rw [TauCeti.normalGraphEmbedding_snd] at hs ⊢
  exact hM.comp_normalGraphL_eq (hφx hxs).hasFDerivWithinAt (hpx hxs).hasFDerivWithinAt hs

/-- Almost everywhere, graph within-derivatives have the canonical tangent-plane restriction
at points where the parameter set has unique derivatives. -/
theorem ae_comp_subtypeL_eq_normalGraphEmbedding_image {s : Set E}
    (hf : LipschitzOnWith L f (TauCeti.normalGraphEmbedding φ '' s))
    (hφ : LipschitzOnWith K φ s) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ TauCeti.normalGraphEmbedding φ '' s → UniqueDiffWithinAt ℝ s y.snd →
        ∀ M : WithLp 2 (ℝ × E) →L[ℝ] F,
          HasFDerivWithinAt f M (TauCeti.normalGraphEmbedding φ '' s) y →
            M.comp (fderivWithin ℝ φ s y.snd).normalGraphL.range.subtypeL =
              ((fderivWithin ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s y.snd).comp
                (WithLp.sndL 2 ℝ ℝ E)).comp
                  (fderivWithin ℝ φ s y.snd).normalGraphL.range.subtypeL := by
  apply (hφ.ae_normalGraphEmbedding_image_iff (μHE[Module.finrank ℝ E] : Measure E)).mpr
  have hp := hf.comp hφ.normalGraphEmbedding (mapsTo_image _ s)
  filter_upwards [hφ.ae_differentiableWithinAt_of_mem
      (μ := (μHE[Module.finrank ℝ E] : Measure E)),
    hp.ae_differentiableWithinAt_of_mem
      (μ := (μHE[Module.finrank ℝ E] : Measure E))] with x hφx hpx hxs hs M hM
  rw [TauCeti.normalGraphEmbedding_snd] at hs ⊢
  exact hM.comp_subtypeL_normalGraphL_range_eq_of_comp_normalGraphEmbedding
    (hφx hxs).hasFDerivWithinAt (hpx hxs).hasFDerivWithinAt hs

/-- The pullback derivative provides a within-derivative almost everywhere on the full graph. -/
theorem ae_hasFDerivWithinAt_range_normalGraphEmbedding
    (hf : LipschitzOnWith L f (range (TauCeti.normalGraphEmbedding φ)))
    (hφ : LipschitzWith K φ) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ range (TauCeti.normalGraphEmbedding φ) →
        HasFDerivWithinAt f
          ((fderiv ℝ (f ∘ TauCeti.normalGraphEmbedding φ) y.snd).comp
            (WithLp.sndL 2 ℝ ℝ E)) (range (TauCeti.normalGraphEmbedding φ)) y := by
  have hf' : LipschitzOnWith L f (TauCeti.normalGraphEmbedding φ '' univ) := by
    simpa only [image_univ] using hf
  simpa only [image_univ, fderivWithin_univ] using
    hf'.ae_hasFDerivWithinAt_normalGraphEmbedding_image hφ.lipschitzOnWith

/-- Rademacher's theorem within the full Lipschitz normal graph. -/
theorem ae_differentiableWithinAt_range_normalGraphEmbedding
    (hf : LipschitzOnWith L f (range (TauCeti.normalGraphEmbedding φ)))
    (hφ : LipschitzWith K φ) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ range (TauCeti.normalGraphEmbedding φ) →
        DifferentiableWithinAt ℝ f (range (TauCeti.normalGraphEmbedding φ)) y := by
  filter_upwards [hf.ae_hasFDerivWithinAt_range_normalGraphEmbedding hφ] with y hy hys
  exact (hy hys).differentiableWithinAt

/-- Almost everywhere on the full graph, every within-derivative pulls back to the
parameter derivative. -/
theorem ae_comp_normalGraphL_eq_range_normalGraphEmbedding
    (hf : LipschitzOnWith L f (range (TauCeti.normalGraphEmbedding φ)))
    (hφ : LipschitzWith K φ) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ range (TauCeti.normalGraphEmbedding φ) →
        ∀ M : WithLp 2 (ℝ × E) →L[ℝ] F,
          HasFDerivWithinAt f M (range (TauCeti.normalGraphEmbedding φ)) y →
            M.comp (fderiv ℝ φ y.snd).normalGraphL =
              fderiv ℝ (f ∘ TauCeti.normalGraphEmbedding φ) y.snd := by
  have hf' : LipschitzOnWith L f (TauCeti.normalGraphEmbedding φ '' univ) := by
    simpa only [image_univ] using hf
  simpa only [image_univ, fderivWithin_univ, uniqueDiffWithinAt_univ, true_implies] using
    hf'.ae_comp_normalGraphL_eq_normalGraphEmbedding_image hφ.lipschitzOnWith

/-- Almost everywhere on the full graph, every within-derivative has the canonical
restriction to the tangent plane. -/
theorem ae_comp_subtypeL_eq_range_normalGraphEmbedding
    (hf : LipschitzOnWith L f (range (TauCeti.normalGraphEmbedding φ)))
    (hφ : LipschitzWith K φ) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ range (TauCeti.normalGraphEmbedding φ) →
        ∀ M : WithLp 2 (ℝ × E) →L[ℝ] F,
          HasFDerivWithinAt f M (range (TauCeti.normalGraphEmbedding φ)) y →
            M.comp (fderiv ℝ φ y.snd).normalGraphL.range.subtypeL =
              ((fderiv ℝ (f ∘ TauCeti.normalGraphEmbedding φ) y.snd).comp
                (WithLp.sndL 2 ℝ ℝ E)).comp (fderiv ℝ φ y.snd).normalGraphL.range.subtypeL := by
  have hf' : LipschitzOnWith L f (TauCeti.normalGraphEmbedding φ '' univ) := by
    simpa only [image_univ] using hf
  have h := hf'.ae_comp_subtypeL_eq_normalGraphEmbedding_image hφ.lipschitzOnWith
  simp only [image_univ, uniqueDiffWithinAt_univ, true_implies] at h
  filter_upwards [h] with y hy
  rw [fderivWithin_univ (f := φ)] at hy
  simpa only [fderivWithin_univ] using hy

end LipschitzOnWith

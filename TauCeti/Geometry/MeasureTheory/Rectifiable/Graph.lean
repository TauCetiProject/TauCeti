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

Over a finite-dimensional real normed parameter space, a Lipschitz function into a
finite-dimensional real normed space on a Lipschitz normal graph is almost everywhere
differentiable within that graph. Derivative existence holds over arbitrary parameter sets.
The uniqueness and coordinate identities require only finite-dimensionality of the parameter
space and unique differentiability at the parameter point, not Lipschitz regularity of the
function on the graph or finite-dimensionality of its codomain. They identify its tangent-plane
derivative with the derivative of its pullback composed with the second projection.
No measurability of the parameter set or ambient Lipschitz regularity is required.

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
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : E → ℝ} {f : WithLp 2 (ℝ × E) → F} {K L : ℝ≥0}

/-- For a Lipschitz function into a finite-dimensional real normed space on a Lipschitz
normal graph over a finite-dimensional parameter space, the pullback derivative provides a
within-derivative almost everywhere. The parameter set is arbitrary, with no
unique-differentiability hypothesis. -/
theorem ae_hasFDerivWithinAt_normalGraphEmbedding_image [FiniteDimensional ℝ F] {s : Set E}
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
theorem ae_differentiableWithinAt_normalGraphEmbedding_image [FiniteDimensional ℝ F] {s : Set E}
    (hf : LipschitzOnWith L f (TauCeti.normalGraphEmbedding φ '' s))
    (hφ : LipschitzOnWith K φ s) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ TauCeti.normalGraphEmbedding φ '' s →
        DifferentiableWithinAt ℝ f (TauCeti.normalGraphEmbedding φ '' s) y := by
  filter_upwards [hf.ae_hasFDerivWithinAt_normalGraphEmbedding_image hφ] with y hy hys
  exact (hy hys).differentiableWithinAt

/-- Almost everywhere, every graph within-derivative pulls back to the parameter derivative
at points where the parameter set has unique derivatives. -/
theorem ae_comp_normalGraphL_eq_of_hasFDerivWithinAt_normalGraphEmbedding_image {s : Set E}
    (hφ : LipschitzOnWith K φ s) (f : WithLp 2 (ℝ × E) → F) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ TauCeti.normalGraphEmbedding φ '' s → UniqueDiffWithinAt ℝ s y.snd →
        ∀ M : WithLp 2 (ℝ × E) →L[ℝ] F,
          HasFDerivWithinAt f M (TauCeti.normalGraphEmbedding φ '' s) y →
            M.comp (fderivWithin ℝ φ s y.snd).normalGraphL =
              fderivWithin ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s y.snd := by
  apply (hφ.ae_normalGraphEmbedding_image_iff (μHE[Module.finrank ℝ E] : Measure E)).mpr
  filter_upwards [hφ.ae_differentiableWithinAt_of_mem
    (μ := (μHE[Module.finrank ℝ E] : Measure E))] with x hφx hxs hs M hM
  rw [TauCeti.normalGraphEmbedding_snd] at hs ⊢
  exact ((hM.comp x (hφx hxs).hasFDerivWithinAt.normalGraphEmbedding
    (mapsTo_image _ s)).fderivWithin hs).symm

/-- Almost everywhere, graph within-derivatives have the canonical tangent-plane restriction
at points where the parameter set has unique derivatives. -/
theorem ae_comp_subtypeL_eq_of_hasFDerivWithinAt_normalGraphEmbedding_image {s : Set E}
    (hφ : LipschitzOnWith K φ s) (f : WithLp 2 (ℝ × E) → F) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ TauCeti.normalGraphEmbedding φ '' s → UniqueDiffWithinAt ℝ s y.snd →
        ∀ M : WithLp 2 (ℝ × E) →L[ℝ] F,
          HasFDerivWithinAt f M (TauCeti.normalGraphEmbedding φ '' s) y →
            M.comp (fderivWithin ℝ φ s y.snd).normalGraphL.range.subtypeL =
              ((fderivWithin ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s y.snd).comp
                (WithLp.sndL 2 ℝ ℝ E)).comp
                  (fderivWithin ℝ φ s y.snd).normalGraphL.range.subtypeL := by
  filter_upwards [hφ.ae_comp_normalGraphL_eq_of_hasFDerivWithinAt_normalGraphEmbedding_image f]
    with y hy hys hs M hM
  exact (M.comp_subtypeL_range_normalGraphL_eq_iff _ _).mpr (hy hys hs M hM)

/-- Almost everywhere on a Lipschitz graph, the chosen graph derivative pulls back to
the chosen parameter derivative at points with unique parameter derivatives.
No regularity of the function on the graph is required. -/
theorem ae_fderivWithin_normalGraphEmbedding_image_comp_normalGraphL {s : Set E}
    (hφ : LipschitzOnWith K φ s) (f : WithLp 2 (ℝ × E) → F) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ TauCeti.normalGraphEmbedding φ '' s → UniqueDiffWithinAt ℝ s y.snd →
        (fderivWithin ℝ f (TauCeti.normalGraphEmbedding φ '' s) y).comp
          (fderivWithin ℝ φ s y.snd).normalGraphL =
            fderivWithin ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s y.snd := by
  apply (hφ.ae_normalGraphEmbedding_image_iff (μHE[Module.finrank ℝ E] : Measure E)).mpr
  filter_upwards [hφ.ae_differentiableWithinAt_of_mem
    (μ := (μHE[Module.finrank ℝ E] : Measure E))] with x hφx hxs hs
  rw [TauCeti.normalGraphEmbedding_snd] at hs ⊢
  exact (hφx hxs).fderivWithin_normalGraphEmbedding_image_comp_normalGraphL hs

/-- Almost everywhere on a Lipschitz graph, the chosen derivative has the pullback's
canonical tangent-plane restriction at points with unique parameter derivatives. -/
theorem ae_fderivWithin_normalGraphEmbedding_image_comp_subtypeL {s : Set E}
    (hφ : LipschitzOnWith K φ s) (f : WithLp 2 (ℝ × E) → F) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ TauCeti.normalGraphEmbedding φ '' s → UniqueDiffWithinAt ℝ s y.snd →
        (fderivWithin ℝ f (TauCeti.normalGraphEmbedding φ '' s) y).comp
          (fderivWithin ℝ φ s y.snd).normalGraphL.range.subtypeL =
            ((fderivWithin ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s y.snd).comp
              (WithLp.sndL 2 ℝ ℝ E)).comp
                (fderivWithin ℝ φ s y.snd).normalGraphL.range.subtypeL := by
  filter_upwards [hφ.ae_fderivWithin_normalGraphEmbedding_image_comp_normalGraphL f]
    with y hy hys hs
  exact (ContinuousLinearMap.comp_subtypeL_range_normalGraphL_eq_iff _ _ _).mpr (hy hys hs)

/-- For a Lipschitz function into a finite-dimensional real normed space on the full graph of
a Lipschitz function over a finite-dimensional parameter space, the pullback derivative composed
with the second projection provides a within-derivative almost everywhere. -/
theorem ae_hasFDerivWithinAt_range_normalGraphEmbedding [FiniteDimensional ℝ F]
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
theorem ae_differentiableWithinAt_range_normalGraphEmbedding [FiniteDimensional ℝ F]
    (hf : LipschitzOnWith L f (range (TauCeti.normalGraphEmbedding φ)))
    (hφ : LipschitzWith K φ) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ range (TauCeti.normalGraphEmbedding φ) →
        DifferentiableWithinAt ℝ f (range (TauCeti.normalGraphEmbedding φ)) y := by
  filter_upwards [hf.ae_hasFDerivWithinAt_range_normalGraphEmbedding hφ] with y hy hys
  exact (hy hys).differentiableWithinAt

end LipschitzOnWith

namespace LipschitzWith

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : E → ℝ} {K : ℝ≥0}

/-- Almost everywhere on the full graph, every within-derivative pulls back to the
parameter derivative. -/
theorem ae_comp_normalGraphL_eq_of_hasFDerivWithinAt_range_normalGraphEmbedding
    (hφ : LipschitzWith K φ) (f : WithLp 2 (ℝ × E) → F) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ range (TauCeti.normalGraphEmbedding φ) →
        ∀ M : WithLp 2 (ℝ × E) →L[ℝ] F,
          HasFDerivWithinAt f M (range (TauCeti.normalGraphEmbedding φ)) y →
            M.comp (fderiv ℝ φ y.snd).normalGraphL =
              fderiv ℝ (f ∘ TauCeti.normalGraphEmbedding φ) y.snd := by
  simpa only [image_univ, fderivWithin_univ, uniqueDiffWithinAt_univ, true_implies] using
    hφ.lipschitzOnWith.ae_comp_normalGraphL_eq_of_hasFDerivWithinAt_normalGraphEmbedding_image
      (s := univ) f

/-- Almost everywhere on the full graph, every within-derivative has the canonical
restriction to the tangent plane. -/
theorem ae_comp_subtypeL_eq_of_hasFDerivWithinAt_range_normalGraphEmbedding
    (hφ : LipschitzWith K φ) (f : WithLp 2 (ℝ × E) → F) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ range (TauCeti.normalGraphEmbedding φ) →
        ∀ M : WithLp 2 (ℝ × E) →L[ℝ] F,
          HasFDerivWithinAt f M (range (TauCeti.normalGraphEmbedding φ)) y →
            M.comp (fderiv ℝ φ y.snd).normalGraphL.range.subtypeL =
              ((fderiv ℝ (f ∘ TauCeti.normalGraphEmbedding φ) y.snd).comp
                (WithLp.sndL 2 ℝ ℝ E)).comp (fderiv ℝ φ y.snd).normalGraphL.range.subtypeL := by
  filter_upwards [hφ.ae_comp_normalGraphL_eq_of_hasFDerivWithinAt_range_normalGraphEmbedding f]
    with y hy hys M hM
  exact (M.comp_subtypeL_range_normalGraphL_eq_iff _ _).mpr (hy hys M hM)

/-- Almost everywhere on the full Lipschitz graph, the chosen within-derivative pulls back
to the parameter derivative, even for an arbitrary function on the graph. -/
theorem ae_fderivWithin_range_normalGraphEmbedding_comp_normalGraphL
    (hφ : LipschitzWith K φ) (f : WithLp 2 (ℝ × E) → F) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ range (TauCeti.normalGraphEmbedding φ) →
        (fderivWithin ℝ f (range (TauCeti.normalGraphEmbedding φ)) y).comp
          (fderiv ℝ φ y.snd).normalGraphL =
            fderiv ℝ (f ∘ TauCeti.normalGraphEmbedding φ) y.snd := by
  simpa only [image_univ, fderivWithin_univ, uniqueDiffWithinAt_univ, true_implies] using
    hφ.lipschitzOnWith.ae_fderivWithin_normalGraphEmbedding_image_comp_normalGraphL
      (s := univ) f

/-- Almost everywhere on the full Lipschitz graph, the chosen within-derivative has the
canonical tangent-plane restriction. -/
theorem ae_fderivWithin_range_normalGraphEmbedding_comp_subtypeL
    (hφ : LipschitzWith K φ) (f : WithLp 2 (ℝ × E) → F) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ range (TauCeti.normalGraphEmbedding φ) →
        (fderivWithin ℝ f (range (TauCeti.normalGraphEmbedding φ)) y).comp
          (fderiv ℝ φ y.snd).normalGraphL.range.subtypeL =
            ((fderiv ℝ (f ∘ TauCeti.normalGraphEmbedding φ) y.snd).comp
              (WithLp.sndL 2 ℝ ℝ E)).comp (fderiv ℝ φ y.snd).normalGraphL.range.subtypeL := by
  filter_upwards [hφ.ae_fderivWithin_range_normalGraphEmbedding_comp_normalGraphL f]
    with y hy hys
  exact (ContinuousLinearMap.comp_subtypeL_range_normalGraphL_eq_iff _ _ _).mpr (hy hys)

end LipschitzWith

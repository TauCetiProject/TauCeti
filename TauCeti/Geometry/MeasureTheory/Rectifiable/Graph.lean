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
the derivative of its pullback composed with the second projection. These assertions also
hold for graphs over parameter sets with unique derivatives; no measurability of the
parameter set or ambient Lipschitz regularity of the function is required.

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

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {φ : E → ℝ} {f : WithLp 2 (ℝ × E) → F} {K L : ℝ≥0}

/-- An almost-everywhere assertion on a Lipschitz graph is equivalent to its pullback
holding almost everywhere in the parameter set. Neither set need be measurable. -/
theorem ae_normalGraphEmbedding_image_iff {s : Set E} (hφ : LipschitzOnWith K φ s)
    {p : WithLp 2 (ℝ × E) → Prop} :
    (∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ TauCeti.normalGraphEmbedding φ '' s → p y) ↔
      ∀ᵐ x ∂(volume : Measure E), x ∈ s → p (TauCeti.normalGraphEmbedding φ x) := by
  obtain ⟨ψ, hψ, hφψ⟩ := hφ.extend_real
  have hset : {y | ¬(y ∈ TauCeti.normalGraphEmbedding φ '' s → p y)} =
      TauCeti.normalGraphEmbedding φ '' {x | ¬(x ∈ s → p (TauCeti.normalGraphEmbedding φ x))} := by
    ext y
    simp only [mem_ofPred_eq, not_imp, mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hp⟩
      exact ⟨x, ⟨hx, hp⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hp⟩
  have heq : TauCeti.normalGraphEmbedding φ ''
      {x | ¬(x ∈ s → p (TauCeti.normalGraphEmbedding φ x))} =
      TauCeti.normalGraphEmbedding ψ ''
      {x | ¬(x ∈ s → p (TauCeti.normalGraphEmbedding φ x))} := by
    apply image_congr
    intro x hx
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · simpa only [WithLp.ofLp_fst, TauCeti.normalGraphEmbedding_fst] using
        hφψ (not_imp.mp hx).1
    · simp
  rw [ae_iff, ae_iff, hset, heq]
  exact hψ.euclideanHausdorffMeasure_normalGraphEmbedding_image_eq_zero_iff _

/-- Rademacher's theorem on a Lipschitz normal graph over an arbitrary parameter set.
Almost everywhere refers to normalized Hausdorff surface measure. -/
theorem ae_differentiableWithinAt_normalGraphEmbedding_image {s : Set E}
    (hf : LipschitzOnWith L f (TauCeti.normalGraphEmbedding φ '' s))
    (hφ : LipschitzOnWith K φ s) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ TauCeti.normalGraphEmbedding φ '' s →
        DifferentiableWithinAt ℝ f (TauCeti.normalGraphEmbedding φ '' s) y := by
  apply hφ.ae_normalGraphEmbedding_image_iff.mpr
  have hp := hf.comp hφ.normalGraphEmbedding (mapsTo_image _ s)
  filter_upwards [hp.ae_differentiableWithinAt_of_mem] with x hx hxs
  exact (hx hxs).hasFDerivWithinAt.of_comp_normalGraphEmbedding.differentiableWithinAt

/-- On a Lipschitz graph over a set with unique derivatives, the pullback derivative
provides a within-derivative almost everywhere. Every within-derivative has this same
restriction to the tangent plane and pulls back to the parameter derivative. -/
theorem ae_hasFDerivWithinAt_normalGraphEmbedding_image {s : Set E}
    (hf : LipschitzOnWith L f (TauCeti.normalGraphEmbedding φ '' s))
    (hφ : LipschitzOnWith K φ s) (hs : UniqueDiffOn ℝ s) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ TauCeti.normalGraphEmbedding φ '' s →
        DifferentiableWithinAt ℝ φ s y.snd ∧
        DifferentiableWithinAt ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s y.snd ∧
        HasFDerivWithinAt f
          ((fderivWithin ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s y.snd).comp
            (WithLp.sndL 2 ℝ ℝ E)) (TauCeti.normalGraphEmbedding φ '' s) y ∧
        ∀ M : WithLp 2 (ℝ × E) →L[ℝ] F,
          HasFDerivWithinAt f M (TauCeti.normalGraphEmbedding φ '' s) y →
            M.comp (fderivWithin ℝ φ s y.snd).normalGraphL.range.subtypeL =
              ((fderivWithin ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s y.snd).comp
                (WithLp.sndL 2 ℝ ℝ E)).comp
                  (fderivWithin ℝ φ s y.snd).normalGraphL.range.subtypeL ∧
            M.comp (fderivWithin ℝ φ s y.snd).normalGraphL =
              fderivWithin ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s y.snd := by
  apply hφ.ae_normalGraphEmbedding_image_iff.mpr
  have hp := hf.comp hφ.normalGraphEmbedding (mapsTo_image _ s)
  filter_upwards [hφ.ae_differentiableWithinAt_of_mem,
    hp.ae_differentiableWithinAt_of_mem] with x hφx hpx hxs
  rw [TauCeti.normalGraphEmbedding_snd]
  have hA := (hφx hxs).hasFDerivWithinAt
  have hB := (hpx hxs).hasFDerivWithinAt
  refine ⟨hφx hxs, hpx hxs, hB.of_comp_normalGraphEmbedding, ?_⟩
  intro M hM
  exact ⟨hM.comp_subtypeL_normalGraphL_range_eq_of_comp_normalGraphEmbedding hA hB (hs x hxs),
    hM.comp_normalGraphL_eq hA hB (hs x hxs)⟩

/-- On the full Lipschitz graph the tangential derivative is almost everywhere the
pullback derivative composed with the second projection and restricted to the tangent plane.
In particular this restriction is independent of the ambient within-derivative. -/
theorem ae_hasFDerivWithinAt_range_normalGraphEmbedding
    (hf : LipschitzOnWith L f (range (TauCeti.normalGraphEmbedding φ)))
    (hφ : LipschitzWith K φ) :
    ∀ᵐ y ∂(μHE[Module.finrank ℝ E] : Measure (WithLp 2 (ℝ × E))),
      y ∈ range (TauCeti.normalGraphEmbedding φ) →
        DifferentiableAt ℝ φ y.snd ∧
        DifferentiableAt ℝ (f ∘ TauCeti.normalGraphEmbedding φ) y.snd ∧
        HasFDerivWithinAt f
          ((fderiv ℝ (f ∘ TauCeti.normalGraphEmbedding φ) y.snd).comp
            (WithLp.sndL 2 ℝ ℝ E)) (range (TauCeti.normalGraphEmbedding φ)) y ∧
        ∀ M : WithLp 2 (ℝ × E) →L[ℝ] F,
          HasFDerivWithinAt f M (range (TauCeti.normalGraphEmbedding φ)) y →
            M.comp (fderiv ℝ φ y.snd).normalGraphL.range.subtypeL =
              ((fderiv ℝ (f ∘ TauCeti.normalGraphEmbedding φ) y.snd).comp
                (WithLp.sndL 2 ℝ ℝ E)).comp
                  (fderiv ℝ φ y.snd).normalGraphL.range.subtypeL ∧
            M.comp (fderiv ℝ φ y.snd).normalGraphL =
              fderiv ℝ (f ∘ TauCeti.normalGraphEmbedding φ) y.snd := by
  have hf' : LipschitzOnWith L f (TauCeti.normalGraphEmbedding φ '' univ) := by
    simpa only [image_univ] using hf
  have h := hf'.ae_hasFDerivWithinAt_normalGraphEmbedding_image
    hφ.lipschitzOnWith uniqueDiffOn_univ
  simp only [image_univ, differentiableWithinAt_univ, fderivWithin_univ] at h
  filter_upwards [h] with y hy hyrange
  have hy' := hy hyrange
  rw [fderivWithin_univ] at hy'
  exact hy'

end LipschitzOnWith

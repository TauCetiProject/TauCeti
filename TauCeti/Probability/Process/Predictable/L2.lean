/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable.Basic
public import TauCeti.MeasureTheory.Function.L2Space.PiSystem

/-!
# Density of elementary predictable rectangles

The rectangles `(s,t] × A`, with `A ∈ ℱ s`, together with the initial slices `{⊥} × A`,
generate the predictable sigma-algebra for linearly ordered time with a least element and a
countable cofinal sequence. Their indicator functions have dense linear span in real L² for
every measure finite on bounded-time strips of that sigma-algebra. This is
the approximation principle used to extend elementary stochastic integrals by continuity.

The measure is already on the native predictable sigma-algebra: no product-measurability
assumption on an arbitrary representative is implicit. The initial slices are retained, so
the result also applies to measures with mass at the initial time. For Brownian time-product
measures on nonnegative real time those slices are null. Neither Brownian motion nor usual
filtration conditions are needed.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed.,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace MeasureTheory.Filtration

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω}
  {ℱ : Filtration ι mΩ} [(atTop : Filter ι).IsCountablyGenerated]

/-- An integrable predictable function whose integral over every elementary predictable
rectangle vanishes is zero almost everywhere. This holds for arbitrary measures, not just
finite ones, provided the function is integrable. -/
theorem
    _root_.MeasureTheory.Integrable.ae_eq_zero_of_forall_setIntegral_predictableRectangles_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : @Measure (ι × Ω) ℱ.predictable} {f : ι × Ω → E}
    (hf : Integrable f μ)
    (hzero : ∀ R ∈ ℱ.predictableRectangles, ∫ p in R, f p ∂μ = 0) : f =ᵐ[μ] 0 := by
  let : MeasurableSpace (ι × Ω) := ℱ.predictable
  obtain ⟨s, hs, hcover⟩ := ℱ.exists_predictableRectangles_cover
  exact TauCeti.ae_eq_zero_of_forall_setIntegral_eq_zero_of_isPiSystem
    ℱ.generateFrom_predictableRectangles ℱ.isPiSystem_predictableRectangles s hs hcover
    (fun _ ↦ hf.integrableOn) hzero

/-- The indicators of elementary predictable rectangles have dense linear span in real L²
for any measure finite on bounded-time strips of the predictable sigma-algebra. Initial slices
are included; no atomlessness, product-measure form or usual filtration conditions are assumed. -/
theorem dense_span_indicatorConstLp_predictableRectangles
    (ℱ : Filtration ι mΩ) (μ : @Measure (ι × Ω) ℱ.predictable)
    (hμ : ∀ t, μ (Iic t ×ˢ univ) ≠ ⊤) :
    let : MeasurableSpace (ι × Ω) := ℱ.predictable
    Dense (Submodule.span ℝ (range (fun R : ℱ.predictableRectangles ↦
      indicatorConstLp 2 (ℱ.measurableSet_of_mem_predictableRectangles R.property)
        (ℱ.measure_ne_top_of_mem_predictableRectangles μ hμ R.property) (1 : ℝ))) :
      Set (Lp ℝ 2 μ)) := by
  let : MeasurableSpace (ι × Ω) := ℱ.predictable
  obtain ⟨s, hs, hcover⟩ := ℱ.exists_predictableRectangles_cover
  exact μ.dense_span_indicatorConstLp_of_isPiSystem
    ℱ.generateFrom_predictableRectangles ℱ.isPiSystem_predictableRectangles
    (fun _ hR ↦ ℱ.measure_ne_top_of_mem_predictableRectangles μ hμ hR) s hs hcover

/-- For a finite measure, elementary predictable rectangle indicators have dense span in L². -/
theorem dense_span_indicatorConstLp_predictableRectangles_of_isFiniteMeasure
    (ℱ : Filtration ι mΩ) (μ : @Measure (ι × Ω) ℱ.predictable) [IsFiniteMeasure μ] :
    let : MeasurableSpace (ι × Ω) := ℱ.predictable
    Dense (Submodule.span ℝ (range (fun R : ℱ.predictableRectangles ↦
      indicatorConstLp 2 (ℱ.measurableSet_of_mem_predictableRectangles R.property)
        (measure_ne_top μ R) (1 : ℝ))) : Set (Lp ℝ 2 μ)) :=
  ℱ.dense_span_indicatorConstLp_predictableRectangles μ (fun _ ↦ measure_ne_top μ _)

/-- If bounded-time strips have finite measure and the initial slice is null,
positive-time rectangle indicators alone have dense span in real L². -/
theorem dense_span_indicatorConstLp_Ioc_prod (ℱ : Filtration ι mΩ)
    (μ : @Measure (ι × Ω) ℱ.predictable) (hfinite : ∀ t, μ (Iic t ×ˢ univ) ≠ ⊤)
    (hμ : μ ({⊥} ×ˢ (univ : Set Ω)) = 0) :
    let : MeasurableSpace (ι × Ω) := ℱ.predictable
    Dense (Submodule.span ℝ {f : Lp ℝ 2 μ |
      ∃ (s t : ι) (A : Set Ω) (hA : MeasurableSet[ℱ s] A),
        f = indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
          (ℱ.measure_ne_top_of_mem_predictableRectangles μ hfinite
            (ℱ.Ioc_prod_mem_predictableRectangles s t hA)) (1 : ℝ)} : Set (Lp ℝ 2 μ)) := by
  let : MeasurableSpace (ι × Ω) := ℱ.predictable
  refine (ℱ.dense_span_indicatorConstLp_predictableRectangles μ hfinite).mono
    (Submodule.span_le.2 ?_)
  rintro f ⟨⟨R, hR⟩, rfl⟩
  rcases ℱ.mem_predictableRectangles.1 hR with ⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩
  · have hnull : μ ({⊥} ×ˢ A) = 0 := measure_mono_null (prod_mono Subset.rfl (subset_univ A)) hμ
    have hz : indicatorConstLp 2 (measurableSet_predictable_singleton_bot_prod hA)
        (ℱ.measure_ne_top_of_mem_predictableRectangles μ hfinite hR) (1 : ℝ) = 0 := by
      apply Lp.eq_zero_iff_ae_eq_zero.2
      exact indicatorConstLp_coeFn.trans
        (indicator_ae_eq_zero.2 (measure_mono_null inter_subset_left hnull))
    simp only [hz, SetLike.mem_coe]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨s, t, A, hA, rfl⟩

end MeasureTheory.Filtration

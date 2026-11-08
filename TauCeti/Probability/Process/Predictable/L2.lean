/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Predictable
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

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
  (ℱ : Filtration ι mΩ)

/-- Elementary predictable rectangles, including the initial slices. Positive-time rectangles
use information at their left endpoint and are open on the left, closed on the right. -/
def predictableRectangles : Set (Set (ι × Ω)) :=
  {R | (∃ A, MeasurableSet[ℱ ⊥] A ∧ R = {⊥} ×ˢ A) ∨
    ∃ s t A, MeasurableSet[ℱ s] A ∧ R = Ioc s t ×ˢ A}

/-- Membership in the elementary predictable rectangle family. -/
theorem mem_predictableRectangles {R : Set (ι × Ω)} :
    R ∈ ℱ.predictableRectangles ↔
      (∃ A, MeasurableSet[ℱ ⊥] A ∧ R = {⊥} ×ˢ A) ∨
        ∃ s t A, MeasurableSet[ℱ s] A ∧ R = Ioc s t ×ˢ A := Iff.rfl

/-- An initial slice is an elementary predictable rectangle. -/
@[simp]
theorem singleton_bot_prod_mem_predictableRectangles {A : Set Ω}
    (hA : MeasurableSet[ℱ ⊥] A) : {⊥} ×ˢ A ∈ ℱ.predictableRectangles :=
  Or.inl ⟨A, hA, rfl⟩

/-- A bounded-time rectangle using information at its left endpoint is predictable. -/
@[simp]
theorem Ioc_prod_mem_predictableRectangles (s t : ι) {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) : Ioc s t ×ˢ A ∈ ℱ.predictableRectangles :=
  Or.inr ⟨s, t, A, hA, rfl⟩

/-- Every elementary predictable rectangle is predictably measurable. -/
theorem measurableSet_of_mem_predictableRectangles {R : Set (ι × Ω)}
    (hR : R ∈ ℱ.predictableRectangles) : MeasurableSet[ℱ.predictable] R := by
  rcases hR with ⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩
  · exact measurableSet_predictable_singleton_bot_prod hA
  · exact measurableSet_predictable_Ioc_prod s t hA

/-- Elementary predictable rectangles are closed under nonempty intersections. -/
theorem isPiSystem_predictableRectangles : IsPiSystem ℱ.predictableRectangles := by
  rintro R (⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩)
    Q (⟨B, hB, rfl⟩ | ⟨u, v, B, hB, rfl⟩) hne
  · simpa only [prod_inter_prod, inter_self] using
      ℱ.singleton_bot_prod_mem_predictableRectangles (hA.inter hB)
  · obtain ⟨p, hp⟩ := hne
    simp only [mem_inter_iff, mem_prod, mem_singleton_iff, mem_Ioc] at hp
    exact False.elim ((not_lt_of_ge (bot_le : (⊥ : ι) ≤ u)) (by simpa [hp.1.1] using hp.2.1.1))
  · obtain ⟨p, hp⟩ := hne
    simp only [mem_inter_iff, mem_prod, mem_singleton_iff, mem_Ioc] at hp
    exact False.elim ((not_lt_of_ge (bot_le : (⊥ : ι) ≤ s)) (by simpa [hp.2.1] using hp.1.1.1))
  · simpa only [prod_inter_prod, Ioc_inter_Ioc] using
      ℱ.Ioc_prod_mem_predictableRectangles (max s u) (min t v)
        ((ℱ.mono (le_max_left _ _) _ hA).inter (ℱ.mono (le_max_right _ _) _ hB))

/-- Every elementary rectangle has finite measure if bounded-time strips do. -/
theorem measure_ne_top_of_mem_predictableRectangles
    (μ : @Measure (ι × Ω) ℱ.predictable)
    (hμ : ∀ t, μ (Iic t ×ˢ univ) ≠ ⊤) {R : Set (ι × Ω)}
    (hR : R ∈ ℱ.predictableRectangles) : μ R ≠ ⊤ := by
  rcases hR with ⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩
  · exact ne_top_of_le_ne_top (hμ ⊥) (measure_mono (prod_mono
      (singleton_subset_iff.2 self_mem_Iic) (subset_univ A)))
  · exact ne_top_of_le_ne_top (hμ t) (measure_mono (prod_mono
      Ioc_subset_Iic_self (subset_univ A)))

variable [(atTop : Filter ι).IsCountablyGenerated]

/-- Bounded-time elementary rectangles generate the native predictable sigma-algebra. -/
theorem generateFrom_predictableRectangles :
    MeasurableSpace.generateFrom ℱ.predictableRectangles = ℱ.predictable := by
  obtain ⟨u, -, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le fun R hR ↦
      ℱ.measurableSet_of_mem_predictableRectangles hR
  · refine measurableSpace_le_predictable_of_measurableSet (fun A hA ↦ ?_) (fun s A hA ↦ ?_)
    · exact MeasurableSpace.measurableSet_generateFrom
        (ℱ.singleton_bot_prod_mem_predictableRectangles hA)
    · rw [← iUnion_Ioc_eq_Ioi_self_iff.2 (fun x _ ↦
        (exists_le_of_tendsto_atTop hu 0 x).imp fun _ h ↦ h.2), iUnion_prod_const]
      exact MeasurableSet.iUnion fun n ↦ MeasurableSpace.measurableSet_generateFrom
        (ℱ.Ioc_prod_mem_predictableRectangles s (u n) hA)

variable {ℱ}

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
  obtain ⟨u, hmono, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  -- The π-system uniqueness theorem also needs equality on univ. Exhaust time by
  -- increasing bounded rectangles, keeping the initial slice separate.
  have htotal : ∫ p, f p ∂μ = 0 := by
    let U : ℕ → Set (ι × Ω) := fun n ↦ {⊥} ×ˢ univ ∪ Ioc ⊥ (u n) ×ˢ univ
    have hU (n : ℕ) : MeasurableSet (U n) :=
      (measurableSet_predictable_singleton_bot_prod MeasurableSet.univ).union
        (measurableSet_predictable_Ioc_prod _ _ MeasurableSet.univ)
    have hmon : Monotone U := by
      intro i j hij p hp
      rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr ⟨⟨hp.1.1, hp.1.2.trans (hmono hij)⟩, hp.2⟩
    have hcover : ⋃ n, U n = univ := by
      simp only [U, ← union_iUnion, ← iUnion_prod_const]
      rw [iUnion_Ioc_eq_Ioi_self_iff.2 (fun x _ ↦
        (exists_le_of_tendsto_atTop hu 0 x).imp fun _ h ↦ h.2), ← union_prod]
      simp only [← Iic_bot, Iic_union_Ioi, univ_prod_univ]
    have hlim := tendsto_setIntegral_of_monotone hU hmon hf.integrableOn
    rw [hcover, Measure.restrict_univ] at hlim
    have hUn (n : ℕ) : ∫ p in U n, f p ∂μ = 0 := by
      rw [setIntegral_union (by
        apply disjoint_left.2
        rintro p ⟨hp, _⟩ ⟨hq, _⟩
        exact (not_lt_of_ge (bot_le : (⊥ : ι) ≤ p.1)) (hp ▸ hq.1))
        (measurableSet_predictable_Ioc_prod _ _ MeasurableSet.univ)
        hf.integrableOn hf.integrableOn,
        hzero _ (ℱ.singleton_bot_prod_mem_predictableRectangles MeasurableSet.univ),
        hzero _ (ℱ.Ioc_prod_mem_predictableRectangles ⊥ (u n) MeasurableSet.univ), zero_add]
    exact tendsto_nhds_unique hlim (by simpa only [hUn] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : E)) atTop (𝓝 0)))
  have hmeasure : μ.withDensityᵥ f = 0 := by
    refine VectorMeasure.ext_of_generateFrom ℱ.predictableRectangles (fun R hR ↦ ?_)
      ℱ.generateFrom_predictableRectangles.symm ℱ.isPiSystem_predictableRectangles ?_
    · rw [withDensityᵥ_apply hf (ℱ.measurableSet_of_mem_predictableRectangles hR),
        hzero R hR, zero_apply]
    · rw [withDensityᵥ_apply hf MeasurableSet.univ, Measure.restrict_univ, htotal,
        zero_apply]
  exact hf.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ μ)
    (hmeasure.trans withDensityᵥ_zero.symm)

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
  let K := Submodule.span ℝ (range (fun R : ℱ.predictableRectangles ↦
    indicatorConstLp 2 (ℱ.measurableSet_of_mem_predictableRectangles R.property)
      (ℱ.measure_ne_top_of_mem_predictableRectangles μ hμ R.property) (1 : ℝ)))
  apply Submodule.dense_iff_topologicalClosure_eq_top.2
  apply Submodule.orthogonal_eq_bot_iff.1
  rw [Submodule.orthogonal_closure]
  apply eq_bot_iff.2
  intro f hf
  apply (Submodule.mem_bot ℝ).2
  apply Lp.eq_zero_iff_ae_eq_zero.2
  -- Orthogonality gives vanishing integrals on the generating rectangles.
  have hzero (R) (hR : R ∈ ℱ.predictableRectangles) : ∫ p in R, f p ∂μ = 0 := by
    have hi := (K.mem_orthogonal f).1 hf _ (Submodule.subset_span (mem_range_self ⟨R, hR⟩))
    rwa [L2.inner_indicatorConstLp_one] at hi
  -- Localize to finite strips to pass from L² to L¹, apply integral separation
  -- there, and recover almost-everywhere vanishing on their countable union.
  obtain ⟨u, -, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  have hcover : ⋃ n, Iic (u n) ×ˢ (univ : Set Ω) = univ := by
    rw [← iUnion_prod_const]
    have htime : ⋃ n, Iic (u n) = univ := by
      ext t
      simpa only [mem_iUnion, mem_Iic, mem_univ, iff_true] using
        (exists_le_of_tendsto_atTop hu 0 t).imp (fun _ h ↦ h.2)
    rw [htime, univ_prod_univ]
  suffices h : (f : ι × Ω → ℝ) =ᵐ[μ.restrict (⋃ n, Iic (u n) ×ˢ univ)] 0 by
    simpa only [hcover, Measure.restrict_univ] using h
  apply (ae_eq_restrict_iUnion_iff _ _ _).2
  intro n
  have : IsFiniteMeasure (μ.restrict (Iic (u n) ×ˢ (univ : Set Ω))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (hμ (u n)).lt_top⟩
  have hfi := ((Lp.memLp f).restrict (Iic (u n) ×ˢ univ)).integrable (by norm_num)
  refine hfi.ae_eq_zero_of_forall_setIntegral_predictableRectangles_eq_zero ?_
  intro R hR
  rw [Measure.restrict_restrict (ℱ.measurableSet_of_mem_predictableRectangles hR)]
  rcases hR with ⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩
  · have heq : ({⊥} ×ˢ A) ∩ (Iic (u n) ×ˢ univ) = {⊥} ×ˢ A := by
      ext p
      simp only [mem_inter_iff, mem_prod, mem_singleton_iff, mem_Iic, mem_univ, and_true]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h.1 ▸ bot_le⟩⟩
    rw [heq]
    exact hzero _ (ℱ.singleton_bot_prod_mem_predictableRectangles hA)
  · rw [prod_inter_prod, Ioc_inter_Iic, inter_univ]
    exact hzero _ (ℱ.Ioc_prod_mem_predictableRectangles s (min t (u n)) hA)

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

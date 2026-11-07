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

The rectangles `(s,t] × A`, with `A ∈ ℱ s`, together with the initial slices `{0} × A`,
generate the predictable sigma-algebra in nonnegative real time. Their indicator functions
have dense linear span in real L² for every finite measure on that sigma-algebra. This is
the approximation principle used to extend elementary stochastic integrals by continuity.

The measure is already on the native predictable sigma-algebra: no product-measurability
assumption on an arbitrary representative is implicit. The initial slices are retained, so
the result also applies to measures with mass at time zero. For Brownian time-product measures
those slices are null. Neither Brownian motion nor usual filtration conditions are needed.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed.,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace MeasureTheory.Filtration

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ)

/-- Elementary predictable rectangles, including the initial slices. Positive-time rectangles
use information at their left endpoint and are open on the left, closed on the right. -/
def predictableRectangles : Set (Set (ℝ≥0 × Ω)) :=
  {R | (∃ A, MeasurableSet[ℱ 0] A ∧ R = {0} ×ˢ A) ∨
    ∃ s t A, MeasurableSet[ℱ s] A ∧ R = Ioc s t ×ˢ A}

/-- Membership in the elementary predictable rectangle family. -/
@[simp]
theorem mem_predictableRectangles {R : Set (ℝ≥0 × Ω)} :
    R ∈ ℱ.predictableRectangles ↔
      (∃ A, MeasurableSet[ℱ 0] A ∧ R = {0} ×ˢ A) ∨
        ∃ s t A, MeasurableSet[ℱ s] A ∧ R = Ioc s t ×ˢ A := Iff.rfl

/-- Every elementary predictable rectangle is predictably measurable. -/
theorem measurableSet_of_mem_predictableRectangles {R : Set (ℝ≥0 × Ω)}
    (hR : R ∈ ℱ.predictableRectangles) : MeasurableSet[ℱ.predictable] R := by
  rcases hR with ⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩
  · exact measurableSet_predictable_singleton_bot_prod hA
  · exact measurableSet_predictable_Ioc_prod s t hA

/-- Elementary predictable rectangles are closed under nonempty intersections. -/
theorem isPiSystem_predictableRectangles : IsPiSystem ℱ.predictableRectangles := by
  rintro R (⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩)
    Q (⟨B, hB, rfl⟩ | ⟨u, v, B, hB, rfl⟩) hne
  · exact Or.inl ⟨A ∩ B, hA.inter hB, by ext p; simp; tauto⟩
  · obtain ⟨p, hp⟩ := hne
    simp only [mem_inter_iff, mem_prod, mem_singleton_iff, mem_Ioc] at hp
    exact False.elim ((not_lt_of_ge (bot_le : 0 ≤ u)) (by simpa [hp.1.1] using hp.2.1.1))
  · obtain ⟨p, hp⟩ := hne
    simp only [mem_inter_iff, mem_prod, mem_singleton_iff, mem_Ioc] at hp
    exact False.elim ((not_lt_of_ge (bot_le : 0 ≤ s)) (by simpa [hp.2.1] using hp.1.1.1))
  · refine Or.inr ⟨max s u, min t v, A ∩ B,
      (ℱ.mono (le_max_left _ _) _ hA).inter
        (ℱ.mono (le_max_right _ _) _ hB), ?_⟩
    ext p
    simp only [mem_inter_iff, mem_prod, mem_Ioc, max_lt_iff, le_min_iff]
    tauto

/-- Bounded-time elementary rectangles generate the native predictable sigma-algebra. -/
theorem generateFrom_predictableRectangles :
    MeasurableSpace.generateFrom ℱ.predictableRectangles = ℱ.predictable := by
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le fun R hR ↦
      ℱ.measurableSet_of_mem_predictableRectangles hR
  · refine measurableSpace_le_predictable_of_measurableSet (fun A hA ↦ ?_) (fun s A hA ↦ ?_)
    · exact MeasurableSpace.measurableSet_generateFrom (Or.inl ⟨A, hA, rfl⟩)
    · have hcover : Ioi s ×ˢ A = ⋃ n : ℕ, Ioc s (n : ℝ≥0) ×ˢ A := by
        ext p
        simp only [mem_prod, mem_Ioi, mem_iUnion, mem_Ioc]
        constructor
        · rintro ⟨hs, hA⟩
          obtain ⟨n, hn⟩ := exists_nat_ge p.1
          exact ⟨n, ⟨hs, hn⟩, hA⟩
        · rintro ⟨n, ⟨hs, _⟩, hA⟩
          exact ⟨hs, hA⟩
      rw [hcover]
      exact MeasurableSet.iUnion fun n ↦
        MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨s, n, A, hA, rfl⟩)

variable {ℱ}

/-- An integrable predictable function whose integral over every elementary predictable
rectangle vanishes is zero almost everywhere. This holds for arbitrary measures, not just
finite ones, provided the function is integrable. -/
theorem _root_.MeasureTheory.Integrable.ae_eq_zero_of_forall_predictableRectangle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : @Measure (ℝ≥0 × Ω) ℱ.predictable} {f : ℝ≥0 × Ω → E}
    (hf : Integrable f μ)
    (hzero : ∀ R ∈ ℱ.predictableRectangles, ∫ p in R, f p ∂μ = 0) : f =ᵐ[μ] 0 := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have htotal : ∫ p, f p ∂μ = 0 := by
    let U : ℕ → Set (ℝ≥0 × Ω) := fun n ↦ {0} ×ˢ univ ∪ Ioc 0 (n : ℝ≥0) ×ˢ univ
    have hU (n : ℕ) : MeasurableSet (U n) :=
      (measurableSet_predictable_singleton_bot_prod MeasurableSet.univ).union
        (measurableSet_predictable_Ioc_prod _ _ MeasurableSet.univ)
    have hmon : Monotone U := by
      intro i j hij p hp
      rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr ⟨⟨hp.1.1, hp.1.2.trans (Nat.cast_le.2 hij)⟩, hp.2⟩
    have hcover : ⋃ n, U n = univ := by
      ext p
      simp only [mem_iUnion, mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_ge p.1
      refine ⟨n, ?_⟩
      rcases eq_or_lt_of_le (bot_le : 0 ≤ p.1) with h | h
      · exact Or.inl ⟨h.symm, mem_univ _⟩
      · exact Or.inr ⟨⟨h, hn⟩, mem_univ _⟩
    have hlim := tendsto_setIntegral_of_monotone hU hmon hf.integrableOn
    rw [hcover, Measure.restrict_univ] at hlim
    have hUn (n : ℕ) : ∫ p in U n, f p ∂μ = 0 := by
      rw [setIntegral_union (by
        apply disjoint_left.2
        rintro p ⟨hp, _⟩ ⟨hq, _⟩
        exact (not_lt_of_ge (bot_le : 0 ≤ p.1)) (hp ▸ hq.1))
        (measurableSet_predictable_Ioc_prod _ _ MeasurableSet.univ)
        hf.integrableOn hf.integrableOn,
        hzero _ (Or.inl ⟨univ, MeasurableSet.univ, rfl⟩),
        hzero _ (Or.inr ⟨0, n, univ, MeasurableSet.univ, rfl⟩), zero_add]
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
for any finite measure on the predictable sigma-algebra. Initial slices are included; no
atomlessness, product-measure form or usual filtration conditions are assumed. -/
theorem dense_span_indicatorConstLp_predictableRectangles
    (ℱ : Filtration ℝ≥0 mΩ) (μ : @Measure (ℝ≥0 × Ω) ℱ.predictable)
    [IsFiniteMeasure μ] :
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    Dense (Submodule.span ℝ (range (fun R : ℱ.predictableRectangles ↦
      indicatorConstLp 2 (ℱ.measurableSet_of_mem_predictableRectangles R.property)
        (measure_ne_top μ R) (1 : ℝ))) : Set (Lp ℝ 2 μ)) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let K := Submodule.span ℝ (range (fun R : ℱ.predictableRectangles ↦
    indicatorConstLp 2 (ℱ.measurableSet_of_mem_predictableRectangles R.property)
      (measure_ne_top μ R) (1 : ℝ)))
  apply Submodule.dense_iff_topologicalClosure_eq_top.2
  apply Submodule.orthogonal_eq_bot_iff.1
  rw [Submodule.orthogonal_closure]
  apply eq_bot_iff.2
  intro f hf
  apply (Submodule.mem_bot ℝ).2
  apply Lp.eq_zero_iff_ae_eq_zero.2
  refine ((Lp.memLp f).integrable (by norm_num)).ae_eq_zero_of_forall_predictableRectangle ?_
  intro R hR
  have hi := (K.mem_orthogonal f).1 hf _ (Submodule.subset_span (mem_range_self ⟨R, hR⟩))
  rwa [L2.inner_indicatorConstLp_one] at hi

/-- If the initial slice is null, positive-time rectangle indicators alone have dense span.
In particular, stochastic integration against Brownian motion needs no initial-slice term. -/
theorem dense_span_indicatorConstLp_Ioc_prod (ℱ : Filtration ℝ≥0 mΩ)
    (μ : @Measure (ℝ≥0 × Ω) ℱ.predictable) [IsFiniteMeasure μ]
    (hμ : μ ({0} ×ˢ (univ : Set Ω)) = 0) :
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    Dense (Submodule.span ℝ {f : Lp ℝ 2 μ |
      ∃ (s t : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[ℱ s] A),
        f = indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
          (measure_ne_top μ _) (1 : ℝ)} : Set (Lp ℝ 2 μ)) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  refine (ℱ.dense_span_indicatorConstLp_predictableRectangles μ).mono (Submodule.span_le.2 ?_)
  rintro f ⟨⟨R, hR⟩, rfl⟩
  rcases ℱ.mem_predictableRectangles.1 hR with ⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩
  · have hnull : μ ({0} ×ˢ A) = 0 := measure_mono_null (prod_mono Subset.rfl (subset_univ A)) hμ
    have hz : indicatorConstLp 2 (measurableSet_predictable_singleton_bot_prod hA)
        (measure_ne_top μ _) (1 : ℝ) = 0 := by
      apply norm_eq_zero.1
      rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
      simp [Measure.real, hnull]
    simp only [hz, SetLike.mem_coe]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨s, t, A, hA, rfl⟩

end MeasureTheory.Filtration

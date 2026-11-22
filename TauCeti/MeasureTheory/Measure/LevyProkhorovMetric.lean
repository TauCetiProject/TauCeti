/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Lévy–Prokhorov distance of pushforwards, and subsequences of finite measures

Mathlib's `MeasureTheory.left_measure_le_of_levyProkhorovEDist_lt` compares the masses of a set and
of its thickening under two measures on the same space. This file restates it for the images
`μ.map T` and `ν.map S` of measures on two measurable spaces `X` and `Y` under a.e.-measurable maps
into a common extended pseudometric space `Z`, in terms of sets of `X` and `Y`.

## Main declarations

* `TauCeti.measure_le_of_levyProkhorovEDist_map_lt`: if `d_LP (T_# μ, S_# ν) < δ`, then
  `μ A ≤ ν {y | ∃ x ∈ A, edist (T x) (S y) < δ} + δ` for every set `A ⊆ X`, measurable or not.
* `MeasureTheory.Measure.levyProkhorovEDist_map_le_of_edist_le`: if an a.e.-measurable self-map
  moves almost every point by at most `δ`, then the Lévy–Prokhorov distance from a measure to its
  pushforward is at most `δ`.
* `MeasureTheory.FiniteMeasure.tendsto_subseq_of_mapClusterPt`: on a separable pseudo-metrizable
  space, a cluster point of a sequence of finite measures is the limit of a subsequence.

Mathlib's Lévy–Prokhorov metrization makes `ProbabilityMeasure X` pseudo-metrizable when `X` is
separable and pseudo-metrizable, but gives no first-countability instance for `FiniteMeasure X`.
A finite measure is determined by its mass and, away from zero, by its normalization, so cluster
points of sequences of finite measures are still subsequential limits.
-/

public section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace TauCeti

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [PseudoEMetricSpace Z]
  [MeasurableSpace Z] [OpensMeasurableSpace Z] {μ : Measure X} {ν : Measure Y} {δ : ℝ≥0∞}

/-- A Lévy–Prokhorov bound between images of `μ` and `ν` in a common space `Z` moves every set
`A ⊆ X` into the points of `Y` whose image is close to the image of `A`. -/
theorem measure_le_of_levyProkhorovEDist_map_lt {T : X → Z} {S : Y → Z}
    (hT : AEMeasurable T μ) (hS : AEMeasurable S ν)
    (h : levyProkhorovEDist (μ.map T) (ν.map S) < δ) (A : Set X) :
    μ A ≤ ν {y | ∃ x ∈ A, edist (T x) (S y) < δ} + δ := by
  rcases eq_or_ne δ ∞ with rfl | hδ
  · exact le_top.trans_eq (add_top _).symm
  calc μ A ≤ μ.map T (closure (T '' A)) :=
        (Measure.le_map_apply_image hT A).trans (measure_mono subset_closure)
    _ ≤ ν.map S (thickening δ.toReal (closure (T '' A))) + δ :=
        left_measure_le_of_levyProkhorovEDist_lt h isClosed_closure.measurableSet
    _ = ν (S ⁻¹' thickening δ.toReal (T '' A)) + δ := by
        rw [thickening_closure, Measure.map_apply_of_aemeasurable hS
          isOpen_thickening.measurableSet]
    _ ≤ ν {y | ∃ x ∈ A, edist (T x) (S y) < δ} + δ := by
        refine add_le_add_left (measure_mono fun y hy ↦ ?_) _
        rw [mem_preimage, mem_thickening_iff_exists_edist_lt] at hy
        obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := hy
        rw [edist_comm, ENNReal.ofReal_toReal hδ] at hxy
        exact ⟨x, hx, hxy⟩

end TauCeti

namespace MeasureTheory.Measure

/-- If an almost-everywhere measurable map moves almost every point by at most `δ`, then its
pushforward is at most `δ` away in the Lévy--Prokhorov extended distance. -/
theorem levyProkhorovEDist_map_le_of_edist_le
    {Z : Type*} [PseudoEMetricSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ρ : Measure Z) {F : Z → Z} (hF : AEMeasurable F ρ)
    {δ : ℝ≥0∞} (hδ : ∀ᵐ z ∂ρ, edist z (F z) ≤ δ) :
    levyProkhorovEDist ρ (ρ.map F) ≤ δ := by
  refine levyProkhorovEDist_le_of_forall _ _ _ fun ε B hδε hε hB => ?_
  have hmem : ∀ᵐ z ∂ρ, (z ∈ B → F z ∈ Metric.thickening ε.toReal B) ∧
      (F z ∈ B → z ∈ Metric.thickening ε.toReal B) := by
    filter_upwards [hδ] with z hz
    have hlt : edist z (F z) < ENNReal.ofReal ε.toReal := by
      rw [ENNReal.ofReal_toReal hε.ne]
      exact hz.trans_lt hδε
    exact ⟨fun h ↦ (Metric.mem_thickening_iff_exists_edist_lt _ _).mpr ⟨z, h, by rwa [edist_comm]⟩,
      fun h ↦ (Metric.mem_thickening_iff_exists_edist_lt _ _).mpr ⟨F z, h, hlt⟩⟩
  have hU : MeasurableSet (Metric.thickening ε.toReal B) := Metric.isOpen_thickening.measurableSet
  constructor
  · rw [Measure.map_apply_of_aemeasurable hF hU]
    exact (measure_mono_ae (by filter_upwards [hmem] with z hz h using hz.1 h)).trans le_self_add
  · rw [Measure.map_apply_of_aemeasurable hF hB]
    exact (measure_mono_ae (by filter_upwards [hmem] with z hz h using hz.2 h)).trans le_self_add

end MeasureTheory.Measure

namespace MeasureTheory.FiniteMeasure

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace.SeparableSpace X]

/-- On a separable pseudo-metrizable space, a cluster point of a sequence of finite measures is
the weak limit of a subsequence. The space of finite measures need not be first countable here:
the subsequence is extracted from the masses and the normalizations, which live in
pseudo-metrizable spaces. -/
theorem tendsto_subseq_of_mapClusterPt {μs : ℕ → FiniteMeasure X} {μ : FiniteMeasure X}
    (h : MapClusterPt μ atTop μs) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  by_cases hzero : μ = 0
  · -- At zero, convergence of the mass alone controls every bounded test function.
    subst hzero
    obtain ⟨φ, hφ, hlim⟩ := (h.continuousAt_comp continuous_mass.continuousAt).tendsto_subseq
    exact ⟨φ, hφ, tendsto_zero_of_tendsto_zero_mass <| by
      simpa only [zero_mass, Function.comp_def] using hlim⟩
  · -- Away from zero, mass and normalized probability determine weak convergence.
    -- Normalization needs `X` nonempty; on an empty space every measure is zero.
    have : Nonempty X := not_isEmpty_iff.mp fun _ ↦ hzero <| toMeasure_injective <| by
      rw [toMeasure_zero]
      exact Measure.eq_zero_of_isEmpty _
    have hpair : ContinuousAt (fun ν : FiniteMeasure X ↦ (ν.mass, ν.normalize)) μ :=
      continuous_mass.continuousAt.prodMk_nhds (tendsto_normalize_of_tendsto tendsto_id hzero)
    obtain ⟨φ, hφ, hlim⟩ := (h.continuousAt_comp hpair).tendsto_subseq
    exact ⟨φ, hφ, tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass hlim.snd_nhds
      hlim.fst_nhds⟩

end MeasureTheory.FiniteMeasure

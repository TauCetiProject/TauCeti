/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Lusin's theorem

A measurable map from a weakly regular measure space into a second-countable topological space is
continuous off a set of arbitrarily small measure: for every measurable set `s` of finite measure
and every `ε > 0` there is a closed set `F ⊆ s` with `μ (s \ F) < ε` on which the map is
continuous. This is **Lusin's theorem**. Its usual formulation with a compact set is the closed
one followed by inner regularity by compact sets, and its usual hypothesis, a finite Borel measure
on a Polish or metrizable space, is one of the regimes in which measures are weakly regular
(Mathlib's `MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure`);
for such a measure the whole space is an admissible `s`, and `μ (Set.univ \ F)` is `μ Fᶜ`.

The proof approximates `s` itself, the part of `s` mapped into each member of a countable basis of
the target, and the part of `s` mapped into its complement, from inside by closed sets, and
intersects the resulting unions; on the intersection every basic preimage is relatively open. For
an almost-everywhere measurable map, the set `s` is first shrunk by the null set on which the map
differs from a measurable one.

The theorem is the bridge from measurability to topology in arguments about weak convergence of
measures: it lets a Borel map be treated as a continuous one on a closed set carrying almost all
of the mass, so that the portmanteau theorem, which only sees closed and open sets, applies to
sets defined through the map. The almost-everywhere measurable version is included because the
maps produced by `ProbabilityTheory.HasLaw` are only almost-everywhere measurable.

## Main statements

* `Measurable.exists_isClosed_measure_sdiff_lt_continuousOn` — **Lusin's theorem**: a measurable
  map into a second-countable space is continuous on a closed subset of any measurable set `s` of
  finite measure whose complement in `s` has measure less than any prescribed `ε > 0`;
* `AEMeasurable.exists_isClosed_measure_sdiff_lt_continuousOn` — the same for an
  almost-everywhere measurable map.

## References

* W. Rudin, *Real and Complex Analysis*, third edition, McGraw-Hill 1987, Theorem 2.24, the
  classical statement for locally compact Hausdorff spaces.
* D. H. Fremlin, *Measure Theory*, Volume 4, Torres Fremlin 2003, §418, Lusin's theorem for
  measurable functions into second-countable spaces from the inner regularity of the measure.
-/

public section

open MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  {μ : Measure X} [μ.WeaklyRegular] {f : X → Y} {s : Set X} {ε : ℝ≥0∞}

/-- **Lusin's theorem.** A measurable map `f` from a weakly regular measure space into a
second-countable topological space is continuous on a closed set `F ⊆ s` with `μ (s \ F) < ε`,
for every measurable set `s` of finite measure and every `ε > 0`. -/
theorem _root_.Measurable.exists_isClosed_measure_sdiff_lt_continuousOn (hf : Measurable f)
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (hε : ε ≠ 0) :
    ∃ F ⊆ s, IsClosed F ∧ μ (s \ F) < ε ∧ ContinuousOn f F := by
  set B := TopologicalSpace.countableBasis Y
  have : Countable B := (TopologicalSpace.countable_countableBasis Y).to_subtype
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε2 B
  have hδ2 : ∀ U : B, δ U / 2 ≠ 0 := fun U ↦ (ENNReal.half_pos (hδ U).ne').ne'
  have hU : ∀ U : B, MeasurableSet (f ⁻¹' U) := fun U ↦
    hf (TopologicalSpace.isOpen_of_mem_countableBasis U.2).measurableSet
  have hne : ∀ t, t ⊆ s → μ t ≠ ∞ := fun t ht ↦ ne_top_of_le_ne_top hμs (measure_mono ht)
  obtain ⟨K, hKs, hKclosed, hKμ⟩ := hs.exists_isClosed_sdiff_lt hμs hε2
  choose F hFsub hFclosed hFμ using fun U : B ↦
    (hs.inter (hU U)).exists_isClosed_sdiff_lt (hne _ inter_subset_left) (hδ2 U)
  choose G hGsub hGclosed hGμ using fun U : B ↦
    (hs.diff (hU U)).exists_isClosed_sdiff_lt (hne _ sdiff_subset) (hδ2 U)
  refine ⟨K ∩ ⋂ U, F U ∪ G U, inter_subset_left.trans hKs,
    hKclosed.inter (isClosed_iInter fun U ↦ (hFclosed U).union (hGclosed U)), ?_, ?_⟩
  · calc μ (s \ (K ∩ ⋂ U, F U ∪ G U))
        = μ ((s \ K) ∪ ⋃ U, s \ (F U ∪ G U)) := by rw [sdiff_inter, sdiff_iInter]
      _ ≤ μ (s \ K) + μ (⋃ U, s \ (F U ∪ G U)) := measure_union_le _ _
      _ ≤ μ (s \ K) + ∑' U, μ (s \ (F U ∪ G U)) := add_le_add_right (measure_iUnion_le _) _
      _ ≤ μ (s \ K) + ∑' U, δ U := add_le_add_right (ENNReal.tsum_le_tsum fun U ↦ ?_) _
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hKμ hδε
      _ = ε := ENNReal.add_halves ε
    have hsub : s \ (F U ∪ G U) ⊆ ((s ∩ f ⁻¹' U) \ F U) ∪ ((s \ f ⁻¹' U) \ G U) := fun x hx ↦ by
      simp only [mem_sdiff, mem_union, not_or] at hx
      by_cases hxU : x ∈ f ⁻¹' U
      · exact Or.inl ⟨⟨hx.1, hxU⟩, hx.2.1⟩
      · exact Or.inr ⟨⟨hx.1, hxU⟩, hx.2.2⟩
    calc μ (s \ (F U ∪ G U))
        ≤ μ ((s ∩ f ⁻¹' U) \ F U) + μ ((s \ f ⁻¹' U) \ G U) :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ δ U / 2 + δ U / 2 := add_le_add (hFμ U).le (hGμ U).le
      _ = δ U := ENNReal.add_halves _
  · refine (TopologicalSpace.isBasis_countableBasis Y).continuousOn_iff.2 fun U hU ↦
      ⟨(G ⟨U, hU⟩)ᶜ, (hGclosed _).isOpen_compl, ?_⟩
    ext x
    refine and_congr_left fun hx ↦ ⟨fun hxU hxG ↦ (hGsub ⟨U, hU⟩ hxG).2 hxU, fun hxG ↦ ?_⟩
    rcases mem_iInter.1 hx.2 ⟨U, hU⟩ with hxF | hxG'
    · exact (hFsub ⟨U, hU⟩ hxF).2
    · exact absurd hxG' hxG

/-- **Lusin's theorem** for an almost-everywhere measurable map: it is continuous on a closed set
`F ⊆ s` with `μ (s \ F) < ε`, for every measurable set `s` of finite measure and every
`ε > 0`. -/
theorem _root_.AEMeasurable.exists_isClosed_measure_sdiff_lt_continuousOn (hf : AEMeasurable f μ)
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (hε : ε ≠ 0) :
    ∃ F ⊆ s, IsClosed F ∧ μ (s \ F) < ε ∧ ContinuousOn f F := by
  set N := toMeasurable μ {x | f x ≠ hf.mk f x} with hN
  have hNμ : μ N = 0 := by rw [hN, measure_toMeasurable]; exact ae_iff.1 hf.ae_eq_mk
  obtain ⟨F, hFs, hF, hFμ, hFf⟩ := hf.measurable_mk.exists_isClosed_measure_sdiff_lt_continuousOn
    (hs.diff (measurableSet_toMeasurable μ _)) (ne_top_of_le_ne_top hμs (measure_mono sdiff_subset))
    hε
  refine ⟨F, hFs.trans sdiff_subset, hF, ?_, ?_⟩
  · rwa [Set.sdiff_sdiff_comm, measure_sdiff_null hNμ] at hFμ
  · refine hFf.congr fun x hx ↦ ?_
    have hxN : x ∉ N := (hFs hx).2
    by_contra hne
    exact hxN (subset_toMeasurable μ _ hne)

end TauCeti

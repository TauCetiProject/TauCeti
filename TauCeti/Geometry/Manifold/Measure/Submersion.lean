/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Submersion
public import TauCeti.Geometry.Manifold.Measure
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph
import TauCeti.MeasureTheory.Measure.Haar.Submersion

/-!
# Null preimages under submersions of manifolds

Let `M'` and `M` be boundaryless manifolds modelled on finite-dimensional real normed spaces `E'`
and `E`. A map `θ : M' → M` that is a `C¹` submersion at every point of a set `A` pulls null sets
of `M` back to sets whose intersection with `A` is null in `M'`
(`TauCeti.IsNullSet.preimage_inter_of_isSubmersionAt`), and a `C¹` submersion pulls null sets
back to null sets (`TauCeti.IsNullSet.preimage_of_isSubmersion`). The dimensions of `M'` and `M`
may differ, and `θ` need not be injective or proper. No measurable structure on `M'` or `M` is
used. Thus a property holding off a null set of `M` holds, after composing with `θ`, off a null
set of `M'`.

In the extended charts at `z ∈ M'` and `y ∈ M` the map reads as
`extChartAt y ∘ θ ∘ (extChartAt z).symm`, which is again a submersion, the charts being local
diffeomorphisms. Its preimages of Haar-null sets are therefore Haar-null on the set where it is a
submersion (`TauCeti.addHaar_preimage_inter_eq_zero_of_isSubmersionAt`), and countably many
target charts cover the chart image of `A`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 6 (sets of measure zero in manifolds).
-/

public section

open MeasureTheory Set Function Manifold
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E' E M' M : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M'] [ChartedSpace E' M'] [TopologicalSpace M] [ChartedSpace E M]
  {n : WithTop ℕ∞} [IsManifold 𝓘(ℝ, E') n M'] [IsManifold 𝓘(ℝ, E) n M]
  {θ : M' → M} {A : Set M'} {s : Set M}

omit [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] [MeasurableSpace E]
  [BorelSpace E] in
/-- A submersion read in extended charts at arbitrary base points `z` and `y` is a submersion at
the chart image of every point `p` of the source chart with `θ p` in the target chart. -/
private theorem isSubmersionAt_extChartAt_comp_comp_symm {z p : M'} {y : M}
    (hp : p ∈ (extChartAt 𝓘(ℝ, E') z).source) (hθp : θ p ∈ (extChartAt 𝓘(ℝ, E) y).source)
    (hθ : IsSubmersionAt 𝓘(ℝ, E') 𝓘(ℝ, E) n θ p) :
    IsSubmersionAt 𝓘(ℝ, E') 𝓘(ℝ, E) n
      (extChartAt 𝓘(ℝ, E) y ∘ θ ∘ (extChartAt 𝓘(ℝ, E') z).symm) (extChartAt 𝓘(ℝ, E') z p) := by
  set e := extChartAt 𝓘(ℝ, E') z
  -- Both extended charts are local diffeomorphisms, since the models have no boundary.
  have hsymm : IsLocalDiffeomorphAt 𝓘(ℝ, E') 𝓘(ℝ, E') n e.symm (e p) :=
    isLocalDiffeomorphAt_extChartAt_symm <| by
      rw [(isOpen_extChartAt_target z).interior_eq]; exact e.map_source hp
  have hchart : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) n (extChartAt 𝓘(ℝ, E) y) (θ p) :=
    isLocalDiffeomorphAt_extChartAt hθp <| by
      rw [(isOpen_extChartAt_target y).interior_eq]; exact (extChartAt 𝓘(ℝ, E) y).map_source hθp
  have hθe : θ p = (θ ∘ e.symm) (e p) := by rw [comp_apply, e.left_inv hp]
  refine (hθe ▸ hchart).comp_isSubmersionAt ?_
  rw [hsymm.isSubmersionAt_comp_iff, e.left_inv hp]
  exact hθ

/-- **Submersions pull back null sets.** If `θ : M' → M` is a `C¹` submersion at every point of
`A`, then the preimage of a null set of `M` meets `A` in a null set of `M'`. -/
theorem IsNullSet.preimage_inter_of_isSubmersionAt (hs : IsNullSet 𝓘(ℝ, E) s)
    (hθ : ∀ x ∈ A, IsSubmersionAt 𝓘(ℝ, E') 𝓘(ℝ, E) n θ x) (hn : 1 ≤ n) :
    IsNullSet 𝓘(ℝ, E') (θ ⁻¹' s ∩ A) := by
  refine (isNullSet_iff _ _).2 fun z ν _ ↦ ?_
  rcases A.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  -- The target model is finite-dimensional, as a quotient of the source model.
  have : FiniteDimensional ℝ E :=
    Module.Finite.of_surjective ((LinearMap.fst ℝ E _).comp (hθ x hx).equiv.toLinearMap)
      fun y ↦ ⟨(hθ x hx).equiv.symm (y, 0), by simp⟩
  set e := extChartAt 𝓘(ℝ, E') z
  -- The chart images of the points of `A` seen by the target chart at `y`.
  let S : Set E' := e '' (A ∩ e.source)
  let V : M → Set E' := fun y ↦ e.target ∩ e.symm ⁻¹' (θ ⁻¹' (extChartAt 𝓘(ℝ, E) y).source)
  have hV : ∀ w ∈ S, V (θ (e.symm w)) ∈ 𝓝[S] w := by
    rintro _ ⟨p, ⟨hpA, hpe⟩, rfl⟩
    rw [e.left_inv hpe]
    refine mem_nhdsWithin_of_mem_nhds (Filter.inter_mem ((isOpen_extChartAt_target z).mem_nhds
      (e.map_source hpe)) ?_)
    have hc : ContinuousAt (θ ∘ e.symm) (e p) :=
      (hθ p hpA).contMDiffAt.continuousAt.comp_of_eq (continuousAt_extChartAt_symm' hpe)
        (e.left_inv hpe)
    rw [← preimage_comp]
    refine hc.preimage_mem_nhds ?_
    rw [comp_apply, e.left_inv hpe]
    exact extChartAt_source_mem_nhds (θ p)
  obtain ⟨t, -, htc, hSt⟩ := TopologicalSpace.countable_cover_nhdsWithin hV
  -- The coordinate expression of `θ` in the charts at `z` and `y`.
  let Θ : M → E' → E := fun y ↦ extChartAt 𝓘(ℝ, E) y ∘ θ ∘ e.symm
  have hΘ : ∀ y, ∀ w ∈ S ∩ V y, IsSubmersionAt 𝓘(ℝ, E') 𝓘(ℝ, E) n (Θ y) w := by
    rintro y _ ⟨⟨p, ⟨hpA, hpe⟩, rfl⟩, -, hpy⟩
    rw [mem_preimage, mem_preimage, e.left_inv hpe] at hpy
    exact isSubmersionAt_extChartAt_comp_comp_symm hpe hpy (hθ p hpA)
  -- Each chart image of `s` is null, so each piece of the cover is null.
  have hpiece : ∀ y, ν ((Θ y) ⁻¹' (extChartAt 𝓘(ℝ, E) y '' (s ∩ (extChartAt 𝓘(ℝ, E) y).source))
      ∩ (S ∩ V y)) = 0 := fun y ↦
    addHaar_preimage_inter_eq_zero_of_isSubmersionAt (μ := Measure.addHaar) (hΘ y) hn
      (hs.chartwise y _)
  refine measure_mono_null ?_ ((measure_biUnion_null_iff htc).2 fun w _ ↦ hpiece (θ (e.symm w)))
  rintro _ ⟨p, ⟨⟨hps, hpA⟩, hpe⟩, rfl⟩
  obtain ⟨w, hwt, hpw⟩ := mem_iUnion₂.1 (hSt ⟨p, ⟨hpA, hpe⟩, rfl⟩)
  refine mem_iUnion₂.2 ⟨w, hwt, ⟨⟨θ p, ⟨hps, ?_⟩, ?_⟩, ⟨p, ⟨hpA, hpe⟩, rfl⟩, hpw⟩⟩
  · simpa [V, e.left_inv hpe] using hpw.2
  · simp [Θ, e.left_inv hpe]

/-- **Submersions pull back null sets.** The preimage of a null set of `M` under a `C¹`
submersion `θ : M' → M` is a null set of `M'`. -/
theorem IsNullSet.preimage_of_isSubmersion (hs : IsNullSet 𝓘(ℝ, E) s)
    (hθ : IsSubmersion 𝓘(ℝ, E') 𝓘(ℝ, E) n θ) (hn : 1 ≤ n) :
    IsNullSet 𝓘(ℝ, E') (θ ⁻¹' s) := by
  simpa using hs.preimage_inter_of_isSubmersionAt (A := univ) (fun x _ ↦ hθ.isSubmersionAt x) hn

end TauCeti

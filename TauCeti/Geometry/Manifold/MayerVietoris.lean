/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import TauCeti.Topology.MayerVietoris

/-!
# Mayer–Vietoris induction over convex chart domains

The Mayer–Vietoris induction principle `TauCeti.mayerVietoris_induction` needs a basis of the
topology that is closed under finite intersections. On a charted space `M` over a model with
corners `I : ModelWithCorners 𝕜 E H`, the natural sets on which a comparison map can be checked
directly are the *convex chart domains*

`U = (chartAt H x).source ∩ (extChartAt I x)⁻¹' C`,

for a point `x`, a convex open set `C ⊆ E` and `C ∩ range I ⊆ (extChartAt I x).target`. The
extended chart at `x` maps such a `U` bijectively onto `C ∩ range I`, which is convex because
`range I` is (`ModelWithCorners.convex_range`), so for instance it contracts onto any of its
points along straight lines in the chart. These sets do not form an intersection-stable
family, since the intersection of convex domains in two different charts need not be convex in
either chart.

This file proves the induction principle with only these sets as base cases, in two steps.
Inside the source of one chart, the convex chart domains of that chart are a basis closed under
intersections, so Mayer–Vietoris induction below an open set
(`TauCeti.mayerVietoris_induction_le`) proves the property for every open subset of the chart
source (`TauCeti.mayerVietoris_induction_subset_chartAt_source`). The open sets contained in some
chart source are then an intersection-stable basis of `M`, so ordinary Mayer–Vietoris induction
proves the property for every open subset of `M`
(`TauCeti.mayerVietoris_induction_extChartAt`).

Typical properties are that a natural map between two (co)homology theories of open subsets is an
isomorphism, such as the inclusion of smooth singular chains into singular chains, the de Rham
homomorphism, or the Poincaré duality map. Each has a Mayer–Vietoris sequence and turns countable
disjoint unions into direct sums or products, and is verified directly on convex chart domains,
for instance by a contraction. Boundary and corners are allowed. The only hypotheses on `M` are
those of `TauCeti.mayerVietoris_induction`; a Hausdorff σ-compact manifold over a
finite-dimensional model satisfies them (`Manifold.locallyCompact_of_finiteDimensional`,
`ChartedSpace.secondCountable_of_sigmaCompact`).

## Main results

* `TauCeti.mayerVietoris_induction_subset_chartAt_source`: induction over the convex chart
  domains of one chart proves a property for every open subset of its source.
* `TauCeti.mayerVietoris_induction_extChartAt`: induction over all convex chart domains proves a
  property for every open subset of `M`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 18, proof of the de Rham
  theorem (Theorem 18.14).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, §5, the Mayer–Vietoris
  argument for Poincaré duality.
-/

public section

open Set TopologicalSpace Topology Metric

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [LocallyCompactSpace M] [SecondCountableTopology M]

/-- **Mayer–Vietoris induction in one chart.** Let `x` be a point of a second-countable locally
compact Hausdorff charted space `M`. A property of open subsets of `M` holds on every open subset
of the source of the chart at `x` if it holds on the empty set and on the convex chart domains
`(chartAt H x).source ∩ (extChartAt I x)⁻¹' C`, for convex open `C ⊆ E` with
`C ∩ range I ⊆ (extChartAt I x).target`, is preserved by binary unions of open subsets of the
chart source when it holds on their intersection, and is preserved by countable disjoint unions of
open subsets of the chart source. -/
theorem mayerVietoris_induction_subset_chartAt_source (I : ModelWithCorners 𝕜 E H) (x : M)
    (P : Opens M → Prop) (hbot : P ⊥)
    (hbase : ∀ (C : Set E) (U : Opens M), IsOpen C → Convex ℝ C →
      C ∩ range I ⊆ (extChartAt I x).target →
      (U : Set M) = (chartAt H x).source ∩ extChartAt I x ⁻¹' C → P U)
    (hsup : ∀ U V : Opens M, (U : Set M) ⊆ (chartAt H x).source →
      (V : Set M) ⊆ (chartAt H x).source → P U → P V → P (U ⊓ V) → P (U ⊔ V))
    (hdisjoint : ∀ s : ℕ → Opens M, (∀ n, (s n : Set M) ⊆ (chartAt H x).source) →
      (∀ i j, i ≠ j → Disjoint (s i) (s j)) → (∀ n, P (s n)) → P (⨆ n, s n)) :
    ∀ U : Opens M, (U : Set M) ⊆ (chartAt H x).source → P U := by
  let B : Set (Opens M) := {U | ∃ C : Set E, IsOpen C ∧ Convex ℝ C ∧
    C ∩ range I ⊆ (extChartAt I x).target ∧
    (U : Set M) = (chartAt H x).source ∩ extChartAt I x ⁻¹' C}
  refine mayerVietoris_induction_le ⟨_, (chartAt H x).open_source⟩ P B ?_ ?_ ?_ hbot ?_ hsup
    hdisjoint
  -- An inequality `U ≤ W` of opens is the inclusion of their underlying sets.
  · rintro U ⟨C, -, -, -, hU⟩ y (hy : y ∈ (U : Set M))
    rw [hU] at hy
    exact hy.1
  · -- A small ball around the chart image of a point gives a convex chart domain inside any
    -- open neighbourhood of that point in the chart source.
    intro U (hUs : (U : Set M) ⊆ (chartAt H x).source) y hy
    have hys : y ∈ (extChartAt I x).source := by
      rw [extChartAt_source]
      exact hUs hy
    have himg : extChartAt I x '' U ∈ 𝓝[range I] extChartAt I x y := by
      rw [← map_extChartAt_nhds' hys]
      exact Filter.image_mem_map (U.isOpen.mem_nhds hy)
    obtain ⟨ε, hε, hball⟩ := mem_nhdsWithin_iff.1 himg
    refine ⟨⟨_, isOpen_extChartAt_preimage x isOpen_ball⟩,
      ⟨ball (extChartAt I x y) ε, isOpen_ball, convex_ball _ _, ?_, rfl⟩,
      ⟨hUs hy, mem_ball_self hε⟩, ?_⟩
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := hball hz
      exact (extChartAt I x).map_source (by rw [extChartAt_source]; exact hUs hw)
    · rintro z ⟨hzs, hzC⟩
      rw [← extChartAt_source I] at hzs
      obtain ⟨w, hw, hwz⟩ :=
        hball ⟨hzC, extChartAt_target_subset_range x ((extChartAt I x).map_source hzs)⟩
      have hws : w ∈ (extChartAt I x).source := by
        rw [extChartAt_source]
        exact hUs hw
      rwa [← (extChartAt I x).injOn hws hzs hwz]
  · rintro U ⟨C, hC, hCc, hCt, hU⟩ V ⟨D, hD, hDc, -, hV⟩
    refine ⟨C ∩ D, hC.inter hD, hCc.inter hDc, fun z hz ↦ hCt ⟨hz.1.1, hz.2⟩, ?_⟩
    rw [Opens.coe_inf, hU, hV, preimage_inter]
    exact (inter_inter_distrib_left _ _ _).symm
  · rintro U ⟨C, hC, hCc, hCt, hU⟩
    exact hbase C U hC hCc hCt hU

/-- **Mayer–Vietoris induction over convex chart domains.** On a second-countable locally compact
Hausdorff charted space `M`, a property of open subsets holds on every open subset if it holds on
the empty set and on the convex chart domains `(chartAt H x).source ∩ (extChartAt I x)⁻¹' C`,
for points `x` and convex open `C ⊆ E` with `C ∩ range I ⊆ (extChartAt I x).target`, is
preserved by binary unions when it holds on the intersection, and is preserved by countable
disjoint unions. -/
theorem mayerVietoris_induction_extChartAt (I : ModelWithCorners 𝕜 E H) (P : Opens M → Prop)
    (hbot : P ⊥)
    (hbase : ∀ (x : M) (C : Set E) (U : Opens M), IsOpen C → Convex ℝ C →
      C ∩ range I ⊆ (extChartAt I x).target →
      (U : Set M) = (chartAt H x).source ∩ extChartAt I x ⁻¹' C → P U)
    (hsup : ∀ U V, P U → P V → P (U ⊓ V) → P (U ⊔ V))
    (hdisjoint : ∀ s : ℕ → Opens M, (∀ i j, i ≠ j → Disjoint (s i) (s j)) →
      (∀ n, P (s n)) → P (⨆ n, s n)) :
    ∀ U, P U := by
  refine mayerVietoris_induction P {U | ∃ x : M, (U : Set M) ⊆ (chartAt H x).source} ?_ ?_ hbot
    ?_ hsup hdisjoint
  · refine Opens.isBasis_iff_nbhd.2 fun {U} y hy ↦ ?_
    exact ⟨U ⊓ ⟨_, (chartAt H y).open_source⟩, ⟨y, inter_subset_right⟩,
      ⟨hy, mem_chart_source H y⟩, inf_le_left⟩
  · rintro U ⟨x, hx⟩ V -
    exact ⟨x, inter_subset_left.trans hx⟩
  · rintro U ⟨x, hx⟩
    exact mayerVietoris_induction_subset_chartAt_source I x P hbot (hbase x)
      (fun U V _ _ ↦ hsup U V) (fun s _ ↦ hdisjoint s) U hx

end TauCeti

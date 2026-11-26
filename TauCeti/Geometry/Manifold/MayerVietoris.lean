/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import TauCeti.Topology.MayerVietoris
public import TauCeti.Topology.OpenPartialHomeomorph.Basic

import Mathlib.Order.Zorn
import TauCeti.Order.SupClosed

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

This file proves the induction principle with only the nonempty sets of this form as base
cases, in two steps.
Inside the source of one chart, the convex chart domains of that chart are a basis closed under
intersections, so Mayer–Vietoris induction below an open set
(`TauCeti.mayerVietoris_induction_le`) proves the property for every open subset of the chart
source (`TauCeti.mayerVietoris_induction_subset_chartAt_source`). The open sets contained in some
chart source are then an intersection-stable basis of `M`, so ordinary Mayer–Vietoris induction
proves the property for every open subset of `M`
(`TauCeti.mayerVietoris_induction_extChartAt`).

Second countability of `M` can be traded for stability under directed unions of open sets
(`TauCeti.mayerVietoris_induction_extChartAt_of_directed`). By Zorn's lemma, applied to the
unions of chains, an open set `U` contains a maximal open subset with the property; if a point `x`
of `U` were missing from it, the part of `U` in the chart at `x` and its intersection with the
maximal subset both have the property by the one-chart step, and so does their union, against
maximality. This is the form of the argument that applies to manifolds which are not second
countable, as in Hatcher's proof of Poincaré duality.

Typical properties are that a natural map between two (co)homology theories of open subsets is an
isomorphism, such as the inclusion of smooth singular chains into singular chains, the de Rham
homomorphism, or the Poincaré duality map. Each has a Mayer–Vietoris sequence and turns countable
disjoint unions into direct sums or products, and is verified directly on convex chart domains,
for instance by a contraction. Boundary and corners are allowed. The one-chart step only needs
`E` to be locally compact. The only hypotheses on `M` in the global step are those of
`TauCeti.mayerVietoris_induction`; a Hausdorff σ-compact manifold over a finite-dimensional model
satisfies them (`Manifold.locallyCompact_of_finiteDimensional`,
`ChartedSpace.secondCountable_of_sigmaCompact`). On the model space `E` itself, the chart
restricted to a convex chart domain is an open embedding onto its convex set
(`TauCeti.isOpenEmbedding_domRestrict_chartAt_and_convex_range`), which is how the base cases are
verified on a topological manifold.

## Main results

* `TauCeti.mayerVietoris_induction_subset_chartAt_source`: induction over the convex chart
  domains of one chart proves a property for every open subset of its source.
* `TauCeti.mayerVietoris_induction_extChartAt`: induction over all convex chart domains proves a
  property for every open subset of a second-countable `M`.
* `TauCeti.mayerVietoris_induction_extChartAt_of_directed`: the same for every `M`, for a property
  which is also stable under directed unions.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 18, proof of the de Rham
  theorem (Theorem 18.14).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, §5, the Mayer–Vietoris
  argument for Poincaré duality.
* A. Hatcher, *Algebraic Topology*, Section 3.3, the proof of Lemma 3.36, whose last step is the
  Zorn's lemma argument.
-/

public section

open Set TopologicalSpace Topology Metric
open scoped Manifold

universe u

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-- **Mayer–Vietoris induction in one chart.** Let `x` be a point of a charted space `M` over a
locally compact model space `E`. A property of open subsets of `M` holds on every open subset of
the source of the chart at `x` if it holds on the empty set and on the nonempty convex chart
domains `(chartAt H x).source ∩ (extChartAt I x)⁻¹' C`, for convex open `C ⊆ E` with
`C ∩ range I ⊆ (extChartAt I x).target`, is preserved by binary unions of open subsets of the
chart source when it holds on their intersection, and is preserved by countable disjoint unions of
open subsets of the chart source. -/
theorem mayerVietoris_induction_subset_chartAt_source [LocallyCompactSpace E]
    (I : ModelWithCorners 𝕜 E H) (x : M) (P : Opens M → Prop) (hbot : P ⊥)
    (hbase : ∀ (C : Set E) (U : Opens M), IsOpen C → Convex ℝ C →
      C ∩ range I ⊆ (extChartAt I x).target →
      (U : Set M) = (chartAt H x).source ∩ extChartAt I x ⁻¹' C → (U : Set M).Nonempty → P U)
    (hsup : ∀ U V : Opens M, (U : Set M) ⊆ (chartAt H x).source →
      (V : Set M) ⊆ (chartAt H x).source → P U → P V → P (U ⊓ V) → P (U ⊔ V))
    (hdisjoint : ∀ s : ℕ → Opens M, (∀ n, (s n : Set M) ⊆ (chartAt H x).source) →
      (∀ i j, i ≠ j → Disjoint (s i) (s j)) → (∀ n, P (s n)) → P (⨆ n, s n)) :
    ∀ U : Opens M, (U : Set M) ⊆ (chartAt H x).source → P U := by
  let W : Opens M := ⟨_, (chartAt H x).open_source⟩
  -- The chart identifies `W` with an open subset of `H`, which embeds as a closed subset of the
  -- locally compact, hence proper, normed space `E`.
  have hW : IsOpenEmbedding ((chartAt H x).source.domRestrict (chartAt H x)) :=
    (chartAt H x).isOpenEmbedding_restrict
  have : ProperSpace E := .of_locallyCompactSpace ℝ
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : T2Space H := I.isClosedEmbedding.isEmbedding.t2Space
  have : SecondCountableTopology H := I.isClosedEmbedding.isEmbedding.secondCountableTopology
  have : T2Space W := hW.isEmbedding.t2Space
  have : LocallyCompactSpace W := hW.locallyCompactSpace
  have : SecondCountableTopology W := hW.isEmbedding.secondCountableTopology
  let B : Set (Opens M) := {U | ∃ C : Set E, IsOpen C ∧ Convex ℝ C ∧
    C ∩ range I ⊆ (extChartAt I x).target ∧
    (U : Set M) = (chartAt H x).source ∩ extChartAt I x ⁻¹' C}
  intro U hU
  refine mayerVietoris_induction_le W P B ?_ ?_ hbot ?_
    (fun U V hU hV ↦ hsup U V (SetLike.coe_subset_coe.2 hU) (SetLike.coe_subset_coe.2 hV))
    (fun s hs ↦ hdisjoint s fun n ↦ SetLike.coe_subset_coe.2 (hs n)) U
    (SetLike.coe_subset_coe.1 hU)
  · -- A small ball around the chart image of a point gives a convex chart domain inside any
    -- open neighbourhood of that point in the chart source.
    intro U hUW y hy
    have hUs : (U : Set M) ⊆ (chartAt H x).source := SetLike.coe_subset_coe.2 hUW
    have hys : y ∈ (extChartAt I x).source := by
      rw [extChartAt_source]
      exact hUs hy
    have himg : extChartAt I x '' U ∈ 𝓝[range I] extChartAt I x y := by
      rw [← map_extChartAt_nhds' hys]
      exact Filter.image_mem_map (U.isOpen.mem_nhds hy)
    obtain ⟨ε, hε, hball⟩ := mem_nhdsWithin_iff.1 himg
    refine ⟨⟨_, isOpen_extChartAt_preimage x isOpen_ball⟩,
      ⟨ball (extChartAt I x y) ε, isOpen_ball, convex_ball _ _, ?_, rfl⟩,
      Opens.mem_mk.2 ⟨hUs hy, mem_ball_self hε⟩, ?_⟩
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := hball hz
      exact (extChartAt I x).map_source (by rw [extChartAt_source]; exact hUs hw)
    · rw [← SetLike.coe_subset_coe, Opens.coe_mk]
      rintro z ⟨hzs, hzC⟩
      rw [← extChartAt_source I] at hzs
      obtain ⟨w, hw, hwz⟩ :=
        hball ⟨hzC, extChartAt_target_subset_range x ((extChartAt I x).map_source hzs)⟩
      have hws : w ∈ (extChartAt I x).source := by
        rw [extChartAt_source]
        exact hUs hw
      rwa [← (extChartAt I x).injOn hws hzs hwz]
  · rintro U ⟨C, hC, hCc, hCt, hU⟩ - V ⟨D, hD, hDc, -, hV⟩ - -
    refine ⟨C ∩ D, hC.inter hD, hCc.inter hDc, fun z hz ↦ hCt ⟨hz.1.1, hz.2⟩, ?_⟩
    rw [Opens.coe_inf, hU, hV, preimage_inter]
    exact (inter_inter_distrib_left _ _ _).symm
  · rintro U ⟨C, hC, hCc, hCt, hU⟩ - hne
    exact hbase C U hC hCc hCt hU hne

/-- **Mayer–Vietoris induction over convex chart domains.** On a second-countable locally compact
Hausdorff charted space `M`, a property of open subsets holds on every open subset if it holds on
the empty set and on the nonempty convex chart domains
`(chartAt H x).source ∩ (extChartAt I x)⁻¹' C`, for points `x` and convex open `C ⊆ E` with
`C ∩ range I ⊆ (extChartAt I x).target`, is preserved by binary unions when it holds on the
intersection, and is preserved by countable disjoint unions. -/
theorem mayerVietoris_induction_extChartAt [T2Space M] [LocallyCompactSpace M]
    [SecondCountableTopology M] (I : ModelWithCorners 𝕜 E H) (P : Opens M → Prop)
    (hbot : P ⊥)
    (hbase : ∀ (x : M) (C : Set E) (U : Opens M), IsOpen C → Convex ℝ C →
      C ∩ range I ⊆ (extChartAt I x).target →
      (U : Set M) = (chartAt H x).source ∩ extChartAt I x ⁻¹' C → (U : Set M).Nonempty → P U)
    (hsup : ∀ U V, P U → P V → P (U ⊓ V) → P (U ⊔ V))
    (hdisjoint : ∀ s : ℕ → Opens M, (∀ i j, i ≠ j → Disjoint (s i) (s j)) →
      (∀ n, P (s n)) → P (⨆ n, s n)) :
    ∀ U, P U := by
  refine mayerVietoris_induction P {U | ∃ x : M, (U : Set M) ⊆ (chartAt H x).source} ?_ ?_ hbot
    ?_ hsup hdisjoint
  · refine Opens.isBasis_iff_nbhd.2 fun {U} y hy ↦ ?_
    exact ⟨U ⊓ ⟨_, (chartAt H y).open_source⟩, ⟨y, inter_subset_right⟩,
      ⟨hy, mem_chart_source H y⟩, inf_le_left⟩
  · rintro U ⟨x, hx⟩ V - -
    exact ⟨x, inter_subset_left.trans hx⟩
  · rintro U ⟨x, hx⟩ -
    -- A nonempty locally compact manifold is modelled on a locally compact space.
    have : Nonempty M := ⟨x⟩
    have := LocallyCompactSpace.of_locallyCompact_manifold M I
    exact mayerVietoris_induction_subset_chartAt_source I x P hbot (hbase x)
      (fun U V _ _ ↦ hsup U V) (fun s _ ↦ hdisjoint s) U hx

/-- **Mayer–Vietoris induction over convex chart domains, without countability.** On a charted
space `M` over a locally compact model space `E`, a property of open subsets holds on every open
subset if it holds on the empty set and on the nonempty convex chart domains
`(chartAt H x).source ∩ (extChartAt I x)⁻¹' C`, for points `x` and convex open `C ⊆ E` with
`C ∩ range I ⊆ (extChartAt I x).target`, is preserved by binary unions when it holds on the
intersection, and by directed unions. Disjoint unions need no separate hypothesis: they are
directed unions of finite disjoint unions, which are binary unions with empty intersection. No
countability, local compactness or separation property of `M` is needed. -/
theorem mayerVietoris_induction_extChartAt_of_directed [LocallyCompactSpace E]
    (I : ModelWithCorners 𝕜 E H) (P : Opens M → Prop) (hbot : P ⊥)
    (hbase : ∀ (x : M) (C : Set E) (U : Opens M), IsOpen C → Convex ℝ C →
      C ∩ range I ⊆ (extChartAt I x).target →
      (U : Set M) = (chartAt H x).source ∩ extChartAt I x ⁻¹' C → (U : Set M).Nonempty → P U)
    (hsup : ∀ U V, P U → P V → P (U ⊓ V) → P (U ⊔ V))
    (hdirected : ∀ (ι : Type u) [Preorder ι] [IsDirected ι (· ≤ ·)] (U : ι → Opens M),
      Monotone U → (∀ i, P (U i)) → P (⨆ i, U i)) :
    ∀ U, P U := by
  -- Countable disjoint unions are directed unions of finite disjoint unions.
  have hdisjoint (s : ℕ → Opens M) (hs : ∀ i j, i ≠ j → Disjoint (s i) (s j))
      (h : ∀ n, P (s n)) : P (⨆ n, s n) := by
    simpa using iSup_of_pairwise_disjoint (ι := ULift.{u} ℕ) (s := fun i ↦ s i.down) P hbot
      (fun a b hab ha hb ↦ hsup a b ha hb (hab.eq_bot ▸ hbot)) (fun t ht h ↦ hdirected _ t ht h)
      (fun i j hij ↦ hs _ _ fun h ↦ hij (ULift.ext h)) fun i ↦ h i.down
  intro U
  -- A maximal open subset `m` of `U` with the property, by Zorn's lemma: the union of a chain
  -- `c` is the directed union of its members.
  obtain ⟨m, ⟨hmU, hm⟩, hmax⟩ := zorn_le₀ {V : Opens M | V ≤ U ∧ P V} fun c hc hc' ↦ by
    have : IsDirected c (· ≤ ·) := ⟨directedOn_iff_directed.1 hc'.directedOn⟩
    refine ⟨sSup c, ⟨sSup_le fun V hV ↦ (hc hV).1, ?_⟩, fun _ hV ↦ le_sSup hV⟩
    rw [sSup_eq_iSup']
    exact hdirected c (↑) (fun _ _ h ↦ h) fun V ↦ (hc V.property).2
  suffices hUm : U ≤ m from le_antisymm hmU hUm ▸ hm
  intro x hxU
  -- The part `W` of `U` in the chart at `x`, and its intersection with `m`, have the property by
  -- the one-chart step, hence so does `m ⊔ W`, which by maximality lies in `m`.
  let W : Opens M := U ⊓ ⟨_, (chartAt H x).open_source⟩
  have hWs : (W : Set M) ⊆ (chartAt H x).source := inter_subset_right
  have hP := mayerVietoris_induction_subset_chartAt_source I x P hbot (hbase x)
    (fun U V _ _ ↦ hsup U V) (fun s _ ↦ hdisjoint s)
  have hmW : P (m ⊔ W) := hsup m W hm (hP W hWs) (hP (m ⊓ W) (inter_subset_right.trans hWs))
  exact hmax ⟨sup_le hmU inf_le_left, hmW⟩ le_sup_left
    (Opens.mem_sup.2 (Or.inr ⟨hxU, mem_chart_source H x⟩))

omit [NormedSpace ℝ E] in
/-- On a charted space over the model space `E` itself, the chart at `x` restricted to the convex
chart domain `U = (chartAt E x).source ∩ (extChartAt 𝓘(𝕜, E) x)⁻¹' C` has range `C`. -/
theorem range_domRestrict_chartAt_of_eq_inter_preimage {N : Type*} [TopologicalSpace N]
    [ChartedSpace E N] {x : N} {C : Set E} {U : Set N}
    (hCt : C ∩ range 𝓘(𝕜, E) ⊆ (extChartAt 𝓘(𝕜, E) x).target)
    (hU : U = (chartAt E x).source ∩ extChartAt 𝓘(𝕜, E) x ⁻¹' C) :
    range (U.domRestrict (chartAt E x)) = C := by
  have hCt' : C ⊆ (chartAt E x).target := fun y hy ↦ by simpa using hCt ⟨hy, mem_range_self y⟩
  simp only [range_domRestrict, hU, extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]
  rw [image_inter_preimage, (chartAt E x).image_source_eq_target, inter_eq_right.2 hCt']

/-- On a charted space over the model space `E` itself, the chart at `x` restricted to the convex
chart domain `U = (chartAt E x).source ∩ (extChartAt 𝓘(𝕜, E) x)⁻¹' C`, for a convex open `C`, is
an open embedding with convex range. This is the base case of Mayer–Vietoris induction over
convex chart domains (`TauCeti.mayerVietoris_induction_extChartAt`) on a topological manifold. -/
theorem isOpenEmbedding_domRestrict_chartAt_and_convex_range {N : Type*} [TopologicalSpace N]
    [ChartedSpace E N] {x : N} {C : Set E} {U : Set N} (hC : IsOpen C) (hCc : Convex ℝ C)
    (hCt : C ∩ range 𝓘(𝕜, E) ⊆ (extChartAt 𝓘(𝕜, E) x).target)
    (hU : U = (chartAt E x).source ∩ extChartAt 𝓘(𝕜, E) x ⁻¹' C) :
    IsOpenEmbedding (U.domRestrict (chartAt E x)) ∧
      Convex ℝ (range (U.domRestrict (chartAt E x))) := by
  refine ⟨(chartAt E x).isOpenEmbedding_domRestrict ?_ (hU ▸ inter_subset_left),
    (range_domRestrict_chartAt_of_eq_inter_preimage hCt hU).symm ▸ hCc⟩
  simpa [hU] using (chartAt E x).isOpen_inter_preimage hC

end TauCeti

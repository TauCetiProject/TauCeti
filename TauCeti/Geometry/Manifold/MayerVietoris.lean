/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Sets.Opens

import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.ChartedSpace
import TauCeti.Topology.MayerVietoris

/-!
# Mayer–Vietoris induction on manifolds

Let `M` be a Hausdorff, σ-compact space charted on the model space `H` of a real model with corners
`I : ModelWithCorners ℝ E H`, where `E` is locally compact (equivalently, finite-dimensional over
`ℝ`). A property `P` of open subsets of `M` holds on every open set if it holds on the empty set
and on every nonempty open subset `U` contained in an atlas chart `e` whose extended-chart image
`e.extend I '' U` is convex in `E`, passes from `U`, `V`, and `U ⊓ V` to `U ⊔ V`, and passes to
countable pairwise disjoint unions (`ModelWithCorners.mayerVietoris_induction`).

The proof applies the topological Mayer–Vietoris induction principle
(`TauCeti.mayerVietoris_induction`) twice. First, inside any single chart domain `e.source`, the
opens whose images under `e.extend I` are convex form an intersection-stable basis: `e.extend I` is
injective on `e.source` and sends open balls intersected with `range I` (which are convex because
`range I` is convex) to convex sets. This establishes `P` on every open subset of `e.source`
(`ModelWithCorners.mayerVietoris_induction_of_subset_source`). Second, on `M` itself, the opens
contained in the source of some atlas chart form an intersection-stable basis, so a second
application of `TauCeti.mayerVietoris_induction` yields `P` on every open subset of `M`.

Working directly inside chart domains of `M` avoids transporting predicates between `M` and `H`,
so `E`, `H`, and `M` may live in independent universes.

## Main results

* `ModelWithCorners.mayerVietoris_induction_of_subset_source`: Mayer–Vietoris induction for open
  subsets of the source of a chart `e : OpenPartialHomeomorph M H`, from convex-in-chart opens.
* `ModelWithCorners.mayerVietoris_induction`: Mayer–Vietoris induction for all open subsets of a
  Hausdorff, σ-compact charted space modelled on a locally compact real model with corners.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proofs of Theorems 18.7
  and 18.14.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, §5.
-/

public section

open Set TopologicalSpace Function

namespace ModelWithCorners

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace M]

section Chart

variable (e : OpenPartialHomeomorph M H)

/-- Push an open subset of `e.source` forward to an open subset of `M`. -/
private def pushOpen (V : Opens e.source) : Opens M :=
  ⟨Subtype.val '' (V : Set e.source), e.open_source.isOpenMap_subtype_val _ V.isOpen⟩

private lemma pushOpen_bot : pushOpen e ⊥ = ⊥ := by
  ext x
  simp [pushOpen]

private lemma pushOpen_inf (U V : Opens e.source) :
    pushOpen e (U ⊓ V) = pushOpen e U ⊓ pushOpen e V := by
  ext x
  simp [pushOpen, Set.image_inter Subtype.val_injective]

private lemma pushOpen_sup (U V : Opens e.source) :
    pushOpen e (U ⊔ V) = pushOpen e U ⊔ pushOpen e V := by
  ext x
  simp [pushOpen, Set.image_union]

private lemma pushOpen_iSup {ι : Type*} (s : ι → Opens e.source) :
    pushOpen e (⨆ i, s i) = ⨆ i, pushOpen e (s i) := by
  ext x
  simp [pushOpen, Set.image_iUnion]

private lemma pushOpen_disjoint {U V : Opens e.source} (h : Disjoint U V) :
    Disjoint (pushOpen e U) (pushOpen e V) := by
  rw [disjoint_iff, ← pushOpen_inf, disjoint_iff.mp h, pushOpen_bot]

private lemma pushOpen_subset_source (V : Opens e.source) :
    (pushOpen e V : Set M) ⊆ e.source :=
  Subtype.coe_image_subset _ _

omit [LocallyCompactSpace E] in
private lemma isBasis_convex_opens_source :
    Opens.IsBasis {V : Opens e.source | Convex ℝ (e.extend I '' (pushOpen e V : Set M))} := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hx
  -- `e` maps `pushOpen e V` to an open subset of `H`, which is the preimage under `I` of an open
  -- subset `O` of `E`.
  have hVopen : IsOpen (e '' (pushOpen e V : Set M)) :=
    e.isOpen_image_of_subset_source (pushOpen e V).isOpen (pushOpen_subset_source e V)
  obtain ⟨O, hOopen, hIO⟩ := I.isClosedEmbedding.isInducing.isOpen_iff.mp hVopen
  have hxO : e.extend I x.1 ∈ O := by
    have hx' : e x.1 ∈ I ⁻¹' O := by
      rw [hIO]
      exact ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩
    exact hx'
  obtain ⟨r, hr, hballO⟩ := Metric.isOpen_iff.mp hOopen _ hxO
  -- Pull back the open ball of radius `r` around `e.extend I x` to an open subset of `e.source`.
  have hcont : Continuous fun z : e.source ↦ e.extend I z.1 :=
    I.continuous.comp (e.continuousOn.comp_continuous continuous_subtype_val fun z ↦ z.2)
  let W : Opens e.source :=
    ⟨(fun z : e.source ↦ e.extend I z.1) ⁻¹' Metric.ball (e.extend I x.1) r,
      Metric.isOpen_ball.preimage hcont⟩
  have hWV : W ≤ V := by
    intro z hz
    have hmem : e z.1 ∈ e '' (pushOpen e V : Set M) := by
      rw [← hIO]
      exact hballO hz
    obtain ⟨w, ⟨w', hw'V, rfl⟩, hwe⟩ := hmem
    have hzw : z.1 = w'.1 := e.injOn z.2 w'.2 hwe.symm
    exact Subtype.ext hzw ▸ hw'V
  have himg : e.extend I '' (pushOpen e W : Set M) =
      Metric.ball (e.extend I x.1) r ∩ Set.range I := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨_, ⟨z, hzW, rfl⟩, rfl⟩
      exact ⟨hzW, e z.1, rfl⟩
    · rintro y ⟨hyball, h, rfl⟩
      have hh : h ∈ e '' (pushOpen e V : Set M) := by
        rw [← hIO]
        exact hballO hyball
      obtain ⟨z, ⟨z', _, rfl⟩, hze⟩ := hh
      have hzW : z' ∈ W := by
        simpa only [W, Opens.mem_mk, Set.mem_preimage, OpenPartialHomeomorph.extend_coe,
          Function.comp_apply, hze] using hyball
      exact ⟨z'.1, ⟨z', hzW, rfl⟩, by
        simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply, hze]⟩
  refine ⟨W, ?_, Metric.mem_ball_self hr, hWV⟩
  rw [Set.mem_ofPred_eq, himg]
  exact (convex_ball _ _).inter I.convex_range

/-- **Mayer–Vietoris induction inside a single chart domain.** Let `e : OpenPartialHomeomorph M H`
be a chart into a locally compact real model with corners `I`. A property of open subsets of `M`
holds on every open `U ⊆ e.source` if it holds on `⊥` and on every nonempty open subset of
`e.source` whose image under `e.extend I` is convex, passes from `U`, `V`, and `U ⊓ V` to
`U ⊔ V`, and passes to countable pairwise disjoint unions. -/
theorem mayerVietoris_induction_of_subset_source (P : Opens M → Prop)
    (hbot : P ⊥)
    (hconvex : ∀ U : Opens M, (U : Set M).Nonempty → (U : Set M) ⊆ e.source →
      Convex ℝ (e.extend I '' (U : Set M)) → P U)
    (hsup : ∀ U V, P U → P V → P (U ⊓ V) → P (U ⊔ V))
    (hdisjoint : ∀ s : ℕ → Opens M, Pairwise (Disjoint on s) →
      (∀ n, P (s n)) → P (⨆ n, s n)) :
    ∀ U : Opens M, (U : Set M) ⊆ e.source → P U := by
  have : ProperSpace E := ProperSpace.of_locallyCompactSpace ℝ
  have : T2Space H := I.isClosedEmbedding.isEmbedding.t2Space
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : SecondCountableTopology H := I.isClosedEmbedding.isEmbedding.secondCountableTopology
  have : T2Space e.source := e.toHomeomorphSourceTarget.isEmbedding.t2Space
  have : LocallyCompactSpace e.target := e.open_target.locallyCompactSpace
  have : LocallyCompactSpace e.source :=
    e.toHomeomorphSourceTarget.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology e.source :=
    e.toHomeomorphSourceTarget.isEmbedding.secondCountableTopology
  have hQ : ∀ V : Opens e.source, P (pushOpen e V) :=
    TauCeti.mayerVietoris_induction (fun V : Opens e.source ↦ P (pushOpen e V))
      {V : Opens e.source | Convex ℝ (e.extend I '' (pushOpen e V : Set M))}
      (isBasis_convex_opens_source I e)
      (fun U hU V hV ↦ by
        rw [Set.mem_ofPred_eq, pushOpen_inf, Opens.coe_inf,
          (e.extend I).injOn.image_inter (by rw [e.extend_source]; exact pushOpen_subset_source e U)
            (by rw [e.extend_source]; exact pushOpen_subset_source e V)]
        exact hU.inter hV)
      (by rwa [pushOpen_bot])
      (fun V hV ↦ by
        rcases (pushOpen e V : Set M).eq_empty_or_nonempty with hemp | hne
        · have hVbot : pushOpen e V = ⊥ := Opens.ext hemp
          rwa [hVbot]
        · exact hconvex (pushOpen e V) hne (pushOpen_subset_source e V) hV)
      (fun U V hU hV hUV ↦ by
        rw [pushOpen_sup]
        exact hsup _ _ hU hV (pushOpen_inf e U V ▸ hUV))
      (fun s hs hPs ↦ by
        rw [pushOpen_iSup]
        exact hdisjoint (fun n ↦ pushOpen e (s n))
          (fun i j hij ↦ pushOpen_disjoint e (hs i j hij)) hPs)
  intro U hUe
  let V : Opens e.source :=
    ⟨Subtype.val ⁻¹' (U : Set M), U.isOpen.preimage continuous_subtype_val⟩
  have hVU : pushOpen e V = U := by
    ext x
    simp only [pushOpen, V, Opens.coe_mk, Set.mem_image, Set.mem_preimage, Subtype.exists]
    exact ⟨fun ⟨_, _, hyU, hyx⟩ ↦ hyx ▸ hyU, fun hxU ↦ ⟨x, hUe hxU, hxU, rfl⟩⟩
  exact hVU ▸ hQ V

end Chart

section Manifold

variable [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]

/-- **Mayer–Vietoris induction on a manifold.** Let `M` be a Hausdorff, σ-compact charted space
modelled on a locally compact real model with corners `I`. A property of open subsets of `M` holds
on every open set if it holds on `⊥` and on every nonempty open subset contained in an atlas chart
whose extended-chart image is convex, passes from `U`, `V`, and `U ⊓ V` to `U ⊔ V`, and passes
to countable pairwise disjoint unions. -/
theorem mayerVietoris_induction (P : Opens M → Prop)
    (hbot : P ⊥)
    (hconvex : ∀ e ∈ atlas H M, ∀ U : Opens M, (U : Set M).Nonempty →
      (U : Set M) ⊆ e.source → Convex ℝ (e.extend I '' (U : Set M)) → P U)
    (hsup : ∀ U V, P U → P V → P (U ⊓ V) → P (U ⊔ V))
    (hdisjoint : ∀ s : ℕ → Opens M, Pairwise (Disjoint on s) →
      (∀ n, P (s n)) → P (⨆ n, s n)) :
    ∀ U : Opens M, P U := by
  have : ProperSpace E := ProperSpace.of_locallyCompactSpace ℝ
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : SecondCountableTopology H := I.isClosedEmbedding.isEmbedding.secondCountableTopology
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let B : Set (Opens M) := {U : Opens M | ∃ e ∈ atlas H M, (U : Set M) ⊆ e.source}
  have hB : Opens.IsBasis B := by
    rw [Opens.isBasis_iff_nbhd]
    intro U x hx
    refine ⟨U ⊓ ⟨(chartAt H x).source, (chartAt H x).open_source⟩,
      ⟨chartAt H x, chart_mem_atlas H x, Set.inter_subset_right⟩,
      ⟨hx, mem_chart_source H x⟩, inf_le_left⟩
  have hB_inf : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V ∈ B := by
    rintro U ⟨e, he, hUe⟩ V -
    exact ⟨e, he, Set.inter_subset_left.trans hUe⟩
  have hbase : ∀ U ∈ B, P U := by
    rintro U ⟨e, he, hUe⟩
    exact I.mayerVietoris_induction_of_subset_source e P hbot (hconvex e he) hsup hdisjoint U hUe
  exact TauCeti.mayerVietoris_induction P B hB hB_inf hbot hbase hsup hdisjoint

end Manifold

end ModelWithCorners

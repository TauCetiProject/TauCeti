/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Leray
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Topology.OpenPartialHomeomorph.Ball
import TauCeti.Topology.OpenPartialHomeomorph.ChartOpens

/-!
# Finite covers of compact Riemann surfaces by contractible acyclic opens

Small coordinate discs are contractible and have vanishing first cohomology of the holomorphic
structure sheaf. Compactness selects a finite cover with both properties on each member,
refining any prescribed open cover. These covers support the comparison of closed one-forms
with holomorphic Čech cocycles.
-/

public section

open CategoryTheory Metric Set TopologicalSpace
open scoped ContDiff Manifold TauCeti.ComplexManifold Topology

namespace TauCeti

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

local notation "𝒪" => holomorphicStructureSheafModules 𝓘(ℂ) X
local notation "𝒪₊" =>
  (Functor.obj (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat ℂ) AddCommGrpCat)) 𝒪)

private theorem exists_contractible_acyclic_chart_open (x : X) {N : Set X} (hN : N ∈ 𝓝 x) :
    ∃ W : Opens (TopCat.of X), x ∈ W ∧ (W : Set X) ⊆ N ∧ ContractibleSpace W ∧
      Subsingleton (Sheaf.H' 𝒪₊ 1 W) := by
  let e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have hT : e '' (e.source ∩ N) ∈ 𝓝 (e x) :=
    e.image_mem_nhds hx (Filter.inter_mem (e.open_source.mem_nhds hx) hN)
  obtain ⟨r, hr, hRT⟩ := Metric.mem_nhds_iff.1 hT
  have htarget : ball (e x) r ⊆ e.target :=
    hRT.trans ((image_mono inter_subset_left).trans e.image_source_eq_target.subset)
  let W := e.preimageBall (e x) r
  let := contractibleSpace_ball (x := (0 : ℂ)) hr
  have hball : (W : Set X) = e.chartBall x r := by
    ext y
    exact e.mem_preimageBall.trans e.mem_chartBall.symm
  have hcontract : ContractibleSpace W :=
    ((Homeomorph.setCongr hball).trans (e.chartBallHomeomorph htarget)).contractibleSpace
  refine ⟨W, e.mem_preimageBall.2 ⟨hx, mem_ball_self hr⟩, ?_, hcontract, ?_⟩
  · intro y hyW
    obtain ⟨hy, hyr⟩ := e.mem_preimageBall.1 hyW
    obtain ⟨z, ⟨hz, hzN⟩, hzy⟩ := hRT hyr
    rwa [← e.injOn hz hy hzy]
  · have h : eball (e x) (.ofReal r) ⊆ e.target := by rwa [Metric.eball_ofReal]
    have hW : W = ⟨e.source ∩ e ⁻¹' ball (e x) r, e.isOpen_inter_preimage isOpen_ball⟩ := by
      ext y
      exact e.mem_preimageBall
    rw [hW]
    simpa only [Metric.eball_ofReal] using
      subsingleton_H'_one_holomorphicStructureSheafModules_chart_eball
        (IsManifold.chart_mem_maximalAtlas x) h

/-- Every open cover of a compact Riemann surface is refined by a finite cover by contractible
opens on each of which the first cohomology of the holomorphic structure sheaf vanishes. -/
theorem exists_finite_contractible_cover_subsingleton_H'_one_holomorphicStructureSheafModules
    [CompactSpace X] {κ : Type*} (V : κ → Opens (TopCat.of X)) (hV : IsOpenCover V) :
    ∃ (ι : Type) (_ : Finite ι) (U : ι → Opens (TopCat.of X)), IsOpenCover U ∧
      (∀ i, ∃ k, U i ≤ V k) ∧ (∀ i, ContractibleSpace (U i)) ∧
        ∀ i, Subsingleton (Sheaf.H' 𝒪₊ 1 (U i)) := by
  choose k hk using hV.exists_mem
  choose W hx hWV hcontract hacyclic using fun x : X ↦
    exists_contractible_acyclic_chart_open x ((V (k x)).isOpen.mem_nhds (hk x))
  have hW : IsOpenCover W := .mk (eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hx x⟩)
  obtain ⟨s, hs⟩ := hW.exists_finite_of_compactSpace
  exact ⟨↥s, inferInstance, fun i ↦ W i.val, hs, fun i ↦ ⟨k i.val, hWV i.val⟩,
    fun i ↦ hcontract i.val, fun i ↦ hacyclic i.val⟩

end TauCeti

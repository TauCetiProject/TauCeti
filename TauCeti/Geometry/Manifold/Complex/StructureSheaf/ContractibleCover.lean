/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Leray
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Finite covers of compact Riemann surfaces by contractible acyclic opens

Small coordinate discs are contractible and have vanishing first cohomology of the holomorphic
structure sheaf. Compactness selects a finite cover with both properties on each member.
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

private theorem exists_contractible_acyclic_chart_open (x : X) :
    ∃ W : Opens (TopCat.of X), x ∈ W ∧ ContractibleSpace W ∧ Subsingleton (Sheaf.H' 𝒪₊ 1 W) := by
  let e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  obtain ⟨r, hr, htarget⟩ := Metric.mem_nhds_iff.1 (e.open_target.mem_nhds (e.map_source hx))
  let W : Opens (TopCat.of X) :=
    ⟨e.source ∩ e ⁻¹' ball (e x) r, e.isOpen_inter_preimage isOpen_ball⟩
  have himage : e '' (W : Set X) = ball (e x) r := by
    change e '' (e.source ∩ e ⁻¹' ball (e x) r) = ball (e x) r
    rw [image_inter_preimage, e.image_source_eq_target, inter_eq_right.mpr htarget]
  let f := e.homeomorphOfImageSubsetSource (s := (W : Set X)) inter_subset_left himage
  let := contractibleSpace_ball (x := e x) hr
  refine ⟨W, ⟨hx, mem_ball_self hr⟩, f.contractibleSpace, ?_⟩
  have h : eball (e x) (.ofReal r) ⊆ e.target := by rwa [Metric.eball_ofReal]
  simpa only [Metric.eball_ofReal, W] using
    subsingleton_H'_one_holomorphicStructureSheafModules_chart_eball
      (IsManifold.chart_mem_maximalAtlas x) h

/-- A compact Riemann surface has a finite cover by contractible opens on each of which the
first cohomology of the holomorphic structure sheaf vanishes. -/
theorem exists_finite_contractible_cover_subsingleton_H'_one_holomorphicStructureSheafModules
    [CompactSpace X] :
    ∃ (ι : Type) (_ : Finite ι) (U : ι → Opens (TopCat.of X)), IsOpenCover U ∧
      (∀ i, ContractibleSpace (U i)) ∧ ∀ i, Subsingleton (Sheaf.H' 𝒪₊ 1 (U i)) := by
  choose W hx hcontract hacyclic using fun x : X ↦ exists_contractible_acyclic_chart_open x
  have hW : IsOpenCover W := .mk (eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hx x⟩)
  obtain ⟨s, hs⟩ := hW.exists_finite_of_compactSpace
  refine ⟨↥s, inferInstance, fun i ↦ W i.val, hs, ?_, ?_⟩
  · exact fun i ↦ hcontract i.val
  · exact fun i ↦ hacyclic i.val

end TauCeti

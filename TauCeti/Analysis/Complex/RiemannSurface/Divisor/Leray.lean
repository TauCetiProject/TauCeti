/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Trivialization
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Leray
public import TauCeti.Topology.Sheaves.Cohomology.Restriction

/-!
# Acyclic coordinate covers for divisor sheaves

A coordinate disc meeting a divisor's support only at its centre has vanishing first
cohomology for the divisor sheaf. The coordinate trivialization identifies the restricted
sheaf with the holomorphic structure sheaf, whose disc acyclicity follows from the local
Dolbeault lemma.

Such discs form a neighbourhood basis. On a compact Riemann surface, every open cover
therefore admits a finite refinement acyclic in degree one for the divisor sheaf. The
degree-one Leray theorem then computes its first cohomology from these covers, independently
of refinement; no acyclicity of their intersections is needed.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §§12–13 and §16.
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- A coordinate disc meeting the divisor's support only at its centre is acyclic in degree
one for the divisor sheaf. The coefficient at the centre may have either sign. -/
theorem subsingleton_H'_one_divisorSheaf_chart_eball (D : WeilDivisor X)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (x : X) (hx : x ∈ e.source) {R : ENNReal} (hR : 0 < R)
    (hT : Metric.eball (e x) R ⊆ e.target)
    (hD : ∀ y ∈ e.source ∩ e ⁻¹' Metric.eball (e x) R, y ≠ x → D y = 0) :
    Subsingleton (Sheaf.H' ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
      (divisorSheaf D)) 1
      ⟨e.source ∩ e ⁻¹' Metric.eball (e x) R, e.isOpen_inter_preimage Metric.isOpen_eball⟩) := by
  let U : Opens X :=
    ⟨e.source ∩ e ⁻¹' Metric.eball (e x) R, e.isOpen_inter_preimage Metric.isOpen_eball⟩
  let eD := divisorSheafCoordinateIso D e he x U ⟨hx, Metric.mem_eball_self hR⟩
    Set.inter_subset_left hD
  let F := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj (divisorSheaf D)
  let G := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) X)
  let eAb : (U.sheafRestrict (X := TopCat.of X)).obj F ≅
      (U.sheafRestrict (X := TopCat.of X)).obj G :=
    (sheafCompose (Opens.grothendieckTopology U)
      (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).mapIso eD
  have : Subsingleton (Sheaf.H' G 1 U) :=
    TauCeti.subsingleton_H'_one_holomorphicStructureSheafModules_chart_eball he hT
  exact (U.cohomologyIsoOfRestrictIso (X := TopCat.of X) (F := F) (G := G)
    eAb 1).addCommGroupIsoToAddEquiv.subsingleton

/-- Every neighbourhood on a Riemann surface contains an open neighbourhood acyclic in degree
one for a prescribed divisor sheaf. -/
theorem exists_mem_subset_subsingleton_H'_one_divisorSheaf (D : WeilDivisor X) (x : X)
    {N : Set X} (hN : N ∈ 𝓝 x) :
    ∃ W : Opens (TopCat.of X), x ∈ W ∧ (W : Set X) ⊆ N ∧
      Subsingleton (Sheaf.H' ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
        (divisorSheaf D)) 1 W) := by
  classical
  have := ChartedSpace.t1Space ℂ X
  let S : Set X := (↑(D.support.erase x) : Set X)ᶜ
  have hxS : x ∈ S := by simp [S]
  have hS : IsOpen S := (D.support.erase x).finite_toSet.isClosed.isOpen_compl
  let e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have hT : e '' (e.source ∩ (N ∩ S)) ∈ 𝓝 (e x) :=
    e.image_mem_nhds hx (Filter.inter_mem (e.open_source.mem_nhds hx)
      (Filter.inter_mem hN (hS.mem_nhds hxS)))
  obtain ⟨R, hR, hRT⟩ := EMetric.mem_nhds_iff.1 hT
  have hRe : Metric.eball (e x) R ⊆ e.target :=
    hRT.trans ((Set.image_mono Set.inter_subset_left).trans e.image_source_eq_target.subset)
  have hW : e.source ∩ e ⁻¹' Metric.eball (e x) R ⊆ N ∩ S := by
    rintro y ⟨hy, hyR⟩
    obtain ⟨z, ⟨hz, hzNS⟩, hzy⟩ := hRT hyR
    rwa [← e.injOn hz hy hzy]
  refine ⟨⟨e.source ∩ e ⁻¹' Metric.eball (e x) R, e.isOpen_inter_preimage Metric.isOpen_eball⟩,
    ⟨hx, Metric.mem_eball_self hR⟩, fun y hy ↦ (hW hy).1,
    subsingleton_H'_one_divisorSheaf_chart_eball D (IsManifold.chart_mem_maximalAtlas x)
      x hx hR hRe ?_⟩
  intro y hy hyx
  have hnot : y ∉ D.support.erase x := (hW hy).2
  simpa [Finset.mem_erase, hyx, Finsupp.mem_support_iff] using hnot

/-- Every open cover of a compact Riemann surface has a finite refinement whose members have
vanishing first cohomology for the prescribed divisor sheaf. These are the memberwise
acyclicity hypotheses of the degree-one Leray comparison. -/
theorem exists_finite_cover_subsingleton_H'_one_divisorSheaf [CompactSpace X]
    (D : WeilDivisor X) {κ : Type*} (V : κ → Opens (TopCat.of X)) (hV : IsOpenCover V) :
    ∃ (ι : Type) (_ : Finite ι) (U : ι → Opens (TopCat.of X)), ⨆ i, U i = ⊤ ∧
      (∀ i, ∃ k, U i ≤ V k) ∧ ∀ i,
        Subsingleton (Sheaf.H' ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
          (divisorSheaf D)) 1 (U i)) := by
  choose k hk using hV.exists_mem
  choose W hxW hWV hW using fun x ↦
    exists_mem_subset_subsingleton_H'_one_divisorSheaf D x
      ((V (k x)).isOpen.mem_nhds (hk x))
  have hWc : IsOpenCover W := .mk <| eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxW x⟩
  obtain ⟨s, hs⟩ := hWc.exists_finite_of_compactSpace
  exact ⟨s, inferInstance, fun i ↦ W i.1, hs.iSup_eq_top, fun i ↦ ⟨k i.1, hWV i.1⟩,
    fun i ↦ hW i.1⟩

end TauCeti.RiemannSurface

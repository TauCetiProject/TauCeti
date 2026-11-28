/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Leray
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LineBundle.Trivialization
public import TauCeti.Topology.Sheaves.Cohomology.Restriction
public import TauCeti.Topology.Sheaves.Leray.Colimit
import TauCeti.Geometry.Manifold.VectorBundle.MaximalAtlas

/-!
# Coordinate discs on which a line bundle is trivial are acyclic

Let `L` be a holomorphic line bundle, with any normed rank-one model `F`, on a Riemann surface `X`.
On a coordinate disc `e.source ∩ e ⁻¹' D`, for a disc `D ⊆ e.target`, contained in the base set
of a holomorphic trivialization of `L`, the sheaf `𝒪(L)` of holomorphic sections is isomorphic to
the holomorphic structure sheaf `𝒪` (`Bundle.Trivialization.holomorphicSectionSheafIso`). Sheaf
cohomology of an open only depends on the restriction of the sheaf to it, so such a disc has
vanishing `H¹` for `𝒪(L)`, as it has for `𝒪`
(`TauCeti.subsingleton_H'_one_holomorphicStructureSheafModules_chart_eball`).

Every point has a trivializing neighbourhood and a basis of coordinate discs, so these acyclic
discs form a neighbourhood basis of every point. On a compact Riemann surface every open cover is
therefore refined by a finite cover by opens `U i` with `H¹(U i, 𝒪(L)) = 0`, and the degree one
Leray theorem (`CategoryTheory.Sheaf.isIso_toCechCohomology_one_of_subsingleton_H'`) shows that
every such finite cover computes the degree one Čech cohomology of `𝒪(L)`.

## Main results

* `Bundle.Trivialization.subsingleton_H'_one_holomorphicSectionSheaf_chart_eball`: a coordinate
  disc inside the base set of a holomorphic trivialization of a line bundle has vanishing `H¹`
  for its sheaf of holomorphic sections.
* `TauCeti.RiemannSurface.exists_mem_subset_subsingleton_H'_one_holomorphicSectionSheaf`: such
  acyclic opens form a neighbourhood basis of every point.
* `TauCeti.RiemannSurface.exists_finite_cover_subsingleton_H'_one_holomorphicSectionSheaf`: on a
  compact Riemann surface, every open cover has a finite refinement by such acyclic opens.
* `TauCeti.RiemannSurface.isIso_toCechCohomology_one_holomorphicSectionSheaf`: every finite cover
  by opens with vanishing `H¹` for `𝒪(L)` computes the degree one Čech cohomology of `𝒪(L)`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §12 (Leray's theorem) and §29.
-/

public noncomputable section

open Bundle CategoryTheory Metric Opposite Set TopologicalSpace Topology
open scoped ContDiff Manifold

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : X → Type} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V] [ContMDiffVectorBundle ω F V 𝓘(ℂ)]

namespace Bundle.Trivialization

open TauCeti

/-- **Frame discs are acyclic.** On a Riemann surface, a coordinate disc `e.source ∩ e ⁻¹' D`,
for a disc `D ⊆ e.target`, contained in the base set of a holomorphic trivialization `τ` of a line
bundle has vanishing `H¹` for the sheaf of holomorphic sections of the bundle. -/
theorem subsingleton_H'_one_holomorphicSectionSheaf_chart_eball
    (τ : Trivialization F (π F V)) [τ.IsLinear ℂ] (q : F ≃L[ℂ] ℂ)
    (hτa : τ.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear X F 𝓘(ℂ) ω).maximalAtlas (TotalSpace F V))
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) {c : ℂ}
    {R : ENNReal} (hR : eball c R ⊆ e.target) (hτ : e.source ∩ e ⁻¹' eball c R ⊆ τ.baseSet) :
    Subsingleton (Sheaf.H' ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
      (holomorphicSectionSheaf 𝓘(ℂ) F V)) 1
      ⟨e.source ∩ e ⁻¹' eball c R, e.isOpen_inter_preimage isOpen_eball⟩) := by
  let U : Opens X := ⟨e.source ∩ e ⁻¹' eball c R, e.isOpen_inter_preimage isOpen_eball⟩
  let L := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj (holomorphicSectionSheaf 𝓘(ℂ) F V)
  let G := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj (holomorphicStructureSheafModules 𝓘(ℂ) X)
  have : Subsingleton (Sheaf.H' G 1 U) :=
    subsingleton_H'_one_holomorphicStructureSheafModules_chart_eball he hR
  exact (U.cohomologyIsoOfRestrictIso (X := TopCat.of X) (F := L) (G := G)
    ((sheafCompose (Opens.grothendieckTopology U)
      (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).mapIso
        (τ.holomorphicSectionSheafIso q hτa (U := U) hτ)) 1).addCommGroupIsoToAddEquiv.subsingleton

end Bundle.Trivialization

namespace TauCeti.RiemannSurface

/-- **Acyclic neighbourhoods for a line bundle.** Every neighbourhood of a point of a Riemann
surface contains an open neighbourhood with vanishing `H¹` for the sheaf of holomorphic sections
of a holomorphic line bundle, namely a coordinate disc on which the bundle is trivial. -/
theorem exists_mem_subset_subsingleton_H'_one_holomorphicSectionSheaf
    (hF : Module.finrank ℂ F = 1) (x : X) {N : Set X} (hN : N ∈ 𝓝 x) :
    ∃ W : Opens (TopCat.of X), x ∈ W ∧ (W : Set X) ⊆ N ∧
      Subsingleton (Sheaf.H' ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
        (holomorphicSectionSheaf 𝓘(ℂ) F V)) 1 W) := by
  have : Module.Finite ℂ F := Module.finite_of_finrank_eq_succ hF
  obtain ⟨q⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (hF.trans (Module.finrank_self ℂ).symm)
  let τ := trivializationAt F V x
  let e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have hN' : N ∩ τ.baseSet ∈ 𝓝 x :=
    Filter.inter_mem hN (τ.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x))
  have hT : e.target ∩ e.symm ⁻¹' (N ∩ τ.baseSet) ∈ 𝓝 (e x) :=
    Filter.inter_mem (e.open_target.mem_nhds (e.map_source hx))
      ((e.eventually_nhds' (· ∈ N ∩ τ.baseSet) hx).2 hN')
  obtain ⟨R, hR, hRT⟩ := EMetric.mem_nhds_iff.1 hT
  have hRe : eball (e x) R ⊆ e.target := hRT.trans inter_subset_left
  have hW : e.source ∩ e ⁻¹' eball (e x) R ⊆ N ∩ τ.baseSet := by
    rintro y ⟨hy, hyR⟩
    simpa only [mem_preimage, e.left_inv hy] using (hRT hyR).2
  exact ⟨⟨e.source ∩ e ⁻¹' eball (e x) R, e.isOpen_inter_preimage isOpen_eball⟩,
    ⟨hx, mem_eball_self hR⟩, fun y hy ↦ (hW hy).1,
    τ.subsingleton_H'_one_holomorphicSectionSheaf_chart_eball q
      (Trivialization.mem_maximalAtlas_of_memTrivializationAtlas 𝓘(ℂ) ω τ)
      (IsManifold.chart_mem_maximalAtlas x) hRe fun y hy ↦ (hW hy).2⟩

/-- **Finite acyclic covers for a line bundle.** On a compact Riemann surface, every open cover is
refined by a finite open cover whose members have vanishing `H¹` for the sheaf of holomorphic
sections of a holomorphic line bundle. -/
theorem exists_finite_cover_subsingleton_H'_one_holomorphicSectionSheaf [CompactSpace X]
    (hF : Module.finrank ℂ F = 1) {κ : Type*} (W : κ → Opens (TopCat.of X)) (hW : IsOpenCover W) :
    ∃ (ι : Type) (_ : Finite ι) (U : ι → Opens (TopCat.of X)), ⨆ i, U i = ⊤ ∧
      (∀ i, ∃ k, U i ≤ W k) ∧ ∀ i,
        Subsingleton (Sheaf.H' ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
          (holomorphicSectionSheaf 𝓘(ℂ) F V)) 1 (U i)) := by
  choose k hk using hW.exists_mem
  choose U hxU hUW hU using fun x ↦
    exists_mem_subset_subsingleton_H'_one_holomorphicSectionSheaf (V := V) hF x
      ((W (k x)).isOpen.mem_nhds (hk x))
  have hUc : IsOpenCover U := .mk <| eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := hUc.exists_finite_of_compactSpace
  exact ⟨s, inferInstance, fun i ↦ U i.val, hs.iSup_eq_top, fun i ↦ ⟨k i.val, hUW i.val⟩,
    fun i ↦ hU i.val⟩

/-- **Finite acyclic covers compute `H¹(X, 𝒪(L))`.** On a compact Riemann surface, a finite open
cover whose members have vanishing `H¹` for the sheaf of holomorphic sections of a holomorphic line
bundle computes its degree one Čech cohomology. -/
theorem isIso_toCechCohomology_one_holomorphicSectionSheaf [CompactSpace X]
    (hF : Module.finrank ℂ F = 1)
    {ι : Type} [Finite ι] (U : ι → Opens (TopCat.of X)) (hU : ⨆ i, U i = ⊤)
    (hFU : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
        (holomorphicSectionSheaf 𝓘(ℂ) F V)) 1 (U i))) :
    IsIso ((Topology.toCechCohomology (ModuleCat.{0} ℂ) 1 U (IsOpenCover.mk hU)).app
      (holomorphicSectionSheaf 𝓘(ℂ) F V).obj) :=
  Sheaf.isIso_toCechCohomology_one_of_subsingleton_H' _
    (fun W hW ↦ exists_finite_cover_subsingleton_H'_one_holomorphicSectionSheaf hF W hW) U hU hFU

end TauCeti.RiemannSurface

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Hom.ContinuousEval

/-!
# Joint evaluation in the manifold weak Whitney topology

The weak Whitney topology controls map values on compact subsets of source charts. For
a locally compact source model, local compactness gives a compact chart neighbourhood
of each point, so evaluation is continuous jointly in the map and the point. This is the
continuity needed for the natural action of the diffeomorphism group on its manifold.

The compact-neighbourhood argument is the standard one for compact-open evaluation; see
M. Hirsch, *Differential Topology*, Chapter 2, §1.
-/

public section

open Set Topology
open scoped Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J n N]

/-- Evaluation of a `C^n` map is continuous jointly in the map and the source point for the
manifold weak Whitney topology, provided the source model is locally compact. -/
theorem continuous_eval_manifoldWeakWhitney :
    Continuous (fun p : C^n⟮I, M; J, N⟯ × M ↦ p.1 p.2) := by
  rw [continuous_def]
  intro U hU
  apply isOpen_iff_forall_mem_open.mpr
  rintro ⟨f, x⟩ hfx
  let φ := extChartAt I x
  let ψ := extChartAt J (f x)
  obtain ⟨W, hW, hmem, hsub⟩ := continuousOn_iff.mp
    (continuousOn_extChartAt_symm (I := J) (f x)) _ (mem_extChartAt_target (f x))
      U hU (by simpa only [mem_preimage, extChartAt_to_inv] using hfx)
  have hS : IsOpen (ψ.source ∩ ψ ⁻¹' W) :=
    (continuousOn_extChartAt (I := J) (f x)).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := J) (f x)) hW
  let z : φ.target := ⟨φ x, mem_extChartAt_target x⟩
  let Fmap : φ.target → N := fun w ↦ f (φ.symm w)
  have hFmap : Continuous Fmap :=
    (map_continuous f).comp ((continuousOn_extChartAt_symm x).domRestrict)
  have hzO : Fmap z ∈ ψ.source ∩ ψ ⁻¹' W := by
    have hφx : φ.symm (φ x) = x := extChartAt_to_inv x
    have hfx' : f x ∈ ψ.source ∩ ψ ⁻¹' W :=
      ⟨mem_extChartAt_source (f x), hmem⟩
    simpa only [mem_preimage, mem_inter_iff, Fmap, z, hφx] using hfx'
  let : LocallyCompactSpace φ.target := by
    rw [extChartAt_target]
    exact ((chartAt H x).open_target.preimage I.continuous_symm).isLocallyClosed.inter
      I.isClosed_range.isLocallyClosed |>.locallyCompactSpace
  obtain ⟨K, hzK, hK, hKO⟩ :=
    exists_mem_nhds_isCompact_mapsTo hFmap (hS.mem_nhds hzO)
  obtain ⟨B, hB, hB_eq⟩ := isOpen_induced_iff.mp (isOpen_interior : IsOpen (interior K))
  let V : Set (E [×0]→L[𝕜] F) := (fun A ↦ A 0) ⁻¹' W
  have hV : IsOpen V := hW.preimage (by fun_prop)
  let T : Set C^n⟮I, M; J, N⟯ := chartJetSet x (f x) 0 K V
  have hT : IsOpen T := isOpen_chartJetSet x (f x) 0 (by simp) hK hV
  have hfT : f ∈ T := by
    simp only [T, mem_chartJetSet]
    intro w hw
    have hwO := hKO hw
    have hfw : f (φ.symm w) ∈ ψ.source ∩ ψ ⁻¹' W := hwO
    refine ⟨hfw.1, ?_⟩
    simp only [V, mem_preimage, iteratedFDerivWithin_zero_apply, Function.comp_apply]
    exact hfw.2
  let A : Set M := φ.source ∩ φ ⁻¹' B
  have hA : IsOpen A := (continuousOn_extChartAt (I := I) x).isOpen_inter_preimage
    (isOpen_extChartAt_source (I := I) x) hB
  have hxA : x ∈ A := by
    refine ⟨mem_extChartAt_source x, ?_⟩
    have hz : z ∈ interior K := mem_interior_iff_mem_nhds.mpr hzK
    rwa [← hB_eq] at hz
  refine ⟨T ×ˢ A, ?_, hT.prod hA, ⟨hfT, hxA⟩⟩
  rintro ⟨g, y⟩ ⟨hg, hy⟩
  have hyK : (⟨φ y, φ.mapsTo hy.1⟩ : φ.target) ∈ K := by
    have hyB : (⟨φ y, φ.mapsTo hy.1⟩ : φ.target) ∈ interior K := by
      rw [← hB_eq]
      simpa only [mem_preimage] using hy.2
    exact interior_subset hyB
  have hgy := (mem_chartJetSet.mp hg) ⟨φ y, φ.mapsTo hy.1⟩ hyK
  have hgy' : g y ∈ ψ.source ∧ ψ (g y) ∈ W := by
    have hφy : (extChartAt I x).symm ((extChartAt I x) y) = y :=
      (extChartAt I x).left_inv hy.1
    simp only [φ] at hgy
    simpa only [hφy, V, mem_preimage,
      iteratedFDerivWithin_zero_apply, Function.comp_apply] using hgy
  have hu := hsub ⟨hgy'.2, ψ.mapsTo hgy'.1⟩
  have hu' : ψ.symm (ψ (g y)) ∈ U := by
    simpa only [mem_preimage, ψ, Subtype.coe_mk] using hu
  simpa only [mem_preimage, ψ.left_inv hgy'.1] using hu'

/-- Joint evaluation is continuous for the manifold weak Whitney topology. -/
theorem continuousEval_manifoldWeakWhitney :
    ContinuousEval C^n⟮I, M; J, N⟯ M N :=
  ⟨continuous_eval_manifoldWeakWhitney⟩

scoped[TauCeti.ManifoldWeakWhitney] attribute [instance]
  ContMDiffMap.continuousEval_manifoldWeakWhitney

end ContMDiffMap

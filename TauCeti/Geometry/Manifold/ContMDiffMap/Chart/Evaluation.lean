/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Joint evaluation in the manifold weak Whitney topology

The weak Whitney topology controls map values on compact subsets of source charts. For
boundaryless models, local compactness of the source model gives a compact chart neighbourhood
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
  [I.Boundaryless]
  {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J n N]

/-- Evaluation of a `C^n` map is continuous jointly in the map and the source point for the
manifold weak Whitney topology, provided the source model is locally compact. -/
theorem continuous_eval_manifoldWeakWhitney_joint :
    Continuous (fun p : C^n⟮I, M; J, N⟯ × M ↦ p.1 p.2) := by
  rw [continuous_def]
  intro U hU
  apply isOpen_iff_forall_mem_open.mpr
  rintro ⟨f, x⟩ hfx
  let φ := extChartAt I x
  let ψ := extChartAt J (f x)
  have hS : IsOpen (ψ.source ∩ U) := (isOpen_extChartAt_source (I := J) (f x)).inter hU
  let z : φ.target := ⟨φ x, mem_extChartAt_target x⟩
  let Fmap : φ.target → N := fun w ↦ f (φ.symm w)
  have hFmap : Continuous Fmap :=
    (map_continuous f).comp ((continuousOn_extChartAt_symm x).domRestrict)
  have hO : IsOpen (Fmap ⁻¹' (ψ.source ∩ U)) := hS.preimage hFmap
  have hzO : z ∈ Fmap ⁻¹' (ψ.source ∩ U) := by
    have hφx : φ.symm (φ x) = x := extChartAt_to_inv x
    have hfx' : f x ∈ ψ.source ∩ U := ⟨mem_extChartAt_source (f x), hfx⟩
    simpa only [mem_preimage, mem_inter_iff, Fmap, z, hφx] using hfx'
  let : LocallyCompactSpace φ.target :=
    (isOpen_extChartAt_target (I := I) x).locallyCompactSpace
  obtain ⟨K, hK, hzK, hKO⟩ := exists_compact_subset hO hzO
  obtain ⟨B, hB, hB_eq⟩ := isOpen_induced_iff.mp (isOpen_interior : IsOpen (interior K))
  let W : Set F := ψ.target ∩ ψ.symm ⁻¹' U
  have hW : IsOpen W := (continuousOn_extChartAt_symm (I := J) (f x)).isOpen_inter_preimage
    (isOpen_extChartAt_target (I := J) (f x)) hU
  let V : Set (E [×0]→L[𝕜] F) := (fun A ↦ A 0) ⁻¹' W
  have hV : IsOpen V := hW.preimage (by fun_prop)
  let T : Set C^n⟮I, M; J, N⟯ := chartJetSet x (f x) 0 K V
  have hT : IsOpen T := isOpen_chartJetSet x (f x) 0 (by simp) hK hV
  have hfT : f ∈ T := by
    simp only [T, mem_chartJetSet]
    intro w hw
    have hwO := hKO hw
    have hfw : f (φ.symm w) ∈ ψ.source ∩ U := hwO
    refine ⟨hfw.1, ?_⟩
    simp only [V, mem_preimage, iteratedFDerivWithin_zero_apply, Function.comp_apply]
    have hψU : ψ.symm (ψ (f (φ.symm w))) ∈ U := by
      rw [ψ.left_inv hfw.1]
      exact hfw.2
    exact ⟨ψ.mapsTo hfw.1, hψU⟩
  let A : Set M := φ.source ∩ φ ⁻¹' B
  have hA : IsOpen A := (continuousOn_extChartAt (I := I) x).isOpen_inter_preimage
    (isOpen_extChartAt_source (I := I) x) hB
  have hxA : x ∈ A := by
    refine ⟨mem_extChartAt_source x, ?_⟩
    have hz : z ∈ interior K := hzK
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
  simpa only [mem_preimage, ψ.left_inv hgy'.1] using hgy'.2.2

end ContMDiffMap

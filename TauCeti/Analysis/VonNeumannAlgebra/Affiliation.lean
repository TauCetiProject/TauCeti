/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.GraphProjection
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ProjValMeasure
public import TauCeti.Analysis.VonNeumannAlgebra.Basic
public import TauCeti.Analysis.VonNeumannAlgebra.MatrixAmplification

import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import TauCeti.Analysis.InnerProductSpace.InvariantSubspace

/-!
# Affiliation of partial operators with von Neumann algebras

A partial operator is affiliated with `M` when it intertwines every unitary in `M'`, including
preservation of its domain. This condition extends to the entire commutant and passes to graph
closure. For a closed operator it is equivalent to membership of the graph projection in the
`2 × 2` amplification of `M`. For a self-adjoint operator it is also equivalent to membership
of its Cayley transform in `M`, and implies membership of all its spectral projections.

The unitary definition and the self-adjoint spectral projection criterion are from F. Hiai,
*Concise lectures on selected topics of von Neumann algebras*, Definition 4.1 and Lemma 4.2.
-/

public section

open ContinuousLinearMap

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {T : H →ₗ.[ℂ] H} {M N : VonNeumannAlgebra H}

/-- A partial operator is affiliated with `M` when every unitary in the commutant of `M`
preserves its domain and commutes with it there. Density and closedness are separate conditions
on the partial operator. -/
def IsAffiliated (T : H →ₗ.[ℂ] H) (M : VonNeumannAlgebra H) : Prop :=
  ∀ u ∈ M.commutant, u ∈ unitary (H →L[ℂ] H) → T.Intertwines T u

/-- Affiliation is domain-aware commutation with the unitaries of the commutant. -/
theorem isAffiliated_iff : T.IsAffiliated M ↔
    ∀ u ∈ M.commutant, u ∈ unitary (H →L[ℂ] H) → T.Intertwines T u :=
  (Iff.rfl)

/-- Affiliation can be checked on the whole commutant, not just its unitaries. -/
theorem isAffiliated_iff_forall_intertwines :
    T.IsAffiliated M ↔ ∀ u ∈ M.commutant, T.Intertwines T u := by
  refine ⟨fun h u hu ↦ ?_, fun h ↦ isAffiliated_iff.mpr fun u hu _ ↦ h u hu⟩
  let A := M.commutant.toStarSubalgebra
  let S : Submodule ℂ A :=
    { carrier := {u | ∀ p ∈ T.graph, ((u : H →L[ℂ] H) p.1, (u : H →L[ℂ] H) p.2) ∈ T.graph}
      zero_mem' := fun _ _ ↦ by
        have hz : ((0 : A) : H →L[ℂ] H) = 0 := rfl
        simp only [hz, _root_.zero_apply]
        exact T.graph.zero_mem
      add_mem' := fun ha hb p hp ↦ by simpa using T.graph.add_mem (ha p hp) (hb p hp)
      smul_mem' := fun c _ ha p hp ↦ by simpa using T.graph.smul_mem c (ha p hp) }
  have hS : Submodule.span ℂ (unitary A : Set A) ≤ S := Submodule.span_le.mpr fun a ha ↦ by
    have hunit : (a : H →L[ℂ] H) ∈ unitary (H →L[ℂ] H) :=
      (Unitary.map (StarMonoidHom.ofClass A.subtype) ⟨a, ha⟩).property
    exact intertwines_iff_forall_mem_graph.mp (isAffiliated_iff.mp h _ a.property hunit)
  rw [CStarAlgebra.span_unitary] at hS
  exact intertwines_iff_forall_mem_graph.mpr (hS (Submodule.mem_top (x := (⟨u, hu⟩ : A))))

/-- Every operator in the commutant of `M` commutes on the domain of an affiliated operator. -/
theorem IsAffiliated.intertwines (h : T.IsAffiliated M) {u : H →L[ℂ] H}
    (hu : u ∈ M.commutant) : T.Intertwines T u :=
  isAffiliated_iff_forall_intertwines.mp h u hu

/-- Increasing the algebra preserves affiliation. -/
theorem IsAffiliated.mono (h : T.IsAffiliated M) (hMN : M ≤ N) : T.IsAffiliated N :=
  isAffiliated_iff_forall_intertwines.mpr fun _ hu ↦ h.intertwines <|
    VonNeumannAlgebra.mem_commutant_iff.mpr fun x hx ↦
      VonNeumannAlgebra.mem_commutant_iff.mp hu x (hMN hx)

/-- Affiliation passes to graph closure. For a nonclosable operator, `LinearPMap.closure`
returns the original operator. -/
theorem IsAffiliated.closure (h : T.IsAffiliated M) : T.closure.IsAffiliated M := by
  by_cases hT : T.IsClosable
  · refine isAffiliated_iff_forall_intertwines.mpr fun u hu ↦ ?_
    rw [intertwines_iff_forall_mem_graph]
    have hmap : Set.MapsTo (u.prodMap u) (T.graph : Set (H × H)) T.graph :=
      intertwines_iff_forall_mem_graph.mp (h.intertwines hu)
    have hclosed : Set.MapsTo (u.prodMap u) (T.closure.graph : Set (H × H)) T.closure.graph := by
      simpa only [← Submodule.topologicalClosure_coe, hT.graph_closure_eq_closure_graph] using
        hmap.closure (u.prodMap u).continuous
    exact fun _ hp ↦ hclosed hp
  · simpa only [closure_def' hT] using h

/-- A bounded operator, regarded as an everywhere-defined partial operator, is affiliated with
`M` exactly when the bounded operator belongs to `M`. -/
@[simp]
theorem _root_.ContinuousLinearMap.isAffiliated_toPMap_top_iff (u : H →L[ℂ] H) :
    ((u : H →ₗ[ℂ] H).toPMap ⊤).IsAffiliated M ↔ u ∈ M := by
  rw [isAffiliated_iff_forall_intertwines]
  conv_rhs => rw [← M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  simp only [intertwines_toPMap_top_iff, ← mul_def]

/-- A closed operator is affiliated with `M` exactly when its graph projection has all four
entries in `M`. -/
theorem isAffiliated_iff_graphProjection_mem (hT : T.IsClosed) :
    T.IsAffiliated M ↔ T.graphProjection hT ∈ M.toStarSubalgebra.piLpMatrix (Fin 2) := by
  let P := T.graphProjection hT
  let D := PiLp.diagStarAlgHom ℂ H (Fin 2)
  have hentry : P ∈ M.toStarSubalgebra.piLpMatrix (Fin 2) ↔
      ∀ u ∈ M.commutant, Commute (D u) P := by
    rw [StarSubalgebra.mem_piLpMatrix]
    constructor
    · intro h u hu
      exact ext_piLpEntry fun i j ↦ by
        have hij := VonNeumannAlgebra.mem_carrier.mp (h i j)
        simpa only [D, piLpEntry_diagStarAlgHom_mul, piLpEntry_mul_diagStarAlgHom] using
          (VonNeumannAlgebra.mem_commutant_iff.mp hu _ hij).symm
    · intro h i j
      suffices P.piLpEntry i j ∈ M.commutant.commutant by
        exact VonNeumannAlgebra.mem_carrier.mpr (M.commutant_commutant ▸ this)
      refine VonNeumannAlgebra.mem_commutant_iff.mpr fun u hu ↦ ?_
      simpa only [D, piLpEntry_diagStarAlgHom_mul, piLpEntry_mul_diagStarAlgHom] using
        congrArg (fun A ↦ piLpEntry A i j) (h u hu).eq
  have hgraph (u : H →L[ℂ] H) : T.Intertwines T u ↔
      T.piLpGraph ∈ Module.End.invtSubmodule (D u).toLinearMap := by
    rw [intertwines_iff_forall_mem_graph, Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    simp only [mem_piLpGraph, coe_coe, D, PiLp.diagStarAlgHom_apply]
    refine ⟨fun h x hx ↦ h (x 0, x 1) hx, fun h p hp ↦ ?_⟩
    exact h (WithLp.toLp 2 ![p.1, p.2]) hp
  rw [isAffiliated_iff_forall_intertwines, hentry]
  constructor
  · intro h u hu
    let := hT.piLpGraph.completeSpace_coe
    have hred : T.piLpGraph.IsReducing (D u).toLinearMap :=
      isReducing_iff_mem_invtSubmodule_adjoint.mpr
        ⟨(hgraph u).mp (h u hu), by
          rw [← star_eq_adjoint, ← map_star]
          exact (hgraph (star u)).mp (h _ (star_mem hu))⟩
    simpa only [P, T.graphProjection_eq_starProjection hT] using
      (Submodule.isReducing_coe_iff_commute_starProjection.mp hred).symm
  · intro h u hu
    apply (hgraph u).mpr
    let := hT.piLpGraph.completeSpace_coe
    have hc := (h u hu).symm
    simp only [P, T.graphProjection_eq_starProjection hT] at hc
    exact (Submodule.isReducing_coe_iff_commute_starProjection.mpr hc).mem_invtSubmodule

/-- If `-i` is in the resolvent set, affiliation is equivalent to membership of the bounded
Cayley transform in the algebra. -/
theorem isAffiliated_iff_cayley_mem (hT : -Complex.I ∈ T.resolventSet) :
    T.IsAffiliated M ↔ T.cayley ∈ M := by
  rw [isAffiliated_iff_forall_intertwines]
  conv_rhs => rw [← M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  simp only [intertwines_iff_comp_cayley_eq hT hT, ← mul_def]

/-- The spectral projections of a self-adjoint affiliated operator belong to the algebra. -/
theorem IsAffiliated.spectralPVM_proj_mem (h : T.IsAffiliated M) (hT : IsSelfAdjoint T)
    {B : Set ℝ} (hB : MeasurableSet B) : (T.spectralPVM hT).proj B hB ∈ M := by
  have hU := (isAffiliated_iff_cayley_mem hT.neg_I_mem_resolventSet).mp h
  have := hT.isStarNormal_cayley
  rw [hT.spectralPVM_proj, ← M.commutant_commutant,
    VonNeumannAlgebra.mem_commutant_iff]
  intro u hu
  exact ((T.cayley.forall_commute_spectralPVM_proj_iff u).mpr
    (VonNeumannAlgebra.mem_commutant_iff.mp hu _ hU).symm _ _).eq

end LinearPMap

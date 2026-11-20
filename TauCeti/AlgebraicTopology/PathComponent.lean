/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic
public import TauCeti.Topology.ConnectedComponents

/-!
# The algebraic topology of a path component

Loops and path homotopies based in `pathComponent x₀` remain there. Consequently, when the
ambient space is semilocally simply connected, the path component inherits semilocal simple
connectivity, and its inclusion into the ambient space induces an isomorphism on fundamental
groups at every point of the component. In particular the path component is simply connected
exactly when the ambient fundamental group is trivial.

## Main declarations

* An instance making `↥(pathComponent x₀)` semilocally simply connected.
* `FundamentalGroup.pathComponentMulEquiv`: the inclusion of `pathComponent x₀`
  induces an isomorphism of fundamental groups at any point of the component.
* `FundamentalGroup.pathComponentMulEquiv_symm_fromPath`: the inverse corestricts a loop
  to its path component.
* `TauCeti.simplyConnectedSpace_pathComponent_iff`: a path component is simply connected exactly
  when the ambient fundamental group at its points is trivial.
-/

public section

open scoped unitInterval
open Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

/-- A path component inherits semilocal simple connectivity: an ambient null-homotopy based in
the component remains in that component. -/
instance instSemilocallySimplyConnectedSpaceSubtypePathComponent
    [SemilocallySimplyConnectedSpace X] :
    SemilocallySimplyConnectedSpace (pathComponent x₀) :=
  ⟨fun a => by
    obtain ⟨U, hU, hloop⟩ := semilocallySimplyConnectedAt_def.mp
      (SemilocallySimplyConnectedSpace.semilocallySimplyConnectedAt (a : X))
    refine semilocallySimplyConnectedAt_def.mpr
      ⟨Subtype.val ⁻¹' U, continuous_subtypeVal.tendsto a hU, fun γ hγ => ?_⟩
    apply homotopic_pathComponent_of_map_subtypeVal_homotopic x₀
    rw [Path.map_refl]
    refine hloop (γ.map continuous_subtypeVal) ?_
    rintro _ ⟨t, rfl⟩
    exact hγ ⟨t, rfl⟩⟩

/-- A fibre of the quotient to connected components is semilocally simply connected when the
ambient space is locally path-connected and semilocally simply connected. -/
instance instSemilocallySimplyConnectedSpaceConnectedComponentsFiber
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (C : ConnectedComponents X) :
    SemilocallySimplyConnectedSpace (ConnectedComponents.mk ⁻¹' {C} : Set X) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [connectedComponents_preimage_singleton, ← pathComponent_eq_connectedComponent]
  infer_instance

/-- **The path component of `x₀` carries the ambient fundamental group at each of its
points.** Loops at such a point and their homotopies never leave the path component. -/
noncomputable def _root_.FundamentalGroup.pathComponentMulEquiv (a : pathComponent x₀) :
    FundamentalGroup (pathComponent x₀) a ≃* FundamentalGroup X (a : X) :=
  MulEquiv.ofBijective
    (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtypeVal⟩ : C(pathComponent x₀, X)) a) <| by
    constructor
    · rw [injective_iff_map_eq_one]
      intro ⟨g⟩ hg
      obtain ⟨γ, rfl⟩ := Quotient.exists_rep g
      simp only [Path.Homotopic.Quotient.mk''_eq_mk] at hg
      have hnull : (γ.map continuous_subtypeVal).Homotopic (Path.refl (a : X)) := by
        refine (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mp ?_
        simpa only [Path.Homotopic.Quotient.mk''_eq_mk] using
          (congrArg CategoryTheory.End.asHom (FundamentalGroup.map_fromPath
            (⟨Subtype.val, continuous_subtypeVal⟩ : C(pathComponent x₀, X)) a γ)).symm.trans
          ((congrArg CategoryTheory.End.asHom hg).trans
            (FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk (a : X))))
      refine CategoryTheory.End.ext ((FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mpr ?_)
      apply homotopic_pathComponent_of_map_subtypeVal_homotopic x₀
      rw [Path.map_refl]
      exact hnull
    · intro ⟨g⟩
      obtain ⟨γ, rfl⟩ := Quotient.exists_rep g
      have hmem : ∀ t, γ t ∈ pathComponent x₀ := γ.mem_pathComponent_of_mem a.property
      refine ⟨FundamentalGroup.fromPath
        ⟦Path.codRestrict (x := a) (y := a) γ hmem⟧, ?_⟩
      simp only [Path.Homotopic.Quotient.mk''_eq_mk]
      rw [FundamentalGroup.map_fromPath, Path.map_codRestrict]

@[simp]
theorem _root_.FundamentalGroup.pathComponentMulEquiv_apply (a : pathComponent x₀)
    (g : FundamentalGroup (pathComponent x₀) a) :
    FundamentalGroup.pathComponentMulEquiv x₀ a g =
      FundamentalGroup.map
        (⟨Subtype.val, continuous_subtypeVal⟩ : C(pathComponent x₀, X)) a g :=
  MulEquiv.ofBijective_apply _ _ g

/-- The inverse path-component equivalence corestricts a representative loop to the path
component containing its basepoint. -/
@[simp]
theorem _root_.FundamentalGroup.pathComponentMulEquiv_symm_fromPath (a : pathComponent x₀)
    (γ : Path (a : X) (a : X)) :
    (FundamentalGroup.pathComponentMulEquiv x₀ a).symm
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (Path.codRestrict (x := a) (y := a) γ (γ.mem_pathComponent_of_mem a.property))) := by
  rw [MulEquiv.symm_apply_eq, FundamentalGroup.pathComponentMulEquiv_apply]
  exact congrArg FundamentalGroup.fromPath <| congrArg Path.Homotopic.Quotient.mk <|
    (Path.map_codRestrict (s := pathComponent x₀) (x := a) (y := a) γ
      (γ.mem_pathComponent_of_mem a.property)).symm

/-- **Simple connectivity of a path component.** The path component of `x₀` is simply connected
exactly when the fundamental group of the ambient space at `x₀` is trivial. -/
theorem simplyConnectedSpace_pathComponent_iff :
    SimplyConnectedSpace (pathComponent x₀) ↔ Subsingleton (FundamentalGroup X x₀) := by
  rw [← (FundamentalGroup.pathComponentMulEquiv x₀
    (pathComponentSelf x₀)).toEquiv.subsingleton_congr]
  exact ⟨fun _ ↦ inferInstance,
    fun _ ↦ simplyConnectedSpace_of_subsingleton_fundamentalGroup (pathComponentSelf x₀)⟩

end TauCeti

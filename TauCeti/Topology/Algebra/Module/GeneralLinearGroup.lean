/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# The topology of finite-dimensional linear automorphisms

The endomorphism algebra of a finite-dimensional vector space has its canonical module topology.
Mathlib's `IsModuleTopology.isTopologicalRing` supplies continuous composition. The unit
topology on that algebra records both an automorphism and its inverse. Transporting it
along Mathlib's `LinearMap.GeneralLinearGroup.generalLinearEquiv` equips linear automorphisms with
a topological group structure. In particular, continuity into this group is equivalent to
continuity of both the forward and inverse endomorphisms. Orthogonal point groups inherit this
same topology as subgroups.
-/

public section

namespace TauCeti

open scoped Topology

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The endomorphism algebra carries the canonical module topology. -/
noncomputable instance instTopologicalSpaceModuleEnd : TopologicalSpace (Module.End K V) :=
  moduleTopology K (Module.End K V)

/-- Composition of endomorphisms is continuous for their module topology. -/
instance instIsTopologicalRingModuleEnd : IsTopologicalRing (Module.End K V) :=
  IsModuleTopology.isTopologicalRing K (Module.End K V)

/-- A linear automorphism has the topology induced by its forward and inverse endomorphisms. -/
noncomputable instance instTopologicalSpaceLinearEquiv : TopologicalSpace (V ≃ₗ[K] V) :=
  TopologicalSpace.induced
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm inferInstance

/-- Linear automorphisms form a topological group in the forward-and-inverse topology. -/
instance instIsTopologicalGroupLinearEquiv : IsTopologicalGroup (V ≃ₗ[K] V) :=
  isTopologicalGroup_induced
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.toMonoidHom

/-- The canonical equivalence between invertible endomorphisms and linear automorphisms is an
isomorphism of topological groups. -/
noncomputable def generalLinearContinuousMulEquiv :
    LinearMap.GeneralLinearGroup K V ≃ₜ* V ≃ₗ[K] V where
  __ := LinearMap.GeneralLinearGroup.generalLinearEquiv K V
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    convert (continuous_id : Continuous (fun x : LinearMap.GeneralLinearGroup K V => x)) using 1
    funext x
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm_apply_apply x
  continuous_invFun := continuous_induced_dom

omit [IsTopologicalRing K] [FiniteDimensional K V] in
/-- The underlying endomorphism varies continuously with a linear automorphism. -/
@[fun_prop]
theorem continuous_linearEquiv_toLinearMap :
    Continuous (fun e : V ≃ₗ[K] V => (e : Module.End K V)) := by
  have h : Continuous ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm :
      (V ≃ₗ[K] V) → LinearMap.GeneralLinearGroup K V) := continuous_induced_dom
  exact Units.continuous_val.comp h

omit [IsTopologicalRing K] [FiniteDimensional K V] in
/-- A family of linear automorphisms is continuous exactly when its forward and inverse
endomorphisms are both continuous. -/
theorem continuous_linearEquiv_iff {X : Type*} [TopologicalSpace X]
    {f : X → V ≃ₗ[K] V} :
    Continuous f ↔
      Continuous (fun x => (f x : Module.End K V)) ∧
      Continuous (fun x => (((f x)⁻¹ : V ≃ₗ[K] V) : Module.End K V)) := by
  let e := generalLinearContinuousMulEquiv (K := K) (V := V)
  have h := e.symm.isEmbedding.isInducing.continuous_iff (f := f)
  rw [h, Units.continuous_iff]
  rfl

end TauCeti

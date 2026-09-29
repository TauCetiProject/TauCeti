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
continuity of both the forward and inverse endomorphisms.
-/

public section

namespace TauCeti

open scoped Topology

section EndTopology

variable {K V : Type*} [CommSemiring K] [TopologicalSpace K]
  [AddCommMonoid V] [Module K V]

/-- The endomorphism algebra carries the canonical module topology. -/
noncomputable instance instTopologicalSpaceModuleEnd : TopologicalSpace (Module.End K V) :=
  moduleTopology K (Module.End K V)

end EndTopology

section EndRing

variable {K V : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [AddCommGroup V] [Module K V] [Module.Finite K (Module.End K V)]

/-- The endomorphism algebra is a topological ring when it is finite over the scalar ring. -/
instance instIsTopologicalRingModuleEnd : IsTopologicalRing (Module.End K V) :=
  IsModuleTopology.isTopologicalRing K (Module.End K V)

end EndRing

variable {K V : Type*} [CommSemiring K] [TopologicalSpace K]
  [AddCommMonoid V] [Module K V]

/-- A linear automorphism has the topology induced by its forward and inverse endomorphisms. -/
noncomputable instance instTopologicalSpaceLinearEquiv : TopologicalSpace (V ≃ₗ[K] V) :=
  TopologicalSpace.induced
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm inferInstance

section TopologicalGroup

variable [ContinuousMul (Module.End K V)]

/-- Linear automorphisms form a topological group in the forward-and-inverse topology. -/
instance instIsTopologicalGroupLinearEquiv : IsTopologicalGroup (V ≃ₗ[K] V) :=
  isTopologicalGroup_induced
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.toMonoidHom

end TopologicalGroup

/-- The canonical equivalence between invertible endomorphisms and linear automorphisms is
continuous in both directions. -/
noncomputable def generalLinearContinuousMulEquiv :
    LinearMap.GeneralLinearGroup K V ≃ₜ* V ≃ₗ[K] V where
  __ := LinearMap.GeneralLinearGroup.generalLinearEquiv K V
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    convert (continuous_id : Continuous (fun x : LinearMap.GeneralLinearGroup K V => x)) using 1
    funext x
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm_apply_apply x
  continuous_invFun := continuous_induced_dom

namespace LinearEquiv

omit [TopologicalSpace K] in
/-- The endomorphism underlying a linear automorphism agrees with the forward projection of
its image in the general linear group. -/
@[simp]
theorem coe_generalLinearEquiv_symm (f : V ≃ₗ[K] V) :
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm f :
      LinearMap.GeneralLinearGroup K V) : Module.End K V) = (f : Module.End K V) := rfl

omit [TopologicalSpace K] in
/-- The inverse endomorphism underlying a linear automorphism agrees with the inverse
projection of its image in the general linear group. -/
@[simp]
theorem coe_inv_generalLinearEquiv_symm (f : V ≃ₗ[K] V) :
    (((((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm f)⁻¹ :
      LinearMap.GeneralLinearGroup K V) : Module.End K V)) =
      ((f⁻¹ : V ≃ₗ[K] V) : Module.End K V) := rfl

end LinearEquiv

/-- The underlying endomorphism varies continuously with a linear automorphism. -/
@[fun_prop]
theorem continuous_linearEquiv_toLinearMap :
    Continuous (fun e : V ≃ₗ[K] V => (e : Module.End K V)) := by
  have h : Continuous ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm :
      (V ≃ₗ[K] V) → LinearMap.GeneralLinearGroup K V) := continuous_induced_dom
  simpa only [Function.comp_def, LinearEquiv.coe_generalLinearEquiv_symm] using
    Units.continuous_val.comp h

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
  let g := LinearMap.GeneralLinearGroup.generalLinearEquiv K V
  have he : e.toMulEquiv = g := rfl
  have he_symm (a : V ≃ₗ[K] V) : e.symm.toHomeomorph a = g.symm a := by
    exact congrArg (fun t : LinearMap.GeneralLinearGroup K V ≃* V ≃ₗ[K] V =>
      t.symm a) he
  simp only [Function.comp_def, he_symm]
  dsimp only [g]
  simp only [LinearEquiv.coe_generalLinearEquiv_symm,
    LinearEquiv.coe_inv_generalLinearEquiv_symm]

end TauCeti

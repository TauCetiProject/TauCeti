/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic

/-!
# Restriction of discrete representations along a continuous homomorphism

A continuous monoid homomorphism `φ : H →* G` restricts a discrete `G`-module with continuous
`G`-action to a discrete `H`-module with continuous `H`-action on the same underlying module:
`h` acts by `φ h`. This file packages that restriction for `TauCeti.DiscreteRep` and, through the
dictionary `TauCeti.ofSmoothDiscrete`, `TauCeti.toSmoothDiscrete`, for smooth discrete
representations.

Restriction to a subgroup along its inclusion is the special case
`TauCeti.smoothDiscreteResFunctor`, which is stated directly through `TopRep.res`.

## Main definitions

* `TauCeti.DiscreteRep.res`: restriction of a discrete representation along `φ`.
* `TauCeti.DiscreteRep.resFunctor`: restriction along `φ` as a functor.
* `TauCeti.smoothResFunctor`: restriction along `φ` on smooth discrete representations.
-/

public section

open CategoryTheory

universe u v v' w

namespace TauCeti

namespace DiscreteRep

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Monoid G] [TopologicalSpace G] {H : Type v'} [Monoid H] [TopologicalSpace H]
  (φ : H →* G) (hφ : Continuous φ)

/-- Restriction of a discrete representation along a continuous monoid homomorphism `φ`: the same
module, on which `h` acts by `φ h`. -/
@[expose] def res (A : DiscreteRep.{u, v, w} R G) : DiscreteRep.{u, v', w} R H :=
  letI : DistribMulAction H A.V := .compHom A.V φ
  letI : SMulCommClass H R A.V := ⟨fun h r x ↦ smul_comm (φ h) r x⟩
  letI : ContinuousSMul H A.V :=
    ⟨(continuous_smul.comp ((hφ.comp continuous_fst).prodMk continuous_snd)).congr
      fun _ ↦ rfl⟩
  { V := A.V }

/-- Restriction does not change the underlying module. -/
@[simp] theorem res_V (A : DiscreteRep.{u, v, w} R G) : (res φ hφ A).V = A.V := (rfl)

/-- The restricted action is the original action through `φ`. -/
@[simp] theorem res_ρ_apply (A : DiscreteRep.{u, v, w} R G) (h : H) (x : A.V) :
    (res φ hφ A).ρ h x = A.ρ (φ h) x := (rfl)

/-- Restriction along a continuous monoid homomorphism, as a functor of discrete
representations. A morphism keeps its underlying linear map. -/
@[expose] def resFunctor : DiscreteRep.{u, v, w} R G ⥤ DiscreteRep.{u, v', w} R H where
  obj A := res φ hφ A
  map f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' := fun h ↦ f.isIntertwining' (φ h) }
  map_id A := Representation.IntertwiningMap.ext (DiscreteRep.id_toLinearMap A)
  map_comp f g := Representation.IntertwiningMap.ext (DiscreteRep.comp_toLinearMap f g)

/-- The object map of `resFunctor` is `res`. -/
@[simp] theorem resFunctor_obj (A : DiscreteRep.{u, v, w} R G) :
    (resFunctor φ hφ).obj A = res φ hφ A := (rfl)

/-- Restriction keeps the underlying linear map of a morphism. -/
@[simp] theorem resFunctor_map_toLinearMap {A B : DiscreteRep.{u, v, w} R G} (f : A ⟶ B) :
    ((resFunctor φ hφ).map f).toLinearMap = f.toLinearMap := (rfl)

end DiscreteRep

variable (R : Type u) [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type v'} [Monoid H] [TopologicalSpace H] (φ : H →* G) (hφ : Continuous φ)

/-- Restriction along a continuous monoid homomorphism from a topological monoid to a topological
group, on smooth discrete representations.

The functor passes through the equivalent category of discrete continuous representations. The
body is exposed so that `smoothResFunctor_map` can be stated without transports between the
functor's objects and the named restricted objects. -/
@[expose] def smoothResFunctor :
    SmoothDiscreteTopRep.{u, v, w} R G ⥤ SmoothDiscreteTopRep.{u, v', w} R H :=
  ofSmoothDiscrete R G ⋙ DiscreteRep.resFunctor φ hφ ⋙ toSmoothDiscrete R H

/-- The object map of smooth restriction is discrete restriction of the coefficient module
underlying the smooth representation. -/
@[simp] theorem smoothResFunctor_obj (A : SmoothDiscreteTopRep.{u, v, w} R G) :
    (smoothResFunctor R φ hφ).obj A =
      (toSmoothDiscrete R H).obj (DiscreteRep.res φ hφ ((ofSmoothDiscrete R G).obj A)) :=
  (rfl)

/-- The morphism map of smooth restriction applies discrete restriction to the underlying
equivariant linear map, then returns through the smooth-discrete dictionary. -/
@[simp] theorem smoothResFunctor_map {A B : SmoothDiscreteTopRep.{u, v, w} R G} (f : A ⟶ B) :
    (smoothResFunctor R φ hφ).map f =
      (toSmoothDiscrete R H).map
        ((DiscreteRep.resFunctor φ hφ).map ((ofSmoothDiscrete R G).map f)) :=
  (rfl)

end TauCeti

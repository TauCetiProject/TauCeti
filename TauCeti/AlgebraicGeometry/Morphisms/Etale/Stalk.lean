/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
import TauCeti.RingTheory.KrullDimension.Fiber

/-!
# Local rings along étale morphisms

An étale morphism `f : X ⟶ Y` induces at each point `x` a flat local homomorphism
`𝒪_{Y, f x} ⟶ 𝒪_{X, x}`, essentially of finite type, under which the maximal ideal of the source
generates the maximal ideal of the target
(`TauCeti.AlgebraicGeometry.map_maximalIdeal_stalkMap_of_formallyUnramified`). Such a
homomorphism is faithfully flat, so Noetherianity descends along it, and it ascends because the
target is a localization of a finitely generated algebra. Between Noetherian local rings it
preserves the Krull dimension
(`TauCeti.ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq`).

## Main declarations

* `TauCeti.AlgebraicGeometry.isNoetherianRing_stalk_iff_of_etale`
* `TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_of_etale`
-/

public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

variable [Etale f]

/-- An étale morphism `f : X ⟶ Y` preserves and reflects Noetherian local rings: the local ring of
`Y` at `f x` is Noetherian exactly when the local ring of `X` at `x` is. -/
theorem isNoetherianRing_stalk_iff_of_etale :
    IsNoetherianRing (Y.presheaf.stalk (f x)) ↔ IsNoetherianRing (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_toAlgebra f x
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have := essFiniteType_stalkMap_toAlgebra f x
  refine ⟨fun _ ↦
    Algebra.EssFiniteType.isNoetherianRing (Y.presheaf.stalk (f x)) (X.presheaf.stalk x),
    fun _ ↦ ?_⟩
  -- a flat local homomorphism is faithfully flat, and Noetherianity descends along it
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    .of_flat_of_isLocalHom
  exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
    (A := X.presheaf.stalk x) <| isNoetherian_of_linearEquiv
      (Algebra.TensorProduct.rid (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (X.presheaf.stalk x)).toLinearEquiv.symm

/-- An étale morphism `f : X ⟶ Y` preserves the Krull dimension of Noetherian local rings: the
local rings of `Y` at `f x` and of `X` at `x` have the same dimension. -/
theorem ringKrullDim_stalk_eq_of_etale [IsNoetherianRing (Y.presheaf.stalk (f x))] :
    ringKrullDim (Y.presheaf.stalk (f x)) = ringKrullDim (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_toAlgebra f x
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have := (isNoetherianRing_stalk_iff_of_etale f x).mp ‹_›
  exact (TauCeti.ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq
    (map_maximalIdeal_stalkMap_of_formallyUnramified f x)).symm

end AlgebraicGeometry

end TauCeti

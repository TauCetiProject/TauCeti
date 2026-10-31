/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import TauCeti.AlgebraicGeometry.Morphisms.StalkMap
import TauCeti.RingTheory.KrullDimension.Fiber

/-!
# Local rings along étale morphisms

An étale morphism `f : X ⟶ Y` induces at each point `x` a flat local homomorphism
`𝒪_{Y, f x} ⟶ 𝒪_{X, x}`, essentially of finite type, under which the maximal ideal of the source
generates the maximal ideal of the target
(`TauCeti.AlgebraicGeometry.map_maximalIdeal_stalkMap_of_formallyUnramified`). Such a
homomorphism is faithfully flat, so Noetherianity descends along it, and it ascends because the
target is a localization of a finitely generated algebra
(`TauCeti.AlgebraicGeometry.isNoetherianRing_stalk_iff_of_flat_of_locallyOfFiniteType`). Between
Noetherian local rings it preserves the Krull dimension
(`TauCeti.ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq`). Consequently, an open of `X` with
Noetherian local rings and its image in `Y` have the same supremum of local dimensions.

## Main declarations

* `TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_of_etale`
* `TauCeti.AlgebraicGeometry.iSup_ringKrullDim_stalk_eq_of_etale`
-/

public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

variable [Etale f]

/-- An étale morphism `f : X ⟶ Y` preserves the Krull dimension of Noetherian local rings: the
local rings of `Y` at `f x` and of `X` at `x` have the same dimension. -/
theorem ringKrullDim_stalk_eq_of_etale [IsNoetherianRing (Y.presheaf.stalk (f x))] :
    ringKrullDim (Y.presheaf.stalk (f x)) = ringKrullDim (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  have := isLocalHom_stalkMap_toAlgebra f x
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have := (isNoetherianRing_stalk_iff_of_flat_of_locallyOfFiniteType f x).mp ‹_›
  exact (TauCeti.ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq
    (map_maximalIdeal_stalkMap_of_formallyUnramified f x)).symm

/-- If `f : X ⟶ Y` is étale and the open `V` of `Y` is the image of an open `U` of `X` whose local
rings are Noetherian, then the local rings at the points of `U` and of `V` have the same
supremum of dimensions. -/
theorem iSup_ringKrullDim_stalk_eq_of_etale (U : X.Opens) (V : Y.Opens) (hUV : f '' U = V)
    (hU : ∀ x : U, IsNoetherianRing (X.presheaf.stalk x)) :
    ⨆ x : U, ringKrullDim (X.presheaf.stalk x) = ⨆ y : V, ringKrullDim (Y.presheaf.stalk y) := by
  refine le_antisymm (iSup_le fun x ↦ ?_) (iSup_le fun y ↦ ?_)
  · have := (isNoetherianRing_stalk_iff_of_flat_of_locallyOfFiniteType f x).mpr (hU x)
    rw [← ringKrullDim_stalk_eq_of_etale f x]
    exact le_iSup (fun y : V ↦ ringKrullDim (Y.presheaf.stalk y))
      ⟨f x, by rw [← SetLike.mem_coe, ← hUV]; exact ⟨x, x.2, rfl⟩⟩
  · obtain ⟨x, hx, hxy⟩ : (y : Y) ∈ f '' U := by rw [hUV]; exact y.2
    have := (isNoetherianRing_stalk_iff_of_flat_of_locallyOfFiniteType f x).mpr (hU ⟨x, hx⟩)
    rw [← hxy, ringKrullDim_stalk_eq_of_etale f x]
    exact le_iSup (fun x : U ↦ ringKrullDim (X.presheaf.stalk x)) ⟨x, hx⟩

end AlgebraicGeometry

end TauCeti

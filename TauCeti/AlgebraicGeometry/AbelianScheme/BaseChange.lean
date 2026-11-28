/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.StructureSheaf
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
public import TauCeti.CategoryTheory.Monoidal.Cartesian.CommGrp
public import TauCeti.CategoryTheory.Preadditive.Endomorphism

/-!
# Base change of commutative abelian schemes and their global functions

A commutative group scheme over `S` is a commutative group object of `Over S`, and an action of
a commutative ring `O` on it is a ring homomorphism from `O` to its endomorphism ring, which is
a ring because commutative group objects form a preadditive category
(`CategoryTheory.CommGrp.instPreadditive`). This file shows that both pass to base change along
any `f : T ⟶ S`:

* `TauCeti.AlgebraicGeometry.AbelianScheme.isCommMonObj_baseChange`: the base change of a
  commutative abelian scheme is commutative, and its commutative group object is the image of
  that of `A` under the pullback functor
  (`TauCeti.AlgebraicGeometry.AbelianScheme.commGrpMk_baseChange_toOver`);
* `TauCeti.AlgebraicGeometry.AbelianScheme.endBaseChange`: base change is a ring homomorphism
  `End A →+* End (A.baseChange f)` of endomorphism rings, so an action `ρ : O →+* End A` induces
  the action `(A.endBaseChange f).comp ρ` on the base change.

It also shows that a regular function on the base change `A ×_K T` of an abelian scheme `A` over a
field `K` takes equal values at any two points of `A ×_K T` with the same image in `T`
(`TauCeti.AlgebraicGeometry.AbelianScheme.appTop_eq_of_comp_snd_eq`). This is the case of
`TauCeti.AlgebraicGeometry.appTop_eq_of_comp_snd_eq`, for quasi-compact quasi-separated schemes
over a field with constant global functions: the structure morphism of `A` is proper, and smooth
with geometrically connected fibres, hence geometrically integral, so the global functions of `A`
are constant
(`AlgebraicGeometry.Scheme.Hom.isIso_app_of_universallyClosed_of_geometricallyIntegral`).

## References

* The statements follow the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207 (`New.ModuleObj`, `New.IsAbelianScheme`,
  `New.Variety.hasConstFunctions_of_isPullback`).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

open scoped CategoryTheory.Obj

namespace TauCeti

namespace AlgebraicGeometry

namespace AbelianScheme

universe u

variable {S T : Scheme.{u}}

/-- The base change of a commutative abelian scheme is commutative. -/
instance isCommMonObj_baseChange (A : AbelianScheme S) [IsCommMonObj A.toOver] (f : T ⟶ S) :
    IsCommMonObj (A.baseChange f).toOver :=
  inferInstanceAs (IsCommMonObj ((Over.pullback f).obj A.toOver))

/-- The commutative group object underlying the base change of a commutative abelian scheme is
the image of the commutative group object of `A` under the pullback functor on commutative group
objects. -/
lemma commGrpMk_baseChange_toOver (A : AbelianScheme S) [IsCommMonObj A.toOver] (f : T ⟶ S) :
    CommGrp.mk (A.baseChange f).toOver = (Over.pullback f).mapCommGrp.obj (CommGrp.mk A.toOver) :=
  (rfl)

/-- Base change along `f : T ⟶ S` as a ring homomorphism from the endomorphism ring of a
commutative abelian scheme `A` over `S` to that of `A.baseChange f`. An action
`ρ : O →+* End (CommGrp.mk A.toOver)` of a commutative ring `O` on `A` thus induces the action
`(A.endBaseChange f).comp ρ` of `O` on the base change. It is `Functor.mapEndRingHom` of the
pullback functor on commutative group objects, whose target is `End (CommGrp.mk
(A.baseChange f).toOver)` by `commGrpMk_baseChange_toOver`. -/
noncomputable def endBaseChange (A : AbelianScheme S) [IsCommMonObj A.toOver] (f : T ⟶ S) :
    End (CommGrp.mk A.toOver) →+* End (CommGrp.mk (A.baseChange f).toOver) :=
  -- The target is `End ((Over.pullback f).mapCommGrp.obj _)` by `commGrpMk_baseChange_toOver`.
  (Over.pullback f).mapCommGrp.mapEndRingHom (CommGrp.mk A.toOver)

/-- The base change of an endomorphism `e` of `A` is the pullback of its underlying morphism. -/
@[simp]
lemma endBaseChange_apply_asHom_hom_hom_hom (A : AbelianScheme S) [IsCommMonObj A.toOver]
    (f : T ⟶ S) (e : End (CommGrp.mk A.toOver)) :
    (A.endBaseChange f e).asHom.hom.hom.hom = (Over.pullback f).map e.asHom.hom.hom.hom := by
  -- `endBaseChange` is `mapEndRingHom` up to `commGrpMk_baseChange_toOver`, which is `rfl`, and
  -- `mapCommGrp` applies the functor to the underlying morphism of a homomorphism.
  exact congrArg (fun h ↦ h.hom.hom.hom)
    (Functor.mapEndRingHom_apply_asHom (Over.pullback f).mapCommGrp _ e)

/-- **Regular functions on the base change of an abelian scheme over a field are constant along
the fibres.** For an abelian scheme `A` over a field `K` and a scheme `T` over `K`, a regular
function on `A ×_K T` takes equal values at any two points with the same image in `T`. -/
theorem appTop_eq_of_comp_snd_eq {K : Type u} [Field K] (A : AbelianScheme (Spec (.of K)))
    {T Y : Scheme.{u}} (g : T ⟶ Spec (.of K)) {u v : Y ⟶ pullback A.toOver.hom g}
    (h : u ≫ pullback.snd A.toOver.hom g = v ≫ pullback.snd A.toOver.hom g)
    (φ : Γ(pullback A.toOver.hom g, ⊤)) : u.appTop φ = v.appTop φ :=
  have : IsIso A.toOver.hom.appTop :=
    A.toOver.hom.isIso_app_of_universallyClosed_of_geometricallyIntegral ⊤
  AlgebraicGeometry.appTop_eq_of_comp_snd_eq A.toOver.hom g h φ

end AbelianScheme

end AlgebraicGeometry

end TauCeti

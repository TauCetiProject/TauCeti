/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Basic
public import TauCeti.AlgebraicGeometry.AbelianScheme.Hom
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.StructureSheaf
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
public import TauCeti.CategoryTheory.Monoidal.Cartesian.CommGrp
public import TauCeti.CategoryTheory.Preadditive.Endomorphism

/-!
# Base change of abelian schemes

This file extends `AbelianScheme.baseChange` and `AbelianScheme.baseChangeFunctor` (defined in
`TauCeti.AlgebraicGeometry.AbelianScheme.Basic`) with:

* `AbelianScheme.toSchemeHom_baseChangeFunctor_map`: underlying scheme morphism of a base-changed
  homomorphism;
* `AbelianScheme.baseChange_mulBy`: compatibility of `[n]` with base change;
* `AbelianScheme.baseChangeIdNatIso`, `AbelianScheme.baseChangeCompNatIso`,
  `AbelianScheme.baseChangeIdIso`, `AbelianScheme.baseChangeCompIso`, and
  `AbelianScheme.baseChangeIdentityIso`: canonical natural and componentwise isomorphisms for
  identity base change, iterated base change, and base change of `AbelianScheme.identity`,
  constructed from Mathlib's `Functor.mapGrpNatIso`, `Functor.mapGrpIdIso`, and
  `Functor.mapGrpCompIso`;
* `TauCeti.AlgebraicGeometry.AbelianScheme.isCommMonObj_baseChange` and
  `TauCeti.AlgebraicGeometry.AbelianScheme.commGrpMk_baseChange_toOver`: the base change of a
  commutative abelian scheme is commutative, and its commutative group object is the image of
  that of `A` under the pullback functor;
* `TauCeti.AlgebraicGeometry.AbelianScheme.endBaseChange`: base change is a ring homomorphism
  `End A →+* End (A.baseChange f)` of endomorphism rings, so an action `ρ : O →+* End A` induces
  the action `(A.endBaseChange f).comp ρ` on the base change;
* `TauCeti.AlgebraicGeometry.AbelianScheme.appTop_eq_of_comp_snd_eq`: a regular function on the
  base change `A ×_K T` of an abelian scheme `A` over a field `K` takes equal values at any two
  points of `A ×_K T` with the same image in `T`.

## References

* The commutative/endomorphism/fibre-constancy statements follow the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207
  (`New.ModuleObj`, `New.IsAbelianScheme`, `New.Variety.hasConstFunctions_of_isPullback`).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

namespace AbelianScheme

universe u

section

variable {S T U : Scheme.{u}}

noncomputable section

/-- The scheme morphism underlying `(baseChangeFunctor f).map φ`. -/
@[simp]
lemma toSchemeHom_baseChangeFunctor_map {A B : AbelianScheme S} (f : T ⟶ S) (φ : A ⟶ B) :
    toSchemeHom ((baseChangeFunctor f).map φ) = ((Over.pullback f).map (toOverHom φ)).left :=
  (rfl)

/-- Multiplication by `n` on a base-changed abelian scheme is the pullback of multiplication by
`n` on the original abelian scheme. -/
@[simp]
lemma baseChange_mulBy (A : AbelianScheme S) (f : T ⟶ S) (n : ℤ) :
    (A.baseChange f).mulBy n = (Over.pullback f).map (A.mulBy n) := by
  rw [mulBy_eq_zpowMap, mulBy_eq_zpowMap, Functor.map_zpowMap]
  -- `(A.baseChange f).toOver` is defeq to `(Over.pullback f).obj A.toOver`
  -- with its `Functor.grpObjObj` instance.
  rfl

/-! ### Identity, composition, and trivial base-change isomorphisms -/

/-- Base change along the identity morphism is naturally isomorphic to the identity functor. -/
def baseChangeIdNatIso (S : Scheme.{u}) :
    baseChangeFunctor (𝟙 S) ≅ 𝟭 (AbelianScheme S) :=
  ((fullyFaithfulInducedFunctor fun X : AbelianScheme S ↦ Grp.mk X.toOver).whiskeringRight
    (AbelianScheme S)).preimageIso
    (Functor.isoWhiskerLeft (inducedFunctor fun X : AbelianScheme S ↦ Grp.mk X.toOver)
      (Functor.mapGrpNatIso (Over.pullbackId (X := S)) ≪≫ Functor.mapGrpIdIso))

/-- Base change along the identity morphism is canonically isomorphic to the original abelian
scheme. -/
def baseChangeIdIso (A : AbelianScheme S) : A.baseChange (𝟙 S) ≅ A :=
  (baseChangeIdNatIso S).app A

@[simp]
lemma toOverHom_baseChangeIdIso_hom (A : AbelianScheme S) :
    toOverHom (baseChangeIdIso A).hom = (Over.pullbackId (X := S)).hom.app A.toOver :=
  Category.comp_id _

/-- Base change along a composite `g ≫ f` is naturally isomorphic to iterated base change. -/
def baseChangeCompNatIso (g : U ⟶ T) (f : T ⟶ S) :
    baseChangeFunctor (g ≫ f) ≅ baseChangeFunctor f ⋙ baseChangeFunctor g :=
  ((fullyFaithfulInducedFunctor fun X : AbelianScheme U ↦ Grp.mk X.toOver).whiskeringRight
    (AbelianScheme S)).preimageIso
    (Functor.isoWhiskerLeft (inducedFunctor fun X : AbelianScheme S ↦ Grp.mk X.toOver)
      (Functor.mapGrpNatIso (Over.pullbackComp g f) ≪≫ Functor.mapGrpCompIso))

/-- Base change along a composite `g ≫ f` is canonically isomorphic to iterated base change. -/
def baseChangeCompIso (A : AbelianScheme S) (g : U ⟶ T) (f : T ⟶ S) :
    A.baseChange (g ≫ f) ≅ (A.baseChange f).baseChange g :=
  (baseChangeCompNatIso g f).app A

@[simp]
lemma toOverHom_baseChangeCompIso_hom (A : AbelianScheme S) (g : U ⟶ T) (f : T ⟶ S) :
    toOverHom (baseChangeCompIso A g f).hom = (Over.pullbackComp g f).hom.app A.toOver :=
  Category.comp_id _

/-- The base change of `identity S` along `f : T ⟶ S` is terminal in `AbelianScheme T`. -/
def isTerminalBaseChangeIdentity (f : T ⟶ S) : IsTerminal ((identity S).baseChange f) :=
  IsTerminal.isTerminalOfObj (inducedFunctor fun X : AbelianScheme T ↦ Grp.mk X.toOver)
    ((identity S).baseChange f)
    (((Grp.isZero_trivial (Over S)).isTerminal.ofIso
      (eqToIso (grpMk_identity_toOver S).symm)).isTerminalObj (Over.pullback f).mapGrp)

/-- Base change carries the identity abelian scheme over `S` to the identity abelian scheme over
`T`. -/
def baseChangeIdentityIso (f : T ⟶ S) : (identity S).baseChange f ≅ identity T :=
  (isTerminalBaseChangeIdentity f).uniqueUpToIso (isZeroIdentity T).isTerminal

end

end

/-! ### Commutative base change, endomorphism rings, and global functions -/

section

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

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Hom
public import TauCeti.AlgebraicGeometry.GroupScheme.BaseChange

/-!
# Base change of abelian schemes: functoriality, points, and coherence isomorphisms

This file defines base change `AbelianScheme.baseChange` and `AbelianScheme.baseChangeFunctor`
along an arbitrary morphism of base schemes `f : T ⟶ S`, and provides:

* `TauCeti.GroupScheme.baseChangePointMulEquiv` applies directly to `A.baseChange f` via
  `AbelianScheme.grpMk_baseChange_toOver`;
* `AbelianScheme.baseChange_mulBy`: compatibility of `[n]` with base change;
* `AbelianScheme.baseChangeIdNatIso`, `AbelianScheme.baseChangeCompNatIso`,
  `AbelianScheme.baseChangeIdIso`, `AbelianScheme.baseChangeCompIso`, and
  `AbelianScheme.baseChangeIdentityIso`: canonical natural and componentwise isomorphisms for
  identity base change, iterated base change, and base change of `AbelianScheme.identity`,
  constructed from Mathlib's `Functor.mapGrpNatIso`, `Functor.mapGrpIdIso`, and
  `Functor.mapGrpCompIso`.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianScheme

variable {S T U : Scheme.{u}}

noncomputable section

/-! ### Base change object and functor -/

/-- The base change of an abelian scheme along a morphism `f : T ⟶ S`, obtained by pulling back
the group scheme along `f`.

Properness, smoothness and geometric connectedness are stable under base change, and the monoidal
pullback functor carries the group-object structure (`Functor.grpObjObj`). -/
@[expose] def baseChange (A : AbelianScheme S) (f : T ⟶ S) : AbelianScheme T where
  toOver := (Over.pullback f).obj A.toOver
  grpObj := Functor.grpObjObj
  isProper := inferInstanceAs (IsProper (pullback.snd A.toOver.hom f))
  smooth := inferInstanceAs (Smooth (pullback.snd A.toOver.hom f))
  geometricallyConnected := inferInstanceAs (GeometricallyConnected (pullback.snd A.toOver.hom f))

@[simp]
lemma baseChange_toOver (A : AbelianScheme S) (f : T ⟶ S) :
    (A.baseChange f).toOver = (Over.pullback f).obj A.toOver :=
  (rfl)

/-- The underlying scheme of a base change is the fibre product of `A` with `T` over `S`. -/
lemma baseChange_toScheme (A : AbelianScheme S) (f : T ⟶ S) :
    (A.baseChange f).toScheme = pullback A.toOver.hom f :=
  (rfl)

/-- The group object underlying a base change is the image of the group object of `A` under the
pullback functor on group objects. In particular the points of the base change are identified
with points of `A` by `TauCeti.GroupScheme.baseChangePointMulEquiv`. -/
lemma grpMk_baseChange_toOver (A : AbelianScheme S) (f : T ⟶ S) :
    Grp.mk (A.baseChange f).toOver = (Over.pullback f).mapGrp.obj (Grp.mk A.toOver) :=
  (rfl)

/-- The zero section of a base change is the pullback of the zero section of `A`: the point of
`pullback A.toOver.hom f` given by `f ≫ A.zeroSection` and `𝟙 T`. -/
lemma zeroSection_baseChange (A : AbelianScheme S) (f : T ⟶ S) :
    (A.baseChange f).zeroSection = pullback.lift (f ≫ A.zeroSection) (𝟙 T) (by
      rw [Category.assoc, zeroSection_comp_toOver_hom, Category.comp_id, Category.id_comp]) := by
  refine pullback.hom_ext ?_ ((A.baseChange f).zeroSection_comp_toOver_hom.trans
    (pullback.lift_snd _ _ _).symm)
  rw [pullback.lift_fst]
  have h1 := GroupScheme.pullback_mapGrp_one_left_fst f (Grp.mk A.toOver) (𝟙_ (Over T))
  simp only [Hom.one_def, Over.comp_left, Over.tensorUnit_hom] at h1
  rw [toUnit_unique (toUnit (𝟙_ (Over T))) (𝟙 _), Over.id_left, Category.id_comp] at h1
  exact h1

/-- The base-change functor along `f : T ⟶ S`, sending an abelian scheme `A` to `A.baseChange f`
and a homomorphism to its pullback. -/
@[expose] def baseChangeFunctor (f : T ⟶ S) : AbelianScheme S ⥤ AbelianScheme T where
  obj A := A.baseChange f
  map g := InducedCategory.homMk ((Over.pullback f).mapGrp.map g.hom)
  map_id A := InducedCategory.hom_ext ((Over.pullback f).mapGrp.map_id (Grp.mk A.toOver))
  map_comp g h := InducedCategory.hom_ext ((Over.pullback f).mapGrp.map_comp g.hom h.hom)

@[simp]
lemma baseChangeFunctor_obj (f : T ⟶ S) (A : AbelianScheme S) :
    (baseChangeFunctor f).obj A = A.baseChange f :=
  (rfl)

/-- The base change of a homomorphism is its image under the pullback functor of `Over S`. -/
@[simp]
lemma toOverHom_baseChangeFunctor_map (f : T ⟶ S) {A B : AbelianScheme S} (g : A ⟶ B) :
    toOverHom ((baseChangeFunctor f).map g) = (Over.pullback f).map (toOverHom g) :=
  (rfl)

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
  (isTerminalBaseChangeIdentity f).uniqueUpToIso (isTerminalIdentity T)

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti

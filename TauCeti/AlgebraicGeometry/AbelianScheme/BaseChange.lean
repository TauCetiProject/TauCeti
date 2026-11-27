/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Hom

/-!
# Base change of abelian schemes: multiplication maps and coherence isomorphisms

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

end AbelianScheme

end AlgebraicGeometry

end TauCeti

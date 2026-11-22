/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Hom
public import TauCeti.AlgebraicGeometry.GroupScheme.BaseChange

/-!
# Base change of abelian schemes: points and coherence isomorphisms

`TauCeti.AlgebraicGeometry.AbelianScheme.Basic` defines `AbelianScheme.baseChange` and
`AbelianScheme.baseChangeFunctor`. This file provides:

* `TauCeti.GroupScheme.baseChangePointMulEquiv` applies directly to `A.baseChange f` via
  `AbelianScheme.grpMk_baseChange_toOver`;
* `AbelianScheme.baseChangeIdIso`, `AbelianScheme.baseChangeCompIso`, and
  `AbelianScheme.baseChangeIdentityIso`: canonical isomorphisms for identity base change, iterated
  base change, and base change of `AbelianScheme.identity`, constructed from Mathlib's
  `Functor.mapGrpNatIso`, `Functor.mapGrpIdIso`, and `Functor.mapGrpCompIso`.
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

/-- The unit of a base-changed abelian scheme is the pullback of the original unit. -/
@[simp]
lemma baseChange_one (A : AbelianScheme S) (f : T ⟶ S) :
    η[(A.baseChange f).toOver] =
      Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map η[A.toOver] :=
  Functor.obj.η_def _

/-- The multiplication of a base-changed abelian scheme is the pullback of the original
multiplication. -/
@[simp]
lemma baseChange_mul (A : AbelianScheme S) (f : T ⟶ S) :
    μ[(A.baseChange f).toOver] =
      Functor.LaxMonoidal.μ (Over.pullback f) A.toOver A.toOver ≫
        (Over.pullback f).map μ[A.toOver] :=
  Functor.obj.μ_def _

/-- The inversion of a base-changed abelian scheme is the pullback of the original inversion. -/
@[simp]
lemma baseChange_inv (A : AbelianScheme S) (f : T ⟶ S) :
    ι[(A.baseChange f).toOver] = (Over.pullback f).map ι[A.toOver] :=
  rfl

/-! ### Identity, composition, and trivial base-change isomorphisms -/

/-- Base change along the identity morphism is canonically isomorphic to the original abelian
scheme. -/
def baseChangeIdIso (A : AbelianScheme S) : A.baseChange (𝟙 S) ≅ A :=
  (fullyFaithfulInducedFunctor fun X : AbelianScheme S ↦ Grp.mk X.toOver).preimageIso
    ((Functor.mapGrpNatIso (Over.pullbackId (X := S)) ≪≫ Functor.mapGrpIdIso).app (Grp.mk A.toOver))

@[simp]
lemma toOverHom_baseChangeIdIso_hom (A : AbelianScheme S) :
    toOverHom (baseChangeIdIso A).hom = (Over.pullbackId (X := S)).hom.app A.toOver :=
  Category.comp_id _

/-- Base change along a composite `g ≫ f` is canonically isomorphic to iterated base change. -/
def baseChangeCompIso (A : AbelianScheme S) (g : U ⟶ T) (f : T ⟶ S) :
    A.baseChange (g ≫ f) ≅ (A.baseChange f).baseChange g :=
  (fullyFaithfulInducedFunctor fun X : AbelianScheme U ↦ Grp.mk X.toOver).preimageIso
    ((Functor.mapGrpNatIso (Over.pullbackComp g f) ≪≫ Functor.mapGrpCompIso).app (Grp.mk A.toOver))

@[simp]
lemma toOverHom_baseChangeCompIso_hom (A : AbelianScheme S) (g : U ⟶ T) (f : T ⟶ S) :
    toOverHom (baseChangeCompIso A g f).hom = (Over.pullbackComp g f).hom.app A.toOver :=
  Category.comp_id _

/-- The base change of `identity S` along `f : T ⟶ S` is terminal in `AbelianScheme T`. -/
def isTerminalBaseChangeIdentity (f : T ⟶ S) : IsTerminal ((identity S).baseChange f) :=
  let hterm : IsTerminal ((identity S).baseChange f).toOver :=
    (isTerminalIdentityToOver S).isTerminalObj (Over.pullback f)
  IsTerminal.ofUniqueHom
    (fun B ↦ homMk (hterm.from B.toOver) (hterm.hom_ext _ _) (hterm.hom_ext _ _))
    fun _ _ ↦ hom_ext (congrArg Over.Hom.left (hterm.hom_ext _ _))

/-- Base change carries the identity abelian scheme over `S` to the identity abelian scheme over
`T`. -/
def baseChangeIdentityIso (f : T ⟶ S) : (identity S).baseChange f ≅ identity T :=
  (isTerminalBaseChangeIdentity f).uniqueUpToIso (isTerminalIdentity T)

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti

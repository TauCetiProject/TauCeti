/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.RegularFunctions
public import TauCeti.AlgebraicGeometry.Modules.Dual
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.InternalHom.Pullback

/-!
# Sections of the pullback of a free sheaf

For a finite type `I` and a scheme `q : T ⟶ X` over `X`, the global sections `𝒪_T ⟶ q^* 𝒪_X^I`
of the pullback of the free sheaf on `I` correspond to `I`-indexed families of global functions on
`T` (`pullbackFreeSectionsEquiv`). A section `s` goes to the values on the basis sections of
`𝒪_X^I` of the transpose of the linear functional
`q^* 𝒪_X^I ≅ q^* 𝓗om(𝒪_X^I, 𝒪_X) ≅ 𝓗om(q^* 𝒪_X^I, 𝒪_T) ⟶ 𝒪_T` given by evaluation at `s`
(`pullbackFreeSectionsEquiv_apply`).

## Main declarations

* `TauCeti.AlgebraicGeometry.pullbackFreeSectionsEquiv`: global sections of `q^* 𝒪_X^I` are
  `I`-indexed families of global functions on `T`.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry FiniteLocallyFreeSheaf

universe u

noncomputable section

variable {X : Scheme.{u}} (I : Type u) [Finite I]

/-- **Sections of the pullback of a free sheaf.** For a finite type `I` and a scheme `q : T ⟶ X`
over `X`, global sections `𝒪_T ⟶ q^* 𝒪_X^I` correspond to `I`-indexed families of global
functions on `T`. A section `s` goes to the values on the basis sections of `𝒪_X^I` of the
transpose `𝒪_X^I ⟶ q_* 𝒪_T` of the linear functional on `q^* 𝒪_X^I` that pairs with `s`: the
pullback of the self-duality `𝒪_X^I ≅ 𝓗om(𝒪_X^I, 𝒪_X)`, the base-change isomorphism
`q^* 𝓗om(𝒪_X^I, 𝒪_X) ≅ 𝓗om(q^* 𝒪_X^I, 𝒪_T)`, and evaluation at `s`
(`pullbackFreeSectionsEquiv_apply`). -/
def pullbackFreeSectionsEquiv (T : Over X) :
    (𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj (free X I).obj) ≃
      (I → Γ(T.left, ⊤)) :=
  (Scheme.Modules.dualHomUnitEquiv
      ((Scheme.Modules.pullback T.hom).obj (free X I).obj)).symm.trans <|
    (((Scheme.Modules.isFiniteLocallyFree X).ι ⋙ Scheme.Modules.pullback T.hom).mapIso
        (freeIsoDual X I) ≪≫
      asIso ((pullbackIhomComparison (free X I).obj T.hom).app (𝟙_ X.Modules) ≫
        (ihom ((Scheme.Modules.pullback T.hom).obj (free X I).obj)).map
          (Scheme.Modules.pullbackObjUnitIso T.hom).hom)).symm.homFromEquiv.trans <|
    ((Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _).trans <|
    (eqToIso (free_obj X I)).homFromEquiv.trans (T.hom.freeHomPushforwardEquiv I)

/-- The coordinates of a section `s` of `q^* 𝒪_X^I` are the values on the basis sections of the
transpose of the functional `q^* 𝒪_X^I ≅ q^* 𝓗om(𝒪_X^I, 𝒪_X) ≅ 𝓗om(q^* 𝒪_X^I, 𝒪_T) ⟶ 𝒪_T`
given by evaluation at `s`. -/
lemma pullbackFreeSectionsEquiv_apply (T : Over X)
    (s : 𝟙_ T.left.Modules ⟶ (Scheme.Modules.pullback T.hom).obj (free X I).obj) :
    pullbackFreeSectionsEquiv I T s = T.hom.freeHomPushforwardEquiv I
      (eqToHom (free_obj X I).symm ≫
        (Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _
          ((Scheme.Modules.pullback T.hom).map (freeIsoDual X I).hom.hom ≫
            ((pullbackIhomComparison (free X I).obj T.hom).app (𝟙_ X.Modules) ≫
              (ihom ((Scheme.Modules.pullback T.hom).obj (free X I).obj)).map
                (Scheme.Modules.pullbackObjUnitIso T.hom).hom) ≫
            (Scheme.Modules.dualHomUnitEquiv _).symm s)) :=
  congrArg (fun φ ↦ T.hom.freeHomPushforwardEquiv I
    (eqToHom (free_obj X I).symm ≫ (Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv
      _ _ φ)) (Category.assoc ((Scheme.Modules.pullback T.hom).map (freeIsoDual X I).hom.hom)
        ((pullbackIhomComparison (free X I).obj T.hom).app (𝟙_ X.Modules) ≫
          (ihom ((Scheme.Modules.pullback T.hom).obj (free X I).obj)).map
            (Scheme.Modules.pullbackObjUnitIso T.hom).hom)
        ((Scheme.Modules.dualHomUnitEquiv _).symm s))

end

end TauCeti.AlgebraicGeometry

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cup.Basic
public import TauCeti.Topology.Sheaves.Cech.Pullback
public import TauCeti.Topology.Sheaves.LocallyConstant.Algebra

/-!
# Pullback of Čech cochains preserves cup products

Let `f : X ⟶ Y` be a continuous map, `P` a presheaf of `R`-algebras on `Y`, `Q` a presheaf of
`R`-algebras on `X` and `α : P ⟶ f_* Q` a morphism of presheaves of algebras. For a family `U` of
opens of `Y`, the pullback map of Čech complexes `TopCat.Hom.cechComplexPullback f U α` sends the
Čech complex of the presheaf of modules underlying `P` for `U` to that of `Q` for the inverse-image
family `f⁻¹(U)`. This file proves that it preserves the cup product of Čech cochains
(`TauCeti.CategoryTheory.cechCup`) and the unit cochain:

`f^* (a ⌣ b) = f^* a ⌣ f^* b` and `f^* 1 = 1`.

On each tuple the pullback applies the component of `α`, a homomorphism of algebras, and then
identifies the inverse image of an intersection with the intersection of the inverse images, so
both steps are multiplicative (`TauCeti.CategoryTheory.cechComplexFunctor_map_cechCup`,
`TauCeti.CategoryTheory.cechComplexCompIso_inv_cechCup`).

The main example is Čech cohomology with constant coefficients: for the sheaves of `R`-algebras of
locally constant functions `R_Y` and `R_X`, composing with `f` is a morphism
`R_Y ⟶ f_* R_X` (`TopCat.Hom.locallyConstantAlgCatComap`), and the pullback of Čech cochains it
induces is multiplicative. Since the pullback also commutes with refinements
(`TopCat.Hom.cechComplexMap_comp_cechComplexPullback`), these cochain identities are the input for
pullback on Čech cohomology being a homomorphism of graded algebras.

## Main results

* `TopCat.Hom.cechComplexPullback_cechCup`: pullback preserves cup products of Čech cochains.
* `TopCat.Hom.cechComplexPullback_cechOne`: pullback preserves the unit cochain.

## References

* The Stacks Project, Cohomology of Sheaves, Section 20.25 (tag 01FP), for the cup product on Čech
  complexes, and Section 20.15 (tag 09UY), for the maps of Čech complexes along continuous maps.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open TauCeti.CategoryTheory

universe u u'

namespace TopCat.Hom

variable {X Y : TopCat.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Opens Y) {R : Type u'}
  [CommRing R] {P : Y.Presheaf (AlgCat.{u} R)} {Q : X.Presheaf (AlgCat.{u} R)}
  (α : P ⟶ (Presheaf.pushforward (AlgCat.{u} R) f).obj Q)

/-- **Pullback preserves cup products.** For a continuous map `f : X ⟶ Y` and a morphism
`α : P ⟶ f_* Q` of presheaves of algebras, the pullback of Čech cochains from `U` to the
inverse-image family satisfies `f^* (a ⌣ b) = f^* a ⌣ f^* b`. -/
theorem cechComplexPullback_cechCup {p q n : ℕ} (h : p + q = n) (a : (cechAlgebraComplex U P).X p)
    (b : (cechAlgebraComplex U P).X q) :
    ((cechComplexPullback (Q := Q ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) f U
        (Functor.whiskerRight α (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)))).f n).hom
        (cechCup p q n h a b) =
      cechCup p q n h
        ((cechComplexPullback (Q := Q ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) f U
          (Functor.whiskerRight α (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)))).f p |>.hom a)
        ((cechComplexPullback (Q := Q ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) f U
          (Functor.whiskerRight α (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)))).f q |>.hom b) := by
  simp only [cechComplexPullback_def, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  rw [cechComplexFunctor_map_cechCup, cechComplexCompIso_inv_cechCup]

/-- **Pullback preserves the unit.** For a continuous map `f : X ⟶ Y` and a morphism
`α : P ⟶ f_* Q` of presheaves of algebras, the pullback of Čech cochains sends the unit cochain
to the unit cochain. -/
@[simp]
theorem cechComplexPullback_cechOne :
    ((cechComplexPullback (Q := Q ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) f U
        (Functor.whiskerRight α (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)))).f 0).hom
        (cechOne U P) =
      cechOne (fun i ↦ (Opens.map f).obj (U i)) Q := by
  simp only [cechComplexPullback_def, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  rw [cechComplexFunctor_map_cechOne]
  -- `f_* Q` is `(Opens.map f).op ⋙ Q` by definition
  exact cechComplexCompIso_inv_cechOne (U := U) (Opens.map f) _

/-- With constant coefficients, the pullback of Čech cochains along composition with `f`,
`R_Y ⟶ f_* R_X`, preserves cup products. -/
example {R : Type u} [CommRing R] {p q n : ℕ} (h : p + q = n)
    (a : (cechAlgebraComplex U (locallyConstantAlgCatPresheaf Y R)).X p)
    (b : (cechAlgebraComplex U (locallyConstantAlgCatPresheaf Y R)).X q) :
    ((cechComplexPullback
        (Q := locallyConstantAlgCatPresheaf X R ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) f U
        (Functor.whiskerRight (f.locallyConstantAlgCatComap R)
          (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)))).f n).hom (cechCup p q n h a b) =
      cechCup p q n h
        ((cechComplexPullback
          (Q := locallyConstantAlgCatPresheaf X R ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) f U
          (Functor.whiskerRight (f.locallyConstantAlgCatComap R)
            (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)))).f p |>.hom a)
        ((cechComplexPullback
          (Q := locallyConstantAlgCatPresheaf X R ⋙ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) f U
          (Functor.whiskerRight (f.locallyConstantAlgCatComap R)
            (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)))).f q |>.hom b) :=
  cechComplexPullback_cechCup f U _ h a b

end TopCat.Hom

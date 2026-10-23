/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.Equivalence
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda

/-!
# Sheaf cohomology along an equivalence of sites

An equivalence of categories `e : C ≌ D`, compatible with Grothendieck topologies `J` on `C` and
`K` on `D`, induces Mathlib's equivalence `e.sheafCongr J K` of categories of abelian sheaves,
sending a sheaf `F` on `C` to the sheaf `V ↦ F(e.inverse V)` on `D`. This file shows that sheaf
cohomology is invariant under this transport: the cohomology of the transported sheaf at `V` is
the cohomology of `F` at `e.inverse V`.

The comparison applies whenever `e.inverse` is a dense subsite. Its direction transports a sheaf
from `C` to `D` and identifies its cohomology over `V : D` with the original sheaf's cohomology
over `e.inverse.obj V`.

## Main declarations

* `TauCeti.CategoryTheory.sheafCongrInverseFreeYonedaIso`: the transport back of the free abelian
  sheaf on `V` is the free abelian sheaf on `e.inverse V`.
* `TauCeti.CategoryTheory.cohomologyPresheafEvaluationIsoSheafCongr`: the comparison, natural in
  the coefficient sheaf.
* `TauCeti.CategoryTheory.cohomologyPresheafObjIsoSheafCongr`: the comparison
  `Hⁿ(V, e_* F) ≅ Hⁿ(e.inverse V, F)` for a single sheaf `F`.
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.CategoryTheory

universe v u₁ u₂

noncomputable section

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
  [e.inverse.IsDenseSubsite K J]
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]

private def sheafCongrInverseFreeYonedaCorepresentation (V : D) :
    ((sheafSections J AddCommGrpCat.{v}).obj (op (e.inverse.obj V)) ⋙
        forget AddCommGrpCat).CorepresentableBy
      ((e.sheafCongr J K AddCommGrpCat.{v}).inverse.obj ((freeYonedaSheafFunctor K).obj V)) where
  homEquiv :=
    ((e.sheafCongr J K AddCommGrpCat.{v}).symm.toAdjunction.homEquiv _ _).trans
      (freeYonedaSheafSectionsEquiv K V _).toEquiv
  homEquiv_comp g f := by
    let adj := (e.sheafCongr J K AddCommGrpCat.{v}).symm.toAdjunction
    exact (congrArg (freeYonedaSheafSectionsEquiv K V _)
      (adj.homEquiv_naturality_right f g)).trans
      (freeYonedaSheafSectionsEquiv_naturality_right K _
        ((e.sheafCongr J K AddCommGrpCat.{v}).functor.map g))

/-- Transporting the free abelian sheaf on `V : D` back along `e.sheafCongr J K` gives the free
abelian sheaf on `e.inverse.obj V`. -/
def sheafCongrInverseFreeYonedaIso (V : D) :
    (e.sheafCongr J K AddCommGrpCat.{v}).inverse.obj ((freeYonedaSheafFunctor K).obj V) ≅
      (freeYonedaSheafFunctor J).obj (e.inverse.obj V) :=
  (sheafCongrInverseFreeYonedaCorepresentation J K e V).uniqueUpToIso
    (freeYonedaSheafCorepresentableBy J (e.inverse.obj V))

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [HasExt.{v} (Sheaf K AddCommGrpCat.{v})]

local instance : (e.sheafCongr J K AddCommGrpCat.{v}).symm.functor.Additive :=
  Functor.additive_of_preserves_binary_products _

local instance : (e.sheafCongr J K AddCommGrpCat.{v}).symm.inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Sheaf cohomology is invariant under an equivalence of sites: the cohomology at `V : D` of the
sheaf transported along `e.sheafCongr J K` is the cohomology of the original sheaf at
`e.inverse.obj V`, naturally in the coefficient sheaf. -/
def cohomologyPresheafEvaluationIsoSheafCongr (n : ℕ) (V : D) :
    (e.sheafCongr J K AddCommGrpCat.{v}).functor ⋙
        _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor K n ⋙
          (evaluation Dᵒᵖ AddCommGrpCat.{v}).obj (op V) ≅
      _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op (e.inverse.obj V)) := by
  rw [cohomologyPresheafFunctor_eq, cohomologyPresheafFunctor_eq]
  let adj := (e.sheafCongr J K AddCommGrpCat.{v}).symm.toAdjunction
  exact NatIso.ofComponents (fun F ↦ (adj.extEquiv (n := n)).symm.toAddCommGrpIso)
      (by
        intro F G f
        ext x
        exact adj.extEquiv_symm_naturality_right₀ x f) ≪≫
    (Abelian.extFunctor n).mapIso (sheafCongrInverseFreeYonedaIso J K e V).symm.op

/-- Sheaf cohomology is invariant under an equivalence of sites: the cohomology at `V : D` of the
sheaf transported along `e.sheafCongr J K` is the cohomology of the original sheaf at
`e.inverse.obj V`. -/
def cohomologyPresheafObjIsoSheafCongr (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (V : D) :
    _root_.CategoryTheory.Sheaf.H'.{v} ((e.sheafCongr J K AddCommGrpCat.{v}).functor.obj F) n V ≅
      _root_.CategoryTheory.Sheaf.H'.{v} F n (e.inverse.obj V) :=
  (cohomologyPresheafEvaluationIsoSheafCongr J K e n V).app F

end

end TauCeti.CategoryTheory

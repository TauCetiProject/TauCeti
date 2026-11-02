/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# Nerves of functor categories

The evaluation functor `C × (C ⥤ D) ⥤ D` induces a comparison map
`N(C ⥤ D) ⟶ Fun(N C, N D)` from the nerve of the functor category to the internal hom of
nerves. It sends the vertex `F` to the vertex classifying `nerveMap F`.

Together with the isomorphisms in the homotopy category of a nerve given by isomorphisms of the
category, this turns a natural isomorphism `F ≅ G` into an isomorphism between the vertices
`nerveMap F` and `nerveMap G` of the homotopy category of `Fun(N C, N D)`.

## Main declarations

* `CategoryTheory.Iso.toNerveHomotopyCategory`: an isomorphism `a ≅ b` in `E` gives an
  isomorphism between the corresponding objects of the homotopy category of `nerve E`.
* `TauCeti.nerveFunctorCategoryToIhom`: the comparison map `N(C ⥤ D) ⟶ Fun(N C, N D)`.
* `TauCeti.nerveFunctorCategoryToIhom_app_nerveEquiv_symm`: it sends the vertex `F` to the vertex
  classifying `nerveMap F`.
-/

public section

universe v u

open CategoryTheory MonoidalCategory Simplicial SSet

namespace CategoryTheory.Iso

variable {E : Type u} [Category.{v} E]

/-- An isomorphism `a ≅ b` in a category `E` gives an isomorphism between the corresponding
objects of the homotopy category of the nerve of `E`. -/
noncomputable def toNerveHomotopyCategory {a b : E} (u : a ≅ b) :
    HomotopyCategory.mk (X := nerve E) (nerveEquiv.symm a) ≅ .mk (nerveEquiv.symm b) where
  hom := HomotopyCategory.homMk (nerve.edgeMk u.hom)
  inv := HomotopyCategory.homMk (nerve.edgeMk u.inv)
  hom_inv_id := (HomotopyCategory.homMk_comp_homMk
    ((nerve.nonempty_compStruct_iff u.hom u.inv (𝟙 a)).2 u.hom_inv_id).some).trans
      ((congrArg HomotopyCategory.homMk (nerve.edgeMk_id a)).trans (HomotopyCategory.homMk_id _))
  inv_hom_id := (HomotopyCategory.homMk_comp_homMk
    ((nerve.nonempty_compStruct_iff u.inv u.hom (𝟙 b)).2 u.inv_hom_id).some).trans
      ((congrArg HomotopyCategory.homMk (nerve.edgeMk_id b)).trans (HomotopyCategory.homMk_id _))

@[simp]
lemma toNerveHomotopyCategory_hom {a b : E} (u : a ≅ b) :
    u.toNerveHomotopyCategory.hom = HomotopyCategory.homMk (nerve.edgeMk u.hom) := (rfl)

@[simp]
lemma toNerveHomotopyCategory_inv {a b : E} (u : a ≅ b) :
    u.toNerveHomotopyCategory.inv = HomotopyCategory.homMk (nerve.edgeMk u.inv) := (rfl)

end CategoryTheory.Iso

namespace TauCeti

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

variable (C D) in
/-- The comparison map `N(C ⥤ D) ⟶ Fun(N C, N D)`, adjoint to the nerve of the evaluation
functor `C × (C ⥤ D) ⥤ D`. -/
noncomputable def nerveFunctorCategoryToIhom : nerve (C ⥤ D) ⟶ (ihom (nerve C)).obj (nerve D) :=
  (Functor.functorHomEquiv _ _ _).symm
    { app _ Φ := ↾fun c ↦ c.prod' Φ ⋙ evaluationUncurried C D
      naturality _ _ := rfl }

/-- The comparison map `N(C ⥤ D) ⟶ Fun(N C, N D)` sends the vertex `F` to the vertex
classifying `nerveMap F`. -/
@[simp]
lemma nerveFunctorCategoryToIhom_app_nerveEquiv_symm (F : C ⥤ D) :
    (nerveFunctorCategoryToIhom C D).app (Opposite.op ⦋0⦌) (nerveEquiv.symm F) =
      unitHomEquiv _ (Functor.natTransEquiv.symm (nerveMap F)) := by
  refine Functor.functorHom_ext fun n f ↦ ConcreteCategory.hom_ext _ _ fun c ↦
    CategoryTheory.Functor.ext (F := c.prod' ((nerve (C ⥤ D)).map f (nerveEquiv.symm F)) ⋙
      evaluationUncurried C D) (G := c ⋙ F) (fun _ ↦ rfl) (fun i j g ↦ ?_)
  -- The simplex of `N(C ⥤ D)` is constant at `F`, so its edges are identities.
  exact (Category.id_comp (F.map (c.map g) ≫ 𝟙 _)).symm

end TauCeti

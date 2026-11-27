/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.Grp.FunctorTensor
public import TauCeti.CategoryTheory.Limits.Shapes.Coend.EssentiallySmall

/-!
# Tensor diagrams of abelian-group-valued functors

The external tensor product of a contravariant and a covariant functor to abelian groups
gives a bifunctor whose coend imposes the balancing relations. Every such diagram has a
coend when its indexing category is essentially small in the abelian groups' value universe.
-/

public section

open CategoryTheory Limits Opposite TensorProduct

universe w v u

namespace TauCeti

/-- Pairwise tensor product of a contravariant and a covariant functor to abelian groups.
The resulting bifunctor sends `(i, j)` to `G(i) ⊗[ℤ] F(j)`. -/
@[expose, implicit_reducible]
noncomputable def tensorBifunctor (D : Type u) [Category.{v} D] :
    ((Dᵒᵖ ⥤ AddCommGrpCat.{w}) × (D ⥤ AddCommGrpCat.{w})) ⥤ Dᵒᵖ ⥤ D ⥤ AddCommGrpCat.{w} :=
  let tensorPair := ((objectwiseTensor (AddCommGrpCat.{w} × AddCommGrpCat.{w})).obj
    (CategoryTheory.Prod.fst _ _)).obj (CategoryTheory.Prod.snd _ _)
  CategoryTheory.prodFunctor ⋙ (Functor.whiskeringRight _ _ _).obj tensorPair ⋙ Functor.curry

section TensorBifunctor

variable {D : Type u} [Category.{v} D]
  {G G' : Dᵒᵖ ⥤ AddCommGrpCat.{w}} {F F' : D ⥤ AddCommGrpCat.{w}}

/-- At `(i, j)`, the tensor diagram is the ordinary tensor product of the two values. -/
lemma tensorBifunctor_obj_obj (i : Dᵒᵖ) (j : D) :
    (((tensorBifunctor D).obj (G, F)).obj i).obj j =
      AddCommGrpCat.of (G.obj i ⊗[ℤ] F.obj j) :=
  (rfl)

-- Index these simp lemmas by the diagram morphism. The types of the pure tensor's factors
-- may elaborate through the product functor instead of directly as `G.obj i` and `F.obj j`.

/-- In the first diagram variable, only the first factor of a pure tensor changes. -/
@[simp]
lemma tensorBifunctor_map_app_tmul {i i' : Dᵒᵖ} (f : i ⟶ i') (j : D)
    (x : G.obj i) (y : F.obj j) :
    (((tensorBifunctor D).obj (G, F)).map f).app j
      (no_index (x ⊗ₜ[ℤ] y) : (((tensorBifunctor D).obj (G, F)).obj i).obj j) =
      (G.map f x) ⊗ₜ[ℤ] y := by
  calc
    _ = G.map f x ⊗ₜ[ℤ] F.map (𝟙 j) y :=
      objectwiseTensor.obj_obj_map_tmul (CategoryTheory.Prod.fst _ _) (CategoryTheory.Prod.snd _ _)
        (c := (G.obj i, F.obj j)) (c' := (G.obj i', F.obj j)) (G.map f, F.map (𝟙 j)) x y
    _ = _ := congrArg (G.map f x ⊗ₜ[ℤ] ·) (ConcreteCategory.congr_hom (F.map_id j) y)

/-- In the second diagram variable, only the second factor of a pure tensor changes. -/
@[simp]
lemma tensorBifunctor_obj_map_tmul (i : Dᵒᵖ) {j j' : D} (f : j ⟶ j')
    (x : G.obj i) (y : F.obj j) :
    (((tensorBifunctor D).obj (G, F)).obj i).map f
      (no_index (x ⊗ₜ[ℤ] y) : (((tensorBifunctor D).obj (G, F)).obj i).obj j) =
      x ⊗ₜ[ℤ] (F.map f y) := by
  calc
    _ = G.map (𝟙 i) x ⊗ₜ[ℤ] F.map f y :=
      objectwiseTensor.obj_obj_map_tmul (CategoryTheory.Prod.fst _ _) (CategoryTheory.Prod.snd _ _)
        (c := (G.obj i, F.obj j)) (c' := (G.obj i, F.obj j')) (G.map (𝟙 i), F.map f) x y
    _ = _ := congrArg (· ⊗ₜ[ℤ] F.map f y) (ConcreteCategory.congr_hom (G.map_id i) x)

/-- Maps of the two input functors act componentwise on pure tensors. -/
@[simp]
lemma tensorBifunctor_map_app_app_tmul (α : G ⟶ G') (β : F ⟶ F') (i : Dᵒᵖ) (j : D)
    (x : G.obj i) (y : F.obj j) :
    (((tensorBifunctor D).map (X := (G, F)) (Y := (G', F')) (no_index (α, β))).app i).app j
      (no_index (x ⊗ₜ[ℤ] y) : (((tensorBifunctor D).obj (G, F)).obj i).obj j) =
      (α.app i x) ⊗ₜ[ℤ] (β.app j y) := by
  exact objectwiseTensor.obj_obj_map_tmul (CategoryTheory.Prod.fst _ _)
    (CategoryTheory.Prod.snd _ _)
    (c := (G.obj i, F.obj j)) (c' := (G'.obj i, F'.obj j)) (α.app i, β.app j) x y

end TensorBifunctor

instance {D : Type u} [Category.{v} D] [EssentiallySmall.{w} D] :
    ∀ H : Dᵒᵖ ⥤ D ⥤ AddCommGrpCat.{w}, HasCoend H :=
  hasCoend_of_essentiallySmall

end TauCeti

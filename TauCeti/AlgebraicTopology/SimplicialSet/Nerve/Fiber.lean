/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import TauCeti.AlgebraicTopology.SimplicialSet.Fiber
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Strict fibers of ordinary nerves

The nerve of the ordinary fiber of a functor is isomorphic to the strict simplicial fiber
of its nerve. A string in the ordinary fiber is sent to its underlying string. Conversely,
a string whose image is constant lifts to the ordinary fiber by
`CategoryTheory.Functor.Fiber.inducedFunctor`.

The comparison retains the natural universe `max u v` of the nerve of a category with
objects in `Type u` and morphisms in `Type v`. It is useful for computing the fibers of
operator nerves, where the ordinary fibers are categories of finite families.
-/

public section

universe v u

open CategoryTheory Simplicial Opposite SSet

namespace CategoryTheory.nerve

variable {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) (b : D)

/-- The nerve of a functor with constant composite lands in the simplicial fiber. -/
lemma nerveMap_comp_eq_const {E : Type u} [Category.{v} E] (G : E ⥤ C)
    (h : G ⋙ F = (Functor.const _).obj b) :
    nerveMap G ≫ nerveMap F = const (nerveEquiv.symm b) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  exact (Functor.assoc _ _ _).trans (by rw [h]; rfl)

/-- Strings in the ordinary fiber correspond to simplices in the strict simplicial fiber. -/
def fiberSimplexEquiv (n : SimplexCategoryᵒᵖ) :
    (nerve (F.Fiber b)).obj n ≃
      (fiber (nerveMap F) (nerveEquiv.symm b) : SSet).obj n where
  toFun s := ⟨s ⋙ Functor.Fiber.fiberInclusion,
    (mem_fiber_iff _ _ _).2 ((Functor.assoc _ _ _).trans (by
      rw [Functor.Fiber.fiberInclusion_comp_eq_const]
      rfl))⟩
  invFun s := Functor.Fiber.inducedFunctor ((mem_fiber_iff _ _ _).1 s.property)
  left_inv s := by
    refine CategoryTheory.Functor.hext (F := Functor.Fiber.inducedFunctor _) (G := s)
      (fun i ↦ Subtype.ext rfl) ?_
    intro i j f
    rfl
  right_inv s := Subtype.ext (Functor.Fiber.inducedFunctor_comp _)

/-- The forward comparison forgets the fiber condition at each object and arrow of a string. -/
-- Normalize the subfunctor simplex type, also in implicit arguments, for simp matching.
@[simp]
lemma fiberSimplexEquiv_apply_coe (n : SimplexCategoryᵒᵖ)
    (s : (nerve (F.Fiber b)).obj n) :
    (dsimp% only [Subfunctor.toFunctor_obj] (fiberSimplexEquiv F b n s).val) =
      s ⋙ Functor.Fiber.fiberInclusion :=
  (rfl)

/-- The inverse comparison lifts a string with constant image to the ordinary fiber. -/
lemma fiberSimplexEquiv_symm_apply (n : SimplexCategoryᵒᵖ)
    (s : (fiber (nerveMap F) (nerveEquiv.symm b) : SSet).obj n) :
    (fiberSimplexEquiv F b n).symm s =
      Functor.Fiber.inducedFunctor ((mem_fiber_iff _ _ _).1 s.property) :=
  (rfl)

/-- Forgetting the fiber condition after lifting recovers the original string. -/
@[simp]
lemma fiberSimplexEquiv_symm_apply_comp (n : SimplexCategoryᵒᵖ)
    (s : (fiber (nerveMap F) (nerveEquiv.symm b) : SSet).obj n) :
    (dsimp% only [Subfunctor.toFunctor_obj]
      (fiberSimplexEquiv F b n).symm s ⋙ Functor.Fiber.fiberInclusion) = s.val :=
  Functor.Fiber.inducedFunctor_comp ((mem_fiber_iff _ _ _).1 s.property)

/-- The comparison commutes with every simplicial operator, including faces and degeneracies. -/
lemma fiberSimplexEquiv_naturality {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n)
    (s : (nerve (F.Fiber b)).obj m) :
    fiberSimplexEquiv F b n ((nerve (F.Fiber b)).map f s) =
      (fiber (nerveMap F) (nerveEquiv.symm b) : SSet).map f
        (fiberSimplexEquiv F b m s) :=
  Subtype.ext (Functor.assoc _ _ _)

/-- The nerve of the ordinary fiber is the strict fiber of the nerve map. -/
def fiberIso : nerve (F.Fiber b) ≅ fiber (nerveMap F) (nerveEquiv.symm b) :=
  NatIso.ofComponents (fun n ↦ (fiberSimplexEquiv F b n).toIso) fun f ↦ by
    ext s
    exact fiberSimplexEquiv_naturality F b f s

/-- The comparison's forward map sends a string to its underlying string. -/
@[simp]
lemma fiberIso_hom_app_coe (n : SimplexCategoryᵒᵖ) (s : (nerve (F.Fiber b)).obj n) :
    (dsimp% only [Subfunctor.toFunctor_obj] ((fiberIso F b).hom.app n s).val) =
      s ⋙ Functor.Fiber.fiberInclusion :=
  (rfl)

/-- The inverse comparison lifts a string and then forgets to the same string. -/
@[simp]
lemma fiberIso_inv_app_comp (n : SimplexCategoryᵒᵖ)
    (s : (fiber (nerveMap F) (nerveEquiv.symm b) : SSet).obj n) :
    (dsimp% only [Subfunctor.toFunctor_obj]
      (fiberIso F b).inv.app n s ⋙ Functor.Fiber.fiberInclusion) = s.val :=
  fiberSimplexEquiv_symm_apply_comp F b n s

/-- The comparison intertwines the two inclusions into the nerve of `C`. -/
@[reassoc (attr := simp)]
lemma fiberIso_hom_ι :
    (fiberIso F b).hom ≫ (fiber (nerveMap F) (nerveEquiv.symm b)).ι =
      nerveMap (Functor.Fiber.fiberInclusion : F.Fiber b ⥤ C) :=
  (rfl)

/-- The inverse comparison intertwines the two inclusions into the nerve of `C`. -/
@[reassoc (attr := simp)]
lemma fiberIso_inv_nerveMap_fiberInclusion :
    (fiberIso F b).inv ≫ nerveMap (Functor.Fiber.fiberInclusion : F.Fiber b ⥤ C) =
      (fiber (nerveMap F) (nerveEquiv.symm b)).ι := by
  rw [← fiberIso_hom_ι, Iso.inv_hom_id_assoc]

/-- The comparison identifies the ordinary and simplicial factorizations of any functor
whose composite with `F` is constant at `b`. -/
lemma nerveMap_inducedFunctor_comp_fiberIso_hom {E : Type u} [Category.{v} E]
    (G : E ⥤ C) (h : G ⋙ F = (Functor.const _).obj b) :
    nerveMap (Functor.Fiber.inducedFunctor h) ≫ (fiberIso F b).hom =
      fiber.lift (nerveMap G) (nerveMap F) (nerveEquiv.symm b)
        (nerveMap_comp_eq_const F b G h) := by
  rw [← cancel_mono (fiber (nerveMap F) (nerveEquiv.symm b)).ι]
  simp only [Category.assoc, fiberIso_hom_ι]
  exact (fiber.lift_ι _ _ _ _).symm

end CategoryTheory.nerve

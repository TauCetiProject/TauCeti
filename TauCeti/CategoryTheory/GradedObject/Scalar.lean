/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# Degree-dependent scalars on graded tensor products

`CategoryTheory.GradedObject.Monoidal.scaleTensorObj` multiplies the summand of bidegree
`(i, j)` by a prescribed scalar. Unit-valued scalars give an automorphism
`scaleTensorIso`. These maps provide tensorators for changes of cocycle in graded categories.
The construction uses Mathlib's `tensorObjDesc` and its coproduct inclusions.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.GradedObject.Monoidal

variable {I R C : Type*} [AddMonoid I] [Semiring R] [Category* C]
  [MonoidalCategory C] [Preadditive C] [Linear R C]
  (X Y : GradedObject I C) [HasTensor X Y]

/-- Multiply the summand of bidegree `(i, j)` by `u i j`. -/
def scaleTensorObj (u : I → I → R) : tensorObj X Y ⟶ tensorObj X Y := fun n ↦
  tensorObjDesc fun i j h ↦ u i j • ιTensorObj X Y i j n h

/-- The action of a degree-dependent scalar on a tensor summand. -/
@[reassoc (attr := simp)]
lemma ι_scaleTensorObj (u : I → I → R) (i j n : I) (h : i + j = n) :
    ιTensorObj X Y i j n h ≫ scaleTensorObj X Y u n =
      u i j • ιTensorObj X Y i j n h := by
  simp [scaleTensorObj]

/-- The constant scalar one acts as the identity. -/
@[simp]
lemma scaleTensorObj_one : scaleTensorObj X Y (fun _ _ ↦ (1 : R)) = 𝟙 _ := by
  ext n i j h
  simp

/-- Composition multiplies the scalar functions. -/
@[reassoc]
lemma scaleTensorObj_comp (u v : I → I → R) :
    scaleTensorObj X Y u ≫ scaleTensorObj X Y v =
      scaleTensorObj X Y (fun i j ↦ u i j * v i j) := by
  ext n i j h
  simp [smul_smul]

variable {X Y}

/-- Degree-dependent scalars commute with maps of graded tensor products. -/
@[reassoc]
lemma tensorHom_scaleTensorObj {X' Y' : GradedObject I C} [HasTensor X' Y']
    (f : X ⟶ X') (g : Y ⟶ Y') (u : I → I → R) :
    tensorHom f g ≫ scaleTensorObj X' Y' u =
      scaleTensorObj X Y u ≫ tensorHom f g := by
  ext n i j h
  simp

variable (X Y)

/-- Unit-valued degree-dependent scalars give an automorphism of a graded tensor product. -/
def scaleTensorIso (u : I → I → Rˣ) : tensorObj X Y ≅ tensorObj X Y where
  hom := scaleTensorObj X Y fun i j ↦ (u i j : R)
  inv := scaleTensorObj X Y fun i j ↦ (((u i j)⁻¹ : Rˣ) : R)
  hom_inv_id := by rw [scaleTensorObj_comp]; simp
  inv_hom_id := by rw [scaleTensorObj_comp]; simp

/-- The forward map of `scaleTensorIso`. -/
@[simp]
lemma scaleTensorIso_hom (u : I → I → Rˣ) :
    (scaleTensorIso X Y u).hom = scaleTensorObj X Y fun i j ↦ (u i j : R) := (rfl)

/-- The inverse map of `scaleTensorIso`. -/
@[simp]
lemma scaleTensorIso_inv (u : I → I → Rˣ) :
    (scaleTensorIso X Y u).inv = scaleTensorObj X Y fun i j ↦ (((u i j)⁻¹ : Rˣ) : R) := (rfl)

section Triple

variable [MonoidalPreadditive C] [MonoidalLinear R C]
  (X Y Z : GradedObject I C) [HasTensor X Y] [HasTensor Y Z]
  [HasTensor (tensorObj X Y) Z] [HasTensor X (tensorObj Y Z)]
  (u : I → I → R) (i j k n : I) (h : i + j + k = n)

omit [MonoidalPreadditive C] [MonoidalLinear R C]
  [HasTensor Y Z] [HasTensor X (tensorObj Y Z)] in
/-- A scalar on the outer left-associated tensor product acts in bidegree `(i + j, k)`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj₃'_scaleTensorObj :
    ιTensorObj₃' X Y Z i j k n h ≫ scaleTensorObj (tensorObj X Y) Z u n =
      u (i + j) k • ιTensorObj₃' X Y Z i j k n h := by
  simp [ιTensorObj₃', Linear.comp_smul]

omit [MonoidalPreadditive C] [MonoidalLinear R C]
  [HasTensor X Y] [HasTensor (tensorObj X Y) Z] in
/-- A scalar on the outer right-associated tensor product acts in bidegree `(i, j + k)`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj₃_scaleTensorObj :
    ιTensorObj₃ X Y Z i j k n h ≫ scaleTensorObj X (tensorObj Y Z) u n =
      u i (j + k) • ιTensorObj₃ X Y Z i j k n h := by
  simp [ιTensorObj₃, Linear.comp_smul]

omit [HasTensor Y Z] [HasTensor X (tensorObj Y Z)] in
/-- Scaling the first two factors of a homogeneous triple acts in bidegree `(i, j)`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj₃'_tensorHom_scaleTensorObj :
    ιTensorObj₃' X Y Z i j k n h ≫ tensorHom (scaleTensorObj X Y u) (𝟙 Z) n =
      u i j • ιTensorObj₃' X Y Z i j k n h := by
  simp [ιTensorObj₃', tensorHom_id, ← MonoidalCategory.comp_whiskerRight_assoc,
    Linear.smul_comp]

omit [HasTensor X Y] [HasTensor (tensorObj X Y) Z] in
/-- Scaling the last two factors of a homogeneous triple acts in bidegree `(j, k)`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj₃_tensorHom_scaleTensorObj :
    ιTensorObj₃ X Y Z i j k n h ≫ tensorHom (𝟙 X) (scaleTensorObj Y Z u) n =
      u j k • ιTensorObj₃ X Y Z i j k n h := by
  simp [ιTensorObj₃, id_tensorHom, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Linear.smul_comp]

end Triple

section Unit

variable [DecidableEq I] [Limits.HasInitial C]
  [∀ X, Limits.PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
  [∀ X, Limits.PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]

omit [∀ X, Limits.PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)] in
/-- A scalar function normalized on the left acts trivially when the first object is the unit. -/
lemma scaleTensorObj_tensorUnit_left (X : GradedObject I C) [HasTensor tensorUnit X]
    (u : I → I → R) (hu : ∀ i, u 0 i = 1) :
    scaleTensorObj tensorUnit X u = 𝟙 _ := by
  ext n i j h
  by_cases hi : i = 0
  · subst hi
    simp [hu]
  · exact ((isInitialTensorUnitApply i hi).isInitialObj
      ((curriedTensor C).flip.obj (X j))).hom_ext _ _

omit [∀ X, Limits.PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)] in
/-- A scalar function normalized on the right acts trivially when the second object is the unit. -/
lemma scaleTensorObj_tensorUnit_right (X : GradedObject I C) [HasTensor X tensorUnit]
    (u : I → I → R) (hu : ∀ i, u i 0 = 1) :
    scaleTensorObj X tensorUnit u = 𝟙 _ := by
  ext n i j h
  by_cases hj : j = 0
  · subst hj
    simp [hu]
  · exact ((isInitialTensorUnitApply j hj).isInitialObj
      ((curriedTensor C).obj (X i))).hom_ext _ _

end Unit

end CategoryTheory.GradedObject.Monoidal

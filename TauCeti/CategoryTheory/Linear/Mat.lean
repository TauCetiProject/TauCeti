/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.Mat
public import TauCeti.CategoryTheory.Linear.Biproduct

/-!
# Linear structure on the matrix category

Mathlib equips the additive envelope `Mat_ C` of a preadditive category `C`, whose objects are
finite families of objects of `C` and whose morphisms are matrices of morphisms of `C`, with its
preadditive structure only. This file shows that an `R`-linear structure on `C` also passes to
`Mat_ C`, with scalars acting entrywise on matrices.

The embedding `Mat_.embedding C` is then `R`-linear, and so are the functor
`F.mapMat_ : Mat_ C ⥤ Mat_ D` and, when `D` has finite biproducts, the extension
`Mat_.lift F : Mat_ C ⥤ D` of an `R`-linear functor `F : C ⥤ D`.

The same holds for Mathlib's matrix category `Mat R` over a ring `R`: when `R` is an algebra
over a commutative semiring `S`, or more generally an `S`-module on which `S` commutes and
associates with multiplication, the category `Mat R` is `S`-linear.

Together with the linear structure on `Karoubi C` (`TauCeti/CategoryTheory/Linear/Karoubi.lean`),
this makes the additive and idempotent envelope `Karoubi (Mat_ C)` of an `R`-linear category
`R`-linear.

## Main results

* `CategoryTheory.Mat_.smul_apply`: scalars act entrywise on matrices.
* The instance `CategoryTheory.Linear R (Mat_ C)`.
* `CategoryTheory.Mat.instLinear`: the matrix category `Mat R` of an `S`-algebra `R` is
  `S`-linear, with scalars acting entrywise (`CategoryTheory.Mat.smul_apply`).
* The instances `(Mat_.embedding C).Linear R`, `F.mapMat_.Linear R` and
  `(Mat_.lift F).Linear R` for an `R`-linear functor `F`.
-/

public section

namespace CategoryTheory

open Limits

universe w v₁ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {R : Type w} [Semiring R] [Linear R C]

namespace Mat_

/-- The `R`-module of matrices of morphisms between two objects of `Mat_ C`, with scalars acting
entrywise. -/
instance instModuleHom (M N : Mat_ C) : Module R (M ⟶ N) :=
  inferInstanceAs <| Module R (∀ i j, M.X i ⟶ N.X j)

/-- Scalars act entrywise on matrices of morphisms. -/
@[simp]
theorem smul_apply {M N : Mat_ C} (r : R) (f : M ⟶ N) (i : M.ι) (j : N.ι) :
    (r • f) i j = r • f i j :=
  (rfl)

/-- The matrix category of an `R`-linear category is `R`-linear. -/
instance : Linear R (Mat_ C) where
  smul_comp _ _ _ r f g := by
    ext
    simp [Finset.smul_sum]
  comp_smul _ _ _ f r g := by
    ext
    simp [Finset.smul_sum]

/-- The embedding of `C` into `Mat_ C` as one-by-one matrices is `R`-linear. -/
instance : (embedding C).Linear R where

variable {D : Type u₂} [Category.{v₁} D] [Preadditive D] [Linear R D]

/-- The functor induced on matrix categories by an `R`-linear functor is `R`-linear. -/
instance (F : C ⥤ D) [F.Additive] [F.Linear R] : F.mapMat_.Linear R where
  map_smul f r := by
    ext i j
    -- `F.mapMat_` applies `F.map` entrywise (`Functor.mapMat__map`), and scalars act entrywise
    -- (`Mat_.smul_apply`). Neither lemma rewrites here, since the types of `i` and `j` mention
    -- `F.mapMat_.obj`, so the goal is closed up to these two definitional unfoldings.
    exact (F.map_smul r (f i j) :)

variable {E : Type u₁} [Category.{v₁} E] [Preadditive E] [Linear R E]

/-- The extension `Mat_.lift F : Mat_ C ⥤ E` of an `R`-linear functor `F : C ⥤ E` is
`R`-linear. -/
instance lift_linear [HasFiniteBiproducts E] (F : C ⥤ E) [F.Additive] [F.Linear R] :
    (lift F).Linear R where
  map_smul f r := by
    simp only [lift_map, smul_apply, F.map_smul]
    exact biproduct.matrix_smul r _

end Mat_

namespace Mat

variable {R : Type} [Ring R] {S : Type w} [Semiring S] [Module S R]

/-- The `S`-module of `X × Y` matrices over `R`, as morphisms of `Mat R`. -/
instance instModuleHom (X Y : Mat R) : Module S (X ⟶ Y) :=
  inferInstanceAs <| Module S (Matrix X Y R)

/-- Scalars act entrywise on matrices. -/
@[simp]
theorem smul_apply {X Y : Mat R} (s : S) (f : X ⟶ Y) (i : X) (j : Y) :
    (s • f) i j = s • f i j :=
  (rfl)

/-- The matrix category `Mat R` is `S`-linear when scalars from `S` commute and associate with
multiplication in `R`, for instance when `R` is an `S`-algebra. -/
instance instLinear [IsScalarTower S R R] [SMulCommClass S R R] : Linear S (Mat R) where
  smul_comp _ _ _ s f g := by
    ext
    simp [Finset.smul_sum, smul_mul_assoc]
  comp_smul _ _ _ f s g := by
    ext
    simp [Finset.smul_sum, mul_smul_comm]

end Mat

end CategoryTheory

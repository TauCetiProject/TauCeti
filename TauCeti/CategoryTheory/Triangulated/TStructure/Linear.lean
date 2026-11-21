/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Linear truncation equivalences for t-structures

In an `R`-linear pretriangulated category equipped with a t-structure `t`, the universal properties
of canonical truncations lift to `R`-linear equivalences on morphism modules:

* `CategoryTheory.Triangulated.TStructure.homTruncGELinearEquiv`: precomposition with
  `(t.truncGEπ n).app X` identifies `(t.truncGE n).obj X ⟶ Y` with `X ⟶ Y` linearly whenever
  `t.IsGE Y n`.
* `CategoryTheory.Triangulated.TStructure.homTruncLELinearEquiv`: postcomposition with
  `(t.truncLEι n).app Y` identifies `X ⟶ (t.truncLE n).obj Y` with `X ⟶ Y` linearly whenever
  `t.IsLE X n`.

These equivalences provide the truncation reduction step for Hom finiteness in derived categories
(used in `TauCeti.Algebra.Homology.DerivedCategory.FiniteHom`), reducing `X ⟶ Y` to a morphism
space between bounded truncations without requiring lower bounds on `X` or upper bounds on `Y`.
-/

public section

open CategoryTheory Limits Pretriangulated

universe t' v u

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)
  (R : Type t') [Semiring R] [Linear R C]

/-- Precomposition with `(t.truncGEπ n).app X` gives an `R`-linear equivalence
`((t.truncGE n).obj X ⟶ Y) ≃ₗ[R] (X ⟶ Y)` whenever `t.IsGE Y n`. -/
noncomputable def homTruncGELinearEquiv (X Y : C) (n : ℤ) [t.IsGE Y n] :
    ((t.truncGE n).obj X ⟶ Y) ≃ₗ[R] (X ⟶ Y) where
  toFun f := (t.truncGEπ n).app X ≫ f
  invFun g := t.descTruncGE g n
  left_inv f := t.from_truncGE_obj_ext (by simp)
  right_inv g := t.π_descTruncGE g n
  map_add' f₁ f₂ := Preadditive.comp_add _ _ _ _ _ _
  map_smul' r f := by simp

/-- Applying `homTruncGELinearEquiv` precomposes with `(t.truncGEπ n).app X`. -/
@[simp]
theorem homTruncGELinearEquiv_apply (X Y : C) (n : ℤ) [t.IsGE Y n]
    (f : (t.truncGE n).obj X ⟶ Y) :
    t.homTruncGELinearEquiv R X Y n f = (t.truncGEπ n).app X ≫ f :=
  (rfl)

/-- The inverse of `homTruncGELinearEquiv` is `TStructure.descTruncGE`. -/
@[simp]
theorem homTruncGELinearEquiv_symm_apply (X Y : C) (n : ℤ) [t.IsGE Y n] (g : X ⟶ Y) :
    (t.homTruncGELinearEquiv R X Y n).symm g = t.descTruncGE g n :=
  (rfl)

/-- Postcomposition with `(t.truncLEι n).app Y` gives an `R`-linear equivalence
`(X ⟶ (t.truncLE n).obj Y) ≃ₗ[R] (X ⟶ Y)` whenever `t.IsLE X n`. -/
noncomputable def homTruncLELinearEquiv (X Y : C) (n : ℤ) [t.IsLE X n] :
    (X ⟶ (t.truncLE n).obj Y) ≃ₗ[R] (X ⟶ Y) where
  toFun f := f ≫ (t.truncLEι n).app Y
  invFun g := t.liftTruncLE g n
  left_inv f := t.to_truncLE_obj_ext (by simp)
  right_inv g := t.liftTruncLE_ι g n
  map_add' f₁ f₂ := Preadditive.add_comp _ _ _ _ _ _
  map_smul' r f := by simp

/-- Applying `homTruncLELinearEquiv` postcomposes with `(t.truncLEι n).app Y`. -/
@[simp]
theorem homTruncLELinearEquiv_apply (X Y : C) (n : ℤ) [t.IsLE X n]
    (f : X ⟶ (t.truncLE n).obj Y) :
    t.homTruncLELinearEquiv R X Y n f = f ≫ (t.truncLEι n).app Y :=
  (rfl)

/-- The inverse of `homTruncLELinearEquiv` is `TStructure.liftTruncLE`. -/
@[simp]
theorem homTruncLELinearEquiv_symm_apply (X Y : C) (n : ℤ) [t.IsLE X n] (g : X ⟶ Y) :
    (t.homTruncLELinearEquiv R X Y n).symm g = t.liftTruncLE g n :=
  (rfl)

end CategoryTheory.Triangulated.TStructure

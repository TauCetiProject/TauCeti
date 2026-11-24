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

Together with the linear structure on `Karoubi C` (`TauCeti/CategoryTheory/Linear/Karoubi.lean`),
this makes the additive and idempotent envelope `Karoubi (Mat_ C)` of an `R`-linear category
`R`-linear.

## Main results

* `CategoryTheory.Mat_.smul_apply`: scalars act entrywise on matrices.
* The instance `CategoryTheory.Linear R (Mat_ C)`.
* The instances `(Mat_.embedding C).Linear R`, `F.mapMat_.Linear R` and
  `(Mat_.lift F).Linear R` for an `R`-linear functor `F`.
* `CategoryTheory.Mat_.ext_hom_app`: the components of the isomorphism `Mat_.ext α` of additive
  functors out of `Mat_ C`.
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

/-- The components of `Mat_.ext α`: on `M`, decompose `G M` as the biproduct of the `G` of the
entries of `M`, apply `α` entrywise, and reassemble. -/
theorem ext_hom_app [HasFiniteBiproducts E] {G G' : Mat_ C ⥤ E} [G.Additive] [G'.Additive]
    (α : embedding C ⋙ G ≅ embedding C ⋙ G') (M : Mat_ C) :
    (ext α).hom.app M = (additiveObjIsoBiproduct G M).hom ≫
      biproduct.map (fun i ↦ α.hom.app (M.X i)) ≫ (additiveObjIsoBiproduct G' M).inv := by
  simp only [ext, liftUnique, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.cancel_iso_hom_left]
  simp only [biproduct.mapIso_hom, biproduct.mapIso_inv, Iso.app_hom, Iso.app_inv, Iso.refl_inv,
    NatTrans.id_app]
  -- The remaining middle factor is the biproduct of identities.
  congr 1
  conv_rhs => rw [← Category.id_comp (additiveObjIsoBiproduct G' M).inv]
  congr 1
  ext j
  simp

end Mat_

end CategoryTheory

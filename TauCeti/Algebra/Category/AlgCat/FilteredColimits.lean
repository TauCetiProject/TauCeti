/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Filtered colimits of algebras: modules and tensor products

The forgetful functor from algebras over a commutative ring `R` to `R`-modules preserves small
filtered colimits. Both categories compute such colimits on underlying types, and the forgetful
functor from `R`-modules to types reflects them, so this follows from the corresponding fact for
the forgetful functor from algebras to types. It lets module-theoretic properties of a filtered
colimit of algebras, such as flatness, be read off from the colimit of the underlying modules.

Every element of the tensor product of two filtered colimits of algebras comes from the tensor
product of two stages at a common index (`isColimit_exists_tensor_rep`).
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

universe v u

namespace AlgCat

variable {R : Type u} [CommRing R]

/-- The forgetful functor from algebras to modules preserves small filtered colimits. -/
noncomputable instance forget₂Module_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) where
  preserves_filtered_colimits J _ _ :=
    have : PreservesColimitsOfShape J
        (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R) ⋙ forget (ModuleCat.{u} R)) :=
      preservesColimitsOfShape_of_natIso (eqToIso HasForget₂.forget_comp).symm
    preservesColimitsOfShape_of_reflects_of_preserves _ (forget (ModuleCat.{u} R))

/-- Tensor products of cocone legs are compatible with the maps of the two diagrams. -/
theorem tensorProduct_map_ι_app_map {J : Type*} [Category* J]
    {F G : J ⥤ AlgCat.{v} R} (c : Cocone F) (d : Cocone G)
    {j k : J} (f : j ⟶ k) (y : F.obj j ⊗[R] G.obj j) :
    Algebra.TensorProduct.map (c.ι.app k).hom (d.ι.app k).hom
        (Algebra.TensorProduct.map (F.map f).hom (G.map f).hom y) =
      Algebra.TensorProduct.map (c.ι.app j).hom (d.ι.app j).hom y := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
  simp [← hom_comp]

/-- Every element of the tensor product of two filtered colimits comes from the tensor
product of stages at a common index. -/
theorem isColimit_exists_tensor_rep {J : Type v} [SmallCategory J] [IsFiltered J]
    {F G : J ⥤ AlgCat.{v} R} {c : Cocone F} {d : Cocone G}
    (hc : IsColimit c) (hd : IsColimit d) (x : c.pt ⊗[R] d.pt) :
    ∃ j, ∃ y : F.obj j ⊗[R] G.obj j,
      Algebra.TensorProduct.map (c.ι.app j).hom (d.ι.app j).hom y = x := by
  induction x with
  | tmul a b =>
    obtain ⟨i, a, rfl⟩ := Concrete.isColimit_exists_rep F hc a
    obtain ⟨j, b, rfl⟩ := Concrete.isColimit_exists_rep G hd b
    -- `simp` applies `map_tmul` and the cocone conditions `c.w`, `d.w` elementwise.
    exact ⟨IsFiltered.max i j,
      F.map (IsFiltered.leftToMax i j) a ⊗ₜ[R] G.map (IsFiltered.rightToMax i j) b, by simp⟩
  | add a b ha hb =>
    obtain ⟨i, a, rfl⟩ := ha
    obtain ⟨j, b, rfl⟩ := hb
    refine ⟨IsFiltered.max i j,
      Algebra.TensorProduct.map (F.map (IsFiltered.leftToMax i j)).hom
          (G.map (IsFiltered.leftToMax i j)).hom a +
        Algebra.TensorProduct.map (F.map (IsFiltered.rightToMax i j)).hom
          (G.map (IsFiltered.rightToMax i j)).hom b, ?_⟩
    rw [map_add, tensorProduct_map_ι_app_map, tensorProduct_map_ι_app_map]

end AlgCat

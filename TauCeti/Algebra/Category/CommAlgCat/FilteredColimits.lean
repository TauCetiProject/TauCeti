/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Filtered colimits in commutative algebras

The forgetful functor from commutative algebras over a base ring to types preserves small
filtered colimits. This is deduced from the corresponding fact for commutative rings, using the
equivalence between commutative algebras and commutative rings under the base. Since the
forgetful functor from algebras to types reflects filtered colimits, the forgetful functor from
commutative algebras to algebras preserves them as well.

Every element of the tensor product of two such colimits comes from the tensor product
of two stages at a common index (`isColimit_exists_tensor_rep`).
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace CommAlgCat

variable {Base : Type u} [CommRing Base]

/-- The forgetful functor from commutative algebras to types is the composite of the equivalence
with commutative rings under the base, the forgetful functor to commutative rings, and the
forgetful functor to types. -/
@[expose, simps!]
def forgetIsoUnderForget : forget (CommAlgCat.{u} Base) ≅
    (commAlgCatEquivUnder (CommRingCat.of Base)).functor ⋙
      Under.forget (CommRingCat.of Base) ⋙ forget CommRingCat.{u} :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The forgetful functor from commutative algebras to types preserves small filtered colimits. -/
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget (CommAlgCat.{u} Base)) :=
  ⟨fun _ _ _ => preservesColimitsOfShape_of_natIso (forgetIsoUnderForget (Base := Base)).symm⟩

/-- The forgetful functor from commutative algebras to algebras preserves small filtered
colimits. -/
noncomputable instance forget₂AlgCat_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ (CommAlgCat.{u} Base) (AlgCat.{u} Base)) where
  preserves_filtered_colimits J _ _ :=
    have : PreservesColimitsOfShape J
        (forget₂ (CommAlgCat.{u} Base) (AlgCat.{u} Base) ⋙ forget (AlgCat.{u} Base)) :=
      preservesColimitsOfShape_of_natIso (eqToIso HasForget₂.forget_comp).symm
    have : ReflectsColimitsOfShape J (forget (AlgCat.{u} Base)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    preservesColimitsOfShape_of_reflects_of_preserves _ (forget (AlgCat.{u} Base))

/-- Every element of the tensor product of two filtered colimits comes from the tensor
product of stages at a common index. -/
theorem isColimit_exists_tensor_rep {J : Type u} [SmallCategory J] [IsFiltered J]
    {F G : J ⥤ CommAlgCat.{u} Base} {c : Cocone F} {d : Cocone G}
    (hc : IsColimit c) (hd : IsColimit d) (x : c.pt ⊗[Base] d.pt) :
    ∃ j, ∃ y : F.obj j ⊗[Base] G.obj j,
      Algebra.TensorProduct.map (c.ι.app j).hom (d.ι.app j).hom y = x := by
  classical
  have hw (j k : J) (f : j ⟶ k) (y : F.obj j ⊗[Base] G.obj j) :
      Algebra.TensorProduct.map (c.ι.app k).hom (d.ι.app k).hom
          (Algebra.TensorProduct.map (F.map f).hom (G.map f).hom y) =
        Algebra.TensorProduct.map (c.ι.app j).hom (d.ι.app j).hom y := by
    have h : (Algebra.TensorProduct.map (c.ι.app k).hom (d.ι.app k).hom).comp
        (Algebra.TensorProduct.map (F.map f).hom (G.map f).hom) =
        Algebra.TensorProduct.map (c.ι.app j).hom (d.ι.app j).hom := by
      rw [← Algebra.TensorProduct.map_comp, ← hom_comp, ← hom_comp, c.w f, d.w f]
    exact DFunLike.congr_fun h y
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨i, a, rfl⟩ := Concrete.isColimit_exists_rep F hc a
    obtain ⟨j, b, rfl⟩ := Concrete.isColimit_exists_rep G hd b
    refine ⟨IsFiltered.max i j,
      F.map (IsFiltered.leftToMax i j) a ⊗ₜ[Base]
        G.map (IsFiltered.rightToMax i j) b, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul]
    congr 1
    · exact ConcreteCategory.congr_hom (c.w (IsFiltered.leftToMax i j)) a
    · exact ConcreteCategory.congr_hom (d.w (IsFiltered.rightToMax i j)) b
  | add a b ha hb =>
    obtain ⟨i, a, rfl⟩ := ha
    obtain ⟨j, b, rfl⟩ := hb
    refine ⟨IsFiltered.max i j,
      Algebra.TensorProduct.map (F.map (IsFiltered.leftToMax i j)).hom
          (G.map (IsFiltered.leftToMax i j)).hom a +
        Algebra.TensorProduct.map (F.map (IsFiltered.rightToMax i j)).hom
          (G.map (IsFiltered.rightToMax i j)).hom b, ?_⟩
    rw [map_add, hw, hw]

end CommAlgCat

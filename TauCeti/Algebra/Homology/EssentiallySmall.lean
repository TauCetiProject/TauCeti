/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# Essential smallness of categories of complexes and of homotopy categories

If `C` is essentially small relative to a universe `w` and the index type of a complex shape is
`w`-small, then the category `HomologicalComplex C c` is essentially small relative to `w`. Every
complex is isomorphic to one whose terms are chosen among the objects of a small model of `C`:
transport each term along the unit of the equivalence `C ≌ SmallModel C`, and conjugate the
differentials accordingly. Complexes with such terms are indexed by a family of terms and a
compatible family of differentials, and that indexing type is small. The homotopy category has the
same objects and quotient morphism types, so it inherits both smallness properties.

This is what makes categories built from complexes over an essentially small category, such as the
homotopy category of bounded complexes, eligible for categorical Grothendieck groups.

## Main results

* `HomologicalComplex.essentiallySmall`: complexes over an essentially small category, indexed by
  a small type, form an essentially small category.
* `HomotopyCategory.locallySmall` and `HomotopyCategory.essentiallySmall`: the same holds for the
  homotopy category.
-/

public section

open CategoryTheory Limits

universe w v u t

namespace HomologicalComplex

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C] {ι : Type t} (c : ComplexShape ι)

/-- Complexes over a `w`-essentially small category, indexed by a `w`-small type, form a
`w`-essentially small category. -/
instance essentiallySmall [EssentiallySmall.{w} C] [Small.{w} ι] :
    EssentiallySmall.{w} (HomologicalComplex C c) := by
  rw [essentiallySmall_iff_objectPropertyEssentiallySmall]
  refine ⟨inferInstance, ⟨?_⟩⟩
  let E := equivSmallModel.{w} C
  -- The complexes whose terms are objects `E.inverse.obj x` of the chosen small model, indexed
  -- by their terms and differentials.
  let I := Σ x : ι → SmallModel.{w} C,
    {d : ∀ i j, E.inverse.obj (x i) ⟶ E.inverse.obj (x j) //
      (∀ i j, ¬ c.Rel i j → d i j = 0) ∧ ∀ i j k, d i j ≫ d j k = 0}
  let F : I → HomologicalComplex C c := fun x ↦
    { X i := E.inverse.obj (x.1 i)
      d := x.2.1
      shape := x.2.2.1
      d_comp_d' i j k _ _ := x.2.2.2 i j k }
  refine ⟨ObjectProperty.ofObj F, inferInstance, fun K _ ↦ ?_⟩
  let e (i : ι) : K.X i ≅ E.inverse.obj (E.functor.obj (K.X i)) := E.unitIso.app (K.X i)
  let x : I := ⟨fun i ↦ E.functor.obj (K.X i), fun i j ↦ (e i).inv ≫ K.d i j ≫ (e j).hom,
    fun i j h ↦ by simp [K.shape i j h], fun i j k ↦ by simp⟩
  exact ⟨F x, ⟨x⟩, ⟨Hom.isoOfComponents e fun i j _ ↦ by simp [F, x]⟩⟩

end HomologicalComplex

namespace HomotopyCategory

variable (C : Type u) [Category.{v} C] [Preadditive C] {ι : Type t} (c : ComplexShape ι)

/-- The homotopy category of complexes over a `w`-locally small category, indexed by a `w`-small
type, is `w`-locally small. -/
instance locallySmall [LocallySmall.{w} C] [Small.{w} ι] :
    LocallySmall.{w} (HomotopyCategory C c) where
  hom_small _ _ := small_of_surjective (quotient C c).map_surjective

/-- The homotopy category of complexes over a `w`-essentially small category, indexed by a
`w`-small type, is `w`-essentially small. -/
instance essentiallySmall [EssentiallySmall.{w} C] [Small.{w} ι] :
    EssentiallySmall.{w} (HomotopyCategory C c) := by
  rw [essentiallySmall_iff_objectPropertyEssentiallySmall]
  exact ⟨inferInstance, .of_le (Q := (quotient C c).essImage) fun K _ ↦
    (quotient C c).essImage.prop_of_iso ((quotient C c).objObjPreimageIso K)
      ((quotient C c).obj_mem_essImage _)⟩

end HomotopyCategory

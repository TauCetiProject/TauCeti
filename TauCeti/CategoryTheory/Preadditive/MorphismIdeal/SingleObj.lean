/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.OneSided

/-!
# One-sided ideals in the category of a ring

Under the identification of the morphisms of `SingleObj Aᵐᵒᵖ` with `A` via `MulOpposite.unop`,
categorical precomposition corresponds to left multiplication, and postcomposition to right
multiplication. The resulting order isomorphisms identify the principal right ideals on both sides.
-/

public section

open CategoryTheory

namespace TauCeti

variable (A : Type*) [Ring A]

namespace LeftMorphismIdeal

private def ofIdeal (I : Ideal A) : LeftMorphismIdeal (SingleObj Aᵐᵒᵖ) :=
  ofHom
    (fun _ _ ↦ I.toAddSubgroup.comap
      (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ).symm.toAddMonoidHom)
    (by
      intro X Y Z f g hg
      exact I.smul_mem (MulOpposite.unop f) hg)

private theorem mem_ofIdeal_hom (I : Ideal A) {X Y : SingleObj Aᵐᵒᵖ} (f : X ⟶ Y) :
    f ∈ (ofIdeal A I).hom X Y ↔ MulOpposite.unop f ∈ I :=
  Eq.to_iff (congrArg (fun S : AddSubgroup (X ⟶ Y) ↦ f ∈ S) (hom_ofHom _ _ X Y))

private def toIdeal (J : LeftMorphismIdeal (SingleObj Aᵐᵒᵖ)) : Ideal A :=
  { toAddSubmonoid := ((J.hom (SingleObj.star _) (SingleObj.star _)).comap
      (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ).toAddMonoidHom).toAddSubmonoid
    smul_mem' := fun a x hg ↦ J.comp_mem (X := SingleObj.star _) (Y := SingleObj.star _)
      (MulOpposite.op a) (g := MulOpposite.op x) hg }

private theorem mem_toIdeal (J : LeftMorphismIdeal (SingleObj Aᵐᵒᵖ)) (a : A) :
    a ∈ toIdeal A J ↔ MulOpposite.op a ∈ J.hom (SingleObj.star _) (SingleObj.star _) := Iff.rfl

/-- Left ideals of a ring identify with left morphism ideals of its one-object category. -/
def singleObjOrderIso : Ideal A ≃o LeftMorphismIdeal (SingleObj Aᵐᵒᵖ) where
  toFun := ofIdeal A
  invFun := toIdeal A
  left_inv I := Submodule.ext fun a ↦
    (mem_toIdeal A _ a).trans (mem_ofIdeal_hom A I (MulOpposite.op a))
  right_inv J := LeftMorphismIdeal.ext fun {_ _} f ↦
    (mem_ofIdeal_hom A _ f).trans (mem_toIdeal A J (MulOpposite.unop f))
  map_rel_iff' := by
    intro I J
    rw [LeftMorphismIdeal.le_def]
    refine ⟨fun h a ha ↦ ?_, fun h X Y f hf ↦ ?_⟩
    · let f : SingleObj.star Aᵐᵒᵖ ⟶ SingleObj.star Aᵐᵒᵖ := MulOpposite.op a
      exact (mem_ofIdeal_hom A J f).mp (h _ _ ((mem_ofIdeal_hom A I f).mpr ha))
    · exact (mem_ofIdeal_hom A J f).mpr (h ((mem_ofIdeal_hom A I f).mp hf))

@[simp]
theorem mem_singleObjOrderIso_hom (I : Ideal A) {X Y : SingleObj Aᵐᵒᵖ} (f : X ⟶ Y) :
    f ∈ (singleObjOrderIso A I).hom X Y ↔ MulOpposite.unop f ∈ I :=
  mem_ofIdeal_hom A I f

@[simp]
theorem mem_singleObjOrderIso_symm (J : LeftMorphismIdeal (SingleObj Aᵐᵒᵖ)) (a : A) :
    a ∈ (singleObjOrderIso A).symm J ↔
      MulOpposite.op a ∈ J.hom (SingleObj.star _) (SingleObj.star _) :=
  mem_toIdeal A J a

end LeftMorphismIdeal

namespace RightMorphismIdeal

private def ofRightIdeal (I : Submodule Aᵐᵒᵖ A) : RightMorphismIdeal (SingleObj Aᵐᵒᵖ) :=
  ofHom
    (fun _ _ ↦ I.toAddSubgroup.comap
      (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ).symm.toAddMonoidHom)
    (by
      intro X Y Z f g hf
      exact I.smul_mem g hf)

private theorem mem_ofRightIdeal_hom (I : Submodule Aᵐᵒᵖ A) {X Y : SingleObj Aᵐᵒᵖ} (f : X ⟶ Y) :
    f ∈ (ofRightIdeal A I).hom X Y ↔ MulOpposite.unop f ∈ I :=
  Eq.to_iff (congrArg (fun S : AddSubgroup (X ⟶ Y) ↦ f ∈ S) (hom_ofHom _ _ X Y))

private def toRightIdeal (J : RightMorphismIdeal (SingleObj Aᵐᵒᵖ)) : Submodule Aᵐᵒᵖ A :=
  { toAddSubmonoid := ((J.hom (SingleObj.star _) (SingleObj.star _)).comap
      (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ).toAddMonoidHom).toAddSubmonoid
    smul_mem' := fun a x hf ↦ J.comp_mem (Y := SingleObj.star _) (Z := SingleObj.star _)
      (f := MulOpposite.op x) a hf }

private theorem mem_toRightIdeal (J : RightMorphismIdeal (SingleObj Aᵐᵒᵖ)) (a : A) :
    a ∈ toRightIdeal A J ↔ MulOpposite.op a ∈ J.hom (SingleObj.star _) (SingleObj.star _) := Iff.rfl

/-- Right ideals of a ring identify with right morphism ideals of its one-object category. -/
def singleObjOrderIso : Submodule Aᵐᵒᵖ A ≃o RightMorphismIdeal (SingleObj Aᵐᵒᵖ) where
  toFun := ofRightIdeal A
  invFun := toRightIdeal A
  left_inv I := Submodule.ext fun a ↦
    (mem_toRightIdeal A _ a).trans (mem_ofRightIdeal_hom A I (MulOpposite.op a))
  right_inv J := RightMorphismIdeal.ext fun {_ _} f ↦
    (mem_ofRightIdeal_hom A _ f).trans (mem_toRightIdeal A J (MulOpposite.unop f))
  map_rel_iff' := by
    intro I J
    rw [RightMorphismIdeal.le_def]
    refine ⟨fun h a ha ↦ ?_, fun h X Y f hf ↦ ?_⟩
    · let f : SingleObj.star Aᵐᵒᵖ ⟶ SingleObj.star Aᵐᵒᵖ := MulOpposite.op a
      exact (mem_ofRightIdeal_hom A J f).mp (h _ _ ((mem_ofRightIdeal_hom A I f).mpr ha))
    · exact (mem_ofRightIdeal_hom A J f).mpr (h ((mem_ofRightIdeal_hom A I f).mp hf))

@[simp]
theorem mem_singleObjOrderIso_hom (I : Submodule Aᵐᵒᵖ A) {X Y : SingleObj Aᵐᵒᵖ} (f : X ⟶ Y) :
    f ∈ (singleObjOrderIso A I).hom X Y ↔ MulOpposite.unop f ∈ I :=
  mem_ofRightIdeal_hom A I f

@[simp]
theorem mem_singleObjOrderIso_symm (J : RightMorphismIdeal (SingleObj Aᵐᵒᵖ)) (a : A) :
    a ∈ (singleObjOrderIso A).symm J ↔
      MulOpposite.op a ∈ J.hom (SingleObj.star _) (SingleObj.star _) :=
  mem_toRightIdeal A J a

/-- The span of `a` as a right ideal of `A` corresponds to the principal right morphism ideal
generated by `MulOpposite.op a`. -/
@[simp]
theorem singleObjOrderIso_span_singleton (a : A) :
    singleObjOrderIso A (Submodule.span Aᵐᵒᵖ {a}) =
      principal (X := SingleObj.star Aᵐᵒᵖ) (Y := SingleObj.star Aᵐᵒᵖ) (MulOpposite.op a) := by
  apply RightMorphismIdeal.ext
  intro X Y f
  have hX : X = SingleObj.star Aᵐᵒᵖ := Subsingleton.elim _ _
  subst X
  rw [mem_singleObjOrderIso_hom, mem_principal_hom, Submodule.mem_span_singleton]
  exact exists_congr fun _ ↦
    ⟨fun h ↦ MulOpposite.unop_injective h, fun h ↦ congrArg MulOpposite.unop h⟩

end RightMorphismIdeal

end TauCeti

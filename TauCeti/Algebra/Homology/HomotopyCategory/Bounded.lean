/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# The homotopy category of bounded cochain complexes

This file constructs the full pretriangulated subcategory of the homotopy category whose objects
are represented by cochain complexes vanishing outside a finite interval. It also constructs the
quotient functor from bounded cochain complexes and proves that this functor is full and
essentially surjective.

The boundedness predicate records both bounds at once. This matters for closure under cones: if
the source and target of a cochain map are bounded, the standard mapping cone is bounded by the
minimum of their lower bounds and the maximum of their upper bounds. Consequently the full
subcategory is stable under shifts and distinguished triangles.

The construction follows the organization of Mathlib's bounded-below category
`HomotopyCategory.Plus`, replacing its one-sided support condition by two-sided boundedness.

## Main definitions

* `TauCeti.boundedCochainComplex`: the property of being strictly bounded above and below.
* `TauCeti.BoundedCochainComplex`: the full subcategory of bounded cochain complexes.
* `TauCeti.boundedHomotopyCategory`: the corresponding property in the homotopy category.
* `TauCeti.BoundedHomotopyCategory`: the homotopy category of bounded cochain complexes.
* `TauCeti.BoundedHomotopyCategory.quotient`: the quotient functor from bounded complexes.

## References

* Mathlib's `Mathlib/Algebra/Homology/HomotopyCategory/Plus.lean`, whose construction of the
  bounded-below homotopy category supplies the formal pattern used here.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Exercise 9.15.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
  HomologicalComplex

universe v u

variable (C : Type u) [Category.{v} C]

/-- A cochain complex is bounded when it is strictly bounded both below and above. -/
def boundedCochainComplex [HasZeroMorphisms C] : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ CochainComplex.plus C K ∧ ∃ b : ℤ, K.IsStrictlyLE b

/-- The elementwise characterization of a bounded cochain complex. -/
lemma boundedCochainComplex_iff [HasZeroMorphisms C] (K : CochainComplex C ℤ) :
    boundedCochainComplex C K ↔ ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b := by
  constructor
  · rintro ⟨⟨a, ha⟩, b, hb⟩
    exact ⟨a, b, ha, hb⟩
  · rintro ⟨a, b, ha, hb⟩
    exact ⟨⟨a, ha⟩, b, hb⟩

instance [HasZeroMorphisms C] : (boundedCochainComplex C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro K L e h
    rw [boundedCochainComplex_iff] at h ⊢
    obtain ⟨a, b, ha, hb⟩ := h
    let _ := ha
    let _ := hb
    exact ⟨a, b, K.isStrictlyGE_of_iso e a, K.isStrictlyLE_of_iso e b⟩

instance [Preadditive C] : (boundedCochainComplex C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    ⟨by
      rintro K h
      rw [boundedCochainComplex_iff] at h
      obtain ⟨a, b, ha, hb⟩ := h
      rw [ObjectProperty.prop_shift_iff, boundedCochainComplex_iff]
      let _ := ha
      let _ := hb
      exact ⟨a - n, b - n, K.isStrictlyGE_shift a n (a - n) (by omega),
        K.isStrictlyLE_shift b n (b - n) (by omega)⟩⟩

/-- The full subcategory of bounded cochain complexes. -/
abbrev BoundedCochainComplex [HasZeroMorphisms C] :=
  (boundedCochainComplex C).FullSubcategory

namespace BoundedCochainComplex

variable [HasZeroMorphisms C]

/-- The inclusion of bounded cochain complexes into all cochain complexes. -/
abbrev ι : BoundedCochainComplex C ⥤ CochainComplex C ℤ :=
  (boundedCochainComplex C).ι

/-- The inclusion of bounded cochain complexes is fully faithful. -/
abbrev fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

end BoundedCochainComplex

variable [Preadditive C]

/-- The property of objects of the homotopy category which are represented by bounded cochain
complexes. As for Mathlib's `HomotopyCategory.plus`, the representative is remembered strictly;
the induced full subcategory is nevertheless closed under the pretriangulated operations. -/
def boundedHomotopyCategory : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (boundedCochainComplex C).strictMap (HomotopyCategory.quotient C (.up ℤ))

variable {C}

@[simp]
lemma boundedHomotopyCategory_quotient_obj_iff (K : CochainComplex C ℤ) :
    boundedHomotopyCategory C ((HomotopyCategory.quotient C (.up ℤ)).obj K) ↔
      boundedCochainComplex C K := by
  refine ⟨?_, fun h ↦ ⟨_, h⟩⟩
  simp only [boundedHomotopyCategory, ObjectProperty.strictMap_iff]
  rintro ⟨L, hL, h⟩
  obtain rfl : L = K := congr_arg Quotient.as h
  exact hL

variable (C)

instance [HasZeroObject C] : (boundedHomotopyCategory C).ContainsZero where
  exists_zero :=
    ⟨(HomotopyCategory.quotient C (.up ℤ)).obj 0,
      Functor.map_isZero _ (isZero_zero _), by
        rw [boundedHomotopyCategory_quotient_obj_iff]
        rw [boundedCochainComplex_iff]
        exact ⟨0, 0, inferInstance, inferInstance⟩⟩

instance : (boundedHomotopyCategory C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    ⟨by
      rintro K hK
      obtain ⟨K : CochainComplex C ℤ, rfl⟩ := K.quotient_obj_surjective
      rw [boundedHomotopyCategory_quotient_obj_iff] at hK
      rw [boundedCochainComplex_iff] at hK
      obtain ⟨a, b, ha, hb⟩ := hK
      rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj,
        boundedHomotopyCategory_quotient_obj_iff, boundedCochainComplex_iff]
      let _ := ha
      let _ := hb
      exact ⟨a - n, b - n, K.isStrictlyGE_shift a n (a - n) (by omega),
        K.isStrictlyLE_shift b n (b - n) (by omega)⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance [HasZeroObject C] [HasBinaryBiproducts C] :
    (boundedHomotopyCategory C).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    have h₁' : boundedCochainComplex C T.obj₁.as := by
      rwa [← boundedHomotopyCategory_quotient_obj_iff]
    have h₂' : boundedCochainComplex C T.obj₂.as := by
      rwa [← boundedHomotopyCategory_quotient_obj_iff]
    rw [boundedCochainComplex_iff] at h₁' h₂'
    obtain ⟨a₁, b₁, ha₁, hb₁⟩ := h₁'
    obtain ⟨a₂, b₂, ha₂, hb₂⟩ := h₂'
    let _ := ha₁
    let _ := hb₁
    let _ := ha₂
    let _ := hb₂
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ :=
      (HomotopyCategory.quotient C (.up ℤ)).map_surjective T.mor₁
    refine ⟨_, ?_,
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
        (HomotopyCategory.mappingCone_triangleh_distinguished f)
        (Iso.refl _) (Iso.refl _) ?_)⟩⟩
    · dsimp
      simp only [boundedHomotopyCategory_quotient_obj_iff]
      rw [boundedCochainComplex_iff]
      refine ⟨min (a₁ - 1) a₂, max (b₁ - 1) b₂, ?_, ?_⟩
      · exact CochainComplex.isStrictlyGE_mappingCone f a₁ a₂ _ (by omega) (by omega)
      · rw [CochainComplex.isStrictlyLE_iff]
        intro i hi
        rw [CochainComplex.mappingCone.isZero_X_iff]
        exact ⟨CochainComplex.isZero_of_isStrictlyLE (K := T.obj₁.as) b₁ (i + 1) (by omega),
          CochainComplex.isZero_of_isStrictlyLE (K := T.obj₂.as) b₂ i (by omega)⟩
    · simp [hf]

instance [HasZeroObject C] [HasBinaryBiproducts C] :
    (boundedHomotopyCategory C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- The homotopy category of bounded cochain complexes. -/
abbrev BoundedHomotopyCategory := (boundedHomotopyCategory C).FullSubcategory

namespace BoundedHomotopyCategory

/-- The inclusion of the bounded homotopy category into the homotopy category of all cochain
complexes. -/
abbrev ι : BoundedHomotopyCategory C ⥤ HomotopyCategory C (.up ℤ) :=
  (boundedHomotopyCategory C).ι

/-- The inclusion of the bounded homotopy category is fully faithful. -/
abbrev fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/-- The quotient functor from bounded cochain complexes to their bounded homotopy category. -/
noncomputable abbrev quotient : BoundedCochainComplex C ⥤ BoundedHomotopyCategory C :=
  ObjectProperty.lift _
    (BoundedCochainComplex.ι C ⋙ HomotopyCategory.quotient C (.up ℤ)) (by
      rintro ⟨K, hK⟩
      dsimp
      rw [boundedHomotopyCategory_quotient_obj_iff]
      exact hK)

/-- The bounded quotient followed by the inclusion agrees with the ordinary homotopy quotient. -/
noncomputable abbrev quotientCompιIso :
    quotient C ⋙ ι C ≅
      BoundedCochainComplex.ι C ⋙ HomotopyCategory.quotient C (.up ℤ) :=
  ObjectProperty.liftCompιIso ..

noncomputable instance : (quotient C).CommShift ℤ :=
  ObjectProperty.commShiftLift ..

instance : NatTrans.CommShift (quotientCompιIso C).hom ℤ :=
  ObjectProperty.commShift_liftCompιIso_hom ..

variable {C}

/-- Every bounded homotopy object is represented by a bounded cochain complex. -/
lemma quotient_obj_surjective : Function.Surjective (quotient C).obj := by
  rintro ⟨K, hK⟩
  obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective K
  refine ⟨⟨L, ?_⟩, ?_⟩
  · rw [← boundedHomotopyCategory_quotient_obj_iff, hL]
    exact hK
  · ext
    exact hL

instance : (quotient C).EssSurj where
  mem_essImage K := by
    obtain ⟨L, rfl⟩ := quotient_obj_surjective K
    exact ⟨L, ⟨Iso.refl _⟩⟩

instance : (quotient C).Full := by
  dsimp [quotient]
  infer_instance

end BoundedHomotopyCategory

end TauCeti

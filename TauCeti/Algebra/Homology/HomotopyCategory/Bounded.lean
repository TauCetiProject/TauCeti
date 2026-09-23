/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-!
# The bounded homotopy category

For an additive category `C`, this file constructs the category `TauCeti.BoundedHomotopyCategory C`
of bounded cochain complexes up to homotopy. A complex is bounded when it vanishes strictly below
some integer and strictly above another. The property is stable under shifts and mapping cones, so
it defines a triangulated full subcategory of Mathlib's homotopy category.

The category comes with a full and essentially surjective quotient functor from bounded cochain
complexes. This presentation lets invariants of bounded complexes descend to the bounded homotopy
category; in particular, it is the categorical domain for the alternating-term comparison between
split `K₀` and triangulated `K₀`.

## Main definitions

* `TauCeti.boundedCochainComplex`: the property of being bounded above and below.
* `TauCeti.BoundedCochainComplex`: the full subcategory of bounded cochain complexes.
* `TauCeti.boundedHomotopyCategory`: the corresponding property in the homotopy category.
* `TauCeti.BoundedHomotopyCategory`: the bounded homotopy category.
* `TauCeti.BoundedHomotopyCategory.quotient`: the quotient functor from bounded complexes.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Exercise 9.15, for the comparison between split `K₀` and the `K₀` of the bounded homotopy
  category.
* Mathlib's `Mathlib.Algebra.Homology.HomotopyCategory.Plus`, whose bounded-below homotopy
  category and quotient interface are extended here to complexes bounded on both sides.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
  HomologicalComplex

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- A cochain complex is bounded when it is strictly bounded below and strictly bounded above. -/
def boundedCochainComplex : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b

/-- The defining characterization of a bounded cochain complex. -/
lemma boundedCochainComplex_iff (K : CochainComplex C ℤ) :
    boundedCochainComplex C K ↔ ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b :=
  Iff.rfl

instance : (boundedCochainComplex C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro K L e ⟨a, b, _, _⟩
    exact ⟨a, b, K.isStrictlyGE_of_iso e a, K.isStrictlyLE_of_iso e b⟩

instance : (boundedCochainComplex C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K ⟨a, b, _, _⟩ ↦
    ⟨a - n, b - n, K.isStrictlyGE_shift a n (a - n) (by lia),
      K.isStrictlyLE_shift b n (b - n) (by lia)⟩⟩

/-- The full subcategory of bounded cochain complexes. -/
abbrev BoundedCochainComplex := (boundedCochainComplex C).FullSubcategory

namespace BoundedCochainComplex

/-- The inclusion of bounded cochain complexes into all cochain complexes. -/
abbrev ι : BoundedCochainComplex C ⥤ CochainComplex C ℤ :=
  (boundedCochainComplex C).ι

/-- The inclusion of bounded cochain complexes is fully faithful. -/
abbrev fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

end BoundedCochainComplex

variable {C}

/-- The mapping cone of a morphism between bounded-above cochain complexes is bounded above. -/
lemma isStrictlyLE_mappingCone [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (b₁ b₂ b : ℤ) [K.IsStrictlyLE b₁] [L.IsStrictlyLE b₂]
    (hb₁ : b₁ ≤ b := by lia) (hb₂ : b₂ ≤ b := by lia) :
    (CochainComplex.mappingCone f).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  simp only [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyLE b₁ (i + 1) (by lia),
    L.isZero_of_isStrictlyLE b₂ i (by lia)⟩

variable (C)

/-- The property of a homotopy-category object isomorphic to the quotient of a bounded cochain
complex. -/
def boundedHomotopyCategory : ObjectProperty (_root_.HomotopyCategory C (.up ℤ)) :=
  (boundedCochainComplex C).map (_root_.HomotopyCategory.quotient C (.up ℤ))

/-- An object belongs to the bounded homotopy category exactly when it is isomorphic to the
homotopy quotient of a bounded cochain complex. -/
lemma boundedHomotopyCategory_iff (X : _root_.HomotopyCategory C (.up ℤ)) :
    boundedHomotopyCategory C X ↔
      ∃ K : CochainComplex C ℤ, boundedCochainComplex C K ∧
        Nonempty ((_root_.HomotopyCategory.quotient C (.up ℤ)).obj K ≅ X) :=
  Iff.rfl

/-- The homotopy quotient of a bounded complex belongs to the bounded homotopy category. -/
lemma boundedHomotopyCategory_quotient_obj (K : CochainComplex C ℤ)
    (hK : boundedCochainComplex C K) :
    boundedHomotopyCategory C ((_root_.HomotopyCategory.quotient C (.up ℤ)).obj K) :=
  (boundedCochainComplex C).prop_map_obj _ hK

instance [HasZeroObject C] : (boundedHomotopyCategory C).ContainsZero where
  exists_zero :=
    ⟨(_root_.HomotopyCategory.quotient C (.up ℤ)).obj 0,
      Functor.map_isZero _ (isZero_zero _), by
        exact boundedHomotopyCategory_quotient_obj C 0
          ⟨0, 0, inferInstance, inferInstance⟩⟩

instance : (boundedHomotopyCategory C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun K hK ↦ by
    obtain ⟨L, ⟨a, b, _, _⟩, ⟨e⟩⟩ := hK
    refine ⟨L⟦n⟧, ⟨a - n, b - n,
      L.isStrictlyGE_shift a n (a - n) (by lia),
      L.isStrictlyLE_shift b n (b - n) (by lia)⟩, ⟨?_⟩⟩
    exact ((_root_.HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).app L ≪≫
      (shiftFunctor (_root_.HomotopyCategory C (.up ℤ)) n).mapIso e⟩

instance [HasZeroObject C] [HasBinaryBiproducts C] :
    (boundedHomotopyCategory C).IsTriangulatedClosed₃ where
  ext₃' T hT := by
    rintro ⟨K, ⟨a₁, b₁, _, _⟩, ⟨e₁⟩⟩ ⟨L, ⟨a₂, b₂, _, _⟩, ⟨e₂⟩⟩
    obtain ⟨f, hf⟩ := (_root_.HomotopyCategory.quotient C (.up ℤ)).map_surjective
      (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
    have comm :
        (_root_.HomotopyCategory.quotient C (.up ℤ)).map f ≫ e₂.hom =
          e₁.hom ≫ T.mor₁ := by simp [hf]
    let e := isoTriangleOfIso₁₂ (CochainComplex.mappingCone.triangleh f) T
      (_root_.HomotopyCategory.mappingCone_triangleh_distinguished f) hT e₁ e₂ comm
    refine (boundedHomotopyCategory C).le_isoClosure _
      ⟨CochainComplex.mappingCone f, ⟨min (a₁ - 1) a₂, max b₁ b₂,
        CochainComplex.isStrictlyGE_mappingCone f a₁ a₂ _ (by simp) (by simp),
        isStrictlyLE_mappingCone f b₁ b₂ _ (by simp) (by simp)⟩,
        ⟨Triangle.π₃.mapIso e⟩⟩

instance [HasZeroObject C] [HasBinaryBiproducts C] :
    (boundedHomotopyCategory C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- The homotopy category of bounded cochain complexes. -/
abbrev BoundedHomotopyCategory := (boundedHomotopyCategory C).FullSubcategory

namespace BoundedHomotopyCategory

/-- The inclusion of the bounded homotopy category into the homotopy category of all cochain
complexes. -/
abbrev ι : BoundedHomotopyCategory C ⥤ _root_.HomotopyCategory C (.up ℤ) :=
  (boundedHomotopyCategory C).ι

/-- The inclusion of the bounded homotopy category is fully faithful. -/
abbrev fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/-- The full and essentially surjective quotient functor from bounded cochain complexes to the
bounded homotopy category. -/
@[expose, implicit_reducible, simps!]
def quotient : BoundedCochainComplex C ⥤ BoundedHomotopyCategory C :=
  ObjectProperty.lift _
    (BoundedCochainComplex.ι C ⋙ _root_.HomotopyCategory.quotient C (.up ℤ)) (by
      rintro ⟨K, hK⟩
      exact boundedHomotopyCategory_quotient_obj C K hK)

/-- The bounded quotient followed by the inclusion is the ordinary homotopy quotient restricted
to bounded complexes. -/
@[expose, simps! -isSimp]
def quotientCompιIso :
    quotient C ⋙ ι C ≅
      BoundedCochainComplex.ι C ⋙ _root_.HomotopyCategory.quotient C (.up ℤ) :=
  ObjectProperty.liftCompιIso ..

noncomputable instance : (quotient C).CommShift ℤ :=
  ObjectProperty.commShiftLift ..

instance : NatTrans.CommShift (quotientCompιIso C).hom ℤ :=
  ObjectProperty.commShift_liftCompιIso_hom ..

instance : (quotient C).EssSurj where
  mem_essImage K := by
    obtain ⟨L, hL, ⟨e⟩⟩ := K.property
    exact ⟨⟨L, hL⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

instance : (quotient C).Full := by
  dsimp [quotient]
  infer_instance

instance : (quotient C).Additive := by
  have : (quotient C ⋙ ι C).Additive :=
    Functor.additive_of_iso (quotientCompιIso C).symm
  exact Functor.additive_of_comp_faithful _ (ι C)

end BoundedHomotopyCategory

end TauCeti

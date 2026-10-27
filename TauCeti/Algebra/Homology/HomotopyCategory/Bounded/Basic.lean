/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Localization.OfQuotient
public import TauCeti.Algebra.Homology.EssentiallySmall
public import TauCeti.Algebra.Homology.Embedding.CochainComplex
public import TauCeti.CategoryTheory.ObjectProperty

/-!
# The homotopy category of bounded cochain complexes

This file constructs the full pretriangulated subcategory of the homotopy category whose objects
are represented by cochain complexes vanishing outside a finite interval. It also constructs the
quotient functor from bounded cochain complexes and proves that this functor is full and
essentially surjective.

The boundedness predicate records both bounds at once. This matters for closure under cones: if
the source has bounds `(a₁, b₁)` and the target has bounds `(a₂, b₂)`, the standard mapping
cone has bounds `(min (a₁ - 1) a₂, max (b₁ - 1) b₂)`. Consequently the full subcategory is
stable under shifts and distinguished triangles.

The construction follows the organization of Mathlib's bounded-below category
`HomotopyCategory.Plus`, replacing its one-sided support condition by two-sided boundedness.

## Main definitions

* `CochainComplex.bounded`: the property of being strictly bounded above and below.
* `CochainComplex.Bounded`: the full subcategory of bounded cochain complexes.
* `TauCeti.HomotopyCategory.bounded`: the corresponding property in the homotopy category.
* `TauCeti.HomotopyCategory.Bounded`: the homotopy category of bounded cochain complexes.
* `TauCeti.HomotopyCategory.Bounded.quotient`: the quotient functor from bounded complexes. It is
  a localization functor with respect to the homotopy equivalences, so functors and their shift
  compatibilities descend along it.

The homotopy category of bounded complexes over an essentially small category is essentially
small (through `HomotopyCategory.essentiallySmall` and
`CategoryTheory.ObjectProperty.essentiallySmall_of_ambient`), so it has a triangulated
Grothendieck group.

## References

* Mathlib's `Mathlib/Algebra/Homology/HomotopyCategory/Plus.lean`, whose construction of the
  bounded-below homotopy category supplies the formal pattern used here.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Exercise 9.15.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
  HomologicalComplex

universe v u

variable (C : Type u) [Category.{v} C]

namespace CochainComplex

/-- A cochain complex is bounded when it is strictly bounded both below and above. -/
def bounded [HasZeroMorphisms C] : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ CochainComplex.plus C K ∧ ∃ b : ℤ, K.IsStrictlyLE b

/-- The elementwise characterization of a bounded cochain complex. -/
lemma bounded_iff [HasZeroMorphisms C] (K : CochainComplex C ℤ) :
    CochainComplex.bounded C K ↔ ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b := by
  constructor
  · rintro ⟨⟨a, ha⟩, b, hb⟩
    exact ⟨a, b, ha, hb⟩
  · rintro ⟨a, b, ha, hb⟩
    exact ⟨⟨a, ha⟩, b, hb⟩

/-- A cochain complex is bounded exactly when it vanishes outside a finite set of degrees. -/
lemma bounded_iff_exists_finset_isZero_X [HasZeroMorphisms C] (K : CochainComplex C ℤ) :
    CochainComplex.bounded C K ↔ ∃ s : Finset ℤ, ∀ n ∉ s, IsZero (K.X n) := by
  rw [CochainComplex.bounded_iff]
  constructor
  · rintro ⟨a, b, ha, hb⟩
    exact ⟨Finset.Icc a b, fun n hn ↦ K.isZero_X_of_notMem_Icc a b hn⟩
  · rintro ⟨s, hs⟩
    obtain ⟨a, ha⟩ := s.bddBelow
    obtain ⟨b, hb⟩ := s.bddAbove
    exact ⟨a, b, (K.isStrictlyGE_iff a).2 fun i hi ↦ hs i fun h ↦ absurd (ha h) (not_le.2 hi),
      (K.isStrictlyLE_iff b).2 fun i hi ↦ hs i fun h ↦ absurd (hb h) (not_le.2 hi)⟩

instance [HasZeroMorphisms C] : (CochainComplex.bounded C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro K L e h
    rw [CochainComplex.bounded_iff] at h ⊢
    obtain ⟨a, b, ha, hb⟩ := h
    let _ := ha
    let _ := hb
    exact ⟨a, b, K.isStrictlyGE_of_iso e a, K.isStrictlyLE_of_iso e b⟩

instance [Preadditive C] : (CochainComplex.bounded C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    ⟨by
      rintro K h
      rw [CochainComplex.bounded_iff] at h
      obtain ⟨a, b, ha, hb⟩ := h
      rw [ObjectProperty.prop_shift_iff, CochainComplex.bounded_iff]
      let _ := ha
      let _ := hb
      exact ⟨a - n, b - n, K.isStrictlyGE_shift a n (a - n) (by omega),
        K.isStrictlyLE_shift b n (b - n) (by omega)⟩⟩

/-- The full subcategory of bounded cochain complexes. -/
abbrev Bounded [HasZeroMorphisms C] :=
  (CochainComplex.bounded C).FullSubcategory

section

variable {C} [Preadditive C] [HasBinaryBiproducts C]

/-- The cylinder of a bounded cochain complex is bounded. -/
lemma bounded_cylinder {K : CochainComplex C ℤ} (hK : CochainComplex.bounded C K) :
    CochainComplex.bounded C K.cylinder := by
  obtain ⟨a, b, ha, hb⟩ := (CochainComplex.bounded_iff C K).1 hK
  obtain ⟨a', ha'⟩ := K.plus_cylinder ⟨a, ha⟩
  refine (CochainComplex.bounded_iff C _).2 ⟨a', b, ha', ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  refine homotopyCofiber.isZero_X (biprod.lift (𝟙 K) (-𝟙 K)) _ ?_ (fun j hj ↦ ?_)
  · refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (.up ℤ) i).mapBiprod _ _)
    simpa using K.isZero_of_isStrictlyLE b i
  · simp only [ComplexShape.up_Rel] at hj
    exact K.isZero_of_isStrictlyLE b _ (by lia)

/-- The mapping cone of a morphism `K ⟶ L` is strictly bounded above by `n` when `K` is strictly
bounded above by `n + 1` and `L` by `n`. This is the upper-bound counterpart of Mathlib's
`CochainComplex.isStrictlyGE_mappingCone`. -/
lemma isStrictlyLE_mappingCone {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (n₁ n₂ n : ℤ) [K.IsStrictlyLE n₁] [L.IsStrictlyLE n₂] (hn₁ : n₁ ≤ n + 1 := by lia)
    (hn₂ : n₂ ≤ n := by lia) :
    (CochainComplex.mappingCone f).IsStrictlyLE n := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyLE n₁ (i + 1) (by lia), L.isZero_of_isStrictlyLE n₂ i (by lia)⟩

/-- The mapping cone of a morphism between bounded cochain complexes is bounded. If the source
and target have bounds `(a₁, b₁)` and `(a₂, b₂)`, the cone has bounds
`(min (a₁ - 1) a₂, max (b₁ - 1) b₂)`. -/
lemma bounded_mappingCone {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : CochainComplex.bounded C K) (hL : CochainComplex.bounded C L) :
    CochainComplex.bounded C (CochainComplex.mappingCone f) := by
  obtain ⟨a₁, b₁, ha₁, hb₁⟩ := (CochainComplex.bounded_iff C K).1 hK
  obtain ⟨a₂, b₂, ha₂, hb₂⟩ := (CochainComplex.bounded_iff C L).1 hL
  exact (CochainComplex.bounded_iff C _).2 ⟨min (a₁ - 1) a₂, max (b₁ - 1) b₂,
    CochainComplex.isStrictlyGE_mappingCone f a₁ a₂ _,
    isStrictlyLE_mappingCone f b₁ b₂ _⟩

end

namespace Bounded

variable [HasZeroMorphisms C]

/-- The inclusion of bounded cochain complexes into all cochain complexes. -/
abbrev ι : CochainComplex.Bounded C ⥤ CochainComplex C ℤ :=
  (CochainComplex.bounded C).ι

/-- The inclusion of bounded cochain complexes is fully faithful. -/
abbrev fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

end Bounded

end CochainComplex

namespace TauCeti

namespace HomotopyCategory

variable [Preadditive C]

/-- The property of objects of the homotopy category which are represented by bounded cochain
complexes. As for Mathlib's `HomotopyCategory.plus`, the representative is remembered strictly;
the induced full subcategory is nevertheless closed under the pretriangulated operations. -/
def bounded : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (CochainComplex.bounded C).strictMap (HomotopyCategory.quotient C (.up ℤ))

variable {C}

/-- The ordinary homotopy quotient of a cochain complex is bounded exactly when the complex
itself is bounded. -/
@[simp]
lemma bounded_quotient_obj_iff (K : CochainComplex C ℤ) :
    HomotopyCategory.bounded C ((HomotopyCategory.quotient C (.up ℤ)).obj K) ↔
      CochainComplex.bounded C K := by
  refine ⟨?_, fun h ↦ ⟨_, h⟩⟩
  simp only [HomotopyCategory.bounded, ObjectProperty.strictMap_iff]
  rintro ⟨L, hL, h⟩
  obtain rfl : L = K := congr_arg Quotient.as h
  exact hL

variable (C)

instance [HasZeroObject C] : (HomotopyCategory.bounded C).ContainsZero where
  exists_zero :=
    ⟨(HomotopyCategory.quotient C (.up ℤ)).obj 0,
      Functor.map_isZero _ (isZero_zero _), by
        rw [HomotopyCategory.bounded_quotient_obj_iff]
        rw [CochainComplex.bounded_iff]
        exact ⟨0, 0, inferInstance, inferInstance⟩⟩

instance : (HomotopyCategory.bounded C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    ⟨by
      rintro K hK
      obtain ⟨K : CochainComplex C ℤ, rfl⟩ := K.quotient_obj_surjective
      rw [HomotopyCategory.bounded_quotient_obj_iff] at hK
      rw [CochainComplex.bounded_iff] at hK
      obtain ⟨a, b, ha, hb⟩ := hK
      rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj,
        HomotopyCategory.bounded_quotient_obj_iff, CochainComplex.bounded_iff]
      let _ := ha
      let _ := hb
      exact ⟨a - n, b - n, K.isStrictlyGE_shift a n (a - n) (by omega),
        K.isStrictlyLE_shift b n (b - n) (by omega)⟩⟩

instance [HasZeroObject C] [HasBinaryBiproducts C] :
    (HomotopyCategory.bounded C).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    have h₁' : CochainComplex.bounded C T.obj₁.as := by
      rwa [← HomotopyCategory.bounded_quotient_obj_iff]
    have h₂' : CochainComplex.bounded C T.obj₂.as := by
      rwa [← HomotopyCategory.bounded_quotient_obj_iff]
    have quotient_obj_of_as (K : HomotopyCategory C (.up ℤ)) :
        (HomotopyCategory.quotient C (.up ℤ)).obj K.as = K := by
      cases K
      rfl
    let e₁ : (HomotopyCategory.quotient C (.up ℤ)).obj T.obj₁.as ≅ T.obj₁ :=
      eqToIso (quotient_obj_of_as T.obj₁)
    let e₂ : (HomotopyCategory.quotient C (.up ℤ)).obj T.obj₂.as ≅ T.obj₂ :=
      eqToIso (quotient_obj_of_as T.obj₂)
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ :=
      (HomotopyCategory.quotient C (.up ℤ)).map_surjective
        (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
    refine ⟨(HomotopyCategory.quotient C (.up ℤ)).obj (CochainComplex.mappingCone f), ?_,
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
        (HomotopyCategory.mappingCone_triangleh_distinguished f)
        e₁.symm e₂.symm ?_)⟩⟩
    · rw [HomotopyCategory.bounded_quotient_obj_iff]
      exact CochainComplex.bounded_mappingCone f h₁' h₂'
    -- Unfold the compatibility condition from `isoTriangleOfIso₁₂`; the explicit transports
    -- `e₁` and `e₂` avoid the nonstandard definitional-equality options used by Mathlib's proof.
    · change T.mor₁ ≫ e₂.inv =
        e₁.inv ≫ (HomotopyCategory.quotient C (.up ℤ)).map f
      rw [hf]
      simp

instance [HasZeroObject C] [HasBinaryBiproducts C] :
    (HomotopyCategory.bounded C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- Every object of the homotopy category represented by a bounded complex is represented by a
bounded below complex. -/
lemma bounded_le_plus : HomotopyCategory.bounded C ≤ _root_.HomotopyCategory.plus C := by
  rintro _ ⟨K, hK⟩
  exact ⟨K, hK.1⟩

/-- The homotopy category of bounded cochain complexes. -/
abbrev Bounded := (HomotopyCategory.bounded C).FullSubcategory

namespace Bounded

/-- The inclusion of the bounded homotopy category into the homotopy category of all cochain
complexes. -/
abbrev ι : HomotopyCategory.Bounded C ⥤ HomotopyCategory C (.up ℤ) :=
  (HomotopyCategory.bounded C).ι

/-- The inclusion of the bounded homotopy category is fully faithful. -/
abbrev fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

variable {C} in
/-- The bounded cochain complex underlying an object of the bounded homotopy category. -/
def rep (K : HomotopyCategory.Bounded C) : CochainComplex C ℤ :=
  K.obj.as

variable {C} in
/-- An object of the bounded homotopy category is the homotopy class of its underlying complex. -/
@[simp]
lemma quotient_obj_rep (K : HomotopyCategory.Bounded C) :
    (HomotopyCategory.quotient C (.up ℤ)).obj (rep K) = K.obj :=
  (rfl)

variable {C} in
/-- The underlying complex of an object of the bounded homotopy category is bounded. -/
lemma bounded_rep (K : HomotopyCategory.Bounded C) : CochainComplex.bounded C (rep K) := by
  rw [← HomotopyCategory.bounded_quotient_obj_iff, quotient_obj_rep]
  exact K.property

/-- The quotient functor from bounded cochain complexes to their bounded homotopy category. -/
@[implicit_reducible]
def quotient : CochainComplex.Bounded C ⥤ HomotopyCategory.Bounded C :=
  ObjectProperty.lift _
    (CochainComplex.Bounded.ι C ⋙ HomotopyCategory.quotient C (.up ℤ)) (by
      rintro ⟨K, hK⟩
      dsimp
      rw [HomotopyCategory.bounded_quotient_obj_iff]
      exact hK)

private lemma quotient_obj_obj_private (X : CochainComplex.Bounded C) :
    ((quotient C).obj X).obj = (HomotopyCategory.quotient C (.up ℤ)).obj X.obj := rfl

/-- Inclusion sends a bounded quotient object to the ordinary homotopy quotient. -/
@[simp]
lemma quotient_obj_obj (X : CochainComplex.Bounded C) :
    ((quotient C).obj X).obj = (HomotopyCategory.quotient C (.up ℤ)).obj X.obj :=
  quotient_obj_obj_private C X

private lemma quotient_map_hom_private {X Y : CochainComplex.Bounded C} (f : X ⟶ Y) :
    ((quotient C).map f).hom =
      eqToHom (quotient_obj_obj C X) ≫
        (HomotopyCategory.quotient C (.up ℤ)).map f.hom ≫
        eqToHom (quotient_obj_obj C Y).symm := by
  simp [quotient]

/-- The bounded quotient acts on maps by the ordinary homotopy quotient, after transporting
along the object comparison equalities. -/
@[simp]
lemma quotient_map_hom {X Y : CochainComplex.Bounded C} (f : X ⟶ Y) :
    ((quotient C).map f).hom =
      eqToHom (quotient_obj_obj C X) ≫
        (HomotopyCategory.quotient C (.up ℤ)).map f.hom ≫
        eqToHom (quotient_obj_obj C Y).symm := quotient_map_hom_private C f

variable {C} in
/-- The underlying complex of the class of a bounded complex has the same homotopy class as that
complex. -/
lemma quotient_obj_rep_quotient_obj (K : CochainComplex.Bounded C) :
    (HomotopyCategory.quotient C (.up ℤ)).obj (rep ((quotient C).obj K)) =
      (HomotopyCategory.quotient C (.up ℤ)).obj K.obj :=
  (quotient_obj_rep _).trans (quotient_obj_obj C K)

private def quotientCompιIsoAux :
    quotient C ⋙ ι C ≅
      CochainComplex.Bounded.ι C ⋙ HomotopyCategory.quotient C (.up ℤ) :=
  ObjectProperty.liftCompιIso ..

/-- The bounded quotient followed by the inclusion agrees with the ordinary homotopy quotient. -/
def quotientCompιIso :
    quotient C ⋙ ι C ≅
      CochainComplex.Bounded.ι C ⋙ HomotopyCategory.quotient C (.up ℤ) :=
  quotientCompιIsoAux C

private lemma quotientCompιIso_hom_app_private (X : CochainComplex.Bounded C) :
    (quotientCompιIso C).hom.app X = eqToHom (quotient_obj_obj C X) := rfl

/-- The comparison isomorphism has the canonical component at each bounded complex. -/
@[simp]
lemma quotientCompιIso_hom_app (X : CochainComplex.Bounded C) :
    (quotientCompιIso C).hom.app X = eqToHom (quotient_obj_obj C X) :=
  quotientCompιIso_hom_app_private C X

/-- The inverse comparison has the reverse canonical component at each bounded complex. -/
@[simp]
lemma quotientCompιIso_inv_app (X : CochainComplex.Bounded C) :
    (quotientCompιIso C).inv.app X = eqToHom (quotient_obj_obj C X).symm := by
  rfl

noncomputable instance : (quotient C).CommShift ℤ :=
  Functor.CommShift.ofComp (quotientCompιIso C) ℤ

instance : NatTrans.CommShift (quotientCompιIso C).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

variable {C}

/-- Every bounded homotopy object is represented by a bounded cochain complex. -/
lemma quotient_obj_surjective : Function.Surjective (quotient C).obj := by
  rintro ⟨K, hK⟩
  obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective K
  refine ⟨⟨L, ?_⟩, ?_⟩
  · rw [← HomotopyCategory.bounded_quotient_obj_iff, hL]
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

variable (C) in
/-- The quotient functor from bounded cochain complexes is a localization functor with respect to
the homotopy equivalences. This is the bounded analogue of Mathlib's corresponding instance for
`HomotopyCategory.Plus.quotient`. -/
instance [HasBinaryBiproducts C] :
    (quotient C).IsLocalization
      ((homotopyEquivalences C (.up ℤ)).inverseImage (CochainComplex.Bounded.ι C)) :=
  Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _
    (fun _ _ f hf ↦ by
      simpa [← isIso_iff_of_reflects_iso _ (ι C),
        ← HomotopyCategory.inverseImage_quotient_isomorphisms] using hf) (by
    rintro K L f₀ f₁ hf
    obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjective f₀
    obtain ⟨f₁, rfl⟩ := ObjectProperty.homMk_surjective f₁
    replace hf := HomotopyCategory.homotopyOfEq f₀ f₁ (by
      simpa [quotient_map_hom, cancel_epi, cancel_mono] using congrArg InducedCategory.Hom.hom hf)
    exact ⟨K.obj.precylinder.toFullSubcategory (CochainComplex.bounded_cylinder K.property),
      HomotopicalAlgebra.Precylinder.LeftHomotopy.fullSubcategoryEquiv.symm
        { h := cylinder.desc _ _ hf
          h₀ := cylinder.ι₀_desc _ _ hf
          h₁ := cylinder.ι₁_desc _ _ hf },
      ⟨cylinder.homotopyEquiv _ (fun n ↦ ⟨n - 1, by simp⟩), rfl⟩⟩)

section

variable (C) [HasZeroObject C]

private noncomputable def singleFunctorLift (n : ℤ) : C ⥤ HomotopyCategory.Bounded C :=
  (HomotopyCategory.bounded C).lift (HomotopyCategory.singleFunctor C n)
    (fun X ↦ by
      rw [← HomotopyCategory.quotient_obj_singleFunctors_obj,
        HomotopyCategory.bounded_quotient_obj_iff, CochainComplex.bounded_iff]
      exact ⟨n, n, inferInstance, inferInstance⟩)

private noncomputable def singleFunctorLiftCompιIso (n : ℤ) :
    singleFunctorLift C n ⋙ ι C ≅ HomotopyCategory.singleFunctor C n :=
  Iso.refl _

/-- The collection of all single functors `C ⥤ HomotopyCategory.Bounded C` for `n : ℤ`,
along with their compatibilities with shifts. -/
noncomputable def singleFunctors : SingleFunctors C (HomotopyCategory.Bounded C) ℤ :=
  SingleFunctors.lift (HomotopyCategory.singleFunctors C) (ι C)
    (singleFunctorLift C) (singleFunctorLiftCompιIso C)

/-- The single functor `C ⥤ HomotopyCategory.Bounded C`. -/
noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ HomotopyCategory.Bounded C :=
  (singleFunctors C).functor n

/-- The bounded single functor is induced by
`HomotopyCategory.singleFunctor C n : C ⥤ HomotopyCategory C (.up ℤ)`. -/
noncomputable def singleFunctorCompιIso (n : ℤ) :
    singleFunctor C n ⋙ ι C ≅ HomotopyCategory.singleFunctor C n :=
  (SingleFunctors.evaluation C (HomotopyCategory C (.up ℤ)) n).mapIso
    (SingleFunctors.liftPostcompIso (HomotopyCategory.singleFunctors C) (ι C)
      (singleFunctorLift C) (singleFunctorLiftCompιIso C))

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

end

end Bounded

end HomotopyCategory

end TauCeti

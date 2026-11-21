/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Compression.GlobalDimension
public import TauCeti.Algebra.Homology.Periodic.Compression.ZeroDifferential
public import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.CategoryTheory.Shift.CommShift

/-!
# Gradable periodic objects

Let `C` be an abelian category. Following Stai, an object of the `n`-periodic derived category
`D_n(C)` is **gradable** when it lies in the essential image of compression
`D^b(C) ⥤ D_n(C)` (`TauCeti.PeriodicComplex.gradable`). Equivalently, it is isomorphic in
`D_n(C)` to the class of the compression `⨁_{i ≡ r (mod n)} Kⁱ` of a bounded complex `K`
(`TauCeti.PeriodicComplex.gradable_iff_exists_bounded`). Periodic complexes with zero
differential are gradable, as is every shift of a gradable object.

The orbit functor `D^b(C)/[n] ⥤ D_n(C)` is the descent of compression along the projection
`D^b(C) ⥤ D^b(C)/[n]`, which is the identity on objects, so its essential image is exactly the
class of gradable objects (`TauCeti.PeriodicComplex.essImage_orbitDerivedCompressionFunctor`).
In finite global dimension the orbit functor is fully faithful (Stai's Lemma 3.12), so the orbit
category is equivalent to the full subcategory of gradable objects
(`TauCeti.PeriodicComplex.orbitDerivedCompressionEquivalence`), and the orbit functor is an
equivalence exactly when every object of `D_n(C)` is gradable
(`TauCeti.PeriodicComplex.isEquivalence_orbitDerivedCompressionFunctor_iff`).

The gradable objects generate `D_n(C)` under shifts and cones in finite global dimension
(`TauCeti.PeriodicComplex.eq_top_of_gradable_le`), but they need not be all of `D_n(C)`, and so
need not form a triangulated subcategory: Stai shows that for a finite-dimensional algebra of
finite global dimension whose quiver has an oriented cycle, the orbit category is strictly
smaller than its triangulated hull `D_n(C)`.

## Main definitions

* `TauCeti.PeriodicComplex.gradable`: the gradable objects of `D_n(C)`.
* `TauCeti.PeriodicComplex.orbitDerivedCompressionEquivalence`: in finite global dimension, the
  equivalence between the orbit category `D^b(C)/[n]` and the gradable objects of `D_n(C)`.

## Main results

* `TauCeti.PeriodicComplex.gradable_iff_exists_bounded`: gradable objects are the classes of
  compressions of bounded complexes, up to isomorphism.
* `TauCeti.PeriodicComplex.gradable_Qh_obj_quotient_obj_of_d_eq_zero`: periodic complexes with
  zero differential are gradable.
* `TauCeti.PeriodicComplex.essImage_orbitDerivedCompressionFunctor`: the essential image of the
  orbit functor is the class of gradable objects.
* `TauCeti.PeriodicComplex.isEquivalence_orbitDerivedCompressionFunctor_iff`: in finite global
  dimension, the orbit functor is an equivalence exactly when every object is gradable.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3, Lemma 3.12 and Section 5.
-/

public section

open CategoryTheory Limits

universe w v u

namespace TauCeti.PeriodicComplex

variable (C : Type u) [Category.{v} C] [Abelian C] (n : ℕ) [HasDerivedCategory.{w} C]

/-- An object of the `n`-periodic derived category `D_n(C)` is **gradable** when it lies in the
essential image of compression `D^b(C) ⥤ D_n(C)`, that is, when it is isomorphic to the
compression of an object of the bounded derived category. -/
def gradable : ObjectProperty (DerivedCategory C n) :=
  (derivedCompressionFunctor n).essImage

variable {C n}

/-- The essential image of compression `D^b(C) ⥤ D_n(C)` is the class of gradable objects. -/
@[simp]
theorem essImage_derivedCompressionFunctor :
    (derivedCompressionFunctor (C := C) n).essImage = gradable C n :=
  (rfl)

/-- An object of `D_n(C)` is gradable exactly when it is isomorphic to the compression of an
object of `D^b(C)`. -/
theorem gradable_iff (Y : DerivedCategory C n) :
    gradable C n Y ↔ ∃ X, Nonempty ((derivedCompressionFunctor n).obj X ≅ Y) :=
  Iff.rfl

/-- The compression of an object of `D^b(C)` is gradable. -/
@[simp]
theorem gradable_derivedCompressionFunctor_obj (X : _root_.DerivedCategory.Bounded C) :
    gradable C n ((derivedCompressionFunctor n).obj X) :=
  (derivedCompressionFunctor n).obj_mem_essImage X

instance : (gradable C n).IsClosedUnderIsomorphisms :=
  inferInstanceAs (derivedCompressionFunctor (C := C) n).essImage.IsClosedUnderIsomorphisms

/-- Gradable objects are stable under the shifts of `D_n(C)`, because compression commutes with
the shifts. -/
instance : (gradable C n).IsStableUnderShift ℤ :=
  inferInstanceAs ((derivedCompressionFunctor (C := C) n).essImage.IsStableUnderShift ℤ)

/-- The compression of the class of a bounded complex `K` in `D^b(C)` is the class of the
periodic complex `compression n K` in `D_n(C)`. -/
private noncomputable def derivedCompressionFunctorObjIso (K : CochainComplex.Bounded C) :
    (derivedCompressionFunctor n).obj
        ((TauCeti.DerivedCategory.Bounded.Qh C).obj ((HomotopyCategory.Bounded.quotient C).obj K)) ≅
      (DerivedCategory.Qh C n).obj
        ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj (compression n K.obj)) :=
  (derivedCompressionFunctorFactors n).app _ ≪≫
    (DerivedCategory.Qh C n).mapIso ((quotientCompHomotopyCompressionFunctorIso n).app K ≪≫
      (HomotopyCategory.quotient C _).mapIso (eqToIso (compressionFunctor_obj n K)))

/-- The class in `D_n(C)` of the compression of a bounded complex is gradable. -/
theorem gradable_Qh_obj_quotient_obj_compression (K : CochainComplex.Bounded C) :
    gradable C n ((DerivedCategory.Qh C n).obj
      ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj (compression n K.obj))) :=
  (gradable C n).prop_of_iso (derivedCompressionFunctorObjIso K)
    (gradable_derivedCompressionFunctor_obj _)

/-- **Gradable objects at the level of complexes.** An object of `D_n(C)` is gradable exactly
when it is isomorphic to the class of the compression `⨁_{i ≡ r (mod n)} Kⁱ` of a bounded
complex `K`. -/
theorem gradable_iff_exists_bounded (Y : DerivedCategory C n) :
    gradable C n Y ↔ ∃ K : CochainComplex.Bounded C, Nonempty ((DerivedCategory.Qh C n).obj
      ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj (compression n K.obj)) ≅
        Y) := by
  refine ⟨fun ⟨X, ⟨e⟩⟩ ↦ ?_, fun ⟨K, ⟨e⟩⟩ ↦
    (gradable C n).prop_of_iso e (gradable_Qh_obj_quotient_obj_compression K)⟩
  -- Every object of `D^b(C)` is the class of a bounded complex.
  let F := HomotopyCategory.Bounded.quotient C ⋙ TauCeti.DerivedCategory.Bounded.Qh C
  exact ⟨F.objPreimage X, ⟨(derivedCompressionFunctorObjIso _).symm ≪≫
    (derivedCompressionFunctor n).mapIso (F.objObjPreimageIso X) ≪≫ e⟩⟩

/-- **Periodic complexes with zero differential are gradable.** For positive `n`, the class in
`D_n(C)` of a periodic complex with zero differential is the compression of a bounded complex
with zero differential. -/
theorem gradable_Qh_obj_quotient_obj_of_d_eq_zero [NeZero n] (K : CochainComplex C (ZMod n))
    (hd : ∀ i j, K.d i j = 0) :
    gradable C n ((DerivedCategory.Qh C n).obj
      ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj K)) :=
  (gradable C n).prop_of_iso ((DerivedCategory.Qh C n).mapIso
    ((HomotopyCategory.quotient C _).mapIso (K.compressionIsoOfDEqZero hd)))
    (gradable_Qh_obj_quotient_obj_compression (boundedGradedLift K.X))

/-- **The essential image of the orbit functor.** The essential image of the orbit functor
`D^b(C)/[n] ⥤ D_n(C)` is the class of gradable objects. -/
theorem essImage_orbitDerivedCompressionFunctor :
    (orbitDerivedCompressionFunctor (C := C) n).essImage = gradable C n :=
  OrbitCategory.essImage_lift _ _

/-- The image of an object of the orbit category `D^b(C)/[n]` under the orbit functor is
gradable. -/
theorem gradable_orbitDerivedCompressionFunctor_obj
    (X : OrbitCategory (_root_.DerivedCategory.Bounded C) n) :
    gradable C n ((orbitDerivedCompressionFunctor n).obj X) := by
  rw [← essImage_orbitDerivedCompressionFunctor]
  exact (orbitDerivedCompressionFunctor n).obj_mem_essImage X

/-- The orbit functor `D^b(C)/[n] ⥤ D_n(C)` is essentially surjective exactly when every object
of `D_n(C)` is gradable. -/
theorem essSurj_orbitDerivedCompressionFunctor_iff :
    (orbitDerivedCompressionFunctor (C := C) n).EssSurj ↔ gradable C n = ⊤ := by
  rw [← essImage_orbitDerivedCompressionFunctor]
  exact ⟨fun h ↦ top_unique fun _ _ ↦ h.mem_essImage _,
    fun h ↦ ⟨fun _ ↦ h ▸ trivial⟩⟩

section GlobalDimension

variable [EnoughProjectives C] [NeZero n] (n)

/-- **The orbit category is the category of gradable objects** (Stai, Lemma 3.12). Let `C` be an
abelian category with enough projectives in which every object has projective dimension `< d`,
and let `n` be positive. Then the orbit functor identifies the orbit category `D^b(C)/[n]` with
the full subcategory of gradable objects of `D_n(C)`. -/
noncomputable def orbitDerivedCompressionEquivalence (d : ℕ)
    (hd : ∀ X : C, HasProjectiveDimensionLT X d) :
    OrbitCategory (_root_.DerivedCategory.Bounded C) n ≌ (gradable C n).FullSubcategory :=
  have hF := fullyFaithfulOrbitDerivedCompressionFunctor (C := C) n d hd
  let G := (gradable C n).lift (orbitDerivedCompressionFunctor n)
    gradable_orbitDerivedCompressionFunctor_obj
  have hG : G.FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful (G := (gradable C n).ι)
      (hF.ofIso ((gradable C n).liftCompιIso _ _).symm)
  have := hG.full
  have := hG.faithful
  have : G.EssSurj := (ObjectProperty.essSurj_lift_iff _ _ _).2
    essImage_orbitDerivedCompressionFunctor.ge
  have : G.IsEquivalence := {}
  G.asEquivalence

/-- The functor of `orbitDerivedCompressionEquivalence` is the orbit functor, viewed as landing
in the gradable objects. -/
@[simp]
theorem orbitDerivedCompressionEquivalence_functor (d : ℕ)
    (hd : ∀ X : C, HasProjectiveDimensionLT X d) :
    (orbitDerivedCompressionEquivalence (C := C) n d hd).functor =
      (gradable C n).lift (orbitDerivedCompressionFunctor n)
        gradable_orbitDerivedCompressionFunctor_obj :=
  (rfl)

/-- **The orbit functor is an equivalence exactly when every object is gradable.** In finite
global dimension, the orbit functor `D^b(C)/[n] ⥤ D_n(C)` is an equivalence if and
only if every object of `D_n(C)` is gradable. -/
theorem isEquivalence_orbitDerivedCompressionFunctor_iff (d : ℕ)
    (hd : ∀ X : C, HasProjectiveDimensionLT X d) :
    (orbitDerivedCompressionFunctor (C := C) n).IsEquivalence ↔ gradable C n = ⊤ := by
  rw [← essSurj_orbitDerivedCompressionFunctor_iff]
  have hF := fullyFaithfulOrbitDerivedCompressionFunctor (C := C) n d hd
  have := hF.full
  have := hF.faithful
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ {}⟩

end GlobalDimension

end TauCeti.PeriodicComplex

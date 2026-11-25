/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Compression.Derived
public import TauCeti.Algebra.Homology.Periodic.Compression.ZeroDifferential
public import TauCeti.CategoryTheory.ObjectProperty.Biproducts
public import TauCeti.CategoryTheory.ObjectProperty.Shift

/-!
# Gradable periodic objects

Let `C` be an abelian category. Following Stai, an object of the `n`-periodic derived category
`D_n(C)` is **gradable** when it lies in the essential image of compression
`D^b(C) ⥤ D_n(C)` (`TauCeti.PeriodicComplex.gradable`,
`TauCeti.PeriodicComplex.essImage_derivedCompressionFunctor`). Equivalently, it is isomorphic in
`D_n(C)` to the class of the compression `⨁_{i ≡ r (mod n)} Kⁱ` of a bounded complex `K`
(`TauCeti.PeriodicComplex.gradable_iff_exists_bounded`); this description is the definition, so
that it needs no choice of bounded derived category. Gradable objects are stable under shifts
and finite direct sums, zero objects are gradable, and for positive `n` periodic complexes with
zero differential are gradable.

The orbit functor `D^b(C)/[n] ⥤ D_n(C)` is the descent of compression along the projection
`D^b(C) ⥤ D^b(C)/[n]`, which is the identity on objects, so its essential image is exactly the
class of gradable objects (`TauCeti.PeriodicComplex.essImage_orbitDerivedCompressionFunctor`).
For positive `n`, in an abelian category with enough projectives and a uniform finite bound on
projective dimensions, the orbit functor is fully faithful (Stai's Lemma 3.12), so the orbit
category is equivalent to the full subcategory of gradable objects
(`TauCeti.PeriodicComplex.orbitDerivedCompressionEquivalence`, in
`TauCeti.Algebra.Homology.Periodic.Compression.GlobalDimension`).

Under the same hypotheses the gradable objects generate `D_n(C)` under shifts and cones
(`TauCeti.PeriodicComplex.eq_top_of_gradable_le`, in
`TauCeti.Algebra.Homology.Periodic.Compression.Generation`), but they need not be all of
`D_n(C)`, and so need not form a triangulated subcategory: Stai shows that for a
finite-dimensional algebra of finite global dimension whose quiver has an oriented cycle, the
orbit category is strictly smaller than its triangulated hull `D_n(C)`.

## Main definitions

* `TauCeti.PeriodicComplex.gradable`: the gradable objects of `D_n(C)`.

## Main results

* `TauCeti.PeriodicComplex.essImage_derivedCompressionFunctor`: the gradable objects are the
  essential image of compression `D^b(C) ⥤ D_n(C)`.
* `TauCeti.PeriodicComplex.gradable_iff_exists_bounded`: gradable objects are the classes of
  compressions of bounded complexes, up to isomorphism.
* `TauCeti.PeriodicComplex.gradable_Qh_obj_quotient_obj_of_d_eq_zero`: for positive `n`,
  periodic complexes with zero differential are gradable.
* `TauCeti.PeriodicComplex.essImage_orbitDerivedCompressionFunctor`: the essential image of the
  orbit functor is the class of gradable objects.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.3, Lemma 3.12 and Section 5.
-/

public section

open CategoryTheory Limits

universe w v u

namespace TauCeti.PeriodicComplex

variable (C : Type u) [Category.{v} C] [Abelian C] (n : ℕ)

/-- An object of the `n`-periodic derived category `D_n(C)` is **gradable** when it lies in the
essential image of compression `D^b(C) ⥤ D_n(C)` (`essImage_derivedCompressionFunctor`), that
is, when it is isomorphic to the compression of a bounded complex. It is defined through the
homotopy categories, as the essential image of `K^b(C) ⥤ K_n(C) ⥤ D_n(C)`, so that it needs no
choice of bounded derived category. -/
def gradable : ObjectProperty (DerivedCategory C n) :=
  (homotopyCompressionFunctor n ⋙ DerivedCategory.Qh C n).essImage

variable {C n}

instance : (gradable C n).IsClosedUnderIsomorphisms :=
  inferInstanceAs (homotopyCompressionFunctor (C := C) n ⋙
    DerivedCategory.Qh C n).essImage.IsClosedUnderIsomorphisms

/-- Gradable objects are stable under the shifts of `D_n(C)`, because compression commutes with
the shifts. -/
instance : (gradable C n).IsStableUnderShift ℤ :=
  inferInstanceAs ((homotopyCompressionFunctor (C := C) n ⋙
    DerivedCategory.Qh C n).essImage.IsStableUnderShift ℤ)

/-- The zero objects of `D_n(C)` are gradable, as the compression of the zero complex. -/
instance : (gradable C n).ContainsZero :=
  inferInstanceAs (homotopyCompressionFunctor (C := C) n ⋙
    DerivedCategory.Qh C n).essImage.ContainsZero

/-- Gradable objects are closed under binary products, because compression is additive. -/
instance : (gradable C n).IsClosedUnderBinaryProducts :=
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (homotopyCompressionFunctor (C := C) n ⋙ DerivedCategory.Qh C n)
  inferInstanceAs (homotopyCompressionFunctor (C := C) n ⋙
    DerivedCategory.Qh C n).essImage.IsClosedUnderBinaryProducts

instance : (gradable C n).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- The image in `D_n(C)` of the class of a bounded complex `K` in `K^b(C)` is the class of the
periodic complex `compression n K`. -/
private noncomputable def homotopyCompressionFunctorCompQhObjIso (K : CochainComplex.Bounded C) :
    (homotopyCompressionFunctor n ⋙ DerivedCategory.Qh C n).obj
        ((HomotopyCategory.Bounded.quotient C).obj K) ≅
      (DerivedCategory.Qh C n).obj
        ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj (compression n K.obj)) :=
  (DerivedCategory.Qh C n).mapIso ((quotientCompHomotopyCompressionFunctorIso n).app K ≪≫
    (HomotopyCategory.quotient C _).mapIso (eqToIso (compressionFunctor_obj n K)))

/-- The class in `D_n(C)` of the compression of a bounded complex is gradable. -/
theorem gradable_Qh_obj_quotient_obj_compression (K : CochainComplex.Bounded C) :
    gradable C n ((DerivedCategory.Qh C n).obj
      ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj (compression n K.obj))) :=
  (gradable C n).prop_of_iso (homotopyCompressionFunctorCompQhObjIso K)
    (Functor.obj_mem_essImage _ _)

/-- **Gradable objects at the level of complexes.** An object of `D_n(C)` is gradable exactly
when it is isomorphic to the class of the compression `⨁_{i ≡ r (mod n)} Kⁱ` of a bounded
complex `K`. -/
theorem gradable_iff_exists_bounded (Y : DerivedCategory C n) :
    gradable C n Y ↔ ∃ K : CochainComplex.Bounded C, Nonempty ((DerivedCategory.Qh C n).obj
      ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj (compression n K.obj)) ≅
        Y) := by
  refine ⟨fun ⟨X, ⟨e⟩⟩ ↦ ?_, fun ⟨K, ⟨e⟩⟩ ↦
    (gradable C n).prop_of_iso e (gradable_Qh_obj_quotient_obj_compression K)⟩
  -- Every object of `K^b(C)` is the class of a bounded complex.
  let F := HomotopyCategory.Bounded.quotient C
  exact ⟨F.objPreimage X, ⟨(homotopyCompressionFunctorCompQhObjIso _).symm ≪≫
    (homotopyCompressionFunctor n ⋙ DerivedCategory.Qh C n).mapIso (F.objObjPreimageIso X) ≪≫
      e⟩⟩

/-- **Periodic complexes with zero differential are gradable.** For positive `n`, the class in
`D_n(C)` of a periodic complex with zero differential is gradable. The underlying complex is
itself isomorphic to the compression of a bounded complex with zero differential
(`CochainComplex.compressionIsoOfDEqZero`). -/
theorem gradable_Qh_obj_quotient_obj_of_d_eq_zero [NeZero n] (K : CochainComplex C (ZMod n))
    (hd : ∀ i j, K.d i j = 0) :
    gradable C n ((DerivedCategory.Qh C n).obj
      ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj K)) :=
  (gradable C n).prop_of_iso ((DerivedCategory.Qh C n).mapIso
    ((HomotopyCategory.quotient C _).mapIso (K.compressionIsoOfDEqZero hd)))
    (gradable_Qh_obj_quotient_obj_compression (boundedGradedLift K.X))

variable [HasDerivedCategory.{w} C]

/-- The essential image of compression `D^b(C) ⥤ D_n(C)` is the class of gradable objects. -/
@[simp]
theorem essImage_derivedCompressionFunctor :
    (derivedCompressionFunctor (C := C) n).essImage = gradable C n := by
  rw [← Functor.essImage_comp_of_essSurj (F := TauCeti.DerivedCategory.Bounded.Qh C)]
  exact Functor.essImage_eq_of_natIso (derivedCompressionFunctorFactors n)

/-- An object of `D_n(C)` is gradable exactly when it is isomorphic to the compression of an
object of `D^b(C)`. -/
theorem gradable_iff (Y : DerivedCategory C n) :
    gradable C n Y ↔ ∃ X, Nonempty ((derivedCompressionFunctor n).obj X ≅ Y) := by
  rw [← essImage_derivedCompressionFunctor]
  exact Iff.rfl

/-- The compression of an object of `D^b(C)` is gradable. -/
@[simp]
theorem gradable_derivedCompressionFunctor_obj (X : _root_.DerivedCategory.Bounded C) :
    gradable C n ((derivedCompressionFunctor n).obj X) := by
  rw [← essImage_derivedCompressionFunctor]
  exact (derivedCompressionFunctor n).obj_mem_essImage X

/-- **The essential image of the orbit functor.** The essential image of the orbit functor
`D^b(C)/[n] ⥤ D_n(C)` is the class of gradable objects. -/
theorem essImage_orbitDerivedCompressionFunctor :
    (orbitDerivedCompressionFunctor (C := C) n).essImage = gradable C n :=
  (OrbitCategory.essImage_lift _ _).trans essImage_derivedCompressionFunctor

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

end TauCeti.PeriodicComplex

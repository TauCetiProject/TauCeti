/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Functor.Triangulated
public import TauCeti.CategoryTheory.Exact.FullSubcategory

/-!
# Frobenius full subcategories and their stable inclusions

An extension-closed full subcategory of a Frobenius exact category inherits a Frobenius
exact structure if it contains the ambient projective-injectives and is closed under kernels
and cokernels of conflations with projective-injective middle term. These are sufficient
closure conditions, recorded by `ExactStructure.IsFrobeniusSubcategory`; extension closure
alone does not guarantee enough projectives or injectives.

For the induced structure, relative projectivity and injectivity agree with their ambient
counterparts. The stable inclusion is fully faithful: every ambient projectively trivial
morphism between subcategory objects already factors through a projective of the subcategory.
It is a triangle functor by `StableConflationExact.stableFunctorIsTriangulated`, applied to
`IsFrobeniusSubcategory.stableConflationExact_ι` and `.isFrobenius`.
The shift comparisons and triangulated structures are the existing Happel constructions;
they are installed locally as in that theorem.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69,
  <https://arxiv.org/abs/0811.1480>, Sections 11–13.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : ExactStructure C} {P : ObjectProperty C}

/-- Sufficient closure conditions for a full subcategory of a Frobenius exact category to
inherit its Frobenius structure and embed fully faithfully on stable categories.

The kernel and cokernel conditions apply to all conflations with projective-injective middle
term. In particular, the ambient projective and injective presentations remain inside `P`.
Containing all ambient projective-injectives also ensures that ambient stable factorizations
between objects of `P` can be carried out within the subcategory. -/
structure IsFrobeniusSubcategory (E : ExactStructure C) (P : ObjectProperty C) : Prop where
  /-- Extensions of objects of the subcategory remain in it. -/
  extensionClosed : E.IsExtensionClosed P
  /-- Every ambient projective-injective object belongs to the subcategory. -/
  contains_projectiveInjective : E.projectiveInjective ≤ P
  /-- Kernels of deflations from projective-injectives to subcategory objects remain in it. -/
  kernel_mem : ∀ {S : ShortComplex C}, E.Conflation S → E.projectiveInjective S.X₂ →
    P S.X₃ → P S.X₁
  /-- Cokernels of inflations into projective-injectives from subcategory objects remain in it. -/
  cokernel_mem : ∀ {S : ShortComplex C}, E.Conflation S → E.projectiveInjective S.X₂ →
    P S.X₁ → P S.X₃

namespace IsFrobeniusSubcategory

variable (hP : E.IsFrobeniusSubcategory P) (hE : E.IsFrobenius)
include hP

/-- Containing the ambient projective-injectives ensures that the subcategory contains zero. -/
theorem containsZero : P.ContainsZero where
  exists_zero := ⟨0, isZero_zero C,
    hP.contains_projectiveInjective _ E.projectiveInjective.prop_zero⟩

/-- Extension closure and the zero object imply closure under binary biproducts. -/
theorem isClosedUnderBinaryProducts : P.IsClosedUnderBinaryProducts := by
  let := hP.containsZero
  let := hP.extensionClosed.isClosedUnderIsomorphisms
  exact hP.extensionClosed.isClosedUnderBinaryProducts

variable [P.ContainsZero] [P.IsClosedUnderBinaryProducts]

include hE

private noncomputable def projectivePresentation (X : P.FullSubcategory) :
    (E.fullSubcategory P hP.extensionClosed).ProjectivePresentation X := by
  let R := hE.enoughProjectives.projectivePresentation X.obj
  have hR : E.projectiveInjective R.P :=
    (E.projectiveInjective_iff R.P).mpr
      ⟨R.isProjective, (hE.projective_iff_injective R.P).mp R.isProjective⟩
  let Q : P.FullSubcategory := ⟨R.P, hP.contains_projectiveInjective _ hR⟩
  let K : P.FullSubcategory := ⟨R.K, hP.kernel_mem R.conflation hR X.property⟩
  refine { P := Q
           K := K
           i := ObjectProperty.homMk R.i
           p := ObjectProperty.homMk R.p
           zero := ObjectProperty.hom_ext _ R.zero
           conflation := ?_
           isProjective :=
             isProjective_fullSubcategory_of_isProjective hP.extensionClosed Q R.isProjective }
  rw [fullSubcategory_conflation_iff]
  exact R.conflation

private noncomputable def injectivePresentation (X : P.FullSubcategory) :
    (E.fullSubcategory P hP.extensionClosed).InjectivePresentation X := by
  let R := hE.enoughInjectives.injectivePresentation X.obj
  have hR : E.projectiveInjective R.I :=
    (E.projectiveInjective_iff R.I).mpr ⟨hE.isProjective_I R, R.isInjective⟩
  let I : P.FullSubcategory := ⟨R.I, hP.contains_projectiveInjective _ hR⟩
  let K : P.FullSubcategory := ⟨R.K, hP.cokernel_mem R.conflation hR X.property⟩
  refine { I := I
           K := K
           i := ObjectProperty.homMk R.i
           p := ObjectProperty.homMk R.p
           zero := ObjectProperty.hom_ext _ R.zero
           conflation := ?_
           isInjective :=
             isInjective_fullSubcategory_of_isInjective hP.extensionClosed I R.isInjective }
  rw [fullSubcategory_conflation_iff]
  exact R.conflation

/-- Relative projectivity in the induced structure is precisely ambient relative projectivity.
The closure conditions guarantee a presentation inside the subcategory; a projective object
is then a retract of its ambient projective middle term. -/
theorem isProjective_iff (X : P.FullSubcategory) :
    (E.fullSubcategory P hP.extensionClosed).isProjective X ↔ E.isProjective X.obj := by
  refine ⟨fun hX => ?_, isProjective_fullSubcategory_of_isProjective hP.extensionClosed X⟩
  let R := hP.projectivePresentation hE X
  let s := (E.fullSubcategory P hP.extensionClosed).splittingOfProjective R.conflation hX
  have hr : Retract X.obj R.P.obj :=
    { i := s.s.hom
      r := R.p.hom
      retract := by simpa using P.ι.congr_map s.s_g }
  exact E.isProjective.prop_of_retract hr
    (hE.enoughProjectives.projectivePresentation X.obj).isProjective

/-- Relative injectivity in the induced structure is precisely ambient relative injectivity.
An injective object is a retract of the ambient injective middle term of its presentation. -/
theorem isInjective_iff (X : P.FullSubcategory) :
    (E.fullSubcategory P hP.extensionClosed).isInjective X ↔ E.isInjective X.obj := by
  refine ⟨fun hX => ?_, isInjective_fullSubcategory_of_isInjective hP.extensionClosed X⟩
  let R := hP.injectivePresentation hE X
  let s := (E.fullSubcategory P hP.extensionClosed).splittingOfInjective R.conflation hX
  have hr : Retract X.obj R.I.obj :=
    { i := R.i.hom
      r := s.r.hom
      retract := by simpa using P.ι.congr_map s.f_r }
  exact E.isInjective.prop_of_retract hr
    (hE.enoughInjectives.injectivePresentation X.obj).isInjective

/-- The exact structure induced on a subcategory satisfying the closure conditions is
Frobenius. Both kinds of presentations are restrictions of ambient presentations. -/
theorem isFrobenius : (E.fullSubcategory P hP.extensionClosed).IsFrobenius where
  enoughProjectives := ⟨fun X => ⟨hP.projectivePresentation hE X⟩⟩
  enoughInjectives := ⟨fun X => ⟨hP.injectivePresentation hE X⟩⟩
  projective_iff_injective X := by
    rw [hP.isProjective_iff hE, hP.isInjective_iff hE]
    exact hE.projective_iff_injective X.obj

/-- The full-subcategory inclusion preserves conflations and projective-injectives, so its
stable functor is a triangle functor by `StableConflationExact.stableFunctorIsTriangulated`
with the Frobenius structures `hP.isFrobenius hE` and `hE`. -/
theorem stableConflationExact_ι :
    StableConflationExact (E.fullSubcategory P hP.extensionClosed) E P.ι where
  isConflationExact := E.isConflationExact_ι hP.extensionClosed
  map_projectiveInjective {X} hX := by
    rw [projectiveInjective_iff] at hX ⊢
    exact ⟨(hP.isProjective_iff hE X).mp hX.1, (hP.isInjective_iff hE X).mp hX.2⟩

/-- The projective stable ideal of the induced structure is exactly the inverse image of the
ambient stable ideal. In particular, the stable inclusion reflects zero morphisms. -/
theorem projectiveStableIdeal_eq_comap :
    (E.fullSubcategory P hP.extensionClosed).projectiveStableIdeal =
      E.projectiveStableIdeal.comap P.ι := by
  refine le_antisymm ((hP.stableConflationExact_ι hE).projectiveStableIdeal_le_comap
    (hP.isFrobenius hE)) ?_
  intro X Y f hf
  rw [MorphismIdeal.mem_comap_hom, mem_projectiveStableIdeal_iff] at hf
  obtain ⟨Q, hQ, i, p, hp⟩ := (ObjectProperty.factorsThrough_iff _ _).mp hf
  let Q' : P.FullSubcategory := ⟨Q, hP.contains_projectiveInjective _
    ((E.projectiveInjective_iff Q).mpr ⟨hQ, (hE.projective_iff_injective Q).mp hQ⟩)⟩
  rw [mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff]
  refine ⟨Q', (hP.isProjective_iff hE Q').mpr hQ, ObjectProperty.homMk i,
    ObjectProperty.homMk p, ?_⟩
  exact P.ι.map_injective (by simpa using hp)

/-- The stable inclusion of a full Frobenius subcategory satisfying the closure conditions is
faithful: an ambient factorization through a projective can be made in the subcategory. -/
theorem stableFunctor_ι_faithful :
    ((hP.stableConflationExact_ι hE).stableFunctor (hP.isFrobenius hE)).Faithful := by
  rw [StableConflationExact.stableFunctor_eq_map]
  apply (MorphismIdeal.faithful_map_iff _ _ _ _).mpr
  exact le_of_eq (hP.projectiveStableIdeal_eq_comap hE).symm

end IsFrobeniusSubcategory

end TauCeti.ExactStructure

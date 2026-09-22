/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Basic
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Presentations are cofinal among rational subsets

The structure presheaf on `Spa(A,A⁺)` is defined on an open `V` as the limit of the coordinate
rings of the rational subsets contained in `V`. The existing construction
`TauCeti.ValuationSpectrum.presentationLimit` instead indexes the limit by admissible
*presentations* `(T,s)` of those subsets. This file supplies the categorical comparison between
the two indices.

`RationalSubsetIndex Aplus V` is the preorder of rational subsets contained in `V`, ordered by
reverse inclusion, so a morphism points in the direction of restriction. The functor
`presentationToRationalSubsetIndex` forgets a presentation and remembers its subset. Every
rational subset has a presentation in this functor's image: openness of its numerator ideal gives
the standing denominator-power condition by
`TauCeti.Huber.PairOfDefinition.hasDenominatorPower_of_isOpen_span`.

The forgetful functor is both final and initial. Finality records the usual meaning of cofinality
for a basis ordered by refinement. Initiality is the form needed for limits: the costructured
arrow category over a rational subset is connected because two presentations containing it have
a common refinement which still contains it. Consequently a limit over rational subsets can be
computed over presentations without choosing a preferred presentation.

## Main definitions

* `TauCeti.ValuationSpectrum.RationalSubsetIndex`: rational subsets contained in an open, ordered
  by reverse inclusion.
* `TauCeti.ValuationSpectrum.presentationToRationalSubsetIndex`: the functor forgetting
  presentation data.

## Main results

* `TauCeti.ValuationSpectrum.exists_presentationToRationalSubsetIndex_obj_eq`: every rational
  subset index is exactly represented by an admissible presentation.
* `CategoryTheory.Functor.Final
    (TauCeti.ValuationSpectrum.presentationToRationalSubsetIndex Aplus V)`: presentations are
  cofinal among rational subsets.
* `CategoryTheory.Functor.Initial
    (TauCeti.ValuationSpectrum.presentationToRationalSubsetIndex Aplus V)`: restriction along the
  presentation functor preserves limits.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory _root_.TopologicalSpace TauCeti.Huber

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {Aplus : Subring A} {V : Opens ↥(spa Aplus)}

/-- A rational subset contained in an open `V`, ordered by reverse inclusion so that arrows point
from a rational subset to a smaller one, in the direction of restriction maps. -/
structure RationalSubsetIndex (Aplus : Subring A) (V : Opens ↥(spa Aplus)) where
  /-- The underlying subset of the adic spectrum. -/
  carrier : Set (spa Aplus)
  /-- The subset has an admissible rational presentation. -/
  isRational : carrier ∈ spaRationalFamily Aplus
  /-- The rational subset is contained in the ambient open. -/
  le_open : carrier ⊆ V

/-- Rational subset indices are ordered by reverse inclusion, matching the direction of
restriction maps. -/
instance : Preorder (RationalSubsetIndex Aplus V) where
  le U W := W.carrier ⊆ U.carrier
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ hUW hWZ := hWZ.trans hUW

omit [IsTopologicalRing A] in
/-- Equality of rational subset indices is equality of their underlying subsets; the remaining
fields are propositions. -/
@[ext]
theorem RationalSubsetIndex.ext {U W : RationalSubsetIndex Aplus V}
    (h : U.carrier = W.carrier) : U = W := by
  cases U
  cases W
  subst h
  rfl

omit [IsTopologicalRing A] in
/-- The order on rational subset indices is reverse inclusion. -/
theorem RationalSubsetIndex.le_iff {U W : RationalSubsetIndex Aplus V} :
    U ≤ W ↔ W.carrier ⊆ U.carrier :=
  Iff.rfl

/-- Forget an admissible presentation and retain the rational subset it presents. Refinement
becomes reverse inclusion by `rationalSubset_subset_rationalSubset_of_le`. -/
noncomputable def presentationToRationalSubsetIndex (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) :
    PresentationIndex (P := P) Aplus V ⥤ RationalSubsetIndex Aplus V where
  obj i :=
    { carrier := Subtype.val ⁻¹' rationalSubset Aplus i.pres.num i.pres.den
      isRational := mem_spaRationalFamily_iff.mpr
        ⟨i.pres.num, i.pres.den, i.isOpen_span, rfl⟩
      le_open := fun _ hx ↦ i.le_open (mem_spaBasicOpen.mpr hx) }
  map {i j} f := homOfLE fun _ hx ↦
    rationalSubset_subset_rationalSubset_of_le Aplus f.le hx
  map_id _ := by subsingleton
  map_comp _ _ := by subsingleton

omit [IsTopologicalRing A] in
/-- The subset underlying the image of a presentation is the rational subset it presents. -/
@[simp]
theorem presentationToRationalSubsetIndex_obj_carrier (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) (i : PresentationIndex (P := P) Aplus V) :
    ((presentationToRationalSubsetIndex Aplus V).obj i).carrier =
      Subtype.val ⁻¹' rationalSubset Aplus i.pres.num i.pres.den :=
  (rfl)

/-- **Every rational subset index has an admissible presentation.** The open numerator ideal in
the definition of `spaRationalFamily` supplies `HasDenominatorPower`, so the chosen presentation
is an object of `PresentationIndex`, and forgetting it recovers the original subset exactly. -/
theorem exists_presentationToRationalSubsetIndex_obj_eq
    (U : RationalSubsetIndex Aplus V) :
    ∃ i : PresentationIndex (P := P) Aplus V,
      (presentationToRationalSubsetIndex Aplus V).obj i = U := by
  obtain ⟨T, s, hT, hU⟩ := mem_spaRationalFamily_iff.mp U.isRational
  let p : P.Presentation :=
    { num := T
      den := s
      hasDenominatorPower := P.hasDenominatorPower_of_isOpen_span T s _ hT }
  let i : PresentationIndex (P := P) Aplus V :=
    { pres := p
      isOpen_span := hT
      le_open := by
        intro x hx
        apply U.le_open
        rw [hU]
        simpa [p] using mem_spaBasicOpen.mp hx }
  exact ⟨i, RationalSubsetIndex.ext hU.symm⟩

/-- The functor from presentations to rational subsets is final: every rational subset is in its
image, and the presentation index is filtered by common refinement. This is the categorical
cofinality assertion for the two index preorders. -/
instance : (presentationToRationalSubsetIndex (P := P) Aplus V).Final :=
  Functor.final_of_exists_of_isFiltered _
    (fun U ↦ by
      obtain ⟨i, hi⟩ := exists_presentationToRationalSubsetIndex_obj_eq (P := P) U
      exact ⟨i, ⟨eqToHom hi.symm⟩⟩)
    (fun {_ i} _ _ ↦ ⟨i, 𝟙 _, by subsingleton⟩)

/-- A common refinement of two presentations lying over a rational subset still lies over that
subset. This is the object connecting any two points of the costructured arrow category used to
prove initiality. -/
private noncomputable def commonCostructuredArrow
    (U : RationalSubsetIndex Aplus V)
    (i j : CostructuredArrow (presentationToRationalSubsetIndex (P := P) Aplus V) U) :
    CostructuredArrow (presentationToRationalSubsetIndex (P := P) Aplus V) U := by
  let k := i.left.commonRefinement j.left
  have hk : (presentationToRationalSubsetIndex (P := P) Aplus V).obj k ≤ U := by
    intro x hx
    rw [presentationToRationalSubsetIndex_obj_carrier,
      PresentationIndex.commonRefinement_pres, rationalSubset_commonRefinement,
      Set.preimage_inter, Set.mem_inter_iff]
    exact ⟨i.hom.le hx, j.hom.le hx⟩
  exact CostructuredArrow.mk (homOfLE hk)

/-- The left presentation maps to the common object in the costructured arrow category. -/
private noncomputable def hom_commonCostructuredArrow_left
    (U : RationalSubsetIndex Aplus V)
    (i j : CostructuredArrow (presentationToRationalSubsetIndex (P := P) Aplus V) U) :
    i ⟶ commonCostructuredArrow U i j :=
  CostructuredArrow.homMk
    (homOfLE (i.left.le_commonRefinement_left j.left)) (by subsingleton)

/-- The right presentation maps to the common object in the costructured arrow category. -/
private noncomputable def hom_commonCostructuredArrow_right
    (U : RationalSubsetIndex Aplus V)
    (i j : CostructuredArrow (presentationToRationalSubsetIndex (P := P) Aplus V) U) :
    j ⟶ commonCostructuredArrow U i j :=
  CostructuredArrow.homMk
    (homOfLE (i.left.le_commonRefinement_right j.left)) (by subsingleton)

/-- The functor from presentations to rational subsets is initial. Thus limits indexed by
rational subsets are unchanged after restricting to presentations. -/
instance : (presentationToRationalSubsetIndex (P := P) Aplus V).Initial where
  out U := by
    let _ : Nonempty
        (CostructuredArrow (presentationToRationalSubsetIndex (P := P) Aplus V) U) := by
      obtain ⟨i, hi⟩ := exists_presentationToRationalSubsetIndex_obj_eq (P := P) U
      exact ⟨CostructuredArrow.mk (eqToHom hi)⟩
    exact zigzag_isConnected fun i j ↦
      Zigzag.of_hom_inv (hom_commonCostructuredArrow_left U i j)
        (hom_commonCostructuredArrow_right U i j)

end

end TauCeti.ValuationSpectrum

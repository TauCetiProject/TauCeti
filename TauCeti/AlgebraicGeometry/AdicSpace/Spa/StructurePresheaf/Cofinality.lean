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

Wedhorn defines the structure presheaf on `Spa(A,A⁺)` at an open `V` as the limit of the
coordinate rings of the rational subsets contained in `V`. The existing construction
`TauCeti.ValuationSpectrum.presentationLimit` instead indexes the limit by admissible
*presentations* `(T,s)` of those subsets. This file supplies the categorical comparison of the
two indices needed once the coordinate rings are assembled into a diagram on rational subsets.

`RationalSubsetIndex Aplus V` is the partial order of rational subsets contained in `V`, ordered by
reverse inclusion, so a morphism points in the direction of restriction. The functor
`presentationToRationalSubsetIndex` forgets a presentation and remembers its subset. Every
rational subset has a presentation in this functor's image: openness of its numerator ideal gives
the standing denominator-power condition by
`TauCeti.Huber.PairOfDefinition.hasDenominatorPower_of_isOpen_span`.

The forgetful functor is both final and initial. Finality records the usual meaning of cofinality
for a basis ordered by refinement. Initiality is the form needed for limits: the costructured
arrow category over a rational subset is connected because two presentations containing it have
a common refinement which still contains it. Consequently, once a compatible coordinate-ring
diagram on rational subsets is constructed, its limit can be computed over presentations without
choosing a preferred presentation.

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
    (TauCeti.ValuationSpectrum.presentationToRationalSubsetIndex Aplus V)`: the cofinality
  condition that will preserve the rational-subset-indexed limit once its diagram is constructed.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory _root_.TopologicalSpace TauCeti.Huber

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {Aplus : Subring A} {V : Opens ↥(spa Aplus)}

/-- A rational open contained in an open `V`, ordered by reverse inclusion so that arrows point
from a rational open to a smaller one, in the direction of restriction maps. -/
abbrev RationalSubsetIndex (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :=
  { U : Opens (spa Aplus) // U ∈ spaRationalOpens Aplus ∧ U ≤ V }ᵒᵈ

omit [IsTopologicalRing A] in
/-- The order on rational-subset indices is reverse inclusion of their underlying opens. -/
@[simp]
theorem rationalSubsetIndex_le_iff (U W : RationalSubsetIndex Aplus V) :
    U ≤ W ↔ ∀ x, x ∈ (OrderDual.ofDual W).1 → x ∈ (OrderDual.ofDual U).1 :=
  Iff.rfl

omit [IsTopologicalRing A] in
/-- Forget an admissible presentation and retain the rational subset it presents. Refinement
becomes reverse inclusion by `rationalSubset_subset_rationalSubset_of_le`. -/
noncomputable def presentationToRationalSubsetIndex (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) :
    PresentationIndex (P := P) Aplus V ⥤ RationalSubsetIndex Aplus V where
  obj i :=
    OrderDual.toDual
      ⟨spaBasicOpen Aplus i.pres.num i.pres.den,
        mem_spaRationalOpens.mpr <| mem_spaRationalFamily_iff.mpr
          ⟨i.pres.num, i.pres.den, i.isOpen_span, Set.ext fun _ ↦ mem_spaBasicOpen⟩,
        i.le_open⟩
  map {i j} f := homOfLE <| spaBasicOpen_le_spaBasicOpen_iff.mpr <|
    rationalSubset_subset_rationalSubset_of_le Aplus f.le
  map_id _ := by subsingleton
  map_comp _ _ := by subsingleton

omit [IsTopologicalRing A] in
/-- The open underlying the image of a presentation is the rational open it presents. -/
@[simp]
theorem presentationToRationalSubsetIndex_obj_open (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) (i : PresentationIndex (P := P) Aplus V) :
    (OrderDual.ofDual ((presentationToRationalSubsetIndex Aplus V).obj i)).1 =
      spaBasicOpen Aplus i.pres.num i.pres.den :=
  (rfl)

/-- **Every rational subset index has an admissible presentation.** The open numerator ideal in
the definition of `spaRationalFamily` supplies `HasDenominatorPower`, so the chosen presentation
is an object of `PresentationIndex`, and forgetting it recovers the original subset exactly. -/
theorem exists_presentationToRationalSubsetIndex_obj_eq
    (U : RationalSubsetIndex Aplus V) :
    ∃ i : PresentationIndex (P := P) Aplus V,
      (presentationToRationalSubsetIndex Aplus V).obj i = U := by
  obtain ⟨T, s, hT, hU⟩ :=
    mem_spaRationalFamily_iff.mp (mem_spaRationalOpens.mp U.2.1)
  let p : P.Presentation :=
    { num := T
      den := s
      hasDenominatorPower := P.hasDenominatorPower_of_isOpen_span T s _ hT }
  have hopen : spaBasicOpen Aplus p.num p.den = (OrderDual.ofDual U).1 := by
    apply Opens.ext
    exact (Set.ext fun _ ↦ mem_spaBasicOpen).trans hU.symm
  let i : PresentationIndex (P := P) Aplus V :=
    { pres := p
      isOpen_span := hT
      le_open := hopen.le.trans U.2.2 }
  refine ⟨i, ?_⟩
  apply OrderDual.ofDual.injective
  apply Subtype.ext
  rw [presentationToRationalSubsetIndex_obj_open]
  exact hopen

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
    rw [rationalSubsetIndex_le_iff, presentationToRationalSubsetIndex_obj_open]
    intro x hx
    change x ∈ spaBasicOpen Aplus (i.left.commonRefinement j.left).pres.num
      (i.left.commonRefinement j.left).pres.den
    rw [spaBasicOpen_commonRefinement, Opens.mem_inf]
    constructor
    · rw [← presentationToRationalSubsetIndex_obj_open]
      exact i.hom.le hx
    · rw [← presentationToRationalSubsetIndex_obj_open]
      exact j.hom.le hx
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

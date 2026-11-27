/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import TauCeti.RingTheory.TestRing

import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Polynomial.Lifts
import TauCeti.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The category of test rings

`TauCeti.TestRingCat` is the full subcategory of `CommRingCat` whose objects are the test rings
(`TauCeti.IsTestRing`): absolutely integrally closed reduced rings in which any two elements become
comparable for divisibility after splitting along an idempotent. With rings in a universe `u`, it
has objects in `Type (u + 1)` and morphisms in `Type u`: a large category with small hom-sets.

A filtered colimit of test rings, taken in `CommRingCat`, is a test ring
(`TauCeti.IsTestRing.of_isColimit`), because finitely many elements of a filtered colimit of rings
come from one member of the diagram, and an element vanishing in the colimit already vanishes in
some member. So the test rings are closed in `CommRingCat` under filtered colimits, and
`TestRingCat` has filtered colimits, computed in `CommRingCat`.

## Main definitions

* `CommRingCat.isTestRing`: the property of a commutative ring of being a test ring.
* `TauCeti.TestRingCat`: the category of test rings, the full subcategory of `CommRingCat` on the
  test rings.

## Main results

* `TauCeti.IsTestRing.of_isColimit`: a filtered colimit of test rings in `CommRingCat` is a test
  ring.
* `CommRingCat.isTestRing` is closed under isomorphisms and under filtered colimits, so
  `TauCeti.TestRingCat` has filtered colimits, computed in `CommRingCat`.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean, files
  `src/Lib/Cohomology/Etale/Basic.lean` (declaration `New.Variety.TestRing`) and
  `src/Lib/Cohomology/Etale/FilteredLimits.lean` (declaration
  `New.Variety.IsTest.filtered_colimit`); Apache 2.0, Copyright 2026 Anthropic, PBC. The category
  of test rings and the statement on filtered colimits are adapted from there.
-/

public section

open CategoryTheory Limits Polynomial

universe u

namespace TauCeti.IsTestRing

variable {J : Type*} [Category J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}}
  [PreservesColimit F (forget CommRingCat.{u})] [∀ j, IsTestRing (F.obj j)] {c : Cocone F}

/-- A filtered colimit of test rings, taken in commutative rings, is a test ring. The hypothesis
that the forgetful functor preserves the colimit holds for every small filtered diagram. -/
theorem of_isColimit (hc : IsColimit c) : IsTestRing c.pt where
  exists_root p hp hdeg := by
    -- The coefficients of `p` come from one member `F.obj k` of the diagram, so `p` is the image
    -- of a monic polynomial of the same degree over `F.obj k`, which has a root there.
    obtain ⟨k, y, hy⟩ := Concrete.isColimit_exists_rep_fin F hc fun n : p.support ↦ p.coeff n
    have hlifts : p ∈ lifts (c.ι.app k).hom := by
      refine (lifts_iff_coeff_lifts p).mpr fun n ↦ ?_
      by_cases hn : n ∈ p.support
      · exact ⟨y ⟨n, hn⟩, hy ⟨n, hn⟩⟩
      · exact ⟨0, by rw [map_zero, notMem_support_iff.mp hn]⟩
    obtain ⟨q, rfl, hqdeg, hq⟩ := lifts_and_natDegree_eq_and_monic hlifts hp
    obtain ⟨a, ha⟩ := IsAbsolutelyIntegrallyClosed.exists_root q hq (hqdeg ▸ hdeg)
    exact ⟨(c.ι.app k).hom a, ha.map _⟩
  eq_zero x := by
    -- If `x ^ n = 0` with `x` the image of `y`, then some map of the diagram kills `y ^ n`, hence
    -- kills `y`, the target being reduced.
    rintro ⟨n, hn⟩
    obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep F hc x
    have h : c.ι.app j (y ^ n) = c.ι.app j 0 := by
      simpa using hn
    obtain ⟨k, f, g, hfg⟩ := (Concrete.isColimit_rep_eq_iff_exists F hc _ _).mp h
    have hy : (F.map f).hom y = 0 :=
      IsReduced.eq_zero _ ⟨n, by simpa using hfg⟩
    rw [← c.w f, ConcreteCategory.comp_apply]
    simp [hy]
  exists_isIdempotentElem_dvd_mul a b := by
    -- `a` and `b` come from one member of the diagram; split them there.
    obtain ⟨k, y, hy⟩ := Concrete.isColimit_exists_rep_fin F hc ![a, b]
    have ha : (c.ι.app k).hom (y 0) = a := hy 0
    have hb : (c.ι.app k).hom (y 1) = b := hy 1
    obtain ⟨e, he, hab, hba⟩ := exists_isIdempotentElem_dvd_mul (y 0) (y 1)
    refine ⟨(c.ι.app k).hom e, he.map _, ?_, ?_⟩
    · simpa [ha, hb] using map_dvd (c.ι.app k).hom hab
    · simpa [ha, hb] using map_dvd (c.ι.app k).hom hba

end TauCeti.IsTestRing

namespace CommRingCat

/-- The property of a commutative ring of being a test ring. -/
def isTestRing : ObjectProperty CommRingCat.{u} :=
  fun R ↦ TauCeti.IsTestRing R

/-- A commutative ring satisfies `CommRingCat.isTestRing` exactly when it is a test ring. -/
@[simp]
theorem isTestRing_iff (R : CommRingCat.{u}) : isTestRing R ↔ TauCeti.IsTestRing R :=
  Iff.rfl

/-- Being a test ring is invariant under isomorphisms of rings. -/
instance : isTestRing.{u}.IsClosedUnderIsomorphisms where
  of_iso e h :=
    have : TauCeti.IsTestRing _ := h
    have := isReduced_of_injective e.commRingCatIsoToRingEquiv.symm
      e.commRingCatIsoToRingEquiv.symm.injective
    .of_surjective e.hom.hom e.commRingCatIsoToRingEquiv.surjective

/-- Test rings are closed under filtered colimits in `CommRingCat`, for instance under all small
filtered colimits. -/
instance {J : Type*} [Category J] [IsFiltered J]
    [PreservesColimitsOfShape J (forget CommRingCat.{u})] :
    isTestRing.{u}.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le _ := fun ⟨h⟩ ↦
    have (j : J) : TauCeti.IsTestRing (h.diag.obj j) := h.prop_diag_obj j
    TauCeti.IsTestRing.of_isColimit h.isColimit

end CommRingCat

namespace TauCeti

/-- The category of test rings: the full subcategory of `CommRingCat` whose objects are the test
rings. -/
abbrev TestRingCat : Type (u + 1) :=
  CommRingCat.isTestRing.{u}.FullSubcategory

/-- The underlying ring of an object of `TestRingCat` is a test ring. -/
instance (A : TestRingCat.{u}) : IsTestRing A.obj :=
  A.property

/-- The category of test rings has filtered colimits, computed in `CommRingCat`. -/
instance : HasFilteredColimits TestRingCat.{u} where
  HasColimitsOfShape _ _ _ := inferInstance

end TauCeti

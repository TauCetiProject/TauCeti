/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Frobenius
public import TauCeti.CategoryTheory.Exact.Karoubi

/-!
# The idempotent completion of a Frobenius exact category

Let `E` be an exact structure on an additive category `C` and `E.karoubi` the induced exact
structure on the idempotent completion `Karoubi C`. This file proves that `E.karoubi` is
Frobenius when `E` is.

* The image `toKaroubi P` of a relatively projective object `P` is relatively projective: a
  deflation of `E.karoubi` is a retract of the image of a deflation `d` of `E`, and a morphism
  out of `toKaroubi P` lifts through `d` since `toKaroubi` is fully faithful.
* Every object `X` of `Karoubi C` is a direct summand of `toKaroubi X.X`, and the projection is
  a split deflation (`TauCeti.ExactStructure.karoubi_isDeflation_decompId_p`). Composing it
  with the image of a projective presentation of `X.X` gives a projective presentation of `X`.
* Hence the relative projectives of `E.karoubi` are the retracts of images of relative
  projectives of `E`, and dually for injectives. When `E` is Frobenius these two classes agree.

## Main results

* `TauCeti.ExactStructure.karoubi_isProjective_toKaroubi_obj` and
  `TauCeti.ExactStructure.karoubi_isInjective_toKaroubi_obj`: `toKaroubi` preserves relative
  projectives and injectives.
* `TauCeti.ExactStructure.karoubi_enoughProjectives`,
  `TauCeti.ExactStructure.karoubi_enoughInjectives`: enough projectives and injectives pass to
  the idempotent completion.
* `TauCeti.ExactStructure.karoubi_isProjective_iff` and
  `TauCeti.ExactStructure.karoubi_isInjective_iff`: the relative projectives (injectives) of the
  idempotent completion are the retracts of images of relative projectives (injectives).
* `TauCeti.ExactStructure.IsFrobenius.karoubi`: the idempotent completion of a Frobenius exact
  category is Frobenius.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69, Section 6,
  Proposition 6.13, for the exact structure on the idempotent completion.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable (E : ExactStructure C)

/-- **`toKaroubi` preserves relative projectives**: a morphism out of `toKaroubi P` lifts through a
deflation of the idempotent completion, a retract of the image of a deflation `d` of `E`, by
lifting its preimage through `d`. -/
theorem karoubi_isProjective_toKaroubi_obj {P : C} (hP : E.isProjective P) :
    E.karoubi.isProjective ((toKaroubi C).obj P) := by
  refine isProjective_iff.2 fun X Y p hp f ↦ ?_
  obtain ⟨B, D, d, hd, ⟨r⟩⟩ := (E.karoubi_isDeflation_iff p).1 hp
  obtain ⟨h, hh⟩ := isProjective_iff.1 hP hd ((toKaroubi C).preimage (f ≫ r.i.right))
  have hh' : (toKaroubi C).map h ≫ (toKaroubi C).map d = f ≫ r.i.right := by
    rw [← Functor.map_comp, hh, Functor.map_preimage]
  exact ⟨(toKaroubi C).map h ≫ r.r.left, by simp [r.r_w, reassoc_of% hh']⟩

/-- **`toKaroubi` preserves relative injectives**: a morphism into `toKaroubi I` extends along an
inflation of the idempotent completion, a retract of the image of an inflation `a` of `E`, by
extending its preimage along `a`. -/
theorem karoubi_isInjective_toKaroubi_obj {I : C} (hI : E.isInjective I) :
    E.karoubi.isInjective ((toKaroubi C).obj I) := by
  refine isInjective_iff.2 fun X Y i hi f ↦ ?_
  obtain ⟨A, B, a, ha, ⟨r⟩⟩ := (E.karoubi_isInflation_iff i).1 hi
  obtain ⟨h, hh⟩ := isInjective_iff.1 hI ha ((toKaroubi C).preimage (r.r.left ≫ f))
  have hh' : (toKaroubi C).map a ≫ (toKaroubi C).map h = r.r.left ≫ f := by
    rw [← Functor.map_comp, hh, Functor.map_preimage]
  exact ⟨r.i.right ≫ (toKaroubi C).map h, by simp [← r.i_w_assoc, hh']⟩

variable {E}

/-- With enough projectives, every object of the idempotent completion is the target of a
deflation from the image of a relative projective: the image of a projective presentation of
`X.X`, followed by the projection onto the summand `X`. -/
theorem karoubi_exists_isDeflation (h : E.EnoughProjectives) (X : Karoubi C) :
    ∃ (P : C) (p : (toKaroubi C).obj P ⟶ X), E.isProjective P ∧ E.karoubi.IsDeflation p := by
  obtain ⟨P⟩ := h.presentation X.X
  exact ⟨P.P, (toKaroubi C).map P.p ≫ X.decompId_p, P.isProjective,
    E.karoubi.isDeflation_comp _ _
      (E.karoubi.isDeflation_g (E.isConflationExact_toKaroubi.map_conflation P.conflation))
      (E.karoubi_isDeflation_decompId_p X)⟩

/-- With enough injectives, every object of the idempotent completion is the source of an
inflation into the image of a relative injective. -/
theorem karoubi_exists_isInflation (h : E.EnoughInjectives) (X : Karoubi C) :
    ∃ (I : C) (i : X ⟶ (toKaroubi C).obj I), E.isInjective I ∧ E.karoubi.IsInflation i := by
  obtain ⟨I⟩ := h.presentation X.X
  exact ⟨I.I, X.decompId_i ≫ (toKaroubi C).map I.i, I.isInjective,
    E.karoubi.isInflation_comp _ _ (E.karoubi_isInflation_decompId_i X)
      (E.karoubi.isInflation_f (E.isConflationExact_toKaroubi.map_conflation I.conflation))⟩

/-- **Enough projectives pass to the idempotent completion.** -/
theorem karoubi_enoughProjectives (h : E.EnoughProjectives) : E.karoubi.EnoughProjectives where
  presentation X := by
    obtain ⟨P, p, hP, hp⟩ := karoubi_exists_isDeflation h X
    obtain ⟨K, i, zero, hK⟩ := (ConflationClass.isDeflation_iff _ p).1 hp
    exact ⟨{ K := K, P := (toKaroubi C).obj P, i := i, p := p, zero := zero, conflation := hK
             isProjective := E.karoubi_isProjective_toKaroubi_obj hP }⟩

/-- **Enough injectives pass to the idempotent completion.** -/
theorem karoubi_enoughInjectives (h : E.EnoughInjectives) : E.karoubi.EnoughInjectives where
  presentation X := by
    obtain ⟨I, i, hI, hi⟩ := karoubi_exists_isInflation h X
    obtain ⟨K, p, zero, hK⟩ := (ConflationClass.isInflation_iff _ i).1 hi
    exact ⟨{ I := (toKaroubi C).obj I, K := K, i := i, p := p, zero := zero, conflation := hK
             isInjective := E.karoubi_isInjective_toKaroubi_obj hI }⟩

/-- With enough projectives, the relative projectives of the idempotent completion are the
retracts of images of relative projectives. -/
theorem karoubi_isProjective_iff (h : E.EnoughProjectives) (Q : Karoubi C) :
    E.karoubi.isProjective Q ↔
      ∃ P : C, E.isProjective P ∧ Nonempty (Retract Q ((toKaroubi C).obj P)) := by
  refine ⟨fun hQ ↦ ?_, fun ⟨P, hP, ⟨r⟩⟩ ↦
    E.karoubi.isProjective.prop_of_retract r (E.karoubi_isProjective_toKaroubi_obj hP)⟩
  obtain ⟨P, p, hP, hp⟩ := karoubi_exists_isDeflation h Q
  obtain ⟨s, hs⟩ := isProjective_iff.1 hQ hp (𝟙 Q)
  exact ⟨P, hP, ⟨⟨s, p, hs⟩⟩⟩

/-- With enough injectives, the relative injectives of the idempotent completion are the
retracts of images of relative injectives. -/
theorem karoubi_isInjective_iff (h : E.EnoughInjectives) (J : Karoubi C) :
    E.karoubi.isInjective J ↔
      ∃ I : C, E.isInjective I ∧ Nonempty (Retract J ((toKaroubi C).obj I)) := by
  refine ⟨fun hJ ↦ ?_, fun ⟨I, hI, ⟨r⟩⟩ ↦
    E.karoubi.isInjective.prop_of_retract r (E.karoubi_isInjective_toKaroubi_obj hI)⟩
  obtain ⟨I, i, hI, hi⟩ := karoubi_exists_isInflation h J
  obtain ⟨r, hr⟩ := isInjective_iff.1 hJ hi (𝟙 J)
  exact ⟨I, hI, ⟨⟨i, r, hr⟩⟩⟩

/-- **The idempotent completion of a Frobenius exact category is Frobenius.** -/
theorem IsFrobenius.karoubi (hE : E.IsFrobenius) : E.karoubi.IsFrobenius where
  enoughProjectives := karoubi_enoughProjectives hE.enoughProjectives
  enoughInjectives := karoubi_enoughInjectives hE.enoughInjectives
  projective_iff_injective X := by
    rw [karoubi_isProjective_iff hE.enoughProjectives,
      karoubi_isInjective_iff hE.enoughInjectives]
    simp only [hE.projective_iff_injective]

end ExactStructure

end TauCeti

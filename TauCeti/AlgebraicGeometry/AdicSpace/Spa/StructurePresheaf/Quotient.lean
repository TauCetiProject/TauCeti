/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.BaseChange
public import TauCeti.RingTheory.Huber.LocalizationTopology.IdealQuotient

import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Base change of completed rational localisations to a quotient ring

Let `J` be an ideal of a ring `A` with a pair of definition `P`, and write `q : A → A ⧸ J` for the
quotient map. For a presentation `p = (T, s)` of `A`, the base change

```text
A⟨T/s⟩ → (A ⧸ J)⟨q(T)/q(s)⟩
```

of `q` (`Presentation.mapHom`) is the completion of the localised quotient map, which is an open
quotient map. So the rational localisation of `A ⧸ J` is a quotient of that of `A`.

## Main results

* `TauCeti.Huber.PairOfDefinition.Presentation.mapHom_quotientMk_surjective`: the base change
  `A⟨T/s⟩ → (A ⧸ J)⟨q(T)/q(s)⟩` is surjective.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 7.38.
-/

public section

open CategoryTheory

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} (J : Ideal A)

/-- **The rational localisation of `A ⧸ J` is a quotient of that of `A`**: for a presentation
`p = (T, s)` of `A` and the presentation `q = (q(T), q(s))` of `A ⧸ J`, the base change
`A⟨p⟩ → (A ⧸ J)⟨q⟩` of the quotient map is surjective. -/
theorem Presentation.mapHom_quotientMk_surjective [DecidableEq (A ⧸ J)] (p : Presentation P)
    (q : Presentation (P.quotient J)) (hnum : q.num = p.num.image (Ideal.Quotient.mk J))
    (hden : q.den = Ideal.Quotient.mk J p.den) :
    Function.Surjective (p.mapHom (Ideal.Quotient.mk J)
      (QuotientRing.isOpenQuotientMap_mk J).continuous q hden
      fun _ ht ↦ hnum ▸ Finset.mem_image_of_mem _ ht).hom := by
  obtain ⟨qnum, qden, hq⟩ := q
  obtain rfl : qnum = p.num.image (Ideal.Quotient.mk J) := hnum
  obtain rfl : qden = Ideal.Quotient.mk J p.den := hden
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have hT' : ((p.num.image (Ideal.Quotient.mk J) : Finset (A ⧸ J)) : Set (A ⧸ J)) =
      Ideal.Quotient.mk J '' p.num := Finset.coe_image
  let _ := locUniformSpace (P.quotient J) _ _ _ hq
  have _ := isUniformAddGroup_locUniformSpace (P.quotient J) _ _ _ hq
  have _ := isTopologicalRing_locUniformSpace (P.quotient J) _ _ _ hq
  let g : TopCommRingCat.of (UniformSpace.Completion (Localization.Away p.den)) ⟶
      TopCommRingCat.of (UniformSpace.Completion
        (Localization.Away (Ideal.Quotient.mk J p.den))) :=
    ⟨completionLocQuotientHom P J p.num p.den _ hT' _ p.hasDenominatorPower,
      continuous_completionLocQuotientHom P J p.num p.den _ hT' _ p.hasDenominatorPower⟩
  have key : p.mapHom (Ideal.Quotient.mk J) (QuotientRing.isOpenQuotientMap_mk J).continuous
      ⟨p.num.image (Ideal.Quotient.mk J), Ideal.Quotient.mk J p.den, hq⟩ rfl
      (fun _ ht ↦ Finset.mem_image_of_mem _ ht) =
      InducedCategory.homMk (eqToHom (completionLocObj_obj P p.num p.den _ _) ≫ g ≫
        eqToHom (completionLocObj_obj (P.quotient J) _ _ _ hq).symm) := by
    refine p.hom_ext ?_
    rw [Presentation.toCompletionLocTopHom_comp_mapHom]
    simp only [Presentation.toCompletionLocTopHom_eq, InducedCategory.homMk_hom, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    simp only [← Category.assoc]
    refine eq_whisker ?_ _
    exact Subtype.ext
      (completionLocQuotientHom_comp_toCompletionLoc P J p.num p.den _ hT' _ _).symm
  rw [key, InducedCategory.homMk_hom]
  intro y
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (eqToHom (completionLocObj_obj (P.quotient J) _ _ _ hq).symm)).2 y
  obtain ⟨a, rfl⟩ :=
    (isOpenQuotientMap_completionLocQuotientHom P J p.num p.den _ hT' _
      p.hasDenominatorPower).surjective b
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower))).2 a
  exact ⟨c, rfl⟩

end TauCeti.Huber.PairOfDefinition

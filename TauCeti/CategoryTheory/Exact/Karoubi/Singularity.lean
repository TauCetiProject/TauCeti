/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Singularity.Stable.Functor
public import TauCeti.CategoryTheory.Exact.Karoubi.Stable

/-!
# The singularity category of the idempotent completion

Let `E` be an exact structure on `C`. The embedding `toKaroubi` of `C` into its idempotent
completion is exact and preserves projective objects, so it induces a triangle functor
`D_sg(E) ⥤ D_sg(E.karoubi)` between the singularity categories.

For a Frobenius exact structure `E`, this functor corresponds to the stable comparison
`stable(E) ⥤ stable(E.karoubi)` under the Keller–Vossieck equivalences `stable(E) ≌ D_sg(E)` and
`stable(E.karoubi) ≌ D_sg(E.karoubi)`: the square

```text
stable(E)         ⥤ D_sg(E)
   ↓                   ↓
stable(E.karoubi) ⥤ D_sg(E.karoubi)
```

commutes up to an isomorphism of triangle functors. Since the stable comparison is fully faithful
and dense up to direct summands, so is the functor on singularity categories. It is an equivalence
when `C` is idempotent complete.

## Main definitions

* `TauCeti.ExactStructure.karoubiSingularityFunctor`: the triangle functor
  `D_sg(E) ⥤ D_sg(E.karoubi)` induced by `toKaroubi`.
* `TauCeti.ExactStructure.IsFrobenius.stableToSingularityCompKaroubiSingularityFunctorIso`: the
  commutation of the square above.
* `TauCeti.ExactStructure.IsFrobenius.karoubiSingularityFunctorFullyFaithful`: the functor on
  singularity categories is fully faithful.

## Main results

* The theorem
  `TauCeti.ExactStructure.IsFrobenius.stableToSingularityCompKaroubiSingularityFunctorIso_commShift`
  states that the square commutes up to an isomorphism of triangle functors.
* `TauCeti.ExactStructure.IsFrobenius.nonempty_retract_karoubiSingularityFunctor_obj`: every
  object of `D_sg(E.karoubi)` is a direct summand of an object in the image.
* `TauCeti.ExactStructure.IsFrobenius.karoubiSingularityFunctor_isEquivalence`: the functor is an
  equivalence when `C` is idempotent complete.

## References

* Bernhard Keller, Dieter Vossieck, *Sous les catégories dérivées*, C. R. Acad. Sci. Paris
  **305** (1987), 225--228, Example 2.3.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69, Section 6.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

variable (E : ExactStructure C)

/-- The triangle functor `D_sg(E) ⥤ D_sg(E.karoubi)` induced by the embedding `toKaroubi` of `C`
into its idempotent completion. -/
noncomputable abbrev karoubiSingularityFunctor :
    E.SingularityCategory ⥤ E.karoubi.SingularityCategory :=
  E.isConflationExact_toKaroubi.mapSingularityCategory E.karoubi_isProjective_toKaroubi_obj

namespace IsFrobenius

variable {E} (hE : E.IsFrobenius)

/-- **The Keller–Vossieck equivalences intertwine the comparisons with the idempotent
completion**: `stable(E) ⥤ D_sg(E) ⥤ D_sg(E.karoubi)` is isomorphic to
`stable(E) ⥤ stable(E.karoubi) ⥤ D_sg(E.karoubi)`. -/
noncomputable def stableToSingularityCompKaroubiSingularityFunctorIso :
    E.stableToSingularity ⋙ E.karoubiSingularityFunctor ≅
      hE.karoubiStableFunctor ⋙ E.karoubi.stableToSingularity :=
  E.stableConflationExact_toKaroubi.stableToSingularityCompMapSingularityCategoryIso hE

/-- The comparison with the idempotent completion is the comparison of
`TauCeti.StableConflationExact.stableToSingularityCompMapSingularityCategoryIso` for `toKaroubi`,
whose component lemmas describe it on objects. -/
theorem stableToSingularityCompKaroubiSingularityFunctorIso_eq :
    hE.stableToSingularityCompKaroubiSingularityFunctorIso =
      E.stableConflationExact_toKaroubi.stableToSingularityCompMapSingularityCategoryIso hE :=
  (rfl)

/-- **The comparison square with the idempotent completion commutes up to an isomorphism of
triangle functors.** -/
theorem stableToSingularityCompKaroubiSingularityFunctorIso_commShift :
    letI := hE.stableHasShift
    letI := hE.karoubi.stableHasShift
    letI := hE.stableToSingularityCommShift
    letI := hE.karoubi.stableToSingularityCommShift
    letI := E.stableConflationExact_toKaroubi.stableFunctorCommShift hE hE.karoubi
    NatTrans.CommShift hE.stableToSingularityCompKaroubiSingularityFunctorIso.hom ℤ :=
  E.stableConflationExact_toKaroubi.stableToSingularityCompMapSingularityCategoryIso_commShift hE
    hE.karoubi

/-- **The comparison of singularity categories with the idempotent completion is fully
faithful**, since the stable comparison is fully faithful and the Keller–Vossieck functors are
equivalences. -/
noncomputable def karoubiSingularityFunctorFullyFaithful :
    E.karoubiSingularityFunctor.FullyFaithful :=
  haveI := hE.isEquivalence_stableToSingularity
  (E.stableToSingularity.asEquivalence.fullyFaithfulInverse.comp
    ((hE.karoubiStableFunctorFullyFaithful.comp
      hE.karoubi.fullyFaithfulStableToSingularity).ofIso
        hE.stableToSingularityCompKaroubiSingularityFunctorIso.symm)).ofIso
    (E.stableToSingularity.asEquivalence.invFunIdAssoc _)

include hE in
/-- **Every object of the singularity category of the idempotent completion is a direct summand
of an object in the image** of `D_sg(E) ⥤ D_sg(E.karoubi)`. -/
theorem nonempty_retract_karoubiSingularityFunctor_obj (Y : E.karoubi.SingularityCategory) :
    ∃ X : E.SingularityCategory, Nonempty (Retract Y (E.karoubiSingularityFunctor.obj X)) := by
  have := hE.karoubi.essSurj_stableToSingularity
  obtain ⟨Z, ⟨r⟩⟩ :=
    hE.nonempty_retract_karoubiStableFunctor_obj (E.karoubi.stableToSingularity.objPreimage Y)
  exact ⟨E.stableToSingularity.obj Z,
    ⟨(Retract.ofIso (E.karoubi.stableToSingularity.objObjPreimageIso Y).symm).trans
      ((r.map E.karoubi.stableToSingularity).trans
        (Retract.ofIso (hE.stableToSingularityCompKaroubiSingularityFunctorIso.app Z).symm))⟩⟩

include hE in
/-- **For an idempotent complete category, the comparison of singularity categories with the
idempotent completion is an equivalence.** -/
theorem karoubiSingularityFunctor_isEquivalence [IsIdempotentComplete C] :
    E.karoubiSingularityFunctor.IsEquivalence := by
  have := hE.karoubi.essSurj_stableToSingularity
  have hff := hE.karoubiSingularityFunctorFullyFaithful
  refine { faithful := hff.faithful, full := hff.full, essSurj := ⟨fun Y ↦ ?_⟩ }
  let Z := (toKaroubi C).objPreimage (E.karoubi.stableToSingularity.objPreimage Y).as
  exact ⟨E.stableToSingularity.obj (E.projectiveStableFunctor.obj Z),
    ⟨hE.stableToSingularityCompKaroubiSingularityFunctorIso.app _ ≪≫
      E.karoubi.stableToSingularity.mapIso (eqToIso
        (E.stableConflationExact_toKaroubi.stableFunctor_obj_projectiveStableFunctor_obj hE Z) ≪≫
        E.karoubi.projectiveStableFunctor.mapIso ((toKaroubi C).objObjPreimageIso _)) ≪≫
      E.karoubi.stableToSingularity.objObjPreimageIso Y⟩⟩

end IsFrobenius

end TauCeti.ExactStructure

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Karoubi.Frobenius
public import TauCeti.CategoryTheory.Exact.Stable.Functor.Triangulated

/-!
# The stable category of the idempotent completion

Let `E` be a Frobenius exact structure on `C`, so that its idempotent completion `E.karoubi` is
Frobenius (`TauCeti.ExactStructure.IsFrobenius.karoubi`). The embedding `toKaroubi` is exact and
preserves projective-injective objects, so it induces a triangle functor
`Stable E ⥤ Stable E.karoubi` between the projective stable categories. This file proves that
this functor is fully faithful and that every object of the target is a direct summand of an
object in its image.

* It is full because `toKaroubi` is full.
* It is faithful: if `toKaroubi f` factors through a projective-injective `Q` of the idempotent
  completion, then `Q` is a retract of `toKaroubi P` for a relative projective `P`, so
  `toKaroubi f` factors through `toKaroubi P`, and `f` factors through `P` because `toKaroubi` is
  fully faithful.
* Every object `X` of the idempotent completion is a retract of `toKaroubi X.X`, and so is its
  image in the stable category.

## Main results

* `TauCeti.ExactStructure.stableConflationExact_toKaroubi`: `toKaroubi` is exact and preserves
  projective-injective objects.
* `TauCeti.ExactStructure.IsFrobenius.karoubiStableFunctor_faithful` and
  `TauCeti.ExactStructure.IsFrobenius.karoubiStableFunctorFullyFaithful`: the induced functor on
  stable categories is faithful, and fully faithful.
* `TauCeti.ExactStructure.IsFrobenius.karoubiStableFunctor_isTriangulated`: it is a triangle
  functor for Happel's triangulations.
* `TauCeti.ExactStructure.IsFrobenius.nonempty_retract_karoubiStableFunctor_obj`: every object of
  the stable category of the idempotent completion is a retract of an object in the image.

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

/-- The embedding of `C` into its idempotent completion is exact and preserves
projective-injective objects. -/
theorem stableConflationExact_toKaroubi : StableConflationExact E E.karoubi (toKaroubi C) where
  isConflationExact := E.isConflationExact_toKaroubi
  map_projectiveInjective hX := by
    rw [projectiveInjective_iff] at hX ⊢
    exact ⟨E.karoubi_isProjective_toKaroubi_obj hX.1, E.karoubi_isInjective_toKaroubi_obj hX.2⟩

namespace IsFrobenius

variable {E} (hE : E.IsFrobenius)

/-- The functor `Stable E ⥤ Stable E.karoubi` induced by `toKaroubi`. -/
noncomputable abbrev karoubiStableFunctor :
    E.ProjectiveStableCategory ⥤ E.karoubi.ProjectiveStableCategory :=
  E.stableConflationExact_toKaroubi.stableFunctor hE

/-- **The stable comparison with the idempotent completion is faithful**: a morphism of `C`
whose image factors through a projective of the idempotent completion factors through a
projective of `C`. -/
instance karoubiStableFunctor_faithful : hE.karoubiStableFunctor.Faithful := by
  rw [karoubiStableFunctor, StableConflationExact.stableFunctor_eq_map,
    MorphismIdeal.faithful_map_iff, MorphismIdeal.le_def]
  intro X Y f hf
  rw [MorphismIdeal.mem_comap_hom, mem_projectiveStableIdeal_iff,
    ObjectProperty.factorsThrough_iff] at hf
  obtain ⟨Q, hQ, i, p, hip⟩ := hf
  obtain ⟨P, hP, ⟨r⟩⟩ := (karoubi_isProjective_iff hE.enoughProjectives Q).1 hQ
  rw [mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff]
  refine ⟨P, hP, (toKaroubi C).preimage (i ≫ r.i), (toKaroubi C).preimage (r.r ≫ p),
    (toKaroubi C).map_injective ?_⟩
  simp [hip]

/-- **The stable comparison with the idempotent completion is fully faithful.** It is full
because `toKaroubi` is full (`TauCeti.StableConflationExact.stableFunctor_full`). -/
noncomputable def karoubiStableFunctorFullyFaithful : hE.karoubiStableFunctor.FullyFaithful :=
  .ofFullyFaithful _

/-- **The stable comparison with the idempotent completion is a triangle functor** for Happel's
triangulations of the two stable categories. -/
theorem karoubiStableFunctor_isTriangulated :
    let := hE.stableHasShift
    let := hE.karoubi.stableHasShift
    let : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hE.stableShiftFunctor_additive
    let : ∀ n : ℤ, (shiftFunctor E.karoubi.ProjectiveStableCategory n).Additive :=
      hE.karoubi.stableShiftFunctor_additive
    let := hE.stablePretriangulated
    let := hE.karoubi.stablePretriangulated
    let := E.stableConflationExact_toKaroubi.stableFunctorCommShift hE hE.karoubi
    hE.karoubiStableFunctor.IsTriangulated :=
  E.stableConflationExact_toKaroubi.stableFunctorIsTriangulated hE hE.karoubi

/-- **Every object of the stable category of the idempotent completion is a direct summand of an
object in the image** of the stable comparison: `X` is a retract of `toKaroubi X.X`. -/
theorem nonempty_retract_karoubiStableFunctor_obj (Y : E.karoubi.ProjectiveStableCategory) :
    ∃ X : E.ProjectiveStableCategory, Nonempty (Retract Y (hE.karoubiStableFunctor.obj X)) := by
  obtain ⟨Y, rfl⟩ : ∃ Y' : Karoubi C, E.karoubi.projectiveStableFunctor.obj Y' = Y :=
    ⟨Y.as, rfl⟩
  refine ⟨E.projectiveStableFunctor.obj Y.X, ⟨?_⟩⟩
  rw [StableConflationExact.stableFunctor_obj_projectiveStableFunctor_obj]
  exact (Karoubi.retract Y).map E.karoubi.projectiveStableFunctor

end IsFrobenius

end ExactStructure

end TauCeti

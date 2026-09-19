/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.CategoryTheory.Exact.Projective

/-!
# Resolving subcategories of exact categories

Let `E` be an exact structure on an additive category `C`. An object property `P` is resolving
for `E` when it contains a zero object, is closed under binary direct sums and extensions, is
closed under kernels of deflations between `P`-objects, and every object of `C` admits a finite
`P`-resolution.

This file packages those hypotheses as `TauCeti.ExactStructure.IsResolving`. The full subcategory
on a resolving property inherits the exact structure induced from `E`; its inclusion preserves
and reflects conflations. These are the exact-category data used by the general resolution
theorem. Repleteness is derived from zero and binary-product closure rather than stored as a
redundant field.

The property of all objects is resolving. More substantially, the relatively projective objects
are resolving whenever every object admits a finite projective resolution. For the latter
example, kernel closure follows because a conflation with projective quotient splits, making its
kernel a retract of the projective middle term.

## Main definitions

* `TauCeti.ExactStructure.IsResolving`: the resolving hypotheses for an object property.
* `TauCeti.ExactStructure.resolvingSubcategory`: the induced exact structure on the full
  subcategory.

## Main results

* `TauCeti.ExactStructure.IsResolving.prop_X₁`: closure under kernels of admissible deflations.
* `TauCeti.ExactStructure.resolvingSubcategory_conflation_iff`: the conflations of the induced
  exact structure are precisely the ambient conflations.
* `TauCeti.ExactStructure.IsResolving.isConflationExact_ι` and
  `TauCeti.ExactStructure.IsResolving.reflectsConflations_ι`: the inclusion preserves and
  reflects conflations.
* `TauCeti.ExactStructure.isResolving_top`: the full category is resolving.
* `TauCeti.ExactStructure.isResolving_isProjective`: finite projective resolutions make the
  relatively projective objects a resolving subcategory.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Section 7, especially Theorem II.7.6.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure

variable (E : ExactStructure C) (P : ObjectProperty C)

/-- An object property is **resolving** for an exact structure when it is additive and extension
closed, is closed under kernels of deflations between its objects, and gives a finite resolution
of every ambient object.

The first two fields imply that `P` is closed under isomorphisms, so repleteness is exposed as a
derived theorem rather than duplicated in the structure. -/
class IsResolving : Prop extends P.ContainsZero, P.IsClosedUnderBinaryProducts where
  /-- Extensions of two resolving objects are resolving. -/
  isExtensionClosed : E.IsExtensionClosed P
  /-- The kernel term of a conflation is resolving when its middle and quotient terms are. -/
  prop_X₁ {S : ShortComplex C} (hS : E.Conflation S) (h₂ : P S.X₂) (h₃ : P S.X₃) : P S.X₁
  /-- Every object admits a finite resolution by resolving objects. -/
  finiteResolution (X : C) : E.admitsFiniteResolution P X

/-- The exact structure on the full subcategory of resolving objects induced from the ambient
exact structure. Its conflations are precisely the ambient conflations whose three terms satisfy
`P`. -/
noncomputable def resolvingSubcategory [E.IsResolving P] : ExactStructure P.FullSubcategory :=
  E.fullSubcategory P IsResolving.isExtensionClosed

/-- A short complex of a resolving subcategory is a conflation of the induced exact structure
exactly when its image in the ambient category is a conflation. -/
@[simp]
theorem resolvingSubcategory_conflation_iff [E.IsResolving P]
    (S : ShortComplex P.FullSubcategory) :
    (E.resolvingSubcategory P).Conflation S ↔ E.Conflation (S.map P.ι) :=
  E.fullSubcategory_conflation_iff IsResolving.isExtensionClosed S

/-- The inclusion of a resolving subcategory preserves conflations. -/
theorem IsResolving.isConflationExact_ι [E.IsResolving P] :
    (E.resolvingSubcategory P).IsConflationExact E P.ι where
  map_conflation hS := (E.resolvingSubcategory_conflation_iff P _).mp hS

/-- The inclusion of a resolving subcategory reflects conflations. -/
theorem IsResolving.reflectsConflations_ι [E.IsResolving P] :
    (E.resolvingSubcategory P).ReflectsConflations E P.ι where
  reflects_conflation hS := (E.resolvingSubcategory_conflation_iff P _).mpr hS

/-- The property of all objects is resolving for every exact structure. -/
instance isResolving_top : E.IsResolving (⊤ : ObjectProperty C) where
  isExtensionClosed := ⟨fun _ _ _ => trivial⟩
  prop_X₁ _ _ _ := trivial
  finiteResolution _ := (E.admitsFiniteResolution_iff _).mpr ⟨.base trivial⟩

/-- If every object admits a finite resolution by relative projectives, then the relative
projectives form a resolving subcategory.

Extension closure follows because an extension with projective quotient splits. For kernel
closure, a conflation with projective quotient identifies its middle term with the biproduct of
its kernel and quotient; hence the kernel is a retract of the projective middle term. -/
theorem isResolving_isProjective
    (hfinite : ∀ X : C, E.admitsFiniteResolution E.isProjective X) :
    E.IsResolving E.isProjective where
  isExtensionClosed := E.isExtensionClosed_of_le_isProjective le_rfl
  prop_X₁ {S} hS h₂ h₃ := by
    let s := E.splittingOfProjective hS h₃
    have hbiprod : E.isProjective (S.X₁ ⊞ S.X₃) :=
      E.isProjective.prop_of_iso s.isoBinaryBiproduct h₂
    exact ObjectProperty.IsStableUnderRetracts.of_biprod_left E.isProjective hbiprod
  finiteResolution := hfinite

end ExactStructure

end TauCeti

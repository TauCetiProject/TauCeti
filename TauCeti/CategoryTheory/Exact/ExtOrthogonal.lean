/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import TauCeti.Algebra.Homology.Ext.Basic
public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.CategoryTheory.Exact.FullSubcategory

/-!
# Ext-orthogonal subcategories of an abelian category

Let `C` be an abelian category and `P` a property of objects of `C`. The objects `X` with
`Extⁿ(X, Y) = 0` for every `Y` satisfying `P` form the `Ext`-left-orthogonal
`P.extLeftOrthogonal n`. By the long exact `Ext` sequence it is closed under extensions, so it
carries the exact structure inherited from the abelian structure of `C`.

In degree one, a projective object `Q` of `C` satisfying `P` is both projective and injective for
this exact structure: it is projective in `C`, and every inflation `X ↪ Y` in the orthogonal has
a cokernel `Z` with `Ext¹(Z, Q) = 0`, so morphisms `X ⟶ Q` extend along it. For `P` the projective
objects, this is the setting of complete resolutions by projectives.

## Main definitions

* `CategoryTheory.ObjectProperty.extLeftOrthogonal`: the objects `X` with `Extⁿ(X, Y) = 0` for
  every `Y` satisfying `P`.
* `CategoryTheory.ObjectProperty.extLeftOrthogonalExactStructure`: its exact structure, inherited
  from the abelian structure of `C`.

## Main results

* `CategoryTheory.ObjectProperty.isExtensionClosed_extLeftOrthogonal`: the orthogonal is closed
  under extensions.
* `CategoryTheory.ObjectProperty.extLeftOrthogonalExactStructure_conflation_iff`: its conflations
  are the short exact sequences of `C`.
* `CategoryTheory.ObjectProperty.isProjective_extLeftOrthogonalExactStructure` and
  `CategoryTheory.ObjectProperty.isInjective_extLeftOrthogonalExactStructure`: in degree one, a
  projective object of `C` satisfying `P` is projective and injective for this exact structure.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TauCeti ZeroObject

universe w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] (P : ObjectProperty C)

/-- The `Ext`-left-orthogonal of `P` in degree `n`: the objects `X` with `Extⁿ(X, Y) = 0` for every
`Y` satisfying `P`. -/
def extLeftOrthogonal (n : ℕ) : ObjectProperty C :=
  fun X ↦ ∀ ⦃Y : C⦄, P Y → ∀ x : Ext.{w} X Y n, x = 0

variable {P} in
/-- An object lies in the `Ext`-left-orthogonal of `P` in degree `n` when it has no `n`-th
extensions by objects satisfying `P`. -/
theorem extLeftOrthogonal_iff {n : ℕ} {X : C} :
    P.extLeftOrthogonal n X ↔ ∀ ⦃Y : C⦄, P Y → ∀ x : Ext.{w} X Y n, x = 0 :=
  Iff.rfl

/-- A projective object has no extensions of positive degree, so it lies in every positive
`Ext`-left-orthogonal. -/
theorem extLeftOrthogonal_of_projective (X : C) [Projective X] (n : ℕ) :
    P.extLeftOrthogonal (n + 1) X :=
  fun _ _ x ↦ Ext.eq_zero_of_projective x

/-- **Extension closure**: the `Ext`-left-orthogonal of `P` is closed under extensions. -/
theorem isExtensionClosed_extLeftOrthogonal (n : ℕ) :
    (ExactStructure.abelian C).IsExtensionClosed (P.extLeftOrthogonal n) where
  prop_X₂ {S} hS h₁ h₃ Y hY x := by
    obtain ⟨y, rfl⟩ := Ext.contravariant_sequence_exact₂
      ((ExactStructure.abelian_conflation S).1 hS) Y x (h₁ hY _)
    rw [h₃ hY y, Ext.comp_zero]

instance (n : ℕ) : (P.extLeftOrthogonal n).ContainsZero :=
  ⟨0, isZero_zero C, fun _ _ _ ↦ (subsingleton_ext_of_isZero_left (isZero_zero C) _ n).elim _ _⟩

instance (n : ℕ) : (P.extLeftOrthogonal n).IsClosedUnderIsomorphisms :=
  (P.isExtensionClosed_extLeftOrthogonal n).isClosedUnderIsomorphisms

instance (n : ℕ) : (P.extLeftOrthogonal n).IsClosedUnderBinaryProducts :=
  (P.isExtensionClosed_extLeftOrthogonal n).isClosedUnderBinaryProducts

/-- The exact structure on the `Ext`-left-orthogonal of `P` in degree `n`, inherited from the
abelian structure of `C`. -/
noncomputable abbrev extLeftOrthogonalExactStructure (n : ℕ) :
    ExactStructure (P.extLeftOrthogonal n).FullSubcategory :=
  (ExactStructure.abelian C).fullSubcategory _ (P.isExtensionClosed_extLeftOrthogonal n)

/-- The conflations of `P.extLeftOrthogonalExactStructure n` are the short exact sequences of
`C`. -/
theorem extLeftOrthogonalExactStructure_conflation_iff {n : ℕ}
    (S : ShortComplex (P.extLeftOrthogonal n).FullSubcategory) :
    (P.extLeftOrthogonalExactStructure n).Conflation S ↔
      (S.map (P.extLeftOrthogonal n).ι).ShortExact := by
  rw [ExactStructure.fullSubcategory_conflation_iff, ExactStructure.abelian_conflation]

/-- A projective object of `C` is projective for the exact structure on an `Ext`-left-orthogonal,
by `TauCeti.ExactStructure.isProjective_fullSubcategory_of_isProjective`. -/
theorem isProjective_extLeftOrthogonalExactStructure {n : ℕ} (Q : C) [Projective Q]
    (hQ : P.extLeftOrthogonal n Q) :
    (P.extLeftOrthogonalExactStructure n).isProjective ⟨Q, hQ⟩ :=
  ExactStructure.isProjective_fullSubcategory_of_isProjective _ _
    ((ExactStructure.abelian_isProjective_iff Q).2 inferInstance)

/-- An object of the degree-one `Ext`-left-orthogonal of `P` that satisfies `P` is injective for
its exact structure: the cokernel `Z` of an inflation satisfies `Ext¹(Z, Q) = 0`, so morphisms to
`Q` extend along the inflation. -/
theorem isInjective_extLeftOrthogonalExactStructure (Q : C) (hQ : P.extLeftOrthogonal 1 Q)
    (hPQ : P Q) : (P.extLeftOrthogonalExactStructure 1).isInjective ⟨Q, hQ⟩ := by
  refine ExactStructure.isInjective_iff.2 fun X Y i hi f ↦ ?_
  obtain ⟨Z, p, hz, hc⟩ := (ConflationClass.isInflation_iff _ i).1 hi
  obtain ⟨g, hg⟩ := ((P.extLeftOrthogonalExactStructure_conflation_iff _).1 hc)
    |>.exists_f_comp_eq_of_ext_eq_zero (Z.property hPQ) f.hom
  exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩

end CategoryTheory.ObjectProperty

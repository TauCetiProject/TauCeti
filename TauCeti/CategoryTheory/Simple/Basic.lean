/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Simple
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct

/-!
# Simple objects: non-simplicity witnesses and simple summands

Mathlib's `CategoryTheory.Simple X` says that a monomorphism into `X` is an isomorphism exactly
when it is nonzero. This file records the contrapositive used to split a non-simple object: a
nonzero object which is not simple receives a nonzero monomorphism that is not an isomorphism,
that is, it has a nonzero proper subobject. It also shows that a nonzero object decomposed as a
biproduct of simple objects receives a nonzero morphism from one of the summands.

## Main results

* `TauCeti.exists_mono_ne_zero_not_isIso_of_not_simple`: a nonzero object which is not simple is
  the target of a nonzero monomorphism which is not an isomorphism.
* `TauCeti.biproduct_ι_comp_inv_ne_zero`: the inclusion of a nonzero summand is nonzero.
* `TauCeti.exists_simple_hom_ne_zero_of_iso_biproduct`: a nonzero object that decomposes into
  simple objects receives a nonzero morphism from a simple object.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- A nonzero object which is not simple has a nonzero proper subobject: it is the target of a
nonzero monomorphism which is not an isomorphism. -/
theorem exists_mono_ne_zero_not_isIso_of_not_simple {X : C} (hX : ¬IsZero X) (hs : ¬Simple X) :
    ∃ (Y : C) (f : Y ⟶ X), Mono f ∧ f ≠ 0 ∧ ¬IsIso f := by
  by_contra! h
  -- A zero isomorphism into `X` is a zero epimorphism, which forces `X` to be a zero object.
  exact hs ⟨fun f _ => ⟨fun _ hf => hX (.of_epi_eq_zero f hf), h _ f inferInstance⟩⟩

/-- The inclusion of a nonzero summand into an object decomposed as a biproduct is nonzero. -/
theorem biproduct_ι_comp_inv_ne_zero {ι : Type*} {a : ι → C} [HasBiproduct a] {Y : C}
    (e : Y ≅ ⨁ a) (i : ι) (h : ¬IsZero (a i)) :
    biproduct.ι a i ≫ e.inv ≠ 0 := fun h' ↦
  h (.of_mono_eq_zero _ h')

/-- A nonzero object isomorphic to a biproduct of simple objects receives a nonzero morphism from
a simple object: the inclusion of a summand. -/
theorem exists_simple_hom_ne_zero_of_iso_biproduct {Y : C} (hY : ¬IsZero Y) {ι : Type*}
    {a : ι → C} [HasBiproduct a] (ha : ∀ i, Simple (a i)) (e : Y ≅ ⨁ a) :
    ∃ (S : C) (_ : Simple S) (f : S ⟶ Y), f ≠ 0 := by
  -- The decomposition of `Y` has a summand, since a biproduct over an empty type is zero.
  obtain ⟨i⟩ : Nonempty ι := by
    by_contra! h
    exact hY ((isZero_biproduct_of_isEmpty a).of_iso e)
  exact ⟨a i, ha i, _, biproduct_ι_comp_inv_ne_zero e i (Simple.not_isZero _)⟩

end TauCeti

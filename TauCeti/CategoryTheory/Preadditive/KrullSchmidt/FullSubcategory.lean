/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.KrullSchmidt.Basic
public import TauCeti.CategoryTheory.Functor.LocalEnd
public import TauCeti.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Krull-Schmidt full subcategories

Let `P` be a property of objects of a preadditive category `C` with finite biproducts, closed under
finite products (hence finite biproducts) and retracts (direct summands). If every object of `P`
decomposes in `C` as a finite biproduct of objects with local endomorphism rings, then the full
subcategory of `P` is Krull-Schmidt: the summands are retracts, so they lie in `P`, and their
endomorphism rings are the same in `P` as in `C`. In particular a full subcategory of a
Krull-Schmidt category closed under finite biproducts and summands is Krull-Schmidt.

## Main results

* `CategoryTheory.ObjectProperty.isKrullSchmidt_fullSubcategory_of_exists_iso_biproduct`: the full
  subcategory is Krull-Schmidt when its objects decompose in `C` into objects with local
  endomorphism rings.
* `CategoryTheory.ObjectProperty.isKrullSchmidt_fullSubcategory`: a full subcategory of a
  Krull-Schmidt category closed under finite biproducts and summands is Krull-Schmidt.

## References

* Henning Krause, *Krull-Schmidt categories and projective covers*, Expo. Math. 33 (2015),
  535–549, Section 4.
-/

public section

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteBiproducts C] (P : ObjectProperty C)

namespace CategoryTheory.ObjectProperty

open TauCeti

/-- **Krull-Schmidt full subcategories.** Let `P` be closed under finite products and retracts. If
every object of `P` is isomorphic in `C` to a finite biproduct of objects with local endomorphism
rings, then the full subcategory of `P` is Krull-Schmidt. -/
theorem isKrullSchmidt_fullSubcategory_of_exists_iso_biproduct [P.IsClosedUnderFiniteProducts]
    [P.IsStableUnderRetracts]
    (h : ∀ X, P X → ∃ (n : ℕ) (Q : Fin n → C), (∀ i, IsLocalRing (End (Q i))) ∧
      Nonempty (X ≅ ⨁ Q)) :
    IsKrullSchmidt P.FullSubcategory where
  exists_iso_biproduct X := by
    obtain ⟨n, Q, hQ, ⟨φ⟩⟩ := h X.obj X.property
    -- Each summand is a retract of `X`, so it lies in `P`.
    have hP (i : Fin n) : P (Q i) :=
      P.prop_of_retract ⟨biproduct.ι Q i ≫ φ.inv, φ.hom ≫ biproduct.π Q i, by simp⟩ X.property
    let Q' : Fin n → P.FullSubcategory := fun i ↦ ⟨Q i, hP i⟩
    exact ⟨n, Q', fun i ↦ (P.ι.isLocalRing_end_obj_iff (Q' i)).1 (hQ i),
      ⟨P.fullyFaithfulι.preimageIso (φ ≪≫ (P.ι.mapBiproduct Q').symm)⟩⟩

/-- **Closure of Krull-Schmidt categories.** A full subcategory of a Krull-Schmidt category, closed
under finite products (equivalently, finite biproducts) and retracts (direct summands), is
Krull-Schmidt. -/
instance isKrullSchmidt_fullSubcategory [IsKrullSchmidt C] [P.IsClosedUnderFiniteProducts]
    [P.IsStableUnderRetracts] : IsKrullSchmidt P.FullSubcategory :=
  P.isKrullSchmidt_fullSubcategory_of_exists_iso_biproduct fun X _ ↦
    IsKrullSchmidt.exists_iso_biproduct X

end CategoryTheory.ObjectProperty

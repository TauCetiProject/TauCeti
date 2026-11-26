/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Automorphisms in a category

This file contains general bookkeeping lemmas for automorphisms of objects in a category.

## Main results

* `CategoryTheory.Aut.comp_pow_hom_of_comp`: iterating an automorphism that reindexes a
  family of morphisms reindexes that family by the corresponding function iterate.
* `CategoryTheory.Iso.conjAut_symm_apply`: the inverse of conjugation by `α` is conjugation by
  `α.symm`.
* `CategoryTheory.Iso.natCard_aut_eq`: isomorphic objects have automorphism groups of the same
  cardinality.
* `CategoryTheory.Functor.FullyFaithful.natCard_aut_obj`: a fully faithful functor preserves the
  cardinality of automorphism groups.
* `TauCeti.small_iso`, `TauCeti.small_aut`: if the morphisms `X ⟶ Y` form a `w`-small type, so do
  the isomorphisms `X ≅ Y`; in particular `Aut X` is `w`-small when `X ⟶ X` is, for instance in a
  `w`-locally small category.
-/

public section

namespace CategoryTheory.Aut

universe v u

variable {C : Type u} [Category.{v} C] {X Y : C} {ι : Type*}

/-- Iterating an automorphism which reindexes a family of morphisms reindexes that family by the
corresponding function iterate. -/
theorem comp_pow_hom_of_comp (γ : Aut X) (F : ι → (Y ⟶ X)) (s : ι → ι)
    (h : ∀ i, F i ≫ γ.asIso.hom = F (s i)) (m : ℕ) (i : ι) :
    F i ≫ (γ ^ m).asIso.hom = F (s^[m] i) := by
  induction m generalizing i with
  | zero => simp
  | succ m ih => simp [pow_succ, reassoc_of% h, ih]

end CategoryTheory.Aut

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The inverse of conjugation by `α` on automorphism groups is conjugation by `α.symm`. -/
@[simp]
lemma Iso.conjAut_symm_apply {X Y : C} (α : X ≅ Y) (f : Aut Y) :
    α.conjAut.symm f = α.symm.conjAut f := by
  rw [MulEquiv.symm_apply_eq]
  ext1
  simp [Iso.conjAut_apply]

/-- Isomorphic objects have automorphism groups of the same cardinality: an isomorphism `x ≅ y`
conjugates `Aut x` onto `Aut y`. -/
theorem Iso.natCard_aut_eq {X Y : C} (e : X ≅ Y) : Nat.card (Aut X) = Nat.card (Aut Y) :=
  Nat.card_congr (Aut.autMulEquivOfIso e).toEquiv

/-- A fully faithful functor preserves the cardinality of automorphism groups. -/
theorem Functor.FullyFaithful.natCard_aut_obj {F : C ⥤ D} (hF : F.FullyFaithful) (x : C) :
    Nat.card (Aut (F.obj x)) = Nat.card (Aut x) :=
  (Nat.card_congr (hF.autMulEquivOfFullyFaithful x).toEquiv).symm

end CategoryTheory

namespace TauCeti

open CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C]

/-- If the morphisms `X ⟶ Y` form a `w`-small type, so do the isomorphisms `X ≅ Y`. -/
instance small_iso (X Y : C) [Small.{w} (X ⟶ Y)] : Small.{w} (X ≅ Y) :=
  small_of_injective (f := Iso.hom) fun _ _ h ↦ Iso.ext h

/-- If the endomorphisms of `X` form a `w`-small type, so does its automorphism group. In
particular automorphism groups in a `w`-locally small category are `w`-small. -/
instance small_aut (X : C) [Small.{w} (X ⟶ X)] : Small.{w} (Aut X) :=
  small_map Aut.isoEquiv

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Transport of commutation across `Multiplicative` and `Additive`

The type tags `Multiplicative` and `Additive` convert addition to multiplication and conversely, so
commuting pairs correspond across `Multiplicative.ofAdd`, `Multiplicative.toAdd`,
`Additive.ofMul`, and `Additive.toMul`.

## Main results

* `TauCeti.commute_ofAdd_iff`, `TauCeti.addCommute_toAdd_iff`: commutation in `Multiplicative α`
  is additive commutation in `α`.
* `TauCeti.addCommute_ofMul_iff`, `TauCeti.commute_toMul_iff`: additive commutation in `Additive α`
  is commutation in `α`.
* `AddCommute.ofAdd`, `Commute.toAdd`, `Commute.ofMul`, `AddCommute.toMul`: dot-notation
  transport of commutation witnesses across the type tags.
-/

public section

namespace TauCeti

/-- `Multiplicative.ofAdd` preserves and reflects commutation. -/
@[simp]
theorem commute_ofAdd_iff {α : Type*} [Add α] {a b : α} :
    Commute (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) ↔ AddCommute a b := by
  simp only [commute_iff_eq, addCommute_iff_eq, ← ofAdd_add, Multiplicative.ofAdd.injective.eq_iff]

/-- `Multiplicative.toAdd` preserves and reflects commutation. -/
@[simp]
theorem addCommute_toAdd_iff {α : Type*} [Add α] {a b : Multiplicative α} :
    AddCommute a.toAdd b.toAdd ↔ Commute a b := by
  rw [← commute_ofAdd_iff, ofAdd_toAdd, ofAdd_toAdd]

/-- `Additive.ofMul` preserves and reflects commutation. -/
@[simp]
theorem addCommute_ofMul_iff {α : Type*} [Mul α] {a b : α} :
    AddCommute (Additive.ofMul a) (Additive.ofMul b) ↔ Commute a b := by
  simp only [addCommute_iff_eq, commute_iff_eq, ← ofMul_mul, Additive.ofMul.injective.eq_iff]

/-- `Additive.toMul` preserves and reflects commutation. -/
@[simp]
theorem commute_toMul_iff {α : Type*} [Mul α] {a b : Additive α} :
    Commute a.toMul b.toMul ↔ AddCommute a b := by
  rw [← addCommute_ofMul_iff, ofMul_toMul, ofMul_toMul]

end TauCeti

namespace AddCommute

/-- `Multiplicative.ofAdd` sends additively commuting elements to commuting elements. -/
theorem ofAdd {α : Type*} [Add α] {a b : α} (h : AddCommute a b) :
    Commute (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) :=
  TauCeti.commute_ofAdd_iff.2 h

/-- `Additive.toMul` sends additively commuting elements to commuting elements. -/
theorem toMul {α : Type*} [Mul α] {a b : Additive α} (h : AddCommute a b) :
    Commute a.toMul b.toMul :=
  TauCeti.commute_toMul_iff.2 h

end AddCommute

namespace Commute

/-- `Additive.ofMul` sends commuting elements to additively commuting elements. -/
theorem ofMul {α : Type*} [Mul α] {a b : α} (h : Commute a b) :
    AddCommute (Additive.ofMul a) (Additive.ofMul b) :=
  TauCeti.addCommute_ofMul_iff.2 h

/-- `Multiplicative.toAdd` sends commuting elements to additively commuting elements. -/
theorem toAdd {α : Type*} [Add α] {a b : Multiplicative α} (h : Commute a b) :
    AddCommute a.toAdd b.toAdd :=
  TauCeti.addCommute_toAdd_iff.2 h

end Commute

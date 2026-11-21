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

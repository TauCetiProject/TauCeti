/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs

/-!
# Simplification lemmas for `MulEquiv.cast` and `AddEquiv.cast`

This file records reflexivity, symmetry, transitivity, and index-composition rules for
`MulEquiv.cast` and `AddEquiv.cast`.
-/

public section

namespace MulEquiv

/-- Reflexive cast of a family of types with multiplication is the identity equivalence. -/
@[to_additive (attr := simp)
  /-- Reflexive cast of a family of types with addition is the identity equivalence. -/]
theorem cast_refl {ι : Type*} {M : ι → Type*} [∀ i, Mul (M i)] {i : ι} (h : i = i) :
    MulEquiv.cast (M := M) h = MulEquiv.refl (M i) :=
  rfl

/-- The inverse of `MulEquiv.cast` is the cast along the symmetric equality. -/
@[to_additive (attr := simp)
  /-- The inverse of `AddEquiv.cast` is the cast along the symmetric equality. -/]
theorem cast_symm {ι : Type*} {M : ι → Type*} [∀ i, Mul (M i)] {i j : ι} (h : i = j) :
    (MulEquiv.cast (M := M) h).symm = MulEquiv.cast (M := M) h.symm := by
  subst h
  rfl

/-- Composing two `MulEquiv.cast` equivalences gives the cast along the transitive equality. -/
@[to_additive (attr := simp)
  /-- Composing two `AddEquiv.cast` equivalences gives the cast along the transitive
  equality. -/]
theorem cast_trans {ι : Type*} {M : ι → Type*} [∀ i, Mul (M i)] {i j l : ι}
    (hij : i = j) (hjl : j = l) :
    (MulEquiv.cast (M := M) hij).trans (MulEquiv.cast (M := M) hjl) =
      MulEquiv.cast (M := M) (hij.trans hjl) := by
  subst hij hjl
  rfl

/-- Casting along a precomposed family agrees with casting along `congrArg`. -/
@[to_additive /-- Casting along a precomposed family agrees with casting along `congrArg`. -/]
theorem cast_comp {ι κ : Type*} {M : κ → Type*} [∀ k, Mul (M k)] (f : ι → κ) {i j : ι}
    (h : i = j) :
    MulEquiv.cast (M := fun x ↦ M (f x)) h = MulEquiv.cast (M := M) (congrArg f h) := by
  subst h
  rfl

end MulEquiv

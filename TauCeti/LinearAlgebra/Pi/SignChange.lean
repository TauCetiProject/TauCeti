/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.LinearAlgebra.Pi

/-!
# Coordinate sign changes and functions changing sign on a two-element orbit

`TauCeti.piSignChange` negates the coordinates selected by an arbitrary decidable predicate
as an involutive linear equivalence, over any semiring acting on an additive commutative group.

Let `σ` be a map without fixed points on a type `α` whose elements are `a` and `σ a`. A function
`α → R` that changes sign under `σ` (`g (σ a') = -g a'`) is determined by its value at `a`, and
that value can be any element of `R`. So evaluation at `a` is a bijection from the functions
changing sign under `σ` onto `R` (`TauCeti.eval_bijective_of_mem_iff_apply_eq_neg`), stated for
any submodule of `α → R` with exactly these functions as elements.

This is the common rank-one argument behind the sign module of a fibre of a double cover
(`TauCeti.signFiberEquiv`, with `σ` the deck involution) and the orientation line of a vector
space (`Orientation.orientationLineEquiv`, with `σ` the negation of orientations).
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R] {α : Type*}

/-- Let `σ` have no fixed points on a type whose elements are `a` and `σ a`. On a submodule of the
functions `α → R` whose elements are exactly the functions changing sign under `σ`, evaluation at
`a` is bijective. -/
theorem eval_bijective_of_mem_iff_apply_eq_neg {σ : α → α} (hfix : ∀ a', σ a' ≠ a') {a : α}
    (hcases : ∀ a', a' = a ∨ a' = σ a) {S : Submodule R (α → R)}
    (hS : ∀ g, g ∈ S ↔ ∀ a', g (σ a') = -g a') :
    Function.Bijective fun g : S ↦ (g : α → R) a := by
  classical
  have hσσ : σ (σ a) = a := (hcases _).resolve_right (hfix _)
  refine ⟨fun g g' hg ↦ Subtype.ext (funext fun a' ↦ ?_), fun r ↦ ?_⟩
  · rcases hcases a' with rfl | rfl
    · exact hg
    · rw [(hS g).1 g.property, (hS g').1 g'.property]
      exact congrArg Neg.neg hg
  · refine ⟨⟨fun a' ↦ if a' = a then r else -r, (hS _).2 fun a' ↦ ?_⟩, by simp⟩
    rcases hcases a' with rfl | rfl
    · simp [hfix]
    · simp [hσσ, hfix]

section CoordinateSignChange

/-- Negate the selected coordinates as an involutive linear equivalence. -/
def piSignChange (R : Type*) [Semiring R] {ι A : Type*} [AddCommGroup A] [Module R A]
    (p : ι → Prop) [DecidablePred p] : (ι → A) ≃ₗ[R] (ι → A) :=
  LinearEquiv.piCongrRight fun e ↦ if p e then LinearEquiv.neg R else LinearEquiv.refl R A

/-- Sign change negates exactly the selected coordinates. -/
@[simp]
theorem piSignChange_apply (R : Type*) [Semiring R] {ι A : Type*}
    [AddCommGroup A] [Module R A] (p : ι → Prop) [DecidablePred p]
    (c : ι → A) (e : ι) :
    piSignChange R p c e = if p e then -c e else c e := by
  simp only [piSignChange, LinearEquiv.piCongrRight_apply]
  split_ifs <;> simp only [LinearEquiv.neg_apply, LinearEquiv.refl_apply]

/-- Sign change is its own inverse linear equivalence. -/
@[simp]
theorem piSignChange_symm (R : Type*) [Semiring R] {ι A : Type*}
    [AddCommGroup A] [Module R A] (p : ι → Prop) [DecidablePred p] :
    (piSignChange R (A := A) p).symm = piSignChange R p := by
  simp only [piSignChange, LinearEquiv.piCongrRight_symm]
  congr 1
  funext e
  split_ifs <;> simp

/-- Applying the same selected sign change twice restores the function. -/
@[simp]
theorem piSignChange_piSignChange (R : Type*) [Semiring R] {ι A : Type*}
    [AddCommGroup A] [Module R A] (p : ι → Prop) [DecidablePred p]
    (c : ι → A) : piSignChange R p (piSignChange R p c) = c := by
  simpa only [piSignChange_symm] using (piSignChange R p).symm_apply_apply c

end CoordinateSignChange

end TauCeti

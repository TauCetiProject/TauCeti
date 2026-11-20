/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic

/-!
# Periodicity under integer combinations of two periods, in a product coordinate, under reflection,
and of single-index families

A function periodic under `c₁` and `c₂` is periodic under every integer combination
`m c₁ + n c₂` (`Function.Periodic.int_mul_add_int_mul`). For the periods `1` and `i` of a
function on `ℂ` these are the vectors of the lattice `ℤ + ℤ i`; for the periods `τ` and `1` of a
function on `ℂ` they are the vectors of the lattice `ℤ τ + ℤ`.

A function on a product is periodic under `(0, c)` exactly when it is `c`-periodic in its second
coordinate (`Function.periodic_zero_prodMk_iff`); for instance a map on the cylinder `ℝ × ℝ` of
period one in `t`.

A function with period `c` composed with the reflection `x ↦ -x` still has period `c`
(`Function.Periodic.comp_neg`).

The family which is a `c`-periodic function `g` at one index and zero at the others is
`c`-periodic at every index (`Function.Periodic.piSingle_apply`).
-/

public section

namespace Function

variable {α β : Type*} [NonAssocRing α] {f : α → β} {c₁ c₂ : α}

/-- A function periodic under `c₁` and `c₂` is periodic under every integer combination
`m c₁ + n c₂`. -/
theorem Periodic.int_mul_add_int_mul (h₁ : Periodic f c₁) (h₂ : Periodic f c₂) (m n : ℤ) :
    Periodic f (m * c₁ + n * c₂) :=
  (h₁.int_mul m).add_period (h₂.int_mul n)

/-- A function on a product is periodic under `(0, c)` if and only if it is `c`-periodic in its
second coordinate. -/
theorem periodic_zero_prodMk_iff {γ δ : Type*} [AddZeroClass γ] [Add δ] {g : γ × δ → β}
    {c : δ} : Periodic g (0, c) ↔ ∀ a, Periodic (fun b ↦ g (a, b)) c :=
  ⟨fun h a b ↦ by simpa using h (a, b), fun h ⟨a, b⟩ ↦ by simpa using h a b⟩

/-- A function with period `c`, composed with the reflection `x ↦ -x`, has period `c`. -/
theorem Periodic.comp_neg {γ : Type*} [AddCommGroup γ] {f : γ → β} {c : γ} (h : Periodic f c) :
    Periodic (fun x ↦ f (-x)) c := by
  simpa only [zero_sub] using h.const_sub 0

/-- The family which is a `c`-periodic function `g` at the index `i` and zero at the other indices
is `c`-periodic at every index. -/
theorem Periodic.piSingle_apply {ι γ δ : Type*} [DecidableEq ι] [Add γ] [Zero δ] {g : γ → δ} {c : γ}
    (hg : Periodic g c) (i j : ι) : Periodic ((Pi.single i g : ι → γ → δ) j) c := by
  rcases eq_or_ne j i with rfl | h
  · simpa using hg
  · rw [Pi.single_eq_of_ne h]
    exact fun _ ↦ rfl

/-- The lift of a periodic function, composed with the quotient map, is the function itself. -/
@[simp]
theorem Periodic.lift_comp_coe {γ : Type*} [AddGroup γ] {f : γ → β} {c : γ} (h : Periodic f c) :
    h.lift ∘ ((↑) : γ → γ ⧸ AddSubgroup.zmultiples c) = f :=
  funext h.lift_coe

end Function

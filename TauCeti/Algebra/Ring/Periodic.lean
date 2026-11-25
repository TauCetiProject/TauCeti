/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Periodic

/-!
# Periodicity under integer combinations of two periods, in a product coordinate, under reflection,
of single-index families and of subgroup indicators

A function periodic under `c₁` and `c₂` is periodic under every integer combination
`m c₁ + n c₂` (`Function.Periodic.int_mul_add_int_mul`). For the periods `1` and `i` of a
function on `ℂ` these are the vectors of the lattice `ℤ + ℤ i`; for the periods `τ` and `1` of a
function on `ℂ` they are the vectors of the lattice `ℤ τ + ℤ`.

A function on a product is periodic under `(0, c)` exactly when it is `c`-periodic in its second
coordinate (`Function.periodic_zero_prodMk_iff`); for instance a map on the cylinder `ℝ × ℝ` of
period one in `t`. A function that agrees with `f ∘ φ` along a line `{a} × γ` has every period
that `φ` has along that line (`Function.periodic_of_forall_comp_eq`).

A function with period `c` composed with the reflection `x ↦ -x` still has period `c`
(`Function.Periodic.comp_neg`).

The family which is a `c`-periodic function `g` at one index and zero at the others is
`c`-periodic at every index (`Function.Periodic.piSingle_apply`).

Restricting a `u`-periodic function to an additive subgroup containing `u` keeps the period `u`
(`Function.Periodic.indicator_addSubgroup`); for instance the indicator of a lattice is periodic
along the lattice.
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

/-- A function `g` that agrees with `f ∘ φ` along a line `{a} × γ` has period `c` when `φ` has
period `c` along that line. For instance, an end structure `J_e(t)` agreeing with `J` in an end
chart of a cylindrical end has period one. -/
theorem periodic_of_forall_comp_eq {γ δ ε : Type*} [Add γ] {φ : δ × γ → ε} {f : ε → β}
    {g : γ → β} {a : δ} {c : γ} (hφ : ∀ b, φ (a, b + c) = φ (a, b))
    (hfg : ∀ b, f (φ (a, b)) = g b) : Periodic g c := fun b ↦ by
  rw [← hfg, ← hfg, hφ]

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

/-- Restricting a `u`-periodic function to an additive subgroup `U` containing `u` keeps the
period `u`: the indicator of `U` with values `f` is `u`-periodic. -/
theorem Periodic.indicator_addSubgroup {γ : Type*} [AddGroup γ] [Zero β] {f : γ → β} {u : γ}
    (hf : Periodic f u) {U : AddSubgroup γ} (hu : u ∈ U) :
    Periodic ((U : Set γ).indicator f) u := fun v ↦ by
  by_cases hv : v ∈ U
  · rw [Set.indicator_of_mem (U.add_mem hv hu), Set.indicator_of_mem hv, hf v]
  · rw [Set.indicator_of_notMem ((U.add_mem_cancel_right hu).not.mpr hv),
      Set.indicator_of_notMem hv]

end Function

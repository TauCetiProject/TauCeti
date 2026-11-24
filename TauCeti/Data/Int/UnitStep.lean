/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Init
public import Mathlib.Logic.Function.Defs
import Mathlib.Algebra.AddConstMap.Basic
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Ring

/-!
# Injective maps of `ℤ` with unit steps

A map `σ : ℤ → ℤ` that sends consecutive integers to adjacent ones, `σ (m + 1) = σ m ± 1`, and is
injective never turns back, so its increments are constant: it is a translation `m ↦ σ 0 + m` or a
reflection `m ↦ σ 0 - m`. In particular such a map that commutes with a nonzero translation is a
translation.

## Main results

* `Int.forall_eq_add_or_forall_eq_sub_of_injective_of_step`: an injective map `σ : ℤ → ℤ` with
  unit steps is `m ↦ σ 0 + m` or `m ↦ σ 0 - m`.
-/

public section

open Function

namespace Int

/-- An injective map `σ : ℤ → ℤ` that sends consecutive integers to adjacent ones is a translation
`m ↦ σ 0 + m` or a reflection `m ↦ σ 0 - m`. -/
theorem forall_eq_add_or_forall_eq_sub_of_injective_of_step {σ : ℤ → ℤ} (hinj : Injective σ)
    (hstep : ∀ m, σ (m + 1) = σ m + 1 ∨ σ (m + 1) = σ m - 1) :
    (∀ m, σ m = σ 0 + m) ∨ ∀ m, σ m = σ 0 - m := by
  -- An injective sequence of steps `±1` never turns back, so its increments are constant.
  have hper : Periodic (fun m => σ (m + 1) - σ m) 1 := fun m => by
    have hm : m + 1 + 1 ≠ m := by omega
    have := hinj.ne hm
    rcases hstep m with h | h <;> rcases hstep (m + 1) with h' | h' <;> dsimp only <;> omega
  have hd (m : ℤ) : σ (m + 1) = σ m + (σ 1 - σ 0) := by
    have := hper.int_mul_eq m
    simp only [Int.cast_id, mul_one, zero_add] at this
    omega
  have haff (m : ℤ) : σ m = σ 0 + m * (σ 1 - σ 0) := by
    simpa using AddConstMapClass.map_add_int' (⟨σ, hd⟩ : AddConstMap ℤ ℤ 1 (σ 1 - σ 0)) 0 m
  rcases hstep 0 with h | h <;> rw [zero_add] at h
  · exact Or.inl fun m => by rw [haff, h]; ring
  · exact Or.inr fun m => by rw [haff, h]; ring

end Int

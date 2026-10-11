/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Shared Alexander clasp algebra

The slot assignment `TauCeti.claspValue` and cancellation lemma `TauCeti.clasp_relations`
supply the same local algebra for the two-arc and two-circle second Reidemeister moves,
over any commutative ring and module, independently of PD codes or Laurent coefficients.
The hypotheses of `clasp_relations` say that each second-crossing weight inverts the
first-crossing weight at the slot joined to it by a clasp arc, and that the same strand
is over at both crossings (with weight `1`).
-/

public section

namespace TauCeti

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The values at the slots of a clasp. The scalars `w₀`, `w₁` are the first crossing's
weights at slots `0`, `1`, whose values are `x`, `y`. The index `i` selects one of the two
crossings and `s` one of its four slots. The first crossing's relations determine slots
`2`, `3`; slots `0`, `1` of the second crossing join slots `3`, `2` of the first. -/
def claspValue (w₀ w₁ : R) (x y : M) (i : Fin 2) (s : Fin 4) : M :=
  let u := w₀ • x + (1 - w₀) • y
  let v := w₁ • y + (1 - w₁) • u
  (if i = 0 then ![x, y, u, v] else ![v, u, y, x]) s

variable (w₀ w₁ : R) (x y : M)

/-- Slot `0` of the first crossing carries the first incoming value. -/
@[simp]
theorem claspValue_zero_zero : claspValue w₀ w₁ x y 0 0 = x := by rfl

/-- Slot `1` of the first crossing carries the second incoming value. -/
@[simp]
theorem claspValue_zero_one : claspValue w₀ w₁ x y 0 1 = y := by rfl

/-- The first crossing's slot `0` relation prescribes slot `2`. -/
@[simp]
theorem claspValue_zero_two :
    claspValue w₀ w₁ x y 0 2 = w₀ • x + (1 - w₀) • y := by rfl

/-- The first crossing's slot `1` relation prescribes slot `3`. -/
@[simp]
theorem claspValue_zero_three :
    claspValue w₀ w₁ x y 0 3 = w₁ • y + (1 - w₁) • claspValue w₀ w₁ x y 0 2 := by rfl

/-- Slot `0` of the second crossing joins slot `3` of the first. -/
@[simp]
theorem claspValue_one_zero :
    claspValue w₀ w₁ x y 1 0 = claspValue w₀ w₁ x y 0 3 := by rfl

/-- Slot `1` of the second crossing joins slot `2` of the first. -/
@[simp]
theorem claspValue_one_one :
    claspValue w₀ w₁ x y 1 1 = claspValue w₀ w₁ x y 0 2 := by rfl

/-- Slot `2` of the second crossing joins slot `1` of the first. -/
@[simp]
theorem claspValue_one_two : claspValue w₀ w₁ x y 1 2 = y := by rfl

/-- Slot `3` of the second crossing joins slot `0` of the first. -/
@[simp]
theorem claspValue_one_three : claspValue w₀ w₁ x y 1 3 = x := by rfl

/-- Reversing both indices is the half-edge pairing of the clasp, so it preserves values. -/
theorem claspValue_rev_rev (i : Fin 2) (s : Fin 4) :
    claspValue w₀ w₁ x y (Fin.rev i) (Fin.rev s) = claspValue w₀ w₁ x y i s := by
  fin_cases i <;> fin_cases s <;> simp [Fin.rev]

/-- If the first crossing prescribes `x₂` and `x₃`, the second returns `x₁` and `x₀`:
`c₀` inverts `a₁` and `c₁` inverts `a₀`, the first-crossing weights at the slots joined
by clasp arcs, and the same strand has weight `1` at both crossings. -/
theorem clasp_relations {a₀ a₁ c₀ c₁ : R} {x₀ x₁ x₂ x₃ : M}
    (h₀ : c₀ * a₁ = 1) (h₁ : c₁ * a₀ = 1)
    (hover : (a₀ = 1 ∧ c₁ = 1) ∨ (a₁ = 1 ∧ c₀ = 1))
    (hx₂ : x₂ = a₀ • x₀ + (1 - a₀) • x₁)
    (hx₃ : x₃ = a₁ • x₁ + (1 - a₁) • x₂) :
    c₀ • x₃ + (1 - c₀) • x₂ = x₁ ∧
      c₁ • x₂ + (1 - c₁) • x₁ = x₀ := by
  rcases hover with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · rw [hA, one_smul, sub_self, zero_smul, add_zero] at hx₂
    rw [hx₃, hx₂, hB]
    constructor
    · linear_combination (norm := module) h₀ • x₁ - h₀ • x₀
    · simp
  · rw [hA, one_smul, sub_self, zero_smul, add_zero] at hx₃
    rw [hx₃, hx₂, hB]
    constructor
    · simp
    · linear_combination (norm := module) h₁ • x₀ - h₁ • x₁

/-- The second crossing's relations hold for the prescribed clasp values when its weights
invert the weights at the first-crossing slots joined by arcs and the same strand is over. -/
theorem claspValue_relations {a₀ a₁ c₀ c₁ : R}
    (h₀ : c₀ * a₁ = 1) (h₁ : c₁ * a₀ = 1)
    (hover : (a₀ = 1 ∧ c₁ = 1) ∨ (a₁ = 1 ∧ c₀ = 1)) (x y : M) :
    claspValue a₀ a₁ x y 1 2 =
        c₀ • claspValue a₀ a₁ x y 1 0 + (1 - c₀) • claspValue a₀ a₁ x y 1 1 ∧
      claspValue a₀ a₁ x y 1 3 =
        c₁ • claspValue a₀ a₁ x y 1 1 + (1 - c₁) • claspValue a₀ a₁ x y 1 2 := by
  obtain ⟨h₂, h₃⟩ := clasp_relations h₀ h₁ hover (x₀ := x) (x₁ := y)
    (x₂ := claspValue a₀ a₁ x y 0 2) (x₃ := claspValue a₀ a₁ x y 0 3)
    (by simp) (by simp)
  exact ⟨by simpa only [claspValue_one_two, claspValue_one_zero, claspValue_one_one] using h₂.symm,
    by simpa only [claspValue_one_three, claspValue_one_one, claspValue_one_two] using h₃.symm⟩

end TauCeti

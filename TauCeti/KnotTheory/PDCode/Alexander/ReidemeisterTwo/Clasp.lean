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

The slot assignment `TauCeti.OrientedPDCode.claspValue` and cancellation lemma
`TauCeti.OrientedPDCode.clasp_relations` supply the same local algebra for the two-arc and
two-circle second Reidemeister moves. The weights are parameters: opposite strands have
inverse weights, and the same strand is over at both crossings.
-/

public section

namespace TauCeti.OrientedPDCode

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The clasp slots prescribed by the first crossing and the arcs between the crossings. -/
def claspValue (w : Fin 4 → R) (x y : M) (i : Fin 2) (s : Fin 4) : M :=
  let u := w 0 • x + (1 - w 0) • y
  let v := w 1 • y + (1 - w 1) • u
  (if i = 0 then ![x, y, u, v] else ![v, u, y, x]) s

/-- The slot assignment of the clasp in terms of its incoming values and first-crossing weights. -/
theorem claspValue_def (w : Fin 4 → R) (x y : M) (i : Fin 2) :
    claspValue w x y i =
      let u := w 0 • x + (1 - w 0) • y
      let v := w 1 • y + (1 - w 1) • u
      if i = 0 then ![x, y, u, v] else ![v, u, y, x] := (rfl)

/-- Reversing both crossing and slot follows an arc of the clasp. -/
theorem claspValue_arc (w : Fin 4 → R) (x y : M) (i : Fin 2) (s : Fin 4) :
    claspValue w x y (Fin.rev i) (Fin.rev s) = claspValue w x y i s := by
  fin_cases i <;> fin_cases s <;> simp [claspValue_def, Fin.rev]

/-- If the first crossing prescribes `x₂` and `x₃`, the second returns `x₁` and `x₀`:
its opposite-strand weights are inverse and the same strand is over at both crossings. -/
theorem clasp_relations {wA wB : Fin 4 → R} {x₀ x₁ x₂ x₃ : M}
    (h₀ : wB 0 * wA 1 = 1) (h₁ : wB 1 * wA 0 = 1)
    (hover : (wA 0 = 1 ∧ wB 1 = 1) ∨ (wA 1 = 1 ∧ wB 0 = 1))
    (hx₂ : x₂ = wA 0 • x₀ + (1 - wA 0) • x₁)
    (hx₃ : x₃ = wA 1 • x₁ + (1 - wA 1) • x₂) :
    wB 0 • x₃ + (1 - wB 0) • x₂ = x₁ ∧
      wB 1 • x₂ + (1 - wB 1) • x₁ = x₀ := by
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

end TauCeti.OrientedPDCode

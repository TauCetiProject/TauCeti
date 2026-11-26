/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.SymbolicDynamics.MulSubshift

/-!
# Check: the action on configurations of `ℤ` and Mathlib's shift

For `ℤ` acting on itself by translation (written multiplicatively, `Multiplicative ℤ`), the action
`(g • ω)(h) = ω(g⁻¹ h)` of the generator `1` moves the indicator of `{0}` to the indicator of
`{1}`, which is Mathlib's shift by `−1` of it, while Mathlib's shift by `1` gives the indicator of
`{−1}`.
-/

open SymbolicDynamics.FullShift

public section

namespace TauCeti.Examples.MulSubshift

/-- The indicator of `{0}` in the full shift of `ℤ` with alphabet `Bool`. -/
abbrev δ₀ : (⊤ : Subshift (Multiplicative ℤ) (Multiplicative ℤ) Bool) :=
  ⟨fun h => decide (h = Multiplicative.ofAdd 0), Subshift.mem_top _⟩

/-- The action of `1` moves the indicator of `{0}` to the indicator of `{1}`. -/
example : ((Multiplicative.ofAdd (1 : ℤ) • δ₀ : (⊤ : Subshift _ _ Bool)) :
    Multiplicative ℤ → Bool) = fun h => decide (h = Multiplicative.ofAdd 1) := by
  funext h
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, Multiplicative.ofAdd n = h := ⟨h.toAdd, rfl⟩
  simp only [Subshift.coe_smul, smul_eq_mul, ← ofAdd_neg, ← ofAdd_add,
    Multiplicative.ofAdd.injective.eq_iff, decide_eq_decide]
  omega

/-- The action of `1` is Mathlib's shift by `−1`. -/
example : ((Multiplicative.ofAdd (1 : ℤ) • δ₀ : (⊤ : Subshift _ _ Bool)) :
    Multiplicative ℤ → Bool) =
      mulShift (Multiplicative.ofAdd (-1)) (δ₀ : Multiplicative ℤ → Bool) :=
  Subshift.coe_smul_eq_mulShift _ _

/-- Mathlib's shift by `1` moves the indicator of `{0}` to the indicator of `{−1}`. -/
example : mulShift (Multiplicative.ofAdd 1) (δ₀ : Multiplicative ℤ → Bool) =
    fun h => decide (h = Multiplicative.ofAdd (-1)) := by
  funext h
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, Multiplicative.ofAdd n = h := ⟨h.toAdd, rfl⟩
  simp only [mulShift_apply, ← ofAdd_add, Multiplicative.ofAdd.injective.eq_iff,
    decide_eq_decide]
  omega

end TauCeti.Examples.MulSubshift

end

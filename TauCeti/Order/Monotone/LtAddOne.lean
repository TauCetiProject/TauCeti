/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Order.Monotone.Basic

/-!
# Values of a sequence rising strictly on a window

If a sequence in a preorder satisfies `hgt k < hgt (k + 1)` for `k₀ ≤ k < j₁`, starts at `z` at
`k₀` and stays below `u` at `j₁`, its values `hgt k` for `k₀ < k ≤ j₁` lie strictly between `z` and
`u` (`TauCeti.lt_and_lt_of_lt_add_one`).
-/

public section

namespace TauCeti

/-- If a sequence in a preorder satisfies `hgt k < hgt (k + 1)` for `k₀ ≤ k < j₁`, starts at `z`
at `k₀` and stays below `u` at `j₁`, then its values `hgt k` for `k₀ < k ≤ j₁` lie strictly
between `z` and `u`. -/
theorem lt_and_lt_of_lt_add_one {β : Type*} [Preorder β] {hgt : ℕ → β} {k₀ j₁ : ℕ} {z u : β}
    (hrise : ∀ k, k₀ ≤ k → k < j₁ → hgt k < hgt (k + 1)) (hk₀ : hgt k₀ = z)
    (hj₁ : hgt j₁ < u) {k : ℕ} (hk₀k : k₀ < k) (hkj : k ≤ j₁) : z < hgt k ∧ hgt k < u := by
  have hsm : StrictMonoOn hgt (Set.Icc k₀ j₁) :=
    strictMonoOn_of_lt_add_one Set.ordConnected_Icc fun m _ hm hm' ↦
      hrise m hm.1 (by simp only [Set.mem_Icc] at hm'; omega)
  refine ⟨?_, ?_⟩
  · rw [← hk₀]
    exact hsm ⟨le_rfl, by omega⟩ ⟨hk₀k.le, hkj⟩ hk₀k
  · exact (hsm.monotoneOn ⟨hk₀k.le, hkj⟩ ⟨by omega, le_rfl⟩ hkj).trans_lt hj₁

end TauCeti

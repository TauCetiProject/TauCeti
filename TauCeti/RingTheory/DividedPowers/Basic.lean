/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.Basic

/-!
# Complements on divided powers

This file provides general infrastructure for Mathlib's `DividedPowers` structure.

## Main results

* `DividedPowers.dpow_eqRec`: transporting a `DividedPowers` structure along an equality of ideals
  preserves `dpow`.
* `DividedPowers.coincide_on_inf`: if `I ⊓ J = I * J`, any divided power structures on `I` and on
  `J` agree on `I ⊓ J`.
* `DividedPowers.coincide_on_inf_bot_right`, `DividedPowers.coincide_on_inf_bot_left`: agreement of
  any divided power structure with `dividedPowersBot A` on `I ⊓ ⊥` and `⊥ ⊓ J`.
-/

public section

namespace DividedPowers

/-- Transporting a `DividedPowers` structure along an equality of ideals preserves `dpow`. -/
@[simp]
theorem dpow_eqRec {A : Type*} [CommSemiring A] {I₁ I₂ : Ideal A} (e : I₁ = I₂)
    (h₁ : DividedPowers I₁) (n : ℕ) (z : A) :
    (e ▸ h₁).dpow n z = h₁.dpow n z := by
  cases e
  rfl

section

variable {A : Type*} [CommSemiring A] {I J : Ideal A} (γ : DividedPowers I) (ε : DividedPowers J)

/-- If `I ⊓ J = I * J`, any divided power structures on `I` and on `J` agree on `I ⊓ J`. -/
theorem coincide_on_inf (hIJ : I ⊓ J = I * J) {n : ℕ} {w : A} (hw : w ∈ I ⊓ J) :
    γ.dpow n w = ε.dpow n w :=
  γ.coincide_on_smul ε (by rwa [Ideal.smul_eq_mul, ← hIJ])

/-- Any divided power structure on `I` agrees with `dividedPowersBot A` on `I ⊓ ⊥`. -/
theorem coincide_on_inf_bot_right :
    ∀ n, ∀ w ∈ I ⊓ ⊥, γ.dpow n w = (dividedPowersBot A).dpow n w :=
  fun _ _ ↦ coincide_on_inf γ (dividedPowersBot A) ((inf_bot_eq I).trans (Ideal.mul_bot I).symm)

/-- `dividedPowersBot A` agrees with any divided power structure on `J` on `⊥ ⊓ J`. -/
theorem coincide_on_inf_bot_left :
    ∀ n, ∀ w ∈ ⊥ ⊓ J, (dividedPowersBot A).dpow n w = ε.dpow n w :=
  fun n w hw ↦ (coincide_on_inf_bot_right ε n w ⟨hw.2, hw.1⟩).symm

end

end DividedPowers

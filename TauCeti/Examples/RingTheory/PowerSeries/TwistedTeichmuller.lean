/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.RingTheory.PowerSeries.TwistedTeichmuller
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.LinearCombination

/-!
# Checks for twisted Teichmüller lifts in equal characteristic

Over `𝔽₂` with `Q = X ^ 2 + π X`, the `Q`-Teichmüller lift of `1` is `1 + π`, a fixed point of
`Q`, rather than the constant lift `1`. The same lift shows `[1 * 1]_Q ≠ [1]_Q * [1]_Q`, so the
lift is not multiplicative, while evaluation at this `Q` is additive and so is the lift.

Over `𝔽₃` with `Q = X ^ 3 + π X`, the second iterate `Q(Q(1)) = 1 + π + π ^ 2 + π ^ 3` determines
`[1]_Q ≡ 1 + π + π ^ 2` modulo `π ^ 3`; the first iterate `1 + π` is not enough.
-/

public section

namespace TauCeti.Examples

open PowerSeries

section Two

local instance : CharP (ZMod 2)⟦X⟧ 2 := charP_of_injective_ringHom C_injective 2

/-- The polynomial `Q = X ^ 2 + π X` over `𝔽₂⟦π⟧`. -/
local notation "Q₂" =>
  (Polynomial.X ^ 2 + Polynomial.C (X : (ZMod 2)⟦X⟧) * Polynomial.X : Polynomial (ZMod 2)⟦X⟧)

private theorem map_constantCoeff_Q₂ : Polynomial.map constantCoeff Q₂ = Polynomial.X ^ 2 ^ 1 := by
  simp

/-- For `Q = X ^ 2 + π X` over `𝔽₂⟦π⟧`, `[1]_Q = 1 + π`, since `1 + π` lifts `1` and is fixed
by `Q`. -/
theorem twistedTeichmuller_Q₂_one : twistedTeichmuller 2 1 Q₂ 1 = 1 + X := by
  have hfix : Polynomial.eval (1 + X : (ZMod 2)⟦X⟧) Q₂ = 1 + X := by
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C]
    linear_combination (X + X ^ 2 : (ZMod 2)⟦X⟧) * CharTwo.two_eq_zero (R := (ZMod 2)⟦X⟧)
  refine ((eq_twistedTeichmuller_iff one_ne_zero map_constantCoeff_Q₂).2 fun n ↦
    ⟨1 + X, by simp, ?_⟩).symm
  rw [Function.iterate_fixed hfix, sub_self]
  exact dvd_zero _

-- The constant lift `1` is not the `Q`-Teichmüller lift.
example : twistedTeichmuller 2 1 Q₂ 1 ≠ C 1 := by
  rw [twistedTeichmuller_Q₂_one]
  intro h
  simpa [coeff_C] using congrArg (coeff 1) h

-- The lift is not multiplicative: `[1 * 1]_Q = 1 + π`, but `(1 + π) ^ 2 = 1 + π ^ 2`.
example : twistedTeichmuller 2 1 Q₂ (1 * 1) ≠
    twistedTeichmuller 2 1 Q₂ 1 * twistedTeichmuller 2 1 Q₂ 1 := by
  rw [mul_one, twistedTeichmuller_Q₂_one]
  have hsq : (1 + X) * (1 + X) = (1 + X ^ 2 : (ZMod 2)⟦X⟧) := by
    linear_combination (X : (ZMod 2)⟦X⟧) * CharTwo.two_eq_zero (R := (ZMod 2)⟦X⟧)
  rw [hsq]
  intro h
  simpa [coeff_X_pow] using congrArg (coeff 1) h

-- Evaluation at `X ^ 2 + π X` is additive in characteristic `2`, hence so is the lift.
example (a b : ZMod 2) : twistedTeichmuller 2 1 Q₂ (a + b) =
    twistedTeichmuller 2 1 Q₂ a + twistedTeichmuller 2 1 Q₂ b := by
  refine twistedTeichmuller_add (fun x y ↦ ?_) a b
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_C]
  linear_combination (x * y) * CharTwo.two_eq_zero (R := (ZMod 2)⟦X⟧)

end Two

section Three

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

local instance : CharP (ZMod 3)⟦X⟧ 3 := charP_of_injective_ringHom C_injective 3

/-- The polynomial `Q = X ^ 3 + π X` over `𝔽₃⟦π⟧`. -/
local notation "Q₃" =>
  (Polynomial.X ^ 3 + Polynomial.C (X : (ZMod 3)⟦X⟧) * Polynomial.X : Polynomial (ZMod 3)⟦X⟧)

-- `[1]_Q ≡ 1 + π + π ^ 2` modulo `π ^ 3`, read off from `Q(Q(1)) = 1 + π + π ^ 2 + π ^ 3`.
example : X ^ 3 ∣ twistedTeichmuller 3 1 Q₃ 1 - (1 + X + X ^ 2) := by
  have hiter : (Polynomial.eval · Q₃)^[2] (1 : (ZMod 3)⟦X⟧) = 1 + X + X ^ 2 + X ^ 3 := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_C]
    linear_combination (X + X ^ 2 : (ZMod 3)⟦X⟧) * CharP.ofNat_eq_zero (ZMod 3)⟦X⟧ 3
  have h := X_pow_succ_dvd_twistedTeichmuller_sub (Q := Q₃) (n := 2) (b := 1) one_ne_zero
    (by simp) (by simp : constantCoeff (1 : (ZMod 3)⟦X⟧) ^ (3 ^ 1) ^ 2 = 1)
  rw [hiter] at h
  have : twistedTeichmuller 3 1 Q₃ 1 - (1 + X + X ^ 2) =
      (twistedTeichmuller 3 1 Q₃ 1 - (1 + X + X ^ 2 + X ^ 3)) + X ^ 3 := by ring
  rw [this]
  exact dvd_add h dvd_rfl

end Three

end TauCeti.Examples

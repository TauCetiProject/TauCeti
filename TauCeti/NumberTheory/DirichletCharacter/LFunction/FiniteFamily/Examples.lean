/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.FiniteFamily.Basic
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Cotangent
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Classification
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Small bounded families of Dirichlet L-functions

These examples include the empty bounded families at bounds zero and one with the explicit
radius one, and the first nonprincipal characters at levels three and four. Every nonprincipal
complex character at level three or four is the cast of the native character
`quadraticChar (ZMod 3)` or `ZMod.χ₄`, respectively. The cotangent formula gives their exact
L-values at one as `π / (3√3)` and `π / 4`. One positive radius gives a closed disk
centered at one on which every nonprincipal complex Dirichlet L-function at levels three
and four is nonzero.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 14.
-/

public section

open Complex

namespace DirichletCharacter

/-- The odd character at level four has continued value `π / 4` at one. -/
example (χ : DirichletCharacter ℂ 4) (hχ : χ.Odd) : χ.LFunction 1 = Real.pi / 4 :=
  χ.LFunction_one_eq_pi_div_four hχ

/-- The odd character at level three has continued value `π / (3√3)` at one. -/
example (χ : DirichletCharacter ℂ 3) (hχ : χ.Odd) :
    χ.LFunction 1 = Real.pi / (3 * (Real.sqrt 3 : ℂ)) :=
  χ.LFunction_one_eq_pi_div_three_mul_sqrt_three hχ

/-- Radius one serves for the empty bounded family at bound zero. -/
example : (0 : ℝ) < 1 ∧ ∀ (N : ℕ) [NeZero N], N ≤ 0 →
    ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 →
      ∀ s : ℂ, ‖s - 1‖ ≤ 1 → χ.LFunction s ≠ 0 :=
  ⟨zero_lt_one, fun N _ hN ↦ False.elim (NeZero.ne N (Nat.le_zero.mp hN))⟩

/-- Radius one also serves at bound one, whose only level carries only the principal character. -/
example : (0 : ℝ) < 1 ∧ ∀ (N : ℕ) [NeZero N], N ≤ 1 →
    ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 →
      ∀ s : ℂ, ‖s - 1‖ ≤ 1 → χ.LFunction s ≠ 0 :=
  ⟨zero_lt_one, fun N _ hN χ hχ ↦
    (hχ (χ.level_one' (Nat.le_antisymm hN (NeZero.pos N)))).elim⟩

/-- Every nonprincipal character in the level-four bounded family has level three or four. -/
example {N : ℕ} [NeZero N] (hN : N ≤ 4) (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    N = 3 ∨ N = 4 := by
  have := three_le_level_of_ne_one hχ
  omega

/-- The complex cast of the native integer-valued character `ZMod.χ₄` is odd. -/
example : Odd (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) := by
  have hneg : ZMod.χ₄ (-1) = -1 := by
    simpa only [Int.cast_neg, Int.cast_one] using
      (ZMod.χ₄_int_three_mod_four (n := -1) (by decide))
  simp only [Odd, MulChar.ringHomComp_apply, hneg, map_neg, map_one]

/-- One positive radius gives a closed disk centered at one where every nonprincipal complex
Dirichlet L-function at levels three and four is nonzero. -/
example : ∃ δ : ℝ, 0 < δ ∧ ∀ χ₃ : DirichletCharacter ℂ 3, χ₃ ≠ 1 →
    ∀ χ₄ : DirichletCharacter ℂ 4, χ₄ ≠ 1 → ∀ s : ℂ, ‖s - 1‖ ≤ δ →
      χ₃.LFunction s ≠ 0 ∧ χ₄.LFunction s ≠ 0 := by
  obtain ⟨δ, hδ, h⟩ := TauCeti.DirichletCharacter.exists_pos_forall_LFunction_ne_zero 4
  exact ⟨δ, hδ, fun χ₃ h₃ χ₄ h₄ s hs ↦
    ⟨h 3 (by decide) χ₃ h₃ s hs, h 4 le_rfl χ₄ h₄ s hs⟩⟩

/-- Every nonprincipal complex character modulo four is the cast of the native quadratic one. -/
example (χ : DirichletCharacter ℂ 4) (hχ : χ ≠ 1) :
    χ = ZMod.χ₄.ringHomComp (Int.castRingHom ℂ) := by
  have hcard : Nat.totient 4 = 2 := by decide
  have hquad : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr (by
    simpa only [ZMod.card_units_eq_totient, hcard] using χ.pow_card_eq_one)
  exact (eq_one_or_eq_χ₄_of_isQuadratic hquad).resolve_left hχ

/-- The complex cast of `quadraticChar (ZMod 3)` is odd and equals every nonprincipal
complex character modulo three. -/
example : Odd ((quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)) ∧
    ∀ χ : DirichletCharacter ℂ 3, χ ≠ 1 →
      χ = (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ) := by
  have hneg : (quadraticChar (ZMod 3)) (-1) = -1 := by
    rw [quadraticChar_neg_one (F := ZMod 3) (by norm_num [ZMod.ringChar_zmod_n]), ZMod.card]
    exact ZMod.χ₄_nat_three_mod_four (by decide)
  constructor
  · simp only [Odd, MulChar.ringHomComp_apply, hneg, map_neg, map_one]
  · intro χ hχ
    have hquad : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr (by
      simpa only [ZMod.card_units_eq_totient, Nat.totient_prime Nat.prime_three] using
        χ.pow_card_eq_one)
    exact ((isQuadratic_iff_eq_one_or_eq_quadraticChar χ).mp hquad).resolve_left hχ

end DirichletCharacter

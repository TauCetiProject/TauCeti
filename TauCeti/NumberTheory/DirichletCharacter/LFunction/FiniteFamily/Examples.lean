/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.FiniteFamily
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Cotangent
import TauCeti.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import TauCeti.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Small bounded families of Dirichlet L-functions

These examples include the empty bounded families at bounds zero and one with the explicit
radius one, and the first nonprincipal characters at levels three and four. Every nonprincipal
complex character at level three or four is the cast of the native character
`quadraticChar (ZMod 3)` or `ZMod.χ₄`, respectively. The cotangent formula gives their exact
L-values at one as `π / (3√3)` and `π / 4`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 14.
-/

public section

open Complex

namespace DirichletCharacter

/-- The odd character at level four has continued value `π / 4` at one. -/
example (χ : DirichletCharacter ℂ 4) (hχ : χ.Odd) : χ.LFunction 1 = Real.pi / 4 := by
  have h := χ.two_mul_LFunction_one_eq_sum_range_mul_cot hχ
  have hres : (3 : ZMod 4) = -1 := by decide
  have hneg : χ (3 : ZMod 4) = -1 := by simpa only [Odd, hres] using hχ
  have htwo : χ (2 : ZMod 4) = 0 := χ.map_nonunit (by decide)
  norm_num [Finset.sum_range_succ, hneg, htwo] at h
  have ht : tan ((Real.pi : ℂ) / 4) = 1 := by exact_mod_cast Real.tan_pi_div_four
  have hc : cot ((Real.pi : ℂ) / 4) = 1 := by
    simpa only [tan_inv_eq_cot, inv_one] using congrArg Inv.inv ht
  have hangle : (Real.pi : ℂ) * (3 / 4) = Real.pi - Real.pi / 4 := by ring
  rw [mul_one_div, hangle, cot_pi_sub, hc] at h
  linear_combination h / 2

/-- The odd character at level three has continued value `π / (3√3)` at one. -/
example (χ : DirichletCharacter ℂ 3) (hχ : χ.Odd) :
    χ.LFunction 1 = Real.pi / (3 * (Real.sqrt 3 : ℂ)) := by
  have h := χ.two_mul_LFunction_one_eq_sum_range_mul_cot hχ
  have hres : (2 : ZMod 3) = -1 := by decide
  have hneg : χ (2 : ZMod 3) = -1 := by simpa only [Odd, hres] using hχ
  norm_num [Finset.sum_range_succ, hneg] at h
  have ht : tan ((Real.pi : ℂ) / 3) = (Real.sqrt 3 : ℂ) := by
    exact_mod_cast Real.tan_pi_div_three
  have hc : cot ((Real.pi : ℂ) / 3) = (Real.sqrt 3 : ℂ)⁻¹ := by
    simpa only [tan_inv_eq_cot] using congrArg Inv.inv ht
  have hangle : (Real.pi : ℂ) * (2 / 3) = Real.pi - Real.pi / 3 := by ring
  rw [mul_one_div, hangle, cot_pi_sub, hc] at h
  linear_combination h / 2

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

/-- The native quadratic character modulo three supplies a nonprincipal member of the family. -/
example : Odd ((quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)) := by
  simp only [Odd, MulChar.ringHomComp_apply, quadraticChar_zmod_three_neg_one, map_neg, map_one]

/-- Casting the native integer-valued character modulo four gives the other nonprincipal member. -/
example : Odd (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) := by
  have hneg : ZMod.χ₄ (-1) = -1 := by decide
  simp only [Odd, MulChar.ringHomComp_apply, hneg, map_neg, map_one]

/-- A single radius works simultaneously for the native functions at levels three and four. -/
example : ∃ δ : ℝ, 0 < δ ∧ ∀ χ₃ : DirichletCharacter ℂ 3, χ₃ ≠ 1 →
    ∀ χ₄ : DirichletCharacter ℂ 4, χ₄ ≠ 1 → ∀ s : ℂ, ‖s - 1‖ ≤ δ →
      χ₃.LFunction s ≠ 0 ∧ χ₄.LFunction s ≠ 0 := by
  obtain ⟨δ, hδ, h⟩ := TauCeti.DirichletCharacter.exists_pos_forall_LFunction_ne_zero 4
  exact ⟨δ, hδ, fun χ₃ h₃ χ₄ h₄ s hs ↦
    ⟨h 3 (by decide) χ₃ h₃ s hs, h 4 le_rfl χ₄ h₄ s hs⟩⟩

/-- Every nonprincipal complex character modulo four is the cast of the native quadratic one. -/
example (χ : DirichletCharacter ℂ 4) (hχ : χ ≠ 1) :
    χ = ZMod.χ₄.ringHomComp (Int.castRingHom ℂ) := by
  have hres : (3 : ZMod 4) = -1 := by decide
  rcases χ.even_or_odd with he | ho
  · apply (hχ ?_).elim
    apply ext_of_level_four
    simpa only [Even, hres, MulChar.one_apply (by decide : IsUnit (-1 : ZMod 4))]
      using he
  · apply ext_of_level_four
    have hneg : ZMod.χ₄ (-1) = -1 := by decide
    simpa only [Odd, hres, MulChar.ringHomComp_apply, hneg, map_neg, map_one] using ho

/-- Every nonprincipal complex character modulo three is the cast of its quadratic character. -/
example (χ : DirichletCharacter ℂ 3) (hχ : χ ≠ 1) :
    χ = (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ) := by
  rcases χ.even_or_odd with he | ho
  · apply (hχ ?_).elim
    apply ext_of_level_three
    simpa only [Even, MulChar.one_apply (by decide : IsUnit (-1 : ZMod 3))] using he
  · apply ext_of_level_three
    simpa only [MulChar.ringHomComp_apply, quadraticChar_zmod_three_neg_one,
      map_neg, map_one, Odd] using ho

end DirichletCharacter

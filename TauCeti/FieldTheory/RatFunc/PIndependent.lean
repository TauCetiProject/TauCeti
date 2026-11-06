/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Frobenius.PIndependent
public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler
public import TauCeti.FieldTheory.RatFunc.Valuation
import TauCeti.Algebra.CharP.Two

/-!
# Two independent nonsquares in a rational function field

In characteristic two, the two variables of `k(s)(u)` are `2`-independent: the elements
`1, s, u, s * u` are linearly independent over the subfield of squares. In particular,
`s` is not a square, and `u` cannot be written as `a² + s b²`. These are the residue-field
conditions for constructing fierce biquadratic extensions of discrete valuation rings.

The first obstruction descends a putative square root of `s` through the relatively
algebraically closed extension `k(s) ⊆ k(s)(u)`. Differentiation with respect to `u` gives
the second obstruction and the linear independence of the four monomials.

## References

* S. Lang, *Algebra*, 3rd ed., Chapter VIII, Section 4, for `p`-independence.
* I. B. Fesenko, S. V. Vostokov, *Local Fields and Their Extensions*, 2nd ed., for
  fierce extensions with inseparable residue fields.
-/

public section

namespace RatFunc

open TauCeti

variable {k : Type*} [Field k]

/-- The first variable of `k(s)(u)` is not a square, over any coefficient field. -/
theorem sq_ne_C_X (a : RatFunc (RatFunc k)) :
    a ^ 2 ≠ RatFunc.C (RatFunc.X : RatFunc k) := by
  intro h
  obtain ⟨b, hb⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow
    (R := RatFunc k) (by decide : 0 < 2) (h ▸ isIntegral_algebraMap)
  have hC : RatFunc.C (b ^ 2) = RatFunc.C (RatFunc.X : RatFunc k) := by
    rw [← RatFunc.algebraMap_eq_C, map_pow, hb]
    exact h
  exact ratFunc_pow_ne_X (by decide : 1 < 2) b (RatFunc.C_injective hC)

variable [CharP k 2]

/-- In characteristic two the variable is not a sum `a² + c b²` with `c` constant. -/
theorem sq_add_C_mul_sq_ne_X (a b : RatFunc k) (c : k) :
    a ^ 2 + RatFunc.C c * b ^ 2 ≠ RatFunc.X := by
  intro h
  have hd := congrArg (KaehlerDifferential.D k (RatFunc k)) h
  have hX := (kaehlerBasisRatFunc k).ne_zero ()
  simp only [kaehlerBasisRatFunc_apply] at hX
  exact hX (by
    simpa [Derivation.leibniz_pow, ← RatFunc.algebraMap_eq_C, two_nsmul,
      add_self_eq_zero_of_charTwo (RatFunc k)] using hd.symm)

end RatFunc

namespace TauCeti

variable {k : Type*} [Field k] [CharP k 2]

/-- The two variables of `k(s)(u)` in characteristic two are `2`-independent. Equivalently,
`1, s, u, s u` are linearly independent over the subfield of squares. -/
theorem isPIndependentPair_ratFunc_C_X_X :
    IsPIndependentPair 2 (RatFunc.C (RatFunc.X : RatFunc k))
      (RatFunc.X : RatFunc (RatFunc k)) := by
  rw [isPIndependentPair_iff]
  intro c hc i hi j hj
  have hsum : c 0 0 ^ 2 + c 0 1 ^ 2 * RatFunc.X +
      (c 1 0 ^ 2 * RatFunc.C (RatFunc.X : RatFunc k) +
        c 1 1 ^ 2 * RatFunc.C (RatFunc.X : RatFunc k) * RatFunc.X) = 0 := by
    simpa [Finset.sum_range_succ] using hc
  have hd := congrArg (KaehlerDifferential.D (RatFunc k) (RatFunc (RatFunc k))) hsum
  have he : c 0 1 ^ 2 + RatFunc.C (RatFunc.X : RatFunc k) * c 1 1 ^ 2 = 0 := by
    have hX := (kaehlerBasisRatFunc (RatFunc k)).ne_zero ()
    simp only [kaehlerBasisRatFunc_apply] at hX
    apply (smul_left_injective (RatFunc (RatFunc k)) hX)
    simpa [Derivation.leibniz_pow, ← RatFunc.algebraMap_eq_C, two_nsmul,
      add_self_eq_zero_of_charTwo (RatFunc (RatFunc k)), add_smul, mul_smul, mul_comm] using hd
  have h11 : c 1 1 = 0 := by
    by_contra h11
    apply RatFunc.sq_ne_C_X (c 0 1 / c 1 1)
    rw [div_pow, div_eq_iff (pow_ne_zero 2 h11)]
    exact CharTwo.add_eq_zero.mp he
  have h01 : c 0 1 = 0 := by simpa [h11] using he
  have he' : c 0 0 ^ 2 + RatFunc.C (RatFunc.X : RatFunc k) * c 1 0 ^ 2 = 0 := by
    simpa [h11, h01, mul_comm] using hsum
  have h10 : c 1 0 = 0 := by
    by_contra h10
    apply RatFunc.sq_ne_C_X (c 0 0 / c 1 0)
    rw [div_pow, div_eq_iff (pow_ne_zero 2 h10)]
    exact CharTwo.add_eq_zero.mp he'
  have h00 : c 0 0 = 0 := by simpa [h10] using he'
  interval_cases i <;> interval_cases j <;> assumption

end TauCeti

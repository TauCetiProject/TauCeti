/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.OddCyclic.GaussSum
import Mathlib.Tactic.NormNum.IsSquare

/-!
# Vanishing Gauss sign does not imply metabolicity

Nikulin's odd cyclic generator of order five with coefficient two has Gauss sign zero
but has no quadratic Lagrangian. Nondegeneracy would force the squared order of such a
Lagrangian to be five, which is impossible.

More generally, a nondegenerate odd cyclic module whose order is not a square is not metabolic.

## Main declarations

* `TauCeti.FiniteQuadraticModule.not_isMetabolic_oddCyclic`: the nonsquare-order obstruction.
* `TauCeti.FiniteQuadraticModule.gaussSign_eq_zero_and_not_isMetabolic_oddCyclic_five`:
  the concrete order-five counterexample with coefficient two.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.11.2 for the odd-generator Gauss-sign formula.
-/

public section

namespace TauCeti.FiniteQuadraticModule

/-- A nondegenerate odd cyclic module of nonsquare order cannot have a quadratic Lagrangian. -/
theorem not_isMetabolic_oddCyclic {m : ℕ} (hm : Odd m) {θ : ℤ}
    (hθ : IsCoprime (m : ℤ) θ) (hm' : ¬ IsSquare m) :
    ¬ (oddCyclic m hm θ).IsMetabolic := by
  intro h
  have hcard : Nat.card (oddCyclic m hm θ) = m := Nat.card_zmod m
  have hnondeg := (isNondegenerate_oddCyclic_iff m hm θ).mpr hθ
  exact hm' (hcard ▸ h.isSquare_natCard hnondeg)

/-- The nondegenerate odd cyclic form of order five with coefficient two has zero Gauss sign
and no quadratic Lagrangian. Thus vanishing of the Gauss sign does not imply metabolicity. -/
theorem gaussSign_eq_zero_and_not_isMetabolic_oddCyclic_five :
    (oddCyclic 5 (by decide) 2).IsNondegenerate ∧
      (oddCyclic 5 (by decide) 2).gaussSign = 0 ∧
      ¬ (oddCyclic 5 (by decide) 2).IsMetabolic := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hc : IsCoprime (5 : ℤ) 2 := by norm_num [Int.isCoprime_iff_gcd_eq_one]
  have hθ : legendreSym 5 2 = -1 := by
    rw [legendreSym.at_two (by decide), ZMod.χ₈_nat_eq_if_mod_eight]
    norm_num
  refine ⟨(isNondegenerate_oddCyclic_iff _ _ _).mpr hc, ?_, ?_⟩
  · simpa [hθ] using gaussSign_oddCyclic (by decide : Odd 5) 1 hc
  · exact not_isMetabolic_oddCyclic (by decide) hc (by norm_num)

end TauCeti.FiniteQuadraticModule

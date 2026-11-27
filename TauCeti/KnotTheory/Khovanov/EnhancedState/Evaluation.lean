/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.EnhancedState.Basic
import TauCeti.KnotTheory.PDCode.Jones.Evaluation

/-!
# Planar evaluations of the enhanced state sum

For every planar oriented PD-code `D` with `c` link components, the `q = 1` specialization
`E(D) = TauCeti.OrientedPDCode.enhancedStateEulerSum D` equals `2 ^ c`. For crossing-free
diagrams this is `TauCeti.OrientedPDCode.enhancedStateEulerSum_of_zero`, and when `D` has crossings
it follows from `TauCeti.OrientedPDCode.enhancedStateSum_eq_mul_eval₂_jonesPolynomial` together
with the Jones evaluation `TauCeti.OrientedPDCode.eval₂_neg_one_jonesPolynomial`.

## Main results

* `TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_two_pow_componentCount`: `E(D) = 2 ^ c` for
  every planar oriented PD-code `D` with `c` components.
* `TauCeti.OrientedPDCode.eval₂_one_enhancedStateSum_eq_two_pow`: evaluating `D.enhancedStateSum`
  at `q = 1` yields `2 ^ c`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359–426.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), 337–370.
-/

public section

open LaurentPolynomial

namespace TauCeti.OrientedPDCode

variable {n : ℕ}

/-- **For every planar oriented PD-code `D` with `c` link components, `E(D) = 2 ^ c`.** -/
theorem enhancedStateEulerSum_eq_two_pow_componentCount (D : OrientedPDCode n)
    (hD : D.toPDCode.IsPlanar) : D.enhancedStateEulerSum = (2 : ℤ) ^ D.componentCount := by
  by_cases hn : n = 0
  · subst hn
    exact D.enhancedStateEulerSum_of_zero
  · have hpos : 0 < D.toPDCode.componentCount := D.toPDCode.componentCount_pos hn
    have hsum := congrArg (eval₂ (RingHom.id ℤ) (1 : ℤˣ))
      (D.enhancedStateSum_eq_mul_eval₂_jonesPolynomial hpos)
    have hhom : (eval₂ (RingHom.id ℤ) (1 : ℤˣ)).comp (Int.castRingHom ℤ[T;T⁻¹]) =
        RingHom.id ℤ := Subsingleton.elim _ _
    have hunit : Units.map (eval₂ (RingHom.id ℤ) (1 : ℤˣ) : ℤ[T;T⁻¹] →* ℤ) (-genericUnit ℤ) =
        (-1 : ℤˣ) := by
      ext
      simp
    have hq : eval₂ (RingHom.id ℤ) (1 : ℤˣ) (T 1 + T (-1) : ℤ[T;T⁻¹]) = 2 := by
      simp only [map_add, eval₂_T, zpow_one, zpow_neg_one, inv_one, Units.val_one]
      norm_num
    rw [D.eval₂_one_enhancedStateSum, map_mul, hq, LaurentPolynomial.hom_eval₂, hhom, hunit,
      D.eval₂_neg_one_jonesPolynomial hD hpos] at hsum
    rw [← pow_mul_pow_sub (2 : ℤ) (Nat.succ_le_of_lt hpos), pow_one]
    exact hsum

/-- **Evaluating the enhanced state sum of a planar diagram at `q = 1` gives `2 ^ c`.** -/
theorem eval₂_one_enhancedStateSum_eq_two_pow (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) :
    eval₂ (RingHom.id ℤ) 1 D.enhancedStateSum = (2 : ℤ) ^ D.componentCount := by
  rw [D.eval₂_one_enhancedStateSum, D.enhancedStateEulerSum_eq_two_pow_componentCount hD]

end TauCeti.OrientedPDCode

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.EnhancedState.Basic
import TauCeti.KnotTheory.PDCode.ResolvedCircle.Planar
import TauCeti.KnotTheory.PDCode.VertexResolution

/-!
# Planar evaluations of the enhanced state sum

For every planar oriented PD-code `D` with `c` link components, the PD-code normalization-sign
parity `TauCeti.OrientedPDCode.neg_one_pow_card_false_add_negativeCrossingCount` shows that each
state `s` with `k(s)` resolution circles contributes `(-1) ^ (n + c) (-2) ^ k(s)` to the
normalized enhanced-state Euler sum `E(D) = TauCeti.OrientedPDCode.enhancedStateEulerSum D`.
Together with the unoriented state sum `∑ₛ (-2) ^ k(s) = (-1) ^ (n + c) 2 ^ c`
(`TauCeti.PDCode.sum_neg_two_pow_stateLoopCount`), this yields `E(D) = 2 ^ c`, the `q = 1`
evaluation of `D.enhancedStateSum`, and the sum of its Laurent coefficients.

## Main results

* `TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_two_pow_componentCount`: `E(D) = 2 ^ c` for
  every planar oriented PD-code `D` with `c` components.
* `TauCeti.OrientedPDCode.eval₂_one_enhancedStateSum_eq_two_pow`: evaluating `D.enhancedStateSum`
  at `q = 1` yields `2 ^ c`.
* `TauCeti.OrientedPDCode.sum_coeff_enhancedStateSum_eq_two_pow`: the sum of all Laurent
  coefficients of `D.enhancedStateSum` is `2 ^ c`.
* `TauCeti.OrientedPDCode.eval₂_neg_one_jonesPolynomial`: for a nonempty planar code, evaluating
  the Jones polynomial at `t ^ (1/2) = -1` gives `2 ^ (c - 1)`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359–426.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), 337–370.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3.
* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, Theorems 14–15 (p. 107).
-/

public section

open Finset LaurentPolynomial

namespace TauCeti.OrientedPDCode

variable {n : ℕ}

/-- **For every planar oriented PD-code `D` with `c` link components, `E(D) = 2 ^ c`.** Every state
contributes `(-1) ^ (n + c) (-2) ^ k(s)` by the PD-code normalization-sign parity
(`TauCeti.OrientedPDCode.neg_one_pow_card_false_add_negativeCrossingCount`), and the unoriented
state sum `∑ₛ (-2) ^ k(s)` is `(-1) ^ (n + c) 2 ^ c`
(`TauCeti.PDCode.sum_neg_two_pow_stateLoopCount`). -/
theorem enhancedStateEulerSum_eq_two_pow_componentCount (D : OrientedPDCode n)
    (hD : D.toPDCode.IsPlanar) : D.enhancedStateEulerSum = (2 : ℤ) ^ D.componentCount := by
  rw [enhancedStateEulerSum_def]
  have hterm (s : Fin n → Bool) :
      (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) *
          2 ^ D.toPDCode.stateLoopCount s =
        (-1) ^ (n + D.componentCount) * (-2) ^ D.toPDCode.stateLoopCount s := by
    rw [D.neg_one_pow_card_false_add_negativeCrossingCount hD s, pow_add, neg_pow (2 : ℤ)]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, D.toPDCode.sum_neg_two_pow_stateLoopCount, ← mul_assoc, ← pow_add,
    Even.neg_one_pow ⟨_, rfl⟩, one_mul]

/-- **Evaluating the enhanced state sum of a planar diagram at `q = 1` gives `2 ^ c`.** -/
theorem eval₂_one_enhancedStateSum_eq_two_pow (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) :
    eval₂ (RingHom.id ℤ) 1 D.enhancedStateSum = (2 : ℤ) ^ D.componentCount := by
  rw [D.eval₂_one_enhancedStateSum, D.enhancedStateEulerSum_eq_two_pow_componentCount hD]

/-- The sum of all Laurent coefficients of `D.enhancedStateSum` for a planar oriented PD-code is
`2 ^ D.componentCount`. -/
theorem sum_coeff_enhancedStateSum_eq_two_pow (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) :
    (D.enhancedStateSum.coeff.sum fun _ c ↦ c) = (2 : ℤ) ^ D.componentCount := by
  rw [← laurentEval_one_eq_sum, laurentEval_eq_eval₂,
    RingHom.ext_int (algebraMap ℤ ℤ) (RingHom.id ℤ),
    D.eval₂_one_enhancedStateSum_eq_two_pow hD]

/-- **Evaluating the Jones polynomial of a nonempty planar diagram at `t ^ (1/2) = -1` gives
`2 ^ (c - 1)`** (Jones 1985, Theorems 14–15; Lickorish 1997, Chapter 3). -/
theorem eval₂_neg_one_jonesPolynomial (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
    (hpos : 0 < D.toPDCode.componentCount) :
    eval₂ (RingHom.id ℤ) (-1 : ℤˣ) D.jonesPolynomial = (2 : ℤ) ^ (D.componentCount - 1) := by
  have hsum := congrArg (eval₂ (RingHom.id ℤ) (1 : ℤˣ))
    (D.enhancedStateSum_eq_mul_eval₂_jonesPolynomial hpos)
  rw [D.eval₂_one_enhancedStateSum_eq_two_pow hD, map_mul, map_add, eval₂_T, eval₂_T,
    LaurentPolynomial.hom_eval₂] at hsum
  have hhom : (eval₂ (RingHom.id ℤ) (1 : ℤˣ)).comp (Int.castRingHom ℤ[T;T⁻¹]) =
      RingHom.id ℤ := Subsingleton.elim _ _
  have hunit : Units.map (eval₂ (RingHom.id ℤ) (1 : ℤˣ) : ℤ[T;T⁻¹] →* ℤ) (-genericUnit ℤ) =
      (-1 : ℤˣ) := by
    ext
    simp
  rw [hhom, hunit] at hsum
  obtain ⟨k, hk⟩ : ∃ k, D.toPDCode.componentCount = k + 1 := ⟨D.toPDCode.componentCount - 1, by
    omega⟩
  rw [hk, pow_succ'] at hsum
  rw [hk, Nat.add_sub_cancel]
  norm_num at hsum
  omega

end TauCeti.OrientedPDCode

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.EnhancedState.Parity
import TauCeti.KnotTheory.PDCode.VertexResolution

/-!
# Planar evaluations of the enhanced state sum

For every planar oriented PD-code `D` with `c` link components, the enhanced-state parity identity
`TauCeti.OrientedPDCode.stateQuantumShift_add_stateLoopCount_mod_two` shows that each state `s`
with `k(s)` resolution circles contributes `(-1) ^ (n + c) (-2) ^ k(s)` to the normalized
enhanced-state Euler sum `E(D) = TauCeti.OrientedPDCode.enhancedStateEulerSum D`. Together with the
unoriented state sum `∑ₛ (-2) ^ k(s) = (-1) ^ (n + c) 2 ^ c`
(`TauCeti.PDCode.sum_neg_two_pow_stateLoopCount`), this yields `E(D) = 2 ^ c`, the `q = 1`
evaluation of `D.enhancedStateSum`, and the sum of its Laurent coefficients.

## Main results

* `TauCeti.OrientedPDCode.enhancedStateEulerSum_eq_two_pow_componentCount`: `E(D) = 2 ^ c` for
  every planar oriented PD-code `D` with `c` components.
* `TauCeti.OrientedPDCode.eval₂_one_enhancedStateSum_eq_two_pow`: evaluating `D.enhancedStateSum`
  at `q = 1` yields `2 ^ c`.
* `TauCeti.OrientedPDCode.sum_coeff_enhancedStateSum_eq_two_pow`: the sum of all Laurent
  coefficients of `D.enhancedStateSum` is `2 ^ c`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359–426.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), 337–370.
-/

public section

open Finset LaurentPolynomial

namespace TauCeti.OrientedPDCode

variable {n : ℕ}

/-- On a planar code, the state `s` with `B`-smoothing set `S` and `k` circles contributes
`(-1) ^ (n + c) (-2) ^ k` to `E(D)`, by the component parity of the quantum grading. -/
private theorem neg_one_pow_mul_two_pow_stateLoopCount (D : OrientedPDCode n)
    (hD : D.toPDCode.IsPlanar) (s : Fin n → Bool) :
    (-1 : ℤ) ^ (#{i | s i = false} + D.negativeCrossingCount) *
        2 ^ D.toPDCode.stateLoopCount s =
      (-1) ^ (n + D.componentCount) * (-2) ^ D.toPDCode.stateLoopCount s := by
  have hpar := D.stateQuantumShift_add_stateLoopCount_mod_two hD s
  have hcount := D.positiveCrossingCount_add_negativeCrossingCount
  have hsign : (D.stateCochainDegree s).negOnePow =
      ((n + D.componentCount + D.toPDCode.stateLoopCount s : ℕ) : ℤ).negOnePow := by
    rw [Int.negOnePow_eq_iff, Int.even_iff, stateCochainDegree_def]
    rw [stateQuantumShift_def] at hpar
    push_cast at hpar ⊢
    omega
  rw [← D.coe_negOnePow_stateCochainDegree, hsign, Int.coe_negOnePow_natCast, neg_pow (2 : ℤ)]
  ring

/-- **For every planar oriented PD-code `D` with `c` link components, `E(D) = 2 ^ c`.** Every state
contributes `(-1) ^ (n + c) (-2) ^ k(s)` by the component parity of the quantum grading, and the
unoriented state sum `∑ₛ (-2) ^ k(s)` is `(-1) ^ (n + c) 2 ^ c`
(`TauCeti.PDCode.sum_neg_two_pow_stateLoopCount`). -/
theorem enhancedStateEulerSum_eq_two_pow_componentCount (D : OrientedPDCode n)
    (hD : D.toPDCode.IsPlanar) : D.enhancedStateEulerSum = (2 : ℤ) ^ D.componentCount := by
  rw [enhancedStateEulerSum_def]
  simp_rw [D.neg_one_pow_mul_two_pow_stateLoopCount hD]
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

end TauCeti.OrientedPDCode

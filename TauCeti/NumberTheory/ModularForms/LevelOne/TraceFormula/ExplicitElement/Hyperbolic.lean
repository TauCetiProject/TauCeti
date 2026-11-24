/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.Translation

/-!
# The hyperbolic trace fibres of Popa–Zagier's element

Let `TauCeti.PopaZagier.weight M` be twelve times the coefficient of the integral matrix `M` in
Popa and Zagier's explicit Hecke element, their eq. (15). This file evaluates the sum of these
weights over the matrices of trace `t` and determinant `n` when the discriminant `t² - 4 n` is
positive. Together with the elliptic fibres
(`TauCeti.PopaZagier.finsum_weight_traceDetFiber_eq_neg_twelve_mul_hurwitzClassNumber`) and the
repeated-root fibres (`TauCeti.PopaZagier.finsum_weight_traceDetFiber_of_discrim_eq_zero`), this
evaluates every trace fibre of positive determinant:

* if `t² - 4 n = u²` with `u > 0` and `n > 0`, the weights sum to `12 u` for `t > 0` and to `0` for
  `t < 0`;
* if `t² - 4 n ≥ 0` is not a square, the weights sum to `0`.

Popa and Zagier's coefficients are a twelfth of the weights, so in the split case the two fibres
of traces `±t` together carry coefficient `u`. Weighted by the binary-form trace `P_{w+2}(t, n)`,
the split fibres give the divisor-sum terms of the trace formula, and the nonsplit fibres give
nothing.

## Main results

* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_of_discrim_eq_sq`: the split hyperbolic fibres.
* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_eq_zero_of_not_isSquare`: the nonsplit
  hyperbolic fibres.

## Proof

Translation `M ↦ M + 1` preserves the sum over a fibre of nonzero determinant
(`TauCeti.PopaZagier.finsum_weight_traceDetFiber_add_two`) and shifts both eigenvalues by `1`.
If `t ≤ 0`, the fibre sum vanishes
(`TauCeti.PopaZagier.finsum_weight_traceDetFiber_eq_zero_of_trace_nonpos`). If `t > 0`,
translating downwards (`TauCeti.PopaZagier.exists_finsum_weight_traceDetFiber_eq`) reaches a fibre
with `0 < n' < t'`, whose sum is evaluated by
`TauCeti.PopaZagier.finsum_weight_traceDetFiber_of_det_lt_trace`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §4, eq. (15).
-/

public section

open Matrix

namespace TauCeti.PopaZagier

variable {t n : ℤ}

/-! ### The hyperbolic fibres -/

/-- **The split hyperbolic trace fibres of Popa–Zagier's element.** If `n > 0` and
`t² - 4 n = u²` with `u > 0`, the weights of the integral matrices of trace `t` and determinant
`n` sum to `12 u` if `t > 0`, and to `0` if `t < 0`. -/
theorem finsum_weight_traceDetFiber_of_discrim_eq_sq {u : ℤ} (hn : 0 < n) (hu : 0 < u)
    (h : t ^ 2 - 4 * n = u ^ 2) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.val = if 0 < t then 12 * u else 0 := by
  have hD : 4 * n ≤ t ^ 2 := by nlinarith [sq_nonneg u]
  rcases le_or_gt t 0 with ht | ht
  · rw [ite_eq_right (by omega)]
    exact finsum_weight_traceDetFiber_eq_zero_of_trace_nonpos ht hD
  rw [ite_eq_left ht]
  obtain ⟨t', n', hD', hn', ht', e⟩ := exists_finsum_weight_traceDetFiber_eq ht hn hD
  rw [e, finsum_weight_traceDetFiber_of_det_lt_trace hn' ht']
  split_ifs with ht'' hn₁
  · subst ht'' hn₁
    nlinarith
  · -- the eigenvalues are `1` and `n'`, so `u = n' - 1`
    subst ht''
    have : (u - (n' - 1)) * (u + (n' - 1)) = 0 := by linear_combination -h - hD'
    rcases mul_eq_zero.mp this with h0 | h0
    · rw [show u = n' - 1 by omega]
    · omega
  · -- otherwise `t'² - 4 n'` would be a square with roots `(t' ± u) / 2` on either side of `1`
    exfalso
    have hlt : n' + 1 < t' := by omega
    have hprod : (t' - u) * (t' + u) = 4 * n' := by linear_combination hD' + h
    have hpos : 0 < t' - u := by nlinarith
    have hone : t' - u = 1 := by nlinarith
    rw [hone, one_mul] at hprod
    omega

/-- **The nonsplit hyperbolic trace fibres of Popa–Zagier's element.** If `t² - 4 n ≥ 0` is not a
square, the weights of the integral matrices of trace `t` and determinant `n` sum to `0`. -/
theorem finsum_weight_traceDetFiber_eq_zero_of_not_isSquare (hD : 4 * n ≤ t ^ 2)
    (h : ¬IsSquare (t ^ 2 - 4 * n)) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.val = 0 := by
  rcases le_or_gt n 0 with hn | hn
  · exact finsum_weight_traceDetFiber_eq_zero_of_det_nonpos hn
  rcases le_or_gt t 0 with ht | ht
  · exact finsum_weight_traceDetFiber_eq_zero_of_trace_nonpos ht hD
  obtain ⟨t', n', hD', hn', ht', e⟩ := exists_finsum_weight_traceDetFiber_eq ht hn hD
  rw [e, finsum_weight_traceDetFiber_of_det_lt_trace hn' ht']
  by_cases ht'' : t' = n' + 1
  · subst ht''
    exact absurd ⟨n' - 1, by linear_combination -hD'⟩ h
  · rw [ite_eq_right ht'']

end TauCeti.PopaZagier

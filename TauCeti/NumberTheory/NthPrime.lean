/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.WeakPNT
import TauCeti.Analysis.SpecialFunctions.LogIntegral
import TauCeti.NumberTheory.PrimeCounting

/-!
# The asymptotic size of the `n`-th prime

The prime number theorem `π(x) ∼ x / log x` (Mathlib's `Nat.isEquivalent_primeCounting`) is
equivalent to the asymptotic `p_n ∼ n log n` for the `n`-th prime `p_n = Nat.nth Nat.Prime n`.
This file proves the forward direction.

The deduction is an asymptotic inversion of the scale `x / log x`, proved first for an arbitrary
function along an arbitrary filter: if `u → ∞` and `u / log u ∼ v`, then taking logarithms gives
`log u − log log u ∼ log v`, and `log log u = o(log u)`, so `log u ∼ log v`; multiplying,
`u = (u / log u) · log u ∼ v log v`. At `u n = p_n` the prime number theorem and
`π(p_n) = n + 1` (`Nat.primeCounting_nth_prime`) give `p_n / log p_n ∼ n + 1 ∼ n`, so the
inversion applies with `v n = n`. The shift by one from the indexing `Nat.nth Nat.Prime 0 = 2`
does not affect any of the equivalences.

## Main results

* `Asymptotics.IsEquivalent.log_of_div_log`, `Asymptotics.IsEquivalent.of_div_log`: if `u → ∞`
  and `u / log u ∼ v`, then `log u ∼ log v` and `u ∼ v log v`.
* `Nat.isEquivalent_nth_prime_div_log`: `p_n / log p_n ∼ n`.
* `Nat.isEquivalent_log_nth_prime`: `log p_n ∼ log n`.
* `Nat.isEquivalent_nth_prime`: `p_n ∼ n log n`.

## References

The statements and the route through `p_n / log p_n ∼ n` and `log p_n ∼ log n` follow
`pi_nth_prime_asymp`, `log_nth_prime_asymp` and `nth_prime_asymp` in the
[PrimeNumberTheoremAnd project](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/692e4768ddaaf12ac8970718bf75ab083afce494/PrimeNumberTheoremAnd/Consequences.lean).
-/

public section

open Filter Asymptotics

namespace Asymptotics.IsEquivalent

variable {α : Type*} {l : Filter α} {u v : α → ℝ}

/-- If `u → ∞` and `u / log u ∼ v`, then `log u ∼ log v`. -/
theorem log_of_div_log (hu : Tendsto u l atTop)
    (h : (fun x ↦ u x / Real.log (u x)) ~[l] v) :
    (fun x ↦ Real.log (u x)) ~[l] fun x ↦ Real.log (v x) := by
  have hlogu := Real.tendsto_log_atTop.comp hu
  have hv := h.tendsto_atTop (TauCeti.Real.tendsto_div_log_atTop.comp hu)
  refine IsEquivalent.trans ?_ (h.log hv)
  have hsub : (fun x ↦ Real.log (u x) - Real.log (Real.log (u x))) ~[l]
      fun x ↦ Real.log (u x) :=
    IsEquivalent.refl.sub_isLittleO (Real.isLittleO_log_id_atTop.comp_tendsto hlogu)
  refine (hsub.congr_left ?_).symm
  filter_upwards [hu.eventually_gt_atTop 1] with x hx
  rw [Real.log_div (by linarith) (Real.log_pos hx).ne']

/-- **Asymptotic inversion of `x / log x`.** If `u → ∞` and `u / log u ∼ v`, then
`u ∼ v log v`. -/
theorem of_div_log (hu : Tendsto u l atTop) (h : (fun x ↦ u x / Real.log (u x)) ~[l] v) :
    u ~[l] fun x ↦ v x * Real.log (v x) := by
  refine (h.mul (h.log_of_div_log hu)).congr_left ?_
  filter_upwards [hu.eventually_gt_atTop 1] with x hx
  exact div_mul_cancel₀ _ (Real.log_pos hx).ne'

end Asymptotics.IsEquivalent

namespace Nat

/-- The `n`-th prime, as a real number, tends to infinity. -/
theorem tendsto_nth_prime_atTop : Tendsto (fun n ↦ (nth Nat.Prime n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_iff.mpr (nth_strictMono infinite_setOfPred_prime).tendsto_atTop

/-- The `n`-th prime satisfies `p_n / log p_n ∼ n`: this is the prime number theorem at
`x = p_n`, where `π(p_n) = n + 1`. -/
theorem isEquivalent_nth_prime_div_log :
    (fun n ↦ (nth Nat.Prime n : ℝ) / Real.log (nth Nat.Prime n)) ~[atTop] fun n ↦ (n : ℝ) := by
  have h := (isEquivalent_primeCounting.comp_tendsto tendsto_nth_prime_atTop).symm
  simp only [Function.comp_def, floor_natCast, primeCounting_nth_prime, cast_add,
    cast_one] at h
  exact h.trans <| IsEquivalent.refl.add_isLittleO <|
    (isLittleO_const_id_atTop (1 : ℝ)).natCast_atTop

/-- The logarithm of the `n`-th prime satisfies `log p_n ∼ log n`. -/
theorem isEquivalent_log_nth_prime :
    (fun n ↦ Real.log (nth Nat.Prime n)) ~[atTop] fun n ↦ Real.log n :=
  isEquivalent_nth_prime_div_log.log_of_div_log
    tendsto_nth_prime_atTop

/-- **The size of the `n`-th prime**: `p_n ∼ n log n`. -/
theorem isEquivalent_nth_prime :
    (fun n ↦ (nth Nat.Prime n : ℝ)) ~[atTop] fun n ↦ n * Real.log n :=
  isEquivalent_nth_prime_div_log.of_div_log
    tendsto_nth_prime_atTop

end Nat

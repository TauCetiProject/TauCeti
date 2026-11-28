/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Boundary
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Laplace

/-!
# The constant term of the signed prime sum

For an odd prime `d` coprime to the progression modulus `q`, the signed prime remainder
`R_q(y)` tends to zero. In particular, the real part of `G_q(1)` used to define the remainder
is the actual constant term of the normalized smoothed sum. This limit uses Newman's
Tauberian theorem and does not require a prime number theorem with a rate.

For the signed normalization see `lsernau/grh-lean`, revision `72fead1`,
`grh/src/New/Reduction/Zeros/PrimeNumberTheorem.lean` (`New.tendsto_primeRemainder`).
-/

public section

open Filter
open scoped Topology

namespace TauCeti.OneSidedBound

/-- At a nonzero modulus coprime to the odd prime `d`, the signed prime remainder tends to
zero as the real cutoff tends to infinity. -/
theorem tendsto_primeRemainder (d q : ℕ) [Fact d.Prime] [NeZero q]
    (hd : d ≠ 2) (hq : q.Coprime d) : Tendsto (primeRemainder d q) atTop (𝓝 0) := by
  have hlim := tendsto_rieszSum_div_sub_log_of_analyticAt (M := 2 * (Real.log 4 + 4))
    (a := fun n ↦ (primeWeight d q n : ℂ)) (A := (q.totient : ℂ)⁻¹) (F := logDerivMean d q)
    (fun x hx ↦ by
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg
        (Finset.sum_nonneg fun n _ ↦ primeWeight_nonneg d q n)]
      exact sum_primeWeight_le d q (zero_le_one.trans hx))
    (fun _ hs ↦ analyticAt_logDerivMean_of_one_le_re hs.ge) (fun _ hs ↦ by
      convert LSeriesHasSum_primeWeight hd hq hs using 1
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring)
  have h := (Complex.continuous_re.tendsto _).comp (hlim.sub_const (logDerivMean d q 1))
  rw [sub_self, Complex.zero_re] at h
  convert h using 1
  funext y
  rw [← Complex.ofReal_re (primeRemainder d q y), ofReal_primeRemainder_eq]
  simp only [Function.comp_apply, div_eq_mul_inv, mul_comm (q.totient : ℂ)⁻¹]

end TauCeti.OneSidedBound

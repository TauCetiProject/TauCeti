/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Summable real powers

A nonnegative family `f` with a summable positive power `f ^ p` tends to `0` along the cofinite
filter, since its terms are the `p`-th roots of a summable family.

For `e < -1`, every constant multiple of the shifted `p`-series `(n + 1) ^ e` over `ℕ` has a
finite sum of nonnegative parts in `ℝ≥0∞`. This is the form of a summable majorant for tail
probabilities decaying polynomially in a sequence index. A union bound over `N ^ (q + 1)` choices
of `q` events, each with the Markov tail `C / (N ^ a) ^ m`, takes this form through the identity
`N ^ (q + 1) * (C / (N ^ a) ^ m) ^ q = C ^ q * N ^ (q + 1 - a m q)` for `N > 0`.

## Main results

* `TauCeti.tendsto_cofinite_zero_of_summable_rpow` — a nonnegative family with a summable positive
  power tends to `0`.
* `TauCeti.tsum_ofReal_mul_natCast_add_one_rpow_lt_top` —
  `∑' n : ℕ, ENNReal.ofReal (C * (n + 1) ^ e) < ∞` for `e < -1`.
* `TauCeti.pow_add_one_mul_div_rpow_pow_pow` —
  `N ^ (q + 1) * (C / (N ^ a) ^ m) ^ q = C ^ q * N ^ (q + 1 - a m q)` for `N > 0`.
-/

public section

namespace TauCeti

/-- A nonnegative family `f` with `f ^ p` summable for some `0 < p` tends to `0` along the
cofinite filter. -/
theorem tendsto_cofinite_zero_of_summable_rpow {ι : Type*} {f : ι → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : ∀ i, 0 ≤ f i) (h : Summable fun i ↦ f i ^ p) :
    Filter.Tendsto f Filter.cofinite (nhds 0) := by
  have h' := h.tendsto_cofinite_zero.rpow_const (p := p⁻¹) (Or.inr (inv_nonneg.2 hp.le))
  rw [Real.zero_rpow (inv_ne_zero hp.ne')] at h'
  exact h'.congr fun i ↦ Real.rpow_rpow_inv (hf i) hp.ne'

open scoped ENNReal in
/-- For `e < -1`, a constant multiple of the shifted real `p`-series `(n + 1) ^ e` has a finite
sum of nonnegative parts in `ℝ≥0∞`. The constant may be negative. -/
theorem tsum_ofReal_mul_natCast_add_one_rpow_lt_top (C : ℝ) {e : ℝ} (he : e < -1) :
    ∑' n : ℕ, ENNReal.ofReal (C * ((n : ℝ) + 1) ^ e) < ∞ := by
  have hsum := ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 he)).mul_left C
  simpa only [Nat.cast_add, Nat.cast_one] using hsum.tsum_ofReal_lt_top

/-- For `N > 0`, `N ^ (q + 1) * (C / (N ^ a) ^ m) ^ q = C ^ q * N ^ (q + 1 - a m q)`. This writes a
union bound over `N ^ (q + 1)` choices of `q` events, each with the Markov tail `C / (N ^ a) ^ m`,
as a single real power of `N`. -/
theorem pow_add_one_mul_div_rpow_pow_pow {N : ℝ} (hN : 0 < N) (C a : ℝ) (m q : ℕ) :
    N ^ (q + 1) * (C / (N ^ a) ^ m) ^ q = C ^ q * N ^ ((q : ℝ) + 1 - a * m * q) := by
  rw [div_pow, ← pow_mul, ← Real.rpow_natCast N (q + 1), ← Real.rpow_mul_natCast hN.le,
    mul_div_left_comm, ← Real.rpow_sub hN]
  push_cast
  ring_nf

end TauCeti

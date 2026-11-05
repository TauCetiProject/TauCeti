/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Lacunary
public import TauCeti.NumberTheory.DiophantineApproximation.Roth.Theorem

/-!
# Transcendence of the lacunary series `∑ b ^ (-r ^ k)` via Roth's theorem

Let `b ≥ 2` and `r ≥ 3` be natural numbers. The lacunary series `x = ∑_{k ≥ 1} b ^ (-r ^ k)` is a
Liouville number with exponent `r > 2`
(`TauCeti.liouvilleWith_tsum_inv_pow_pow`, proved without Roth theory in
`TauCeti.NumberTheory.DiophantineApproximation.Lacunary`), which Roth's theorem
(`IsAlgebraic.not_liouvilleWith`) excludes for algebraic numbers, so `x` is transcendental.
The case `r = 3` is Evertse's Exercise 6.5.

## Main results

* `TauCeti.transcendental_tsum_inv_pow_pow`: for `b ≥ 2` and `r ≥ 3`, `∑_{k ≥ 1} b ^ (-r ^ k)` is
  transcendental.
* `TauCeti.transcendental_tsum_inv_pow_three_pow`: the case `r = 3`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, Exercise 6.5.
-/

public section

namespace TauCeti

/-- **Transcendence of lacunary series.** For natural numbers `b ≥ 2` and `r ≥ 3`, the number
`∑_{k ≥ 1} b ^ (-r ^ k)` is transcendental. It is a Liouville number with exponent `r > 2`
(`TauCeti.liouvilleWith_tsum_inv_pow_pow`), which Roth's theorem excludes for algebraic numbers. -/
theorem transcendental_tsum_inv_pow_pow {b r : ℕ} (hb : 2 ≤ b) (hr : 3 ≤ r) :
    Transcendental ℚ (∑' k : ℕ, ((b : ℝ) ^ r ^ (k + 1))⁻¹) := fun h ↦
  h.not_liouvilleWith (by exact_mod_cast hr) (liouvilleWith_tsum_inv_pow_pow hb (by omega))

/-- **Evertse, Exercise 6.5.** For every natural number `b ≥ 2`, the number
`∑_{k ≥ 1} b ^ (-3 ^ k)` is transcendental. -/
theorem transcendental_tsum_inv_pow_three_pow {b : ℕ} (hb : 2 ≤ b) :
    Transcendental ℚ (∑' k : ℕ, ((b : ℝ) ^ 3 ^ (k + 1))⁻¹) := by
  exact_mod_cast transcendental_tsum_inv_pow_pow hb le_rfl

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Bernoulli
public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Series

/-!
# The Bernoulli-normalized Eisenstein series

This file defines the formal `q`-series `Gₖ(q) = -Bₖ / (2k) + ∑_{n ≥ 1} σₖ₋₁(n) qⁿ` over a
`ℚ`-algebra, built from the divisor-sum series `TauCeti.divisorSumSeries`. Thus
`G₂(0) = -1/24` and `G₄(0) = 1/240`.

## Main definitions

* `TauCeti.eisensteinGSeries A k`: `-Bₖ / (2k) + ∑_{n ≥ 1} σₖ₋₁(n) qⁿ`.
-/

public section

open PowerSeries ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace TauCeti

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The **Bernoulli-normalized Eisenstein series** `Gₖ(q) = -Bₖ / (2k) + ∑_{n ≥ 1} σₖ₋₁(n) qⁿ`,
as a formal power series. For even `k ≥ 4` it is the `q`-expansion of the level-one Eisenstein
series of weight `k`, normalized so that `Eₖ = -(2k / Bₖ) Gₖ`; for `k = 2` it is the
quasimodular `G₂ = -1/24 + q + 3q² + …`. -/
noncomputable def eisensteinGSeries (k : ℕ) : A⟦X⟧ :=
  C (algebraMap ℚ A (-bernoulli k / (2 * k))) + divisorSumSeries (k - 1)

theorem eisensteinGSeries_def (k : ℕ) :
    eisensteinGSeries A k =
      C (algebraMap ℚ A (-bernoulli k / (2 * k))) + divisorSumSeries (k - 1) :=
  (rfl)

@[simp]
theorem coeff_eisensteinGSeries (k n : ℕ) :
    coeff n (eisensteinGSeries A k) =
      if n = 0 then algebraMap ℚ A (-bernoulli k / (2 * k)) else (σ (k - 1) n : A) := by
  rw [eisensteinGSeries_def, map_add, coeff_C, coeff_divisorSumSeries]
  split_ifs with hn <;> simp [hn]

@[simp]
theorem constantCoeff_eisensteinGSeries (k : ℕ) :
    constantCoeff (eisensteinGSeries A k) = algebraMap ℚ A (-bernoulli k / (2 * k)) := by
  simp [eisensteinGSeries_def]

end TauCeti

end

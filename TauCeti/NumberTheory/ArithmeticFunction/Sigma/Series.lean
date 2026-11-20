/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Divisor-sum power series

This file defines the generating series `s_k(q) = ∑_{n ≥ 1} σ_k(n) qⁿ` of the divisor-sum
function `σ k`, and the formal Eisenstein series `G_k(q) = -B_k / (2k) + s_{k-1}(q)` built from it.
For even `k ≥ 4`, `G_k` is the `q`-expansion of a level-one modular form of weight `k`,
normalized so that its higher coefficients are the divisor sums `σ_{k-1}(n)`; `G₂` is the
quasimodular Eisenstein series. In this normalization `log ((X/2) / sinh (X/2))` has
`X^{2k}`-coefficient `2 G_{2k}(0) / (2k)!`, which is why it appears in the characteristic series
of the Witten genus.

## Main definitions

* `TauCeti.divisorSumSeries k`: the power series over a semiring with `n`-th coefficient
  `σ k n`.
* `TauCeti.eisensteinGSeries A k`: the formal Eisenstein series `G_k(q) = -B_k / (2k) + s_{k-1}(q)`
  over a `ℚ`-algebra `A`.
-/

public section

open PowerSeries ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace TauCeti

variable {R : Type*} [Semiring R]

/-- The divisor-sum series `s_k(q) = ∑_{n ≥ 1} σ_k(n) qⁿ` in `R⟦q⟧`, which over any semiring
equals `∑_{n ≥ 1} nᵏ ∑_{m ≥ 1} q^{nm}`; over a ring this is the expansion of the Lambert series
`∑_{n ≥ 1} nᵏ qⁿ / (1 - qⁿ)`. Its constant coefficient is `σ_k(0) = 0`. The coefficient
semiring `R` is implicit, determined by the expected type, as for `PowerSeries.X`. -/
noncomputable def divisorSumSeries (k : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun n ↦ (σ k n : R)

@[simp]
theorem coeff_divisorSumSeries (k n : ℕ) : coeff n (divisorSumSeries k : R⟦X⟧) = σ k n :=
  coeff_mk _ _

@[simp]
theorem constantCoeff_divisorSumSeries (k : ℕ) :
    constantCoeff (divisorSumSeries k : R⟦X⟧) = 0 := by
  simp [← coeff_zero_eq_constantCoeff_apply]

section Eisenstein

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The **formal Eisenstein series** `G_k(q) = -B_k / (2k) + ∑_{n ≥ 1} σ_{k-1}(n) qⁿ` over a
`ℚ`-algebra `A`, in the normalization of Zagier, where `B_k` is `bernoulli k`. It is meant for
even `k ≥ 2`. For even `k ≥ 4` it is `-B_k / (2k)` times the `q`-expansion
`E_k = 1 - (2k / B_k) ∑ σ_{k-1}(n) qⁿ` of the normalized Eisenstein series of weight `k`, and `G₂`
is the quasimodular Eisenstein series of weight `2`. For `k = 0` the junk value `-B₀ / 0 = 0` gives
`G₀ = s₀`. -/
noncomputable def eisensteinGSeries (k : ℕ) : A⟦X⟧ :=
  C (algebraMap ℚ A (-bernoulli k / (2 * k))) + divisorSumSeries (k - 1)

/-- `G_k` is the constant `-B_k / (2k)` plus the divisor-sum series `s_{k-1}`. -/
theorem eisensteinGSeries_def (k : ℕ) :
    eisensteinGSeries A k =
      C (algebraMap ℚ A (-bernoulli k / (2 * k))) + divisorSumSeries (k - 1) :=
  (rfl)

/-- The constant term of `G_k` is `-B_k / (2k)`. -/
@[simp]
theorem constantCoeff_eisensteinGSeries (k : ℕ) :
    constantCoeff (eisensteinGSeries A k) = algebraMap ℚ A (-bernoulli k / (2 * k)) := by
  simp [eisensteinGSeries_def]

/-- The coefficient of `qⁿ` in `G_k`, for `n ≠ 0`, is the divisor sum `σ_{k-1}(n)`. -/
theorem coeff_eisensteinGSeries (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    coeff n (eisensteinGSeries A k) = σ (k - 1) n := by
  rw [eisensteinGSeries_def, map_add, coeff_C]
  simp [hn]

/-- `G₂(q) = -1/24 + ∑ σ₁(n) qⁿ`. -/
theorem constantCoeff_eisensteinGSeries_two :
    constantCoeff (eisensteinGSeries A 2) = algebraMap ℚ A (-1 / 24) := by
  rw [constantCoeff_eisensteinGSeries, bernoulli_two]
  norm_num

/-- `G₄(q) = 1/240 + ∑ σ₃(n) qⁿ`. -/
theorem constantCoeff_eisensteinGSeries_four :
    constantCoeff (eisensteinGSeries A 4) = algebraMap ℚ A (1 / 240) := by
  rw [constantCoeff_eisensteinGSeries, bernoulli_eq_bernoulli'_of_ne_one (by decide),
    bernoulli'_four]
  norm_num

end Eisenstein

end TauCeti

end

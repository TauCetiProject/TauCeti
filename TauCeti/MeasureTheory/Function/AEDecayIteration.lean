/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Iterating a reduction of almost-everywhere bounds on shrinking balls

Let `g` be a function on a metric space with a measure `μ`, and `s` a set. Suppose that an
almost-everywhere bound `g ≤ M'` on `s ∩ B(x₀, 2ρ)` always improves to

`g ≤ c M' + A ρ^γ` almost everywhere on `s ∩ B(x₀, ρ/2)`,

with a contraction factor `c` and an error `A ρ^γ`, `A, γ ≥ 0`. Then a bound `g ≤ M` on
`s ∩ B(x₀, R)`, `M ≥ 0`, decays geometrically along the balls `B(x₀, R / 4ʲ)`:

`g ≤ τʲ (M + D)` almost everywhere on `s ∩ B(x₀, R / 4ʲ)`

for every rate `τ ≥ c` with `τ ≥ 4^(-γ)`, and every `D ≥ 0` with `A R^γ ≤ (τ - c) D`. For `c < τ`
the smallest such `D` is `A R^γ / (τ - c)`.

This is how De Giorgi's reduction of the supremum, at interior or boundary points and with or
without a right-hand side, is iterated into a power decay of the supremum.

## Main declarations

* `TauCeti.ae_le_pow_mul_add_of_forall_ae_le_mul_add`: the iteration.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 8.23 and Theorem 8.29.
-/

public section

open MeasureTheory Metric Set

namespace TauCeti

/-- The radius factor of the iteration: for `R > 0`, `γ ≥ 0` and a rate `τ` with `4^(-γ) ≤ τ`,
the radii `R / 4ʲ / 2` satisfy `(R / 4ʲ / 2)^γ ≤ R^γ τʲ`. -/
private theorem rpow_div_pow_div_two_le_mul_pow {R γ τ : ℝ} (hR : 0 < R) (hγ : 0 ≤ γ)
    (hτ : (4 : ℝ) ^ (-γ) ≤ τ) (j : ℕ) : (R / 4 ^ j / 2) ^ γ ≤ R ^ γ * τ ^ j := by
  have hpow : (R / 4 ^ j) ^ γ = R ^ γ * ((4 : ℝ) ^ (-γ)) ^ j := by
    rw [Real.div_rpow hR.le (by positivity), ← Real.rpow_natCast_mul (by norm_num),
      mul_comm (j : ℝ), Real.rpow_mul_natCast (by norm_num), Real.rpow_neg (by norm_num),
      inv_pow, div_eq_mul_inv]
  calc (R / 4 ^ j / 2) ^ γ ≤ (R / 4 ^ j) ^ γ :=
        Real.rpow_le_rpow (by positivity) (half_le_self (by positivity)) hγ
    _ = R ^ γ * ((4 : ℝ) ^ (-γ)) ^ j := hpow
    _ ≤ R ^ γ * τ ^ j := by gcongr

/-- The arithmetic of one step of the iteration: if the reduction contracts by `c ≤ τ` and the
error is at most `τʲ (τ - c) D`, then the bound `τʲ (M + D)` improves to `τʲ⁺¹ (M + D)`. -/
private theorem mul_add_le_pow_succ_mul {c τ M D E : ℝ} (j : ℕ) (hτ : 0 ≤ τ) (hcτ : c ≤ τ)
    (hM : 0 ≤ M) (hE : E ≤ τ ^ j * ((τ - c) * D)) :
    c * (τ ^ j * (M + D)) + E ≤ τ ^ (j + 1) * (M + D) := by
  have hgap : τ ^ j * ((τ - c) * D) ≤ τ ^ j * ((τ - c) * (M + D)) := by
    have : 0 ≤ τ - c := by linarith
    gcongr
    linarith
  have hid : c * (τ ^ j * (M + D)) + τ ^ j * ((τ - c) * (M + D)) = τ ^ (j + 1) * (M + D) := by
    ring
  linarith

/-- **Iterating a reduction of almost-everywhere bounds on shrinking balls.** Suppose that a bound
`g ≤ M'` almost everywhere on `s ∩ B(x₀, 2ρ)`, `2ρ ≤ R`, always improves to `g ≤ c M' + A ρ^γ`
almost everywhere on `s ∩ B(x₀, ρ/2)`, with `A ≥ 0` and `γ ≥ 0`, and that `g ≤ M` almost
everywhere on `s ∩ B(x₀, R)` with `M ≥ 0`. Let the rate `τ` satisfy `c ≤ τ` and `4^(-γ) ≤ τ`, and
let `D ≥ 0` with `A R^γ ≤ (τ - c) D`. Then for every `j`

`g ≤ τʲ (M + D)` almost everywhere on `s ∩ B(x₀, R / 4ʲ)`. -/
theorem ae_le_pow_mul_add_of_forall_ae_le_mul_add {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] {mu : Measure X} {s : Set X} {g : X → ℝ} {x₀ : X} {R M A D γ c τ : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hA : 0 ≤ A) (hD : 0 ≤ D) (hγ : 0 ≤ γ) (hcτ : c ≤ τ)
    (hτ : (4 : ℝ) ^ (-γ) ≤ τ) (hAD : A * R ^ γ ≤ (τ - c) * D)
    (hle : ∀ᵐ x ∂mu.restrict (s ∩ ball x₀ R), g x ≤ M)
    (hstep : ∀ ρ M', 0 < ρ → 2 * ρ ≤ R → (∀ᵐ x ∂mu.restrict (s ∩ ball x₀ (2 * ρ)), g x ≤ M') →
      ∀ᵐ x ∂mu.restrict (s ∩ ball x₀ (ρ / 2)), g x ≤ c * M' + A * ρ ^ γ) (j : ℕ) :
    ∀ᵐ x ∂mu.restrict (s ∩ ball x₀ (R / 4 ^ j)), g x ≤ τ ^ j * (M + D) := by
  have hτ0 : 0 ≤ τ := (Real.rpow_nonneg (by norm_num) _).trans hτ
  induction j with
  | zero => simpa using hle.mono fun x hx => hx.trans (le_add_of_nonneg_right hD)
  | succ j ih =>
    -- One step from `B(x₀, 2ρ)` to `B(x₀, ρ / 2)`, with `2ρ = R / 4ʲ`.
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = R / 4 ^ j / 2 := ⟨_, rfl⟩
    have h2ρ : R / 4 ^ j = 2 * ρ := by rw [hρdef]; ring
    have hρR : 2 * ρ ≤ R := h2ρ ▸ div_le_self hR.le (one_le_pow₀ (by norm_num))
    have hρ2 : R / 4 ^ (j + 1) = ρ / 2 := by rw [hρdef, pow_succ]; ring
    have hρ : 0 < ρ := by rw [hρdef]; positivity
    have hργ : ρ ^ γ ≤ R ^ γ * τ ^ j := hρdef ▸ rpow_div_pow_div_two_le_mul_pow hR hγ hτ j
    have herr : A * ρ ^ γ ≤ τ ^ j * ((τ - c) * D) :=
      calc _ ≤ A * (R ^ γ * τ ^ j) := by gcongr
        _ = τ ^ j * (A * R ^ γ) := by ring
        _ ≤ _ := by gcongr
    have hnext := mul_add_le_pow_succ_mul j hτ0 hcτ hM herr
    rw [hρ2]
    filter_upwards [hstep ρ _ hρ hρR (by rw [← h2ρ]; exact ih)] with x hx
    linarith

end TauCeti

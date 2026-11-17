/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Geometric decay of almost everywhere bounds along concentric balls

Let `g` be a real function on a pseudo-metric space with a measure, let `S` be a set and let
`B(x₀, ρ)` denote the open balls around a point `x₀`. Suppose that an almost everywhere bound
`g ≤ M'` on `S ∩ B(x₀, 2ρ)` always improves to

`g ≤ (1 - δ) M' + A (ρ / R)^γ` almost everywhere on `S ∩ B(x₀, ρ/2)`

whenever `0 < ρ` and `2ρ ≤ R`, with `δ, γ, A ≥ 0`. Then from `g ≤ M` on `S ∩ B(x₀, R)`
follows

`g ≤ σʲ (M + 2A/δ)` almost everywhere on `S ∩ B(x₀, R / 4ʲ)`, where `σ = max (1 - δ/2) 4^(-γ)`.

Each step shrinks the bound by `1 - δ` and adds an error that itself decays by `4^(-γ)` from one
ball to the next, so for `δ, γ > 0` both decay like `σʲ` with `σ < 1`. This is the iteration
that turns De Giorgi's reduction of the supremum, with the error term of a right-hand side, into a
Hölder modulus: in the boundary version, `S` is the domain `Ω` and the balls are centred at a
boundary point.

## Main declarations

* `TauCeti.ae_le_pow_mul_add_of_forall_ae_le_mul_add`: the iteration.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 8.23 and Theorem 8.27.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set

/-- The arithmetic of one step of geometric decay: for `σ ≥ 1 - δ/2`, a bound `σʲ Q` with
`Q = M + 2A/δ`, `M, A ≥ 0`, reduced by the factor `1 - δ` and increased by at most `A σʲ`, is at
most `σʲ⁺¹ Q`. -/
private theorem mul_pow_mul_add_le_pow_succ_mul {δ σ M A E : ℝ} (j : ℕ) (hδ : 0 < δ)
    (hσ0 : 0 ≤ σ) (hσ : 1 - δ / 2 ≤ σ) (hM : 0 ≤ M) (hA : 0 ≤ A) (hE : E ≤ A * σ ^ j) :
    (1 - δ) * (σ ^ j * (M + 2 / δ * A)) + E ≤ σ ^ (j + 1) * (M + 2 / δ * A) := by
  set Q := M + 2 / δ * A with hQ_def
  have hQ : 0 ≤ Q := by positivity
  -- `A ≤ δ/2 · Q` and `σ - 1 + δ ≥ δ/2`.
  have hAQ : A ≤ δ / 2 * Q := by
    have hQ' : δ / 2 * Q = δ / 2 * M + A := by
      rw [hQ_def]
      field_simp
    have : 0 ≤ δ / 2 * M := by positivity
    linarith
  have hkey : 0 ≤ σ ^ j * ((σ - 1 + δ) * Q - A) := by
    refine mul_nonneg (pow_nonneg hσ0 j) ?_
    have : δ / 2 * Q ≤ (σ - 1 + δ) * Q := mul_le_mul_of_nonneg_right (by linarith) hQ
    linarith
  have hexpand : σ ^ (j + 1) * Q - ((1 - δ) * (σ ^ j * Q) + A * σ ^ j) =
      σ ^ j * ((σ - 1 + δ) * Q - A) := by
    ring
  linarith

/-- **Geometric decay along concentric balls.** Let `δ, γ, A ≥ 0`. If an almost everywhere bound
`g ≤ M'` on `S ∩ B(x₀, 2ρ)` always improves to `g ≤ (1 - δ) M' + A (ρ/R)^γ` on `S ∩ B(x₀, ρ/2)`
when `0 < ρ` and `2ρ ≤ R`, then from `g ≤ M` on `S ∩ B(x₀, R)` follows
`g ≤ σʲ (M + 2A/δ)` on `S ∩ B(x₀, R / 4ʲ)`, with `σ = max (1 - δ/2) 4^(-γ)`.

For `δ = 0` the bound is `M` (with `2A/0 = 0`), and for `M < 0` it already follows from
`g ≤ M`. -/
theorem ae_le_pow_mul_add_of_forall_ae_le_mul_add {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] {mu : Measure X} {S : Set X} {g : X → ℝ} {x₀ : X} {R M A δ γ : ℝ}
    (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hA : 0 ≤ A)
    (hle : ∀ᵐ x ∂mu.restrict (S ∩ ball x₀ R), g x ≤ M)
    (hstep : ∀ ρ M', 0 < ρ → 2 * ρ ≤ R →
      (∀ᵐ x ∂mu.restrict (S ∩ ball x₀ (2 * ρ)), g x ≤ M') →
        ∀ᵐ x ∂mu.restrict (S ∩ ball x₀ (ρ / 2)), g x ≤ (1 - δ) * M' + A * (ρ / R) ^ γ)
    (j : ℕ) :
    ∀ᵐ x ∂mu.restrict (S ∩ ball x₀ (R / 4 ^ j)),
      g x ≤ max (1 - δ / 2) ((4 : ℝ) ^ γ)⁻¹ ^ j * (M + 2 / δ * A) := by
  rcases le_or_gt R 0 with hR | hR
  · -- For `R ≤ 0` the balls are empty.
    simp [ball_eq_empty.2 (div_nonpos_of_nonpos_of_nonneg hR (by positivity) : R / 4 ^ j ≤ 0)]
  set τ : ℝ := ((4 : ℝ) ^ γ)⁻¹ with hτ_def
  have hτ0 : 0 ≤ τ := by positivity
  have hτ1 : τ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow (by norm_num) hγ)
  have hσ0 : 0 ≤ max (1 - δ / 2) τ := hτ0.trans (le_max_right _ _)
  by_cases hδM : 0 < δ ∧ 0 ≤ M
  swap
  · -- For `δ = 0` or `M < 0`, the bound `g ≤ M` on `S ∩ B(x₀, R)` is already enough.
    have hMle : M ≤ max (1 - δ / 2) τ ^ j * (M + 2 / δ * A) := by
      rcases hδ.eq_or_lt with rfl | hδ'
      · simp [max_eq_left hτ1]
      · have hM : M < 0 := not_le.1 fun hM => hδM ⟨hδ', hM⟩
        have hσj0 : 0 ≤ max (1 - δ / 2) τ ^ j := pow_nonneg hσ0 j
        have hσj1 : max (1 - δ / 2) τ ^ j ≤ 1 := pow_le_one₀ hσ0 (max_le (by linarith) hτ1)
        have : 0 ≤ 2 / δ * A := by positivity
        nlinarith
    have hRj : R / 4 ^ j ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (inter_subset_inter_right _ (ball_subset_ball hRj)) hle] with x hx
    exact hx.trans hMle
  obtain ⟨hδ, hM⟩ := hδM
  induction j with
  | zero =>
    have : 0 ≤ 2 / δ * A := by positivity
    simpa using hle.mono fun x hx => hx.trans (by linarith)
  | succ j ih =>
    -- One step from `B(x₀, 2ρ)` to `B(x₀, ρ / 2)`, with `2ρ = R / 4ʲ`.
    set ρ := R / 4 ^ j / 2 with hρ_def
    have h2ρ : R / 4 ^ j = 2 * ρ := by rw [hρ_def]; ring
    have hρ2 : R / 4 ^ (j + 1) = ρ / 2 := by rw [hρ_def, pow_succ]; ring
    have hρ : 0 < ρ := by positivity
    have hρR : 2 * ρ ≤ R := by
      rw [← h2ρ]
      exact div_le_self hR.le (one_le_pow₀ (by norm_num))
    rw [h2ρ] at ih
    rw [hρ2]
    refine (hstep ρ _ hρ hρR ih).mono fun x hx => hx.trans
      (mul_pow_mul_add_le_pow_succ_mul j hδ hσ0 (le_max_left _ _) hM hA ?_)
    -- `(ρ / R)^γ ≤ (4ʲ)^(-γ) = τʲ ≤ σʲ`.
    have h4j : ((4 : ℝ) ^ j) ^ γ = ((4 : ℝ) ^ γ) ^ j := by
      rw [← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_mul_natCast (by norm_num), mul_comm]
    have hργ : (ρ / R) ^ γ ≤ τ ^ j := by
      calc (ρ / R) ^ γ ≤ ((4 : ℝ) ^ j)⁻¹ ^ γ := by
            refine Real.rpow_le_rpow (by positivity) ?_ hγ
            rw [div_le_iff₀ hR, ← div_eq_inv_mul]
            linarith
        _ = τ ^ j := by rw [Real.inv_rpow (by positivity), h4j, hτ_def, inv_pow]
    exact mul_le_mul_of_nonneg_left (hργ.trans (pow_le_pow_left₀ hτ0 (le_max_right _ _) j)) hA

end TauCeti

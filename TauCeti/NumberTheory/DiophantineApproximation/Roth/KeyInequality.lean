/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Roth.DerivativeSelection
public import TauCeti.NumberTheory.DiophantineApproximation.Roth.ValueBounds
public import TauCeti.NumberTheory.Height.Rat

/-!
# The key inequality in the proof of Roth's theorem

Let `α` be a real number and let `β ∈ ℚⁿ` be a tuple of rational approximations of `α` with
`|βᵢ - α| ≤ H(βᵢ) ^ (-κ)`. Let `P ∈ ℤ[X₁, …, Xₙ]` be an auxiliary polynomial with partial degrees
`degreeOf i P ≤ rᵢ`, coefficients at most `exp (C₁ ∑ᵢ rᵢ)` in absolute value, and weighted index
at least `(n / 2) (1 - ε)` at the diagonal point `(α, …, α)`. Suppose that the weighted index of
`P` at `β` is at most `5 n ε / 2`, as Roth's lemma guarantees for approximations of rapidly
increasing heights.

Then a Hasse derivative `Q` of `P` does not vanish at `β` and still has index at least
`t = (1 / 2 - 3 ε) n` at the diagonal point (`TauCeti.exists_roth_hasseDeriv`). Comparing the
lower bound `log |Q(β)| ≥ -∑ᵢ rᵢ log den(βᵢ)` with the upper bound coming from the Taylor
expansion of `Q` at the diagonal point (`TauCeti.log_abs_eval_le_of_le_weightedIndex`) gives the
inequality

`κ D' t ≤ n D + C₂ D / L`, where `C₂ = 4 C₁ + 2 log (2 max(1, |α|)) + 4`,

whenever `D' ≤ rᵢ h(βᵢ) ≤ D` for all `i` and `∑ᵢ rᵢ ≤ 2 D / L`. With `rᵢ = ⌊D / h(βᵢ)⌋` the
ratio `D' / D` tends to `1` as `D` grows, so for `L` large this forces
`κ (1 / 2 - 3 ε) ≤ 1 + o(1)`, which is false once `κ > 2` and `ε` is small. This is the
contradiction that proves Roth's theorem.

## Main results

* `TauCeti.roth_key_inequality_of_eval_ne_zero`: for an integer polynomial `Q` with `Q(β) ≠ 0`
  and weighted index at least `t` at a point `a`,
  `κ D' t ≤ ∑ᵢ rᵢ h(βᵢ) + log B + ∑ᵢ rᵢ (log 2 + log max(1, |aᵢ|)) + 2 ∑ᵢ log (rᵢ + 1)`.
* `TauCeti.roth_key_inequality`: Pottmeyer's inequality (3.42) over `ℚ`,
  `κ D' (1 / 2 - 3 ε) n ≤ n D + C₂ D / L`, for an auxiliary polynomial of small index at `β`.

## References

* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), §3.5.3 and §3.5.4, inequalities (3.40)–(3.42).
-/

public section

namespace TauCeti

open MvPolynomial Finset Height

variable {σ : Type*} [Fintype σ]

/-- **The key inequality for a nonvanishing polynomial.** Let `Q ∈ ℤ[X]` have partial degrees
`degreeOf i Q ≤ r i`, coefficients bounded by `B` in absolute value, and weighted index at least
`t` at `a ∈ ℝ^σ`. If `β ∈ ℚ^σ` satisfies `|βᵢ - aᵢ| ≤ H(βᵢ) ^ (-κ)` and `D ≤ rᵢ h(βᵢ)`, with
`κ, D ≥ 0`, and `Q(β) ≠ 0`, then
`κ D t ≤ ∑ᵢ rᵢ h(βᵢ) + log B + ∑ᵢ rᵢ (log 2 + log max(1, |aᵢ|)) + 2 ∑ᵢ log (rᵢ + 1)`. -/
theorem roth_key_inequality_of_eval_ne_zero {Q : MvPolynomial σ ℤ} {r : σ → ℕ}
    (hdeg : ∀ i, Q.degreeOf i ≤ r i) {B : ℝ} (hB : ∀ μ, |(Q.coeff μ : ℝ)| ≤ B) {a : σ → ℝ}
    {t : ℝ} (ht : ENNReal.ofReal t ≤ weightedIndex r a (Q.map (Int.castRingHom ℝ)))
    {β : σ → ℚ} {κ D : ℝ} (hκ : 0 ≤ κ) (hD : 0 ≤ D)
    (hβ : ∀ i, |(β i : ℝ) - a i| ≤ mulHeight₁ (β i) ^ (-κ))
    (hr : ∀ i, D ≤ r i * logHeight₁ (β i)) (hQ : eval β (Q.map (Int.castRingHom ℚ)) ≠ 0) :
    κ * D * t ≤ ∑ i, r i * logHeight₁ (β i) + Real.log B +
      ∑ i, r i * (Real.log 2 + Real.log (max 1 |a i|)) + 2 * ∑ i, Real.log (r i + 1) := by
  have hcast : eval (fun i ↦ (β i : ℝ)) (Q.map (Int.castRingHom ℝ)) =
      ((eval β (Q.map (Int.castRingHom ℚ)) : ℚ) : ℝ) := by
    simp [eval_map, eval₂_eq']
  have hQ' : eval (fun i ↦ (β i : ℝ)) (Q.map (Int.castRingHom ℝ)) ≠ 0 := by
    rw [hcast]
    exact_mod_cast hQ
  have hdeg' (i : σ) : (Q.map (Int.castRingHom ℝ)).degreeOf i ≤ r i :=
    degreeOf_le_iff.2 fun μ hμ ↦ degreeOf_le_iff.1 (hdeg i) μ (support_map_subset _ _ hμ)
  have hlow := neg_sum_mul_log_den_le_log_abs_eval hdeg β hQ'
  have hup := log_abs_eval_le_of_le_weightedIndex hdeg' (fun μ ↦ by simpa [coeff_map] using hB μ)
    ht hκ hD hβ hr hQ'
  have hden : ∑ i, (r i : ℝ) * Real.log (β i).den ≤ ∑ i, r i * logHeight₁ (β i) :=
    sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_left (Rat.log_den_le_logHeight₁ _) (Nat.cast_nonneg _)
  linarith

/-- **The key inequality in the proof of Roth's theorem** (Pottmeyer, (3.42) over `ℚ`). Let
`P ∈ ℤ[X]` have partial degrees `degreeOf i P ≤ r i`, where `∑ᵢ rᵢ ≤ 2 D / L`, coefficients at
most `exp (C₁ ∑ᵢ rᵢ)` in absolute value, where `C₁ ≥ log 2`, and weighted index at least
`(n / 2) (1 - ε)` at the diagonal point `(α, …, α)`, with `0 ≤ ε`. Let `β ∈ ℚ^σ` satisfy
`|βᵢ - α| ≤ H(βᵢ) ^ (-κ)` and `D' ≤ rᵢ h(βᵢ) ≤ D`, with `κ, D' ≥ 0`. If the weighted index of
`P` at `β` is at most `5 n ε / 2`, then
`κ D' (1 / 2 - 3 ε) n ≤ n D + (4 C₁ + 2 log (2 max(1, |α|)) + 4) D / L`. -/
theorem roth_key_inequality {P : MvPolynomial σ ℤ} {r : σ → ℕ}
    (hdeg : ∀ i, P.degreeOf i ≤ r i) {ε C₁ D L : ℝ} (hε : 0 ≤ ε) (hC₁ : Real.log 2 ≤ C₁)
    (hr : ∑ i, (r i : ℝ) ≤ 2 * D / L)
    (hP : ∀ μ, |(P.coeff μ : ℝ)| ≤ Real.exp (C₁ * ∑ i, (r i : ℝ))) {α : ℝ}
    (hα : ENNReal.ofReal (Fintype.card σ / 2 * (1 - ε)) ≤
      weightedIndex r (fun _ ↦ α) (P.map (Int.castRingHom ℝ)))
    {β : σ → ℚ} (hβP : weightedIndex r β (P.map (Int.castRingHom ℚ)) ≤
      ENNReal.ofReal (5 * Fintype.card σ * ε / 2))
    {κ D' : ℝ} (hκ : 0 ≤ κ) (hD' : 0 ≤ D') (hβ : ∀ i, |(β i : ℝ) - α| ≤ mulHeight₁ (β i) ^ (-κ))
    (hlow : ∀ i, D' ≤ r i * logHeight₁ (β i)) (hup : ∀ i, r i * logHeight₁ (β i) ≤ D) :
    κ * D' * ((1 / 2 - 3 * ε) * Fintype.card σ) ≤
      Fintype.card σ * D + (4 * C₁ + 2 * Real.log (2 * max 1 |α|) + 4) * D / L := by
  obtain ⟨d, hne, hind, hdeg', hcoeff⟩ := exists_roth_hasseDeriv hdeg hε hC₁ hr hP hα hβP
  have key := roth_key_inequality_of_eval_ne_zero hdeg' hcoeff hind hκ hD' hβ hlow hne
  rw [Real.log_exp] at key
  -- Bound the three error terms by `n D`, `log (2 max(1, |α|)) ∑ᵢ rᵢ` and `2 ∑ᵢ rᵢ`.
  have hheight : ∑ i, (r i : ℝ) * logHeight₁ (β i) ≤ Fintype.card σ * D := by
    simpa using sum_le_sum fun i (_ : i ∈ univ) ↦ hup i
  have hc : Real.log 2 + Real.log (max 1 |α|) = Real.log (2 * max 1 |α|) :=
    (Real.log_mul two_ne_zero (by positivity)).symm
  have hc₀ : 0 ≤ Real.log (2 * max 1 |α|) :=
    Real.log_nonneg (by nlinarith [le_max_left 1 |α|])
  have hlin : ∑ i, (r i : ℝ) * (Real.log 2 + Real.log (max 1 |α|)) ≤
      2 * D / L * Real.log (2 * max 1 |α|) := by
    rw [← sum_mul, hc]
    exact mul_le_mul_of_nonneg_right hr hc₀
  have hlog : ∑ i, Real.log ((r i : ℝ) + 1) ≤ 2 * D / L :=
    (sum_le_sum fun i _ ↦ by linarith [Real.log_le_sub_one_of_pos (by positivity :
      (0 : ℝ) < r i + 1)]).trans hr
  have hsplit : (4 * C₁ + 2 * Real.log (2 * max 1 |α|) + 4) * D / L =
      4 * C₁ * D / L + 2 * D / L * Real.log (2 * max 1 |α|) + 2 * (2 * D / L) := by
    ring
  linarith

end TauCeti

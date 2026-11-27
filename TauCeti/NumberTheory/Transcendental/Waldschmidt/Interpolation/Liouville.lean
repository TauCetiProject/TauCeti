/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Data
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.EqOne

/-!
# The Liouville bound for a rational coefficient relation

In the rank argument of Waldschmidt's proof of his lower bound for linear forms in logarithms
(W00 §9.2.3, §9.3.2), the normalized linear form is

`Λ = β₀ + β₁ λ₁ + ⋯ + β_{m-1} λ_{m-1} - λₘ`,

with coefficient vector `c = (β₁, …, β_{m-1}, -1)`. One excluded case of the zero estimate is
`β₀ = 0` together with a nonzero integral vector `s` on the line `ℂ c`. Any such `s` is a rational
coefficient relation (`TauCeti.eq_neg_div_of_intCast_mem_span_snoc`): `sₘ ≠ 0` and
`β_k = -s_k / sₘ`, so that

`sₘ Λ = -(s₁ λ₁ + ⋯ + sₘ λₘ)`, i.e. `exp(-sₘ Λ) = α₁ ^ s₁ ⋯ αₘ ^ sₘ`,

where `αⱼ = exp λⱼ`. This module proves the resulting lower bound on `|sₘ| |Λ|`. A lower bound
`δ ≤ |α^s - 1|`, which Liouville's inequality `RingHom.exp_neg_le_norm_prod_zpow_sub_one_of_le`
supplies when the `αⱼ` are algebraic and `α^s ≠ 1`, gives `min 1 (δ / 2) ≤ |sₘ| |Λ|`. When
`α^s = 1`, the number `sₘ Λ` is a nonzero multiple of `2πi` as soon as `Λ ≠ 0`.

In the rank argument the vector `s` is a sum of differences of grid indices, so the grid also
bounds `|sₘ|` from above; it is this size bound, not span membership, that makes `s` a short
relation. Ruling out the case then still needs a comparison of the bound proved here, divided by
that bound on `|sₘ|`, with the smallness of `|Λ|` assumed in the proof.

Throughout, `m = n + 1`, with the indexing conventions of
`TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Data`.

## Main results

* `TauCeti.exp_neg_intCast_mul_waldschmidtLinearForm`: for a rational coefficient relation with
  `β₀ = 0`, `exp(-sₘ Λ) = α^s`.
* `TauCeti.last_ne_zero_and_min_one_div_two_le_abs_mul_norm_waldschmidtLinearForm_of_mem_span`:
  a nonzero integral vector `s` on the line `ℂ c` has `sₘ ≠ 0`, and if `β₀ = 0`, `Λ ≠ 0` and
  `δ ≤ |α^s - 1|` whenever `α^s ≠ 1`, then `min 1 (δ / 2) ≤ |sₘ| |Λ|`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §9.2.3 and §9.3.2, Step 2.

The formalization is adapted from split 5 of the
[lookahead development](https://github.com/roed-math/TauCeti-w2-fresh/tree/lookahead/DiophantineApproximationAndTranscendence/waldschmidt-interpolation-rank)
of Waldschmidt's interpolation rank argument, at commit `490d2d4`
(<https://github.com/roed-math/TauCeti-w2-fresh/tree/490d2d42b068e7f3910b4660ba01f5d8f94445b2>).
-/

public section

open Complex Finset

namespace TauCeti

variable {n : ℕ}

/-- The exponential form of `TauCeti.intCast_mul_waldschmidtLinearForm_eq_neg_sum`: for a
rational coefficient relation with `β₀ = 0`, `exp(-sₘ Λ) = α₁ ^ s₁ ⋯ αₘ ^ sₘ` with
`αⱼ = exp λⱼ`. So `Λ ≠ 0` as soon as `α^s ≠ 1`. -/
theorem exp_neg_intCast_mul_waldschmidtLinearForm (l b : Fin (n + 1) → ℂ)
    {s : Fin (n + 1) → ℤ} (hlast : s (Fin.last n) ≠ 0) (hb₀ : b 0 = 0)
    (hb : ∀ k : Fin n, b k.succ = -(s k.castSucc : ℂ) / s (Fin.last n)) :
    cexp (-((s (Fin.last n) : ℂ) * waldschmidtLinearForm l b)) = ∏ j, cexp (l j) ^ s j := by
  rw [intCast_mul_waldschmidtLinearForm_eq_neg_sum l b hlast hb₀ hb, neg_neg, Complex.exp_sum]
  exact prod_congr rfl fun j _ ↦ Complex.exp_intCast_mul (s j) (l j)

/-- The Liouville bound in the form the excluded case `β₀ = 0`, `(S - S)[2] ∩ ℂ c ≠ {0}`
presents it: a nonzero integral vector `s` on the line through `c = (β₁, …, β_{m-1}, -1)` has
`sₘ ≠ 0`, and if `Λ ≠ 0` and `δ ≤ |α^s - 1|` whenever `α^s ≠ 1` (for instance by Liouville's
inequality, `RingHom.exp_neg_le_norm_prod_zpow_sub_one_of_le`), then
`min 1 (δ / 2) ≤ |sₘ| |Λ|`. This is because `exp(-sₘ Λ) = α^s`
(`TauCeti.exp_neg_intCast_mul_waldschmidtLinearForm`): if `α^s ≠ 1`, then
`min 1 (|α^s - 1| / 2) ≤ |sₘ Λ|`, and if `α^s = 1`, then `sₘ Λ` is a nonzero multiple of `2πi`. -/
theorem last_ne_zero_and_min_one_div_two_le_abs_mul_norm_waldschmidtLinearForm_of_mem_span
    (l b : Fin (n + 1) → ℂ) {s : Fin (n + 1) → ℤ} (hs : s ≠ 0)
    (hmem : (fun i ↦ (s i : ℂ)) ∈ ℂ ∙ Fin.snoc (fun k : Fin n ↦ b k.succ) (-1)) (hb₀ : b 0 = 0)
    (hΛ : waldschmidtLinearForm l b ≠ 0) {δ : ℝ}
    (hδ : ∏ j, cexp (l j) ^ s j ≠ 1 → δ ≤ ‖∏ j, cexp (l j) ^ s j - 1‖) :
    s (Fin.last n) ≠ 0 ∧
      min 1 (δ / 2) ≤ |(s (Fin.last n) : ℝ)| * ‖waldschmidtLinearForm l b‖ := by
  obtain ⟨hlast, hb⟩ := eq_neg_div_of_intCast_mem_span_snoc b hs hmem
  refine ⟨hlast, ?_⟩
  rw [← exp_neg_intCast_mul_waldschmidtLinearForm l b hlast hb₀ hb] at hδ
  rw [← Complex.norm_intCast, ← norm_mul, ← norm_neg]
  by_cases hα : cexp (-((s (Fin.last n) : ℂ) * waldschmidtLinearForm l b)) = 1
  · refine min_le_of_left_le (le_of_not_gt fun hlt ↦ ?_)
    exact neg_ne_zero.2 (mul_ne_zero (Int.cast_ne_zero.2 hlast) hΛ)
      (Complex.eq_zero_of_exp_eq_one_of_norm_lt hα (by linarith [Real.two_le_pi]))
  · exact (min_le_min_left 1 (by linarith [hδ hα])).trans
      (Complex.min_one_norm_exp_sub_one_div_two_le_norm _)

end TauCeti

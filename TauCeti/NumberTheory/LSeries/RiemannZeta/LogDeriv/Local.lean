/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.Analysis.Meromorphic.Divisor
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.LSeries.DirichletEulerLog
import TauCeti.NumberTheory.LSeries.RiemannZeta.Growth
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne

/-!
# The local expansion of the logarithmic derivative of the Riemann zeta function

Fix a real `σ₀ > 1` and radii `r < r'`. There is a constant `C`, depending only on
`σ₀, r, r'`, such that for every centre `s₀` with `Re s₀ = σ₀` and every `s ≠ 1` with
`‖s - s₀‖ ≤ r` and `ζ(s) ≠ 0`,
`‖ζ′/ζ(s) + 1/(s - 1) - ∑_{‖ρ - s₀‖ ≤ r'} m(ρ)/(s - ρ)‖ ≤ C log(|Im s₀| + 2)`.
The sum runs over every zero `ρ` of `ζ` in the closed disc, trivial zeros included, weighted by
its analytic order `m(ρ)`.

## Main results

* `TauCeti.divisor_LFunctionTrivChar₁_one_closedBall_apply`: the divisor of
  `LFunctionTrivChar₁ 1` on a closed disc records the orders of the zeros of `ζ` in the disc.
* `TauCeti.finsum_subtype_riemannZeta_eq_finsum_divisor`: the order-weighted sum over the zeros
  of `ζ` in a closed disc is the divisor sum of `LFunctionTrivChar₁ 1` on that disc.
* `TauCeti.exists_norm_LFunctionTrivChar₁_one_le_rpow_mul`: on discs centred on a line
  `Re s₀ = σ₀ > 1`, `‖(w - 1) ζ(w)‖ ≤ (|Im s₀| + 2) ^ D ‖(s₀ - 1) ζ(s₀)‖`.
* `TauCeti.riemannZeta_local_logDeriv`: the local expansion of `ζ′/ζ`.

## Implementation notes

The entire function `LFunctionTrivChar₁ 1` has logarithmic derivative `ζ′/ζ(s) + 1/(s - 1)` and
the same zeros and orders as `ζ`. Landau's local lemma, in the uniform
form `TauCeti.exists_norm_logDeriv_sub_finsum_divisor_le`, on the discs of radii `r'` and `r' + 1`
about `s₀` turns a relative growth bound into the expansion. That bound,
`TauCeti.exists_norm_LFunctionTrivChar₁_one_le_rpow_mul`, combines the disc bound
`TauCeti.exists_norm_LFunctionTrivChar₁_one_le_rpow_of_norm_sub_le` with the centre lower bound
`‖(s₀ - 1) ζ(s₀)‖ ≥ (σ₀ - 1) exp(-Re ζ(σ₀))` from
`DirichletCharacter.exp_neg_re_riemannZeta_le_norm_LFunction`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Lemma 8.6, pp.90–91, and
  Lemma 11.2, p.113.
* PrimeNumberTheoremAnd, `StrongPNT.lean` at revision `df0ccba`, proves a weaker `log²` bound on
  a fixed window about `3/2 + i t`; this file follows the nested-disc route instead.
-/

public section

open Complex DirichletCharacter Metric Set Filter Topology

namespace TauCeti

/-- On a closed disc, the divisor of the entire function `LFunctionTrivChar₁ 1` is the analytic
order of `ζ` at its zeros in the disc, and zero elsewhere. -/
theorem divisor_LFunctionTrivChar₁_one_closedBall_apply (s₀ ρ : ℂ) (r' : ℝ) :
    MeromorphicOn.divisor (LFunctionTrivChar₁ 1) (closedBall s₀ r') ρ =
      if ‖ρ - s₀‖ ≤ r' ∧ riemannZeta ρ = 0 then ((analyticOrderAt riemannZeta ρ).toNat : ℤ)
      else 0 := by
  have hF := (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd isOpen_univ
  rw [(hF.mono (subset_univ _)).divisor_closedBall_apply]
  by_cases hρ : ‖ρ - s₀‖ ≤ r' ∧ riemannZeta ρ = 0
  · have hρ1 : ρ ≠ 1 := by
      rintro rfl
      exact riemannZeta_one_ne_zero hρ.2
    rw [ite_eq_left ⟨hρ.1, by rw [LFunctionTrivChar₁_one_apply_of_ne_one hρ1, hρ.2, mul_zero]⟩,
      ite_eq_left hρ, analyticOrderNatAt, analyticOrderAt_LFunctionTrivChar₁_one hρ1]
  · rw [ite_eq_right hρ,
      ite_eq_right fun h ↦ hρ ⟨h.1, by_contra fun hζ ↦ LFunctionTrivChar₁_one_ne_zero hζ h.2⟩]

/-- The zeros of `ζ` in a closed disc, weighted by analytic order, are the divisor of the entire
function `LFunctionTrivChar₁ 1` on that disc. -/
theorem finsum_subtype_riemannZeta_eq_finsum_divisor (s₀ s : ℂ) (r' : ℝ) :
    ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r' ∧ riemannZeta z = 0},
        ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val) =
      ∑ᶠ ρ, (MeromorphicOn.divisor (LFunctionTrivChar₁ 1) (closedBall s₀ r') ρ : ℂ) /
        (s - ρ) := by
  refine (finsum_subtype_eq_finsum_cond (f := fun z ↦
    ((analyticOrderAt riemannZeta z).toNat : ℂ) / (s - z)) _).trans (finsum_congr fun ρ ↦ ?_)
  rw [finsum_eq_if, divisor_LFunctionTrivChar₁_one_closedBall_apply]
  split_ifs <;> simp

/-- The centre lower bound `‖(s₀ - 1) ζ(s₀)‖ ≥ (σ₀ - 1) exp(-Re ζ(σ₀))` for `σ₀ = Re s₀`. For
`σ₀ > 1` it comes from `DirichletCharacter.exp_neg_re_riemannZeta_le_norm_LFunction`; for `σ₀ ≤ 1`
the left side is not positive. -/
private theorem sub_one_mul_exp_neg_le_norm_LFunctionTrivChar₁_one (s₀ : ℂ) :
    (s₀.re - 1) * Real.exp (-(riemannZeta s₀.re).re) ≤ ‖LFunctionTrivChar₁ 1 s₀‖ := by
  rcases le_or_gt s₀.re 1 with h | hs₀
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le).trans (norm_nonneg _)
  have hs₀1 : s₀ ≠ 1 := fun h ↦ by simp [h] at hs₀
  rw [LFunctionTrivChar₁_one_apply_of_ne_one hs₀1, norm_mul]
  gcongr
  · simpa using re_le_norm (s₀ - 1)
  · simpa using (1 : DirichletCharacter ℂ 1).exp_neg_re_riemannZeta_le_norm_LFunction hs₀

/-- **Relative growth of `(s - 1) ζ(s)` on discs.** For real `σ₀ > 1` and a radius `R` there is
an exponent `D` such that `‖(w - 1) ζ(w)‖ ≤ (|Im s₀| + 2) ^ D ‖(s₀ - 1) ζ(s₀)‖` for every centre
`s₀` with `Re s₀ = σ₀` and every `w` with `‖w - s₀‖ ≤ R`. -/
theorem exists_norm_LFunctionTrivChar₁_one_le_rpow_mul {σ₀ : ℝ} (hσ₀ : 1 < σ₀) (R : ℝ) :
    ∃ D : ℝ, ∀ s₀ w : ℂ, s₀.re = σ₀ → ‖w - s₀‖ ≤ R →
      ‖LFunctionTrivChar₁ 1 w‖ ≤ (|s₀.im| + 2) ^ D * ‖LFunctionTrivChar₁ 1 s₀‖ := by
  obtain ⟨K, B, -, hdisc⟩ := exists_norm_LFunctionTrivChar₁_one_le_rpow_of_norm_sub_le σ₀ R
  obtain ⟨D, hD⟩ := Real.exists_mul_rpow_le_rpow_mul K B
    (mul_pos (by linarith) (Real.exp_pos _) : 0 < (σ₀ - 1) * Real.exp (-(riemannZeta σ₀).re))
    one_lt_two
  refine ⟨D, fun s₀ w hs₀ hw ↦ (hdisc s₀ w hs₀ hw).trans (hD _ _ (by simp) ?_)⟩
  simpa [hs₀] using sub_one_mul_exp_neg_le_norm_LFunctionTrivChar₁_one s₀

/-- **The local expansion of `ζ′/ζ`.** For real `σ₀ > 1` and radii `r < r'` there is a
constant `C` such that for every `s₀` with `Re s₀ = σ₀` and every `s ≠ 1` with `‖s - s₀‖ ≤ r` and
`ζ(s) ≠ 0`, `ζ′/ζ(s) + 1/(s - 1)` differs from `∑ m(ρ)/(s - ρ)` over the zeros `ρ` of `ζ` with
`‖ρ - s₀‖ ≤ r'`, counted with analytic order `m(ρ)`, by at most `C log(|Im s₀| + 2)`. -/
theorem riemannZeta_local_logDeriv {σ₀ r r' : ℝ} (hσ₀ : 1 < σ₀) (hrr' : r < r') :
    ∃ C : ℝ, ∀ s₀ s : ℂ, s₀.re = σ₀ → ‖s - s₀‖ ≤ r → s ≠ 1 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r' ∧ riemannZeta z = 0},
            ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
        C * Real.log (|s₀.im| + 2) := by
  have hF := (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨D, hD⟩ := exists_norm_LFunctionTrivChar₁_one_le_rpow_mul hσ₀ (r' + 1)
  obtain ⟨A, hA⟩ := exists_norm_logDeriv_sub_finsum_divisor_le hrr' (lt_add_one r')
  refine ⟨A * D, fun s₀ s hs₀ hs hs1 hζ ↦ ?_⟩
  have key := hA (hF.mono (subset_univ (closedBall s₀ (r' + 1))))
    (fun w hw ↦ hD s₀ w hs₀ (by rw [mem_sphere, dist_eq_norm] at hw; exact hw.le))
    (LFunctionTrivChar₁_one_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by linarith))) hs
    (LFunctionTrivChar₁_one_ne_zero hζ)
  rw [← logDeriv_riemannZeta_add_inv_sub_one hs1 hζ, logDeriv_apply,
    ← finsum_subtype_riemannZeta_eq_finsum_divisor, ← one_div,
    Real.log_rpow (by positivity)] at key
  exact key.trans_eq (by ring)

end TauCeti

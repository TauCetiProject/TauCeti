/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.Analysis.Complex.AbsMax
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.Analysis.Meromorphic.Divisor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.LSeries.DirichletEulerLog
import TauCeti.NumberTheory.LSeries.RiemannZeta.Growth
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne

/-!
# The local expansion of the logarithmic derivative of the Riemann zeta function

Fix a real `σ₀ > 1` and radii `0 < r < r'`. There is a constant `C`, depending only on
`σ₀, r, r'`, such that for every centre `s₀` with `Re s₀ = σ₀` and every `s ≠ 1` with
`‖s - s₀‖ ≤ r` and `ζ(s) ≠ 0`,
`‖ζ′/ζ(s) + 1/(s - 1) - ∑_{‖ρ - s₀‖ ≤ r'} m(ρ)/(s - ρ)‖ ≤ C log(|Im s₀| + 2)`.
The sum runs over every zero `ρ` of `ζ` in the closed disc, trivial zeros included, weighted by
its analytic order `m(ρ)`.

## Main results

* `TauCeti.finsum_subtype_riemannZeta_eq_finsum_divisor`: the order-weighted sum over the zeros
  of `ζ` in a closed disc is the divisor sum of `LFunctionTrivChar₁ 1` on that disc.
* `TauCeti.riemannZeta_local_logDeriv`: the local expansion of `ζ′/ζ`.

## Implementation notes

The entire function `LFunctionTrivChar₁ 1` has logarithmic derivative `ζ′/ζ(s) + 1/(s - 1)` and
the same zeros and orders as `ζ`. Landau's local lemma
`AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le` on the discs of radii `r'` and `r' + 1` about
`s₀` turns two inputs into the expansion: the disc bound
`TauCeti.exists_norm_LFunctionTrivChar₁_one_le_rpow_of_norm_sub_le`, and the centre lower bound
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

/-- The zeros of `ζ` in a closed disc, weighted by analytic order, are the divisor of the entire
function `LFunctionTrivChar₁ 1` on that disc. -/
theorem finsum_subtype_riemannZeta_eq_finsum_divisor (s₀ s : ℂ) (r' : ℝ) :
    ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r' ∧ riemannZeta z = 0},
        ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val) =
      ∑ᶠ ρ, (MeromorphicOn.divisor (LFunctionTrivChar₁ 1) (closedBall s₀ r') ρ : ℂ) /
        (s - ρ) := by
  have hF := (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd isOpen_univ
  refine (finsum_subtype_eq_finsum_cond (f := fun z ↦
    ((analyticOrderAt riemannZeta z).toNat : ℂ) / (s - z)) _).trans (finsum_congr fun ρ ↦ ?_)
  rw [finsum_eq_if]
  by_cases hρ : ‖ρ - s₀‖ ≤ r' ∧ riemannZeta ρ = 0
  · have hρ1 : ρ ≠ 1 := by
      rintro rfl
      exact riemannZeta_one_ne_zero hρ.2
    have hmem : ρ ∈ closedBall s₀ r' := by
      rw [mem_closedBall, dist_eq_norm]
      exact hρ.1
    rw [ite_eq_left hρ, (hF.mono (subset_univ _)).meromorphicOn.divisor_eq_analyticOrderNatAt
      (hF ρ trivial) hmem, analyticOrderNatAt, analyticOrderAt_LFunctionTrivChar₁_one hρ1,
      Int.cast_natCast]
  · rw [ite_eq_right hρ]
    by_cases hmem : ρ ∈ closedBall s₀ r'
    · have hne : LFunctionTrivChar₁ 1 ρ ≠ 0 := by
        rcases eq_or_ne ρ 1 with rfl | hρ1
        · exact LFunctionTrivChar₁_apply_one_ne_zero 1
        rw [LFunctionTrivChar₁_one_apply_of_ne_one hρ1]
        refine mul_ne_zero (sub_ne_zero.mpr hρ1) fun h ↦ hρ ⟨?_, h⟩
        rwa [mem_closedBall, dist_eq_norm] at hmem
      rw [(hF ρ trivial).divisor_apply_eq_zero hne, Int.cast_zero, zero_div]
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hmem, Int.cast_zero, zero_div]

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

/-- **The local expansion of `ζ′/ζ`.** For real `σ₀ > 1` and radii `0 < r < r'` there is a
constant `C` such that for every `s₀` with `Re s₀ = σ₀` and every `s ≠ 1` with `‖s - s₀‖ ≤ r` and
`ζ(s) ≠ 0`, `ζ′/ζ(s) + 1/(s - 1)` differs from `∑ m(ρ)/(s - ρ)` over the zeros `ρ` of `ζ` with
`‖ρ - s₀‖ ≤ r'`, counted with analytic order `m(ρ)`, by at most `C log(|Im s₀| + 2)`. -/
theorem riemannZeta_local_logDeriv {σ₀ r r' : ℝ} (hσ₀ : 1 < σ₀) (hr : 0 < r) (hrr' : r < r') :
    ∃ C : ℝ, ∀ s₀ s : ℂ, s₀.re = σ₀ → ‖s - s₀‖ ≤ r → s ≠ 1 → riemannZeta s ≠ 0 →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) -
          ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r' ∧ riemannZeta z = 0},
            ((analyticOrderAt riemannZeta ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
        C * Real.log (|s₀.im| + 2) := by
  have hF := (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨K, B, hK, hdisc⟩ :=
    exists_norm_LFunctionTrivChar₁_one_le_rpow_of_norm_sub_le σ₀ (r' + 1)
  set c₀ := (σ₀ - 1) * Real.exp (-(riemannZeta σ₀).re)
  have hc₀ : 0 < c₀ := mul_pos (by linarith) (Real.exp_pos _)
  have hlog : 0 < Real.log ((r' + 1) / r') :=
    Real.log_pos ((one_lt_div (by linarith)).mpr (by linarith))
  have hR : 0 < (r' + 1) ^ 2 - r' * r := by nlinarith
  set A := 4 * (r' + r) / (r' - r) ^ 2 +
    r' / (((r' + 1) ^ 2 - r' * r) * Real.log ((r' + 1) / r')) with hAdef
  have hA0 : 0 ≤ A := add_nonneg (div_nonneg (by linarith) (sq_nonneg _))
    (div_nonneg (by linarith) (mul_nonneg hR.le hlog.le))
  have hlog2 := Real.log_pos one_lt_two
  refine ⟨A * ((|Real.log K| + |Real.log c₀|) / Real.log 2 + B), fun s₀ s hs₀ hs hs1 hζ ↦ ?_⟩
  have hFb := hF.mono (subset_univ (closedBall s₀ (r' + 1)))
  set t := |s₀.im| + 2
  have ht : 2 ≤ t := by simp [t]
  set M := K * t ^ B / c₀ with hMdef
  have hcentre : c₀ ≤ ‖LFunctionTrivChar₁ 1 s₀‖ := by
    simpa [c₀, hs₀] using sub_one_mul_exp_neg_le_norm_LFunctionTrivChar₁_one s₀
  have hsphere (w : ℂ) (hw : w ∈ sphere s₀ (r' + 1)) :
      ‖LFunctionTrivChar₁ 1 w‖ ≤ M * ‖LFunctionTrivChar₁ 1 s₀‖ := by
    refine (hdisc s₀ w hs₀ (by rw [mem_sphere, dist_eq_norm] at hw; exact hw.le)).trans ?_
    rw [hMdef, div_mul_eq_mul_div, le_div_iff₀ hc₀]
    gcongr
  have hFs : LFunctionTrivChar₁ 1 s ≠ 0 := by
    rw [LFunctionTrivChar₁_one_apply_of_ne_one hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) hζ
  have hM1 : 1 ≤ M :=
    (hFb.differentiableOn.diffContOnCl_ball Subset.rfl).one_le_of_forall_mem_sphere_norm_le_mul
      (by linarith) (norm_pos_iff.mp (hc₀.trans_le hcentre)) hsphere
  have key := hFb.norm_logDeriv_sub_finsum_divisor_le (lt_add_one r') hsphere (hs.trans_lt hrr') hFs
  rw [← logDeriv_riemannZeta_add_inv_sub_one hs1 hζ, logDeriv_apply,
    ← finsum_subtype_riemannZeta_eq_finsum_divisor, ← one_div] at key
  have hA : 4 * (r' + ‖s - s₀‖) / (r' - ‖s - s₀‖) ^ 2 +
      r' / (((r' + 1) ^ 2 - r' * ‖s - s₀‖) * Real.log ((r' + 1) / r')) ≤ A := by
    rw [hAdef]
    gcongr <;> nlinarith [norm_nonneg (s - s₀)]
  have hlogM : Real.log M ≤ ((|Real.log K| + |Real.log c₀|) / Real.log 2 + B) * Real.log t := by
    have h1 : 1 ≤ Real.log t / Real.log 2 :=
      (one_le_div hlog2).mpr (Real.log_le_log two_pos ht)
    rw [hMdef, Real.log_div (by positivity) hc₀.ne', Real.log_mul hK.ne' (by positivity),
      Real.log_rpow (by linarith), add_mul, div_mul_eq_mul_div, mul_div_assoc]
    nlinarith [le_abs_self (Real.log K), neg_abs_le (Real.log c₀), abs_nonneg (Real.log K),
      abs_nonneg (Real.log c₀)]
  calc _ ≤ _ := key
    _ ≤ A * Real.log M := mul_le_mul_of_nonneg_right hA (Real.log_nonneg hM1)
    _ ≤ A * (((|Real.log K| + |Real.log c₀|) / Real.log 2 + B) * Real.log t) := by gcongr
    _ = _ := by ring

end TauCeti

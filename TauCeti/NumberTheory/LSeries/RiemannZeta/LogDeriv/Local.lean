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
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic
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

* `TauCeti.LFunctionTrivChar₁_one_apply_of_ne_one`: `LFunctionTrivChar₁ 1 s = (s - 1) ζ(s)`
  for `s ≠ 1`.
* `TauCeti.analyticOrderAt_LFunctionTrivChar₁_one`: away from `1`, the analytic orders of
  `LFunctionTrivChar₁ 1` and `ζ` agree.
* `TauCeti.finsum_subtype_riemannZeta_eq_finsum_divisor`: the order-weighted sum over the zeros
  of `ζ` in a closed disc is the divisor sum of `LFunctionTrivChar₁ 1` on that disc.
* `TauCeti.re_sub_one_div_le_norm_LFunctionTrivChar₁_one`: `‖(s₀ - 1) ζ(s₀)‖ ≥ (σ₀ - 1) / Re ζ(σ₀)`
  for `σ₀ = Re s₀ > 1`.
* `TauCeti.exists_norm_LFunctionTrivChar₁_one_le_rpow_of_norm_sub_le`: a polynomial bound for
  `(s - 1) ζ(s)` on discs of fixed radius centred on a vertical line.
* `TauCeti.riemannZeta_local_logDeriv`: the local expansion of `ζ′/ζ`.

## Implementation notes

The entire function `LFunctionTrivChar₁ 1` has logarithmic derivative `ζ′/ζ(s) + 1/(s - 1)` and
the same zeros and orders as `ζ`. Landau's local lemma
`AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le` on the discs of radii `r'` and `r' + 1` about
`s₀` turns the disc bound and the centre lower bound above into the expansion.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Lemma 8.6, pp.90–91, and
  Lemma 11.2, p.113.
* PrimeNumberTheoremAnd, `StrongPNT.lean` at revision `df0ccba`, proves a weaker `log²` bound on
  a fixed window about `3/2 + i t`; this file follows the nested-disc route instead.
-/

public section

open Complex DirichletCharacter Metric Set Filter Topology

namespace TauCeti

/-- Away from `s = 1`, Mathlib's pole-removed zeta function is `(s - 1) ζ(s)`. -/
theorem LFunctionTrivChar₁_one_apply_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    LFunctionTrivChar₁ 1 s = (s - 1) * riemannZeta s := by
  rw [LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar, LFunction_modOne_eq]

/-- Away from `s = 1`, the analytic orders of `(s - 1) ζ(s)` and `ζ(s)` agree. -/
theorem analyticOrderAt_LFunctionTrivChar₁_one {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt (LFunctionTrivChar₁ 1) ρ = analyticOrderAt riemannZeta ρ := by
  have hev : LFunctionTrivChar₁ 1 =ᶠ[𝓝 ρ] (fun z ↦ z - 1) * riemannZeta :=
    Filter.mem_of_superset (isOpen_ne.mem_nhds hρ) fun z hz ↦
      LFunctionTrivChar₁_one_apply_of_ne_one hz
  have hlin : AnalyticAt ℂ (fun z : ℂ ↦ z - 1) ρ := by fun_prop
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hlin (analyticOn_riemannZeta ρ hρ),
    hlin.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hρ), zero_add]

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

/-- At a point with real part `σ₀ > 1`, `‖(s₀ - 1) ζ(s₀)‖ ≥ (σ₀ - 1) / Re ζ(σ₀)`. -/
theorem re_sub_one_div_le_norm_LFunctionTrivChar₁_one {s₀ : ℂ} (hs₀ : 1 < s₀.re) :
    (s₀.re - 1) / (riemannZeta s₀.re).re ≤ ‖LFunctionTrivChar₁ 1 s₀‖ := by
  have hs₀1 : s₀ ≠ 1 := by
    rintro rfl
    simp at hs₀
  rw [LFunctionTrivChar₁_one_apply_of_ne_one hs₀1, norm_mul, div_eq_mul_inv]
  refine mul_le_mul ?_ (inv_riemannZeta_re_le_norm_riemannZeta hs₀)
    (inv_nonneg.mpr (riemannZeta_re_pos_of_one_lt hs₀).le) (norm_nonneg _)
  simpa using re_le_norm (s₀ - 1)

/-- On the closed discs of a fixed radius `R` centred on a vertical line `Re s₀ = σ₀`,
`‖(s - 1) ζ(s)‖ ≤ K (|Im s₀| + 2) ^ B` with `K > 0` and `B` independent of `s₀`. -/
theorem exists_norm_LFunctionTrivChar₁_one_le_rpow_of_norm_sub_le (σ₀ : ℝ) {R : ℝ}
    (hR : 0 ≤ R) :
    ∃ K B : ℝ, 0 < K ∧ ∀ s₀ w : ℂ, s₀.re = σ₀ → ‖w - s₀‖ ≤ R →
      ‖LFunctionTrivChar₁ 1 w‖ ≤ K * (|s₀.im| + 2) ^ B := by
  obtain ⟨C, B, hC⟩ := exists_norm_LFunctionTrivChar₁_one_le_rpow (σ₀ - R) (σ₀ + R)
  refine ⟨max C 1 * (R + 1) ^ max B 0, max B 0,
    mul_pos (lt_max_of_lt_right one_pos) (Real.rpow_pos_of_pos (by linarith) _),
    fun s₀ w hs₀ hw ↦ ?_⟩
  have hre := abs_re_le_norm (w - s₀)
  rw [sub_re, hs₀, abs_le] at hre
  have him := (abs_sub_abs_le_abs_sub w.im s₀.im).trans ((sub_im w s₀ ▸ abs_im_le_norm _).trans hw)
  calc ‖LFunctionTrivChar₁ 1 w‖ ≤ C * (|w.im| + 2) ^ B := hC w (by linarith) (by linarith)
    _ ≤ max C 1 * (|w.im| + 2) ^ max B 0 := by
        gcongr
        · exact le_max_left _ _
        · linarith [abs_nonneg w.im]
        · exact le_max_left _ _
    _ ≤ max C 1 * ((R + 1) * (|s₀.im| + 2)) ^ max B 0 := by
        gcongr
        nlinarith [abs_nonneg s₀.im]
    _ = _ := by rw [Real.mul_rpow (by linarith) (by positivity), mul_assoc]

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
    exists_norm_LFunctionTrivChar₁_one_le_rpow_of_norm_sub_le σ₀ (by linarith : 0 ≤ r' + 1)
  set c₀ := (σ₀ - 1) / (riemannZeta σ₀).re
  have hc₀ : 0 < c₀ := div_pos (by linarith) (riemannZeta_re_pos_of_one_lt hσ₀)
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
    simpa [c₀, hs₀] using re_sub_one_div_le_norm_LFunctionTrivChar₁_one (s₀ := s₀) (by linarith)
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

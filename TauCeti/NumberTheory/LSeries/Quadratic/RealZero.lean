/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.Real.GoldenRatio
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.OfSquarefree
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.DerivBound
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogBound
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.FundamentalDiscriminant
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.LFunction

/-!
# Effective distance of a quadratic real zero from one

Siegel's bound `1 - β ≥ c(ε) N ^ (-ε)` on real zeros of quadratic Dirichlet `L`-functions has an
ineffective implied constant, while effective asymptotic zero-repulsion arguments apply only above a
large explicit conductor threshold. To exclude or separate real zeros across bounded small-conductor
ranges unconditionally, this file establishes explicit effective `N ^ (-1/2 - ε)` and `N⁻¹`
zero-distance bounds valid for **every** primitive nonprincipal quadratic character of conductor
`N ≥ 3`.

Throughout, `N` is a nonzero level (`[NeZero N]`) and `DirichletCharacter.LFunction` is the analytic
continuation of `L(s, χ)`. For any nonprincipal complex character `χ` of level `N` (neither
primitivity nor quadraticity is needed), nonvanishing on `Re(s) ≥ 1`, the near-one derivative bound
`‖L'(σ, χ)‖ ≤ 81 (log N) ^ 2` on `[1 - 1 / log N, 1]`, and the boundary bound
`‖L(1, χ)‖ ≤ 2 + log N` give the unconditional separation
`Re L(1, χ) / (81 (log N) ^ 2) ≤ 1 - β` for every real zero `β` of `L(s, χ)`.

When `χ` is primitive (`χ.IsPrimitive`, so the level `N` equals `χ.conductor`) and quadratic, `χ`
coincides with the Kronecker character of a fundamental discriminant `D ≠ 1` with `|D| = N`. The
quadratic class-number formula and the sharp golden-ratio regulator bound `log φ ≤ R_K` then supply
`2 log φ / √N ≤ Re L(1, χ)`, yielding explicit effective zero-distance bounds in terms of the
conductor `N`, a fundamental discriminant `D ≠ 1`, or a squarefree radicand `d ≠ 1`.

## Main results

* `DirichletCharacter.two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re`:
  `2 log φ / √N ≤ Re L(1, χ)` for primitive nonprincipal quadratic `χ` of level `N`.
* `DirichletCharacter.LFunction_one_re_div_log_sq_le_one_sub_of_LFunction_eq_zero`:
  `Re L(1, χ) / (81 (log N) ^ 2) ≤ 1 - β` for any real zero `β` of any nonprincipal character `χ`
  of nonzero level `N`.
* `DirichletCharacter.div_sqrt_mul_log_sq_le_one_sub_of_LFunction_eq_zero`:
  `2 log φ / (81 √N (log N) ^ 2) ≤ 1 - β` for primitive nonprincipal quadratic `χ`.
* `DirichletCharacter.mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero` and
  `DirichletCharacter.div_level_le_one_sub_of_LFunction_eq_zero`: explicit `N ^ (-1/2 - ε)` and
  `N⁻¹` zero-distance bounds for primitive nonprincipal quadratic `χ`.
* `TauCeti.Multiquadratic.mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero` and
  `TauCeti.Multiquadratic.mul_rpow_neg_half_sub_le_one_sub_of_squarefree_of_LFunction_eq_zero`:
  effective real-zero distance bounds in terms of a fundamental discriminant `D ≠ 1` and of a
  squarefree radicand `d ≠ 1`.

## References

* P. Koymans and C. Pagano, *On Stevenhagen's conjecture*, §7.2, proof of Proposition 7.6, p. 62.
* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Graduate Studies in Mathematics 203,
  American Mathematical Society, 2019, Lemma 11.2, p. 113, and (12.11)–(12.12), p. 124.
* M. A. Bennett, G. Martin, K. O'Bryant, and A. Rechnitzer, *Explicit bounds for primes in
  arithmetic progressions*, Illinois J. Math. 62 (2018), Lemma 6.3, pp. 491–492.
-/

public section

open Complex
open scoped ComplexOrder Real

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- **Effective class-number lower bound on `L(1, χ)` for primitive quadratic characters.** For
every primitive nonprincipal quadratic character `χ` of nonzero level `N`,
`2 log φ / √N ≤ Re L(1, χ)`. -/
theorem two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re
    (hprim : χ.IsPrimitive) (hq : χ.IsQuadratic) (hχ : χ ≠ 1) :
    2 * Real.log Real.goldenRatio / √(N : ℝ) ≤ (χ.LFunction 1).re := by
  obtain ⟨D, hD, hDN, hval⟩ := hprim.exists_isFundamentalDiscr_apply_eq hq
  subst hDN
  have hχ_eq : χ = TauCeti.Multiquadratic.fundamentalDiscriminantCharCast ℂ D hD := by
    ext a
    simpa using hval (ZMod.val (a : ZMod D.natAbs) : ℤ)
  have hD1 : D ≠ 1 := fun h ↦ hχ <| hχ_eq.trans <|
    (TauCeti.Multiquadratic.fundamentalDiscriminantCharCast_eq_one_iff hD).mpr h
  rw [hχ_eq, Nat.cast_natAbs, Int.cast_abs]
  exact TauCeti.Multiquadratic.two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re hD hD1

/-- **Unconditional real-zero separation from `L(1, χ)`** (Koukoulopoulos, (12.11)). For any
nonprincipal character `χ` of nonzero level `N` (not necessarily primitive or quadratic) and any
real zero `β` of `L(s, χ)`, `Re L(1, χ) / (81 (log N) ^ 2) ≤ 1 - β`. -/
theorem LFunction_one_re_div_log_sq_le_one_sub_of_LFunction_eq_zero
    (hχ : χ ≠ 1) {β : ℝ} (hβ : χ.LFunction β = 0) :
    (χ.LFunction 1).re / (81 * Real.log N ^ 2) ≤ 1 - β := by
  have hβ1 : β < 1 :=
    not_le.mp fun h ↦ χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by simpa using h) hβ
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast χ.three_le_level_of_ne_one hχ
  have hL1 : 1 < Real.log N :=
    (by linarith [Real.log_three_gt_d9] : (1 : ℝ) < Real.log 3).trans_le
      (Real.log_le_log (by norm_num) hN3)
  have : 0 < Real.log N := zero_lt_one.trans hL1
  rcases le_or_gt (1 - 1 / Real.log N) β with hnear | hfar
  · -- Near `1`, apply Lagrange's mean value theorem to `σ ↦ Re L(σ, χ)` on `[β, 1]`.
    have hf' (σ : ℝ) :
        HasDerivAt (fun x : ℝ ↦ (χ.LFunction x).re) (deriv χ.LFunction σ).re σ :=
      reCLM.hasFDerivAt.comp_hasDerivAt σ
        ((differentiable_LFunction hχ).differentiableAt.hasDerivAt.comp_ofReal)
    have hfc : ContinuousOn (fun x : ℝ ↦ (χ.LFunction x).re) (Set.Icc β 1) :=
      fun x _ ↦ (hf' x).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope
      (fun x : ℝ ↦ (χ.LFunction x).re) (fun x : ℝ ↦ (deriv χ.LFunction x).re)
      hβ1 hfc (fun x _ ↦ hf' x)
    have hc_le : (deriv χ.LFunction c).re ≤ 81 * Real.log N ^ 2 :=
      (Complex.re_le_norm _).trans
        (χ.norm_deriv_LFunction_le_mul_log_sq hχ (hnear.trans hc.1.le) hc.2.le)
    rw [ofReal_one, hβ, zero_re, sub_zero] at hslope
    rw [div_le_iff₀ (by positivity)]
    have hmul := (div_le_iff₀ (sub_pos.mpr hβ1)).mp (hslope ▸ hc_le)
    linarith
  · -- Left of `1 - 1 / log N`, use `Re L(1, χ) ≤ 2 + log N ≤ 81 log N`.
    calc
      (χ.LFunction 1).re / (81 * Real.log N ^ 2)
          ≤ (2 + Real.log N) / (81 * Real.log N ^ 2) :=
        div_le_div_of_nonneg_right
          ((Complex.re_le_norm _).trans (χ.norm_LFunction_one_le_two_add_log hχ)) (by positivity)
      _ ≤ 81 * Real.log N / (81 * Real.log N ^ 2) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 1 / Real.log N := by field_simp
      _ ≤ 1 - β := by linarith

/-- **Effective logarithmic-square real-zero gap for primitive quadratic characters**
(Koukoulopoulos, (12.12)). Every real zero `β` of a primitive nonprincipal quadratic character `χ`
of nonzero level `N` satisfies `2 log φ / (81 √N (log N) ^ 2) ≤ 1 - β`. -/
theorem div_sqrt_mul_log_sq_le_one_sub_of_LFunction_eq_zero
    (hprim : χ.IsPrimitive) (hq : χ.IsQuadratic) (hχ : χ ≠ 1) {β : ℝ}
    (hβ : χ.LFunction β = 0) :
    2 * Real.log Real.goldenRatio / (81 * √(N : ℝ) * Real.log N ^ 2) ≤ 1 - β := by
  calc
    2 * Real.log Real.goldenRatio / (81 * √(N : ℝ) * Real.log N ^ 2)
        = (2 * Real.log Real.goldenRatio / √(N : ℝ)) / (81 * Real.log N ^ 2) := by ring
    _ ≤ (χ.LFunction 1).re / (81 * Real.log N ^ 2) :=
      div_le_div_of_nonneg_right
        (two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re hprim hq hχ) (by positivity)
    _ ≤ 1 - β := LFunction_one_re_div_log_sq_le_one_sub_of_LFunction_eq_zero hχ hβ

/-- **Effective `N ^ (-1/2 - ε)` distance of a quadratic real zero from one.** For every primitive
nonprincipal quadratic character `χ` of nonzero level `N`, every `ε > 0`, and every real zero `β`
of `L(s, χ)`, `(log φ · ε ^ 2 / 162) N ^ (-1/2 - ε) ≤ 1 - β`. -/
theorem mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero
    (hprim : χ.IsPrimitive) (hq : χ.IsQuadratic) (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε) {β : ℝ}
    (hβ : χ.LFunction β = 0) :
    Real.log Real.goldenRatio * ε ^ 2 / 162 * (N : ℝ) ^ (-(1 / 2 : ℝ) - ε) ≤ 1 - β := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast χ.three_le_level_of_ne_one hχ
  have hN0 : (0 : ℝ) < N := by linarith
  have hL0 : 0 < Real.log N := Real.log_pos (by linarith)
  have hφ0 : 0 < Real.log Real.goldenRatio := Real.log_pos Real.one_lt_goldenRatio
  have hlog_sq : Real.log N ^ 2 ≤ 4 / ε ^ 2 * (N : ℝ) ^ ε := by
    calc
      Real.log N ^ 2 ≤ ((N : ℝ) ^ (ε / 2) / (ε / 2)) ^ 2 :=
        pow_le_pow_left₀ hL0.le (Real.log_le_rpow_div hN0.le (half_pos hε)) 2
      _ = 4 / ε ^ 2 * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) := by field_simp; ring
      _ = 4 / ε ^ 2 * (N : ℝ) ^ ε := by rw [← Real.rpow_add hN0, add_halves]
  have hrpow : (N : ℝ) ^ (-(1 / 2 : ℝ) - ε) = (√(N : ℝ) * (N : ℝ) ^ ε)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0, ← Real.rpow_neg hN0.le]
    congr 1
    ring
  calc
    Real.log Real.goldenRatio * ε ^ 2 / 162 * (N : ℝ) ^ (-(1 / 2 : ℝ) - ε)
        = 2 * Real.log Real.goldenRatio / (81 * √(N : ℝ) * (4 / ε ^ 2 * (N : ℝ) ^ ε)) := by
      rw [hrpow]
      field_simp
      ring
    _ ≤ 2 * Real.log Real.goldenRatio / (81 * √(N : ℝ) * Real.log N ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hlog_sq (by positivity))
    _ ≤ 1 - β := div_sqrt_mul_log_sq_le_one_sub_of_LFunction_eq_zero hprim hq hχ hβ

/-- **Effective inverse-conductor distance of a quadratic real zero from one.** Every real zero `β`
of a primitive nonprincipal quadratic character `χ` of nonzero level `N` satisfies
`log φ / (648 N) ≤ 1 - β` (the `ε = 1 / 2` case of
`mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero`). -/
theorem div_level_le_one_sub_of_LFunction_eq_zero
    (hprim : χ.IsPrimitive) (hq : χ.IsQuadratic) (hχ : χ ≠ 1) {β : ℝ}
    (hβ : χ.LFunction β = 0) :
    Real.log Real.goldenRatio / (648 * (N : ℝ)) ≤ 1 - β := by
  have h := mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero hprim hq hχ
    (ε := (1 / 2 : ℝ)) (by norm_num) hβ
  have hrpow : (N : ℝ) ^ (-(1 / 2 : ℝ) - 1 / 2) = (N : ℝ)⁻¹ := by
    rw [show -(1 / 2 : ℝ) - 1 / 2 = -1 by norm_num, Real.rpow_neg_one]
  rw [hrpow] at h
  linarith [show Real.log Real.goldenRatio / (648 * (N : ℝ)) =
    Real.log Real.goldenRatio * (1 / 2 : ℝ) ^ 2 / 162 * (N : ℝ)⁻¹ by ring]

end DirichletCharacter

namespace TauCeti.Multiquadratic

/-- **Effective distance of a real zero from one for a fundamental discriminant `D ≠ 1`.**
Every real zero `β` of `L(s, χ_D)` satisfies
`(log φ · ε ^ 2 / 162) |D| ^ (-1/2 - ε) ≤ 1 - β` for each `ε > 0`. -/
theorem mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero
    {D : ℤ} [NeZero D.natAbs] (hD : Int.IsFundamentalDiscr D) (hD1 : D ≠ 1) {ε : ℝ} (hε : 0 < ε)
    {β : ℝ} (hβ : (fundamentalDiscriminantCharCast ℂ D hD).LFunction β = 0) :
    Real.log Real.goldenRatio * ε ^ 2 / 162 * |(D : ℝ)| ^ (-(1 / 2 : ℝ) - ε) ≤ 1 - β := by
  have hχ : fundamentalDiscriminantCharCast ℂ D hD ≠ 1 :=
    fun h ↦ hD1 ((fundamentalDiscriminantCharCast_eq_one_iff hD).mp h)
  simpa [Nat.cast_natAbs, Int.cast_abs] using
    DirichletCharacter.mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero
      (isPrimitive_fundamentalDiscriminantCharCast hD)
      (fundamentalDiscriminantCharCast_isQuadratic hD) hχ hε hβ

/-- **Effective distance of a quadratic real zero from one for a squarefree radicand `d ≠ 1`**
(Koymans–Pagano, §7.2, proof of Proposition 7.6, p. 62). For any squarefree integer `d ≠ 1`, any
`ε > 0`, and any real zero `β` of the continued `L`-function of
`fundamentalDiscriminantCharCast ℂ (fundamentalDiscriminant d)`,
`(log φ · ε ^ 2 / (324 · 4 ^ ε)) |d| ^ (-1/2 - ε) ≤ 1 - β`. -/
theorem mul_rpow_neg_half_sub_le_one_sub_of_squarefree_of_LFunction_eq_zero
    {d : ℤ} [NeZero (fundamentalDiscriminant d).natAbs] (hd : Squarefree d) (hd1 : d ≠ 1)
    {ε : ℝ} (hε : 0 < ε) {β : ℝ}
    (hβ : (fundamentalDiscriminantCharCast ℂ (fundamentalDiscriminant d)
      (isFundamentalDiscr_fundamentalDiscriminant hd)).LFunction β = 0) :
    Real.log Real.goldenRatio * ε ^ 2 / (324 * (4 : ℝ) ^ ε) *
      |(d : ℝ)| ^ (-(1 / 2 : ℝ) - ε) ≤ 1 - β := by
  set D := fundamentalDiscriminant d with hD_def
  have hD : Int.IsFundamentalDiscr D := isFundamentalDiscr_fundamentalDiscriminant hd
  have hD1 : D ≠ 1 := by
    rw [hD_def, fundamentalDiscriminant_def]
    split_ifs with h
    · exact hd1
    · omega
  have hD_pos : 0 < |(D : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hD.ne_zero)
  have hD_le : |(D : ℝ)| ≤ 4 * |(d : ℝ)| := by
    rw [hD_def, fundamentalDiscriminant_def]
    split_ifs with h
    · linarith [abs_nonneg (d : ℝ)]
    · push_cast
      rw [abs_mul, abs_of_pos (by norm_num)]
  have hφ0 : 0 < Real.log Real.goldenRatio := Real.log_pos Real.one_lt_goldenRatio
  have h4_rpow : (4 : ℝ) ^ (-(1 / 2 : ℝ) - ε) = (2 * (4 : ℝ) ^ ε)⁻¹ := by
    rw [show -(1 / 2 : ℝ) - ε = -((1 / 2 : ℝ) + ε) by ring,
      Real.rpow_neg (by norm_num), Real.rpow_add (by norm_num), ← Real.sqrt_eq_rpow,
      show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hrpow_le : (4 * |(d : ℝ)|) ^ (-(1 / 2 : ℝ) - ε) ≤ |(D : ℝ)| ^ (-(1 / 2 : ℝ) - ε) :=
    Real.rpow_le_rpow_of_nonpos hD_pos hD_le (by linarith)
  calc
    Real.log Real.goldenRatio * ε ^ 2 / (324 * (4 : ℝ) ^ ε) *
        |(d : ℝ)| ^ (-(1 / 2 : ℝ) - ε)
        = Real.log Real.goldenRatio * ε ^ 2 / 162 *
            (4 * |(d : ℝ)|) ^ (-(1 / 2 : ℝ) - ε) := by
      rw [Real.mul_rpow (by norm_num) (abs_nonneg _), h4_rpow]
      field_simp
      ring
    _ ≤ Real.log Real.goldenRatio * ε ^ 2 / 162 * |(D : ℝ)| ^ (-(1 / 2 : ℝ) - ε) :=
      mul_le_mul_of_nonneg_left hrpow_le (by positivity)
    _ ≤ 1 - β := mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero hD hD1 hε hβ

end TauCeti.Multiquadratic

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
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Log.Pow
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.DerivBound
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.FundamentalDiscriminant
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.LFunction
import TauCeti.NumberTheory.Real.GoldenRatio

/-!
# Effective distance of a quadratic real zero from one

Siegel's bound `1 - β ≥ c(ε) N ^ (-ε)` on real zeros of quadratic Dirichlet `L`-functions has an
ineffective implied constant, while effective asymptotic zero-repulsion arguments apply only above a
large explicit conductor threshold. To exclude or separate real zeros across bounded small-conductor
ranges unconditionally, this file establishes explicit effective `q ^ (-1/2 - ε)`, `N ^ (-1/2 - ε)`,
and `N⁻¹` zero-distance bounds valid for **every** nonprincipal quadratic character (primitive or
imprimitive) of nonzero level `N`.

Throughout, `N` is a nonzero level (`[NeZero N]`) and `DirichletCharacter.LFunction` is the analytic
continuation of `L(s, χ)`. When `χ` is primitive (`χ.IsPrimitive`, so `N = χ.conductor`) and
quadratic, `χ` coincides with the Kronecker character of a fundamental discriminant `D ≠ 1` with
`|D| = N`. The quadratic class-number formula and the sharp golden-ratio regulator bound
`log φ ≤ R_K` supply `2 log φ / √N ≤ Re L(1, χ) ≤ ‖L(1, χ)‖`. Combining this with the general
nonprincipal real-zero separation `‖L(1, χ)‖ / (64 (log N) ^ 2) ≤ 1 - β` from
`DirichletCharacter.norm_LFunction_one_div_log_sq_le_one_sub_of_LFunction_eq_zero`
(`TauCeti.NumberTheory.DirichletCharacter.LFunction.DerivBound`) and descending from an arbitrary
nonprincipal quadratic character to `χ.primitiveCharacter` on `Re(s) > 0`
(`DirichletCharacter.LFunction_changeLevel_eq_zero_iff`) yields explicit effective zero-distance
bounds in terms of the conductor `q = χ.conductor`, the ambient level `N`, a fundamental
discriminant `D ≠ 1`, or a squarefree radicand `d ≠ 1`.

## Main results

* `DirichletCharacter.two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re`:
  `2 log φ / √N ≤ Re L(1, χ)` for primitive nonprincipal quadratic `χ` of level `N`.
* `DirichletCharacter.div_sqrt_conductor_mul_log_sq_le_one_sub_of_LFunction_eq_zero` and
  `DirichletCharacter.div_sqrt_mul_log_sq_le_one_sub_of_LFunction_eq_zero`:
  `log φ / (32 √q (log q) ^ 2) ≤ 1 - β` and `log φ / (32 √N (log N) ^ 2) ≤ 1 - β` for any
  nonprincipal quadratic `χ`.
* `DirichletCharacter.mul_rpow_conductor_neg_half_sub_le_one_sub_of_LFunction_eq_zero`,
  `DirichletCharacter.mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero`,
  `DirichletCharacter.exists_pos_mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero`, and
  `DirichletCharacter.div_level_le_one_sub_of_LFunction_eq_zero`: explicit `q ^ (-1/2 - ε)`,
  `N ^ (-1/2 - ε)`, and `N⁻¹` zero-distance bounds for any nonprincipal quadratic `χ`.
* `TauCeti.Multiquadratic.mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero`,
  `TauCeti.Multiquadratic.mul_rpow_neg_half_sub_le_one_sub_of_squarefree_of_LFunction_eq_zero`,
  and `TauCeti.Multiquadratic.exists_pos_mul_rpow_le_one_sub_of_squarefree_of_LFunction_eq_zero`:
  effective real-zero distance bounds in terms of a fundamental discriminant `D ≠ 1` and of a
  squarefree radicand `d ≠ 1`.

## References

* P. Koymans and C. Pagano, *A sharp upper bound for the 2-torsion of class groups of
  multiquadratic fields*, Mathematika **68** (2022), §7.2, proof of Proposition 7.6.
* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Graduate Studies in Mathematics 203,
  American Mathematical Society, 2019, (12.12), p. 124.
* M. A. Bennett, G. Martin, K. O'Bryant, and A. Rechnitzer, *Explicit bounds for primes in
  arithmetic progressions*, Illinois J. Math. 62 (2018), Lemma 6.3, pp. 491–492.
-/

public section

open scoped Real

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

private theorem three_le_conductor_and_conductor_le_of_ne_one (hχ : χ ≠ 1) :
    3 ≤ (χ.conductor : ℝ) ∧ (χ.conductor : ℝ) ≤ N :=
  ⟨Nat.ofNat_le_cast.mpr (χ.three_le_conductor_of_ne_one hχ),
    Nat.cast_le.mpr (Nat.le_of_dvd (NeZero.pos N) χ.conductor_dvd_level)⟩

/-- **Conductor-level logarithmic-square real-zero gap for quadratic characters**
(Koukoulopoulos, (12.12)). Every real zero `β` of a nonprincipal quadratic character `χ` (primitive
or imprimitive) of nonzero level `N` satisfies
`log φ / (32 √q (log q) ^ 2) ≤ 1 - β`, where `q = χ.conductor`. -/
theorem div_sqrt_conductor_mul_log_sq_le_one_sub_of_LFunction_eq_zero
    (hq : χ.IsQuadratic) (hχ : χ ≠ 1) {β : ℝ} (hβ : χ.LFunction β = 0) :
    Real.log Real.goldenRatio / (32 * √(χ.conductor : ℝ) * Real.log χ.conductor ^ 2) ≤ 1 - β := by
  obtain ⟨hc3, _⟩ := χ.three_le_conductor_and_conductor_le_of_ne_one hχ
  have hlog_gt1 : 1 < Real.log χ.conductor := Real.one_lt_log_of_three_le hc3
  rcases le_or_gt β 0 with hβ0 | hβ0
  · have hsqrt_ge1 : 1 ≤ √(χ.conductor : ℝ) := Real.one_le_sqrt.mpr (by linarith)
    have hden_ge1 : 1 ≤ 32 * √(χ.conductor : ℝ) * Real.log χ.conductor ^ 2 := by nlinarith
    have hdiv_le1 :
        Real.log Real.goldenRatio / (32 * √(χ.conductor : ℝ) * Real.log χ.conductor ^ 2) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [TauCeti.log_goldenRatio_lt_one_half]
    linarith
  · have hprim_ne : χ.primitiveCharacter ≠ 1 := (primitiveCharacter_eq_one_iff χ).not.mpr hχ
    have hprim_zero : χ.primitiveCharacter.LFunction β = 0 :=
      (LFunction_changeLevel_eq_zero_iff χ.primitiveCharacter χ.conductor_dvd_level
        (by simpa using hβ0) (.inl hprim_ne)).mp (by rwa [χ.changeLevel_primitiveCharacter])
    have hgap := χ.primitiveCharacter.norm_LFunction_one_div_log_sq_le_one_sub_of_LFunction_eq_zero
      hprim_ne hprim_zero
    have hL1 : 2 * Real.log Real.goldenRatio / √(χ.conductor : ℝ) ≤
        ‖χ.primitiveCharacter.LFunction 1‖ :=
      (two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re χ.primitiveCharacter_isPrimitive
        hq.primitiveCharacter hprim_ne).trans (Complex.re_le_norm _)
    calc Real.log Real.goldenRatio / (32 * √(χ.conductor : ℝ) * Real.log χ.conductor ^ 2)
        = (2 * Real.log Real.goldenRatio / √(χ.conductor : ℝ)) /
            (64 * Real.log χ.conductor ^ 2) := by ring
      _ ≤ ‖χ.primitiveCharacter.LFunction 1‖ / (64 * Real.log χ.conductor ^ 2) := by gcongr
      _ ≤ 1 - β := hgap

/-- **Level-form logarithmic-square real-zero gap for quadratic characters.** Every real zero `β`
of a nonprincipal quadratic character `χ` of nonzero level `N` satisfies
`log φ / (32 √N (log N) ^ 2) ≤ 1 - β`. -/
theorem div_sqrt_mul_log_sq_le_one_sub_of_LFunction_eq_zero
    (hq : χ.IsQuadratic) (hχ : χ ≠ 1) {β : ℝ} (hβ : χ.LFunction β = 0) :
    Real.log Real.goldenRatio / (32 * √(N : ℝ) * Real.log N ^ 2) ≤ 1 - β := by
  obtain ⟨hc3, hcN⟩ := χ.three_le_conductor_and_conductor_le_of_ne_one hχ
  have hlog_pos : 0 < Real.log χ.conductor :=
    zero_lt_one.trans (Real.one_lt_log_of_three_le hc3)
  have hlog_le : Real.log χ.conductor ≤ Real.log N := Real.log_le_log (by linarith) hcN
  have hphi : 0 ≤ Real.log Real.goldenRatio := (Real.log_pos Real.one_lt_goldenRatio).le
  refine le_trans ?_ (χ.div_sqrt_conductor_mul_log_sq_le_one_sub_of_LFunction_eq_zero hq hχ hβ)
  gcongr

/-- **Conductor-form power zero-gap bound for quadratic characters.** For every nonprincipal
quadratic character `χ` of nonzero level `N`, every `ε > 0`, and every real zero `β` of `L(s, χ)`,
`(log φ · ε ^ 2 / 128) q ^ (-1/2 - ε) ≤ 1 - β`, where `q = χ.conductor`. -/
theorem mul_rpow_conductor_neg_half_sub_le_one_sub_of_LFunction_eq_zero
    (hq : χ.IsQuadratic) (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε) {β : ℝ}
    (hβ : χ.LFunction β = 0) :
    Real.log Real.goldenRatio * ε ^ 2 / 128 * (χ.conductor : ℝ) ^ (-(1 / 2 : ℝ) - ε) ≤ 1 - β := by
  obtain ⟨hc3, _⟩ := χ.three_le_conductor_and_conductor_le_of_ne_one hχ
  have hc0 : (0 : ℝ) < χ.conductor := by linarith
  have hlog_pos : 0 < Real.log χ.conductor :=
    zero_lt_one.trans (Real.one_lt_log_of_three_le hc3)
  have hphi : 0 ≤ Real.log Real.goldenRatio := (Real.log_pos Real.one_lt_goldenRatio).le
  have hpow : 32 * √(χ.conductor : ℝ) * Real.log χ.conductor ^ 2 ≤
      128 / ε ^ 2 * (χ.conductor : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
    calc 32 * √(χ.conductor : ℝ) * Real.log χ.conductor ^ 2
        = 32 * (√(χ.conductor : ℝ) * Real.log χ.conductor ^ 2) := by ring
      _ ≤ 32 * ((2 / ε) ^ 2 * (χ.conductor : ℝ) ^ ((1 / 2 : ℝ) + ε)) :=
          mul_le_mul_of_nonneg_left
            (TauCeti.sqrt_mul_log_sq_le_div_sq_mul_rpow (by linarith) hε) (by positivity)
      _ = 128 / ε ^ 2 * (χ.conductor : ℝ) ^ ((1 / 2 : ℝ) + ε) := by ring
  have : 0 < √(χ.conductor : ℝ) := Real.sqrt_pos.mpr hc0
  have hexp : -(1 / 2 : ℝ) - ε = -((1 / 2 : ℝ) + ε) := by ring
  calc Real.log Real.goldenRatio * ε ^ 2 / 128 * (χ.conductor : ℝ) ^ (-(1 / 2 : ℝ) - ε)
      = Real.log Real.goldenRatio / (128 / ε ^ 2 * (χ.conductor : ℝ) ^ ((1 / 2 : ℝ) + ε)) := by
        rw [hexp, Real.rpow_neg hc0.le]
        field_simp
    _ ≤ Real.log Real.goldenRatio / (32 * √(χ.conductor : ℝ) * Real.log χ.conductor ^ 2) := by
        gcongr
    _ ≤ 1 - β := χ.div_sqrt_conductor_mul_log_sq_le_one_sub_of_LFunction_eq_zero hq hχ hβ

/-- **Effective `N ^ (-1/2 - ε)` distance of a quadratic real zero from one.** For every
nonprincipal quadratic character `χ` of nonzero level `N`, every `ε > 0`, and every real zero `β`
of `L(s, χ)`, `(log φ · ε ^ 2 / 128) N ^ (-1/2 - ε) ≤ 1 - β`. -/
theorem mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero
    (hq : χ.IsQuadratic) (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε) {β : ℝ}
    (hβ : χ.LFunction β = 0) :
    Real.log Real.goldenRatio * ε ^ 2 / 128 * (N : ℝ) ^ (-(1 / 2 : ℝ) - ε) ≤ 1 - β := by
  obtain ⟨hc3, hcN⟩ := χ.three_le_conductor_and_conductor_le_of_ne_one hχ
  have hphi : 0 ≤ Real.log Real.goldenRatio * ε ^ 2 / 128 := by
    have := Real.log_pos Real.one_lt_goldenRatio
    positivity
  have hrpow : (N : ℝ) ^ (-(1 / 2 : ℝ) - ε) ≤ (χ.conductor : ℝ) ^ (-(1 / 2 : ℝ) - ε) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hcN (by linarith)
  exact (mul_le_mul_of_nonneg_left hrpow hphi).trans
    (χ.mul_rpow_conductor_neg_half_sub_le_one_sub_of_LFunction_eq_zero hq hχ hε hβ)

/-- **Uniform existential `N ^ (-1/2 - ε)` zero-gap bound** across all levels and nonprincipal
quadratic characters. -/
theorem exists_pos_mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsQuadratic → χ ≠ 1 → ∀ β : ℝ, χ.LFunction β = 0 →
        c * (N : ℝ) ^ (-(1 / 2 : ℝ) - ε) ≤ 1 - β :=
  ⟨Real.log Real.goldenRatio * ε ^ 2 / 128,
    by have := Real.log_pos Real.one_lt_goldenRatio; positivity,
    fun _ _ χ hq hχ _ hβ ↦ χ.mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero hq hχ hε hβ⟩

/-- **Effective inverse-level distance of a quadratic real zero from one.** Every real zero `β` of
a nonprincipal quadratic character `χ` of nonzero level `N` satisfies
`log φ / (512 N) ≤ 1 - β` (the `ε = 1 / 2` case of
`mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero`). -/
theorem div_level_le_one_sub_of_LFunction_eq_zero
    (hq : χ.IsQuadratic) (hχ : χ ≠ 1) {β : ℝ}
    (hβ : χ.LFunction β = 0) :
    Real.log Real.goldenRatio / (512 * (N : ℝ)) ≤ 1 - β := by
  have h := χ.mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero hq hχ
    (ε := (1 / 2 : ℝ)) (by norm_num) hβ
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hexp : -(1 / 2 : ℝ) - 1 / 2 = -1 := by norm_num
  convert h using 1
  rw [hexp, Real.rpow_neg_one]
  field_simp
  ring

end DirichletCharacter

namespace TauCeti.Multiquadratic

/-- **Effective distance of a real zero from one for a fundamental discriminant `D ≠ 1`.**
Every real zero `β` of `L(s, χ_D)` satisfies
`(log φ · ε ^ 2 / 128) |D| ^ (-1/2 - ε) ≤ 1 - β` for each `ε > 0`. -/
theorem mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero
    {D : ℤ} [NeZero D.natAbs] (hD : Int.IsFundamentalDiscr D) (hD1 : D ≠ 1) {ε : ℝ} (hε : 0 < ε)
    {β : ℝ} (hβ : (fundamentalDiscriminantCharCast ℂ D hD).LFunction β = 0) :
    Real.log Real.goldenRatio * ε ^ 2 / 128 * |(D : ℝ)| ^ (-(1 / 2 : ℝ) - ε) ≤ 1 - β := by
  have hχ : fundamentalDiscriminantCharCast ℂ D hD ≠ 1 :=
    fun h ↦ hD1 ((fundamentalDiscriminantCharCast_eq_one_iff hD).mp h)
  simpa [Nat.cast_natAbs, Int.cast_abs] using
    DirichletCharacter.mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero
      (fundamentalDiscriminantCharCast_isQuadratic hD) hχ hε hβ

/-- **Effective distance of a quadratic real zero from one for a squarefree radicand `d ≠ 1`**
(Koymans–Pagano, §7.2, proof of Proposition 7.6). For any squarefree integer `d ≠ 1`, any `ε > 0`,
and any real zero `β` of the continued `L`-function of
`fundamentalDiscriminantCharCast ℂ (fundamentalDiscriminant d)`,
`(log φ · ε ^ 2 / (256 · 4 ^ ε)) |d| ^ (-1/2 - ε) ≤ 1 - β`. -/
theorem mul_rpow_neg_half_sub_le_one_sub_of_squarefree_of_LFunction_eq_zero
    {d : ℤ} [NeZero (fundamentalDiscriminant d).natAbs] (hd : Squarefree d) (hd1 : d ≠ 1)
    {ε : ℝ} (hε : 0 < ε) {β : ℝ}
    (hβ : (fundamentalDiscriminantCharCast ℂ (fundamentalDiscriminant d)
      (isFundamentalDiscr_fundamentalDiscriminant hd)).LFunction β = 0) :
    Real.log Real.goldenRatio * ε ^ 2 / (256 * (4 : ℝ) ^ ε) *
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
    have h4_half : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 2⁻¹ := by
      have h4 : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
      rw [h4, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), h4_half, Real.rpow_neg (by norm_num), mul_inv]
  have hrpow_le : (4 * |(d : ℝ)|) ^ (-(1 / 2 : ℝ) - ε) ≤ |(D : ℝ)| ^ (-(1 / 2 : ℝ) - ε) :=
    Real.rpow_le_rpow_of_nonpos hD_pos hD_le (by linarith)
  calc
    Real.log Real.goldenRatio * ε ^ 2 / (256 * (4 : ℝ) ^ ε) *
        |(d : ℝ)| ^ (-(1 / 2 : ℝ) - ε)
        = Real.log Real.goldenRatio * ε ^ 2 / 128 *
            (4 * |(d : ℝ)|) ^ (-(1 / 2 : ℝ) - ε) := by
      rw [Real.mul_rpow (by norm_num) (abs_nonneg _), h4_rpow]
      field_simp
      ring
    _ ≤ Real.log Real.goldenRatio * ε ^ 2 / 128 * |(D : ℝ)| ^ (-(1 / 2 : ℝ) - ε) :=
      mul_le_mul_of_nonneg_left hrpow_le (by positivity)
    _ ≤ 1 - β := mul_rpow_neg_half_sub_le_one_sub_of_LFunction_eq_zero hD hD1 hε hβ

/-- **Uniform existential `|d| ^ (-1/2 - ε)` zero-gap bound** across all squarefree integers
`d ≠ 1`. -/
theorem exists_pos_mul_rpow_le_one_sub_of_squarefree_of_LFunction_eq_zero
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ (d : ℤ) [NeZero (fundamentalDiscriminant d).natAbs] (hd : Squarefree d),
      d ≠ 1 → ∀ β : ℝ,
        (fundamentalDiscriminantCharCast ℂ (fundamentalDiscriminant d)
          (isFundamentalDiscr_fundamentalDiscriminant hd)).LFunction β = 0 →
          c * |(d : ℝ)| ^ (-(1 / 2 : ℝ) - ε) ≤ 1 - β :=
  ⟨Real.log Real.goldenRatio * ε ^ 2 / (256 * (4 : ℝ) ^ ε),
    by have := Real.log_pos Real.one_lt_goldenRatio; positivity,
    fun _ _ hd hd1 _ hβ ↦
      mul_rpow_neg_half_sub_le_one_sub_of_squarefree_of_LFunction_eq_zero hd hd1 hε hβ⟩

end TauCeti.Multiquadratic

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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Deriv
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.FundamentalDiscriminant
import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta

/-!
# Effective distance of a quadratic real zero from `1`

For a primitive nonprincipal quadratic Dirichlet character `χ` of level `N`, `χ` is the Kronecker
character `χ_D` of a fundamental discriminant `D ≠ 1` with `|D| = N`, so the analytic class-number
lower bound `2 log ((1 + √5) / 2) / √|D| ≤ (L(1, χ_D)).re`
(`TauCeti.Multiquadratic.two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re`) gives:

`2 log ((1 + √5) / 2) / √N ≤ (L(1, χ)).re ≤ ‖L(1, χ)‖`.

Combining this lower bound with the near-one derivative zero-separation estimate
`‖L(1, χ)‖ / (64 (log N)²) ≤ 1 - β`
(`DirichletCharacter.norm_LFunction_one_div_log_sq_le_one_sub_of_LFunction_eq_zero`) and passing
from an arbitrary nonprincipal quadratic character to its primitive character on `Re(s) > 0`
(`DirichletCharacter.LFunction_changeLevel_eq_zero_iff`) gives an effective zero-free margin left
of `s = 1` for *every* nonprincipal quadratic character `χ` of level `N` and *every* real zero `β`
of `L(s, χ)`:

* `log φ / (32 √q (log q)²) ≤ 1 - β` in terms of the conductor `q = χ.conductor`, hence
  `log φ / (32 √N (log N)²) ≤ 1 - β` in terms of the ambient level `N`;
* `(ε² log φ / 128) N^{-(1/2 + ε)} ≤ 1 - β` for every `ε > 0`;
* `(log φ / 512) N⁻¹ ≤ 1 - β` at `ε = 1 / 2`, excluding real zeros `β > 1 - c / N` up to any fixed
  conductor threshold without ineffective constants.

## Main results

* `DirichletCharacter.IsPrimitive.two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re` and
  `DirichletCharacter.IsPrimitive.two_mul_log_goldenRatio_div_sqrt_le_norm_LFunction_one`:
  `2 log φ / √N ≤ (L(1, χ)).re ≤ ‖L(1, χ)‖` for every primitive nonprincipal quadratic character
  `χ` of level `N`.
* `DirichletCharacter.div_sqrt_conductor_mul_log_sq_le_one_sub_of_LFunction_eq_zero` and
  `DirichletCharacter.div_sqrt_mul_log_sq_le_one_sub_of_LFunction_eq_zero`:
  `log φ / (32 √q (log q)²) ≤ 1 - β` and `log φ / (32 √N (log N)²) ≤ 1 - β` for every real zero `β`
  of `L(s, χ)` of a nonprincipal quadratic character `χ`.
* `DirichletCharacter.mul_rpow_conductor_le_one_sub_of_LFunction_eq_zero`,
  `DirichletCharacter.mul_rpow_le_one_sub_of_LFunction_eq_zero`, and
  `DirichletCharacter.exists_pos_mul_rpow_le_one_sub_of_LFunction_eq_zero`:
  effective `N^{-(1/2 + ε)}` distance of a real zero from `1`.
* `DirichletCharacter.div_level_le_one_sub_of_LFunction_eq_zero`: the `N⁻¹` zero-gap bound
  `log φ / (512 N) ≤ 1 - β`.
* `TauCeti.Multiquadratic.mul_rpow_natAbs_le_one_sub_of_LFunction_eq_zero` and
  `TauCeti.Multiquadratic.exists_pos_mul_rpow_natAbs_le_one_sub_of_LFunction_eq_zero`:
  the corresponding `|d|^{-(1/2 + ε)}` bounds for the quadratic character attached to a squarefree
  integer `d ≠ 1`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, American Mathematical Society, 2019,
  Lemma 11.2 and (12.11)–(12.12).
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Springer, 2000, Chapters 6 and 21.
* P. Koymans and C. Pagano, *A sharp upper bound for the 2-torsion of class groups of
  multiquadratic fields*, Mathematika **68** (2022), §7.2.
-/

public section

open Complex

namespace DirichletCharacter

open TauCeti.Multiquadratic

section LOneLowerBound

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- **Sharp lower bound on `(L(1, χ)).re` for a primitive nonprincipal quadratic character.** For
every primitive nonprincipal quadratic Dirichlet character `χ` of level `N`,
`2 log ((1 + √5) / 2) / √N ≤ (L(1, χ)).re`, with equality at `N = 5`. -/
theorem IsPrimitive.two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re (hprim : χ.IsPrimitive)
    (hq : χ.IsQuadratic) (hχ : χ ≠ 1) :
    2 * Real.log Real.goldenRatio / √(N : ℝ) ≤ (χ.LFunction 1).re := by
  obtain ⟨D, hD, rfl, hval⟩ := hprim.exists_isFundamentalDiscr_apply_eq hq
  have hχ_eq : χ = fundamentalDiscriminantCharCast ℂ D hD :=
    MulChar.ext' fun x ↦ by
      obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
      exact hval n
  have hD1 : D ≠ 1 := fun h1 ↦
    hχ (hχ_eq.trans ((fundamentalDiscriminantCharCast_eq_one_iff hD).mpr h1))
  rw [hχ_eq]
  exact TauCeti.Multiquadratic.two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re hD hD1

/-- **Norm lower bound on `L(1, χ)` for a primitive nonprincipal quadratic character.** -/
theorem IsPrimitive.two_mul_log_goldenRatio_div_sqrt_le_norm_LFunction_one (hprim : χ.IsPrimitive)
    (hq : χ.IsQuadratic) (hχ : χ ≠ 1) :
    2 * Real.log Real.goldenRatio / √(N : ℝ) ≤ ‖χ.LFunction 1‖ :=
  (hprim.two_mul_log_goldenRatio_div_sqrt_le_LFunction_one_re hq hχ).trans (re_le_norm _)

end LOneLowerBound

section ZeroGap

/-- Elementary log-to-power comparison: for any integer `n ≥ 3` and `ε > 0`,
`32 √n (log n)² ≤ (128 / ε²) n ^ (1 / 2 + ε)`. -/
private theorem mul_sqrt_mul_log_sq_le_rpow {n : ℕ} (hn : 3 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    32 * √(n : ℝ) * Real.log n ^ 2 ≤ 128 / ε ^ 2 * (n : ℝ) ^ (1 / 2 + ε) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hn1
  have hlog_nonneg : 0 ≤ Real.log n := Real.log_nonneg hn1.le
  have hlog : Real.log n ≤ (n : ℝ) ^ (ε / 2) / (ε / 2) :=
    Real.log_natCast_le_rpow_div n (half_pos hε)
  have hlog_sq : Real.log n ^ 2 ≤ 4 / ε ^ 2 * (n : ℝ) ^ ε := by
    calc Real.log n ^ 2 ≤ ((n : ℝ) ^ (ε / 2) / (ε / 2)) ^ 2 :=
          pow_le_pow_left₀ hlog_nonneg hlog 2
      _ = 4 / ε ^ 2 * ((n : ℝ) ^ (ε / 2)) ^ 2 := by field_simp; ring
      _ = 4 / ε ^ 2 * (n : ℝ) ^ ε := by
          rw [sq ((n : ℝ) ^ (ε / 2)), ← Real.rpow_add hn0, add_halves]
  calc 32 * √(n : ℝ) * Real.log n ^ 2
      ≤ 32 * (n : ℝ) ^ (1 / 2 : ℝ) * (4 / ε ^ 2 * (n : ℝ) ^ ε) := by
        rw [← Real.sqrt_eq_rpow]
        gcongr
      _ = 128 / ε ^ 2 * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ ε) := by ring
      _ = 128 / ε ^ 2 * (n : ℝ) ^ (1 / 2 + ε) := by rw [← Real.rpow_add hn0]

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- **Conductor-level zero-gap bound for a nonprincipal quadratic character.** For every
nonprincipal quadratic Dirichlet character `χ` (primitive or imprimitive) and every real zero `β`
of `L(s, χ)`, `log ((1 + √5) / 2) / (32 √q (log q)²) ≤ 1 - β`, where `q = χ.conductor`. -/
theorem div_sqrt_conductor_mul_log_sq_le_one_sub_of_LFunction_eq_zero (hq : χ.IsQuadratic)
    (hχ : χ ≠ 1) {β : ℝ} (hβ : χ.LFunction β = 0) :
    Real.log Real.goldenRatio / (32 * √(χ.conductor : ℝ) * Real.log χ.conductor ^ 2) ≤ 1 - β := by
  have hc3 : 3 ≤ χ.conductor := χ.three_le_conductor_of_ne_one hχ
  have : NeZero χ.conductor := ⟨by omega⟩
  have hlog_gt1 : 1 < Real.log χ.conductor := by
    have hc3' : (3 : ℝ) ≤ χ.conductor := mod_cast hc3
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  rcases le_or_gt β 0 with hβ0 | hβ0
  · have hphi_lt1 : Real.log Real.goldenRatio < 1 := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log Real.goldenRatio_pos
        (Real.goldenRatio_lt_two.trans (by linarith [Real.exp_one_gt_d9]))
    have hsqrt_ge1 : 1 ≤ √(χ.conductor : ℝ) :=
      Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1 ≤ χ.conductor))
    have hden_ge1 : 1 ≤ 32 * √(χ.conductor : ℝ) * Real.log χ.conductor ^ 2 := by nlinarith
    have hdiv_le1 :
        Real.log Real.goldenRatio / (32 * √(χ.conductor : ℝ) * Real.log χ.conductor ^ 2) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  · have hprim_ne : χ.primitiveCharacter ≠ 1 := fun h1 ↦
      hχ (by rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
    have hprim_q : χ.primitiveCharacter.IsQuadratic :=
      (isQuadratic_changeLevel_iff χ.conductor_dvd_level).mp
        (by rwa [χ.changeLevel_primitiveCharacter])
    have hprim_zero : χ.primitiveCharacter.LFunction β = 0 :=
      (LFunction_changeLevel_eq_zero_iff χ.primitiveCharacter χ.conductor_dvd_level
        (by simpa using hβ0) (.inl hprim_ne)).mp (by rwa [χ.changeLevel_primitiveCharacter])
    have hgap := χ.primitiveCharacter.norm_LFunction_one_div_log_sq_le_one_sub_of_LFunction_eq_zero
      hprim_ne hprim_zero
    have hL1 :=
      χ.primitiveCharacter_isPrimitive.two_mul_log_goldenRatio_div_sqrt_le_norm_LFunction_one
        hprim_q hprim_ne
    calc Real.log Real.goldenRatio / (32 * √(χ.conductor : ℝ) * Real.log χ.conductor ^ 2)
        = (2 * Real.log Real.goldenRatio / √(χ.conductor : ℝ)) /
            (64 * Real.log χ.conductor ^ 2) := by ring
      _ ≤ ‖χ.primitiveCharacter.LFunction 1‖ / (64 * Real.log χ.conductor ^ 2) := by gcongr
      _ ≤ 1 - β := hgap

/-- **Level-form logarithmic zero-gap bound for a nonprincipal quadratic character.** For every
nonprincipal quadratic character `χ` of level `N` and every real zero `β` of `L(s, χ)`,
`log ((1 + √5) / 2) / (32 √N (log N)²) ≤ 1 - β`. -/
theorem div_sqrt_mul_log_sq_le_one_sub_of_LFunction_eq_zero (hq : χ.IsQuadratic) (hχ : χ ≠ 1)
    {β : ℝ} (hβ : χ.LFunction β = 0) :
    Real.log Real.goldenRatio / (32 * √(N : ℝ) * Real.log N ^ 2) ≤ 1 - β := by
  have hc3 : 3 ≤ χ.conductor := χ.three_le_conductor_of_ne_one hχ
  have hcN : (χ.conductor : ℝ) ≤ N :=
    Nat.cast_le.mpr (Nat.le_of_dvd (NeZero.pos N) χ.conductor_dvd_level)
  have hc_pos : (0 : ℝ) < χ.conductor := by exact_mod_cast (by omega : 0 < χ.conductor)
  have hlog_pos : 0 < Real.log χ.conductor :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < χ.conductor))
  have hlog_le : Real.log χ.conductor ≤ Real.log N := Real.log_le_log hc_pos hcN
  have hphi : 0 ≤ Real.log Real.goldenRatio := (Real.log_pos Real.one_lt_goldenRatio).le
  refine le_trans ?_ (χ.div_sqrt_conductor_mul_log_sq_le_one_sub_of_LFunction_eq_zero hq hχ hβ)
  gcongr

/-- **Conductor-form power zero-gap bound for a nonprincipal quadratic character.** For every
`ε > 0`, every nonprincipal quadratic character `χ`, and every real zero `β` of `L(s, χ)`,
`(ε² log φ / 128) q^{-(1/2 + ε)} ≤ 1 - β`, where `q = χ.conductor`. -/
theorem mul_rpow_conductor_le_one_sub_of_LFunction_eq_zero {ε : ℝ} (hε : 0 < ε)
    (hq : χ.IsQuadratic) (hχ : χ ≠ 1) {β : ℝ} (hβ : χ.LFunction β = 0) :
    ε ^ 2 * Real.log Real.goldenRatio / 128 * (χ.conductor : ℝ) ^ (-(1 / 2 + ε)) ≤ 1 - β := by
  have hc3 : 3 ≤ χ.conductor := χ.three_le_conductor_of_ne_one hχ
  have hc0 : (0 : ℝ) < χ.conductor := by exact_mod_cast (by omega : 0 < χ.conductor)
  have hlog_pos : 0 < Real.log χ.conductor :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < χ.conductor))
  have hphi : 0 ≤ Real.log Real.goldenRatio := (Real.log_pos Real.one_lt_goldenRatio).le
  have hpow := mul_sqrt_mul_log_sq_le_rpow hc3 hε
  have : 0 < √(χ.conductor : ℝ) := Real.sqrt_pos.mpr hc0
  calc ε ^ 2 * Real.log Real.goldenRatio / 128 * (χ.conductor : ℝ) ^ (-(1 / 2 + ε))
      = Real.log Real.goldenRatio / (128 / ε ^ 2 * (χ.conductor : ℝ) ^ (1 / 2 + ε)) := by
        rw [Real.rpow_neg hc0.le]
        field_simp
    _ ≤ Real.log Real.goldenRatio / (32 * √(χ.conductor : ℝ) * Real.log χ.conductor ^ 2) := by
        gcongr
    _ ≤ 1 - β := χ.div_sqrt_conductor_mul_log_sq_le_one_sub_of_LFunction_eq_zero hq hχ hβ

/-- **Effective `N^{-(1/2 + ε)}` distance of a quadratic real zero from `1`.** For every `ε > 0`,
every nonprincipal quadratic Dirichlet character `χ` of level `N`, and every real zero `β` of
`L(s, χ)`, `(ε² log φ / 128) N^{-(1/2 + ε)} ≤ 1 - β`. -/
theorem mul_rpow_le_one_sub_of_LFunction_eq_zero {ε : ℝ} (hε : 0 < ε) (hq : χ.IsQuadratic)
    (hχ : χ ≠ 1) {β : ℝ} (hβ : χ.LFunction β = 0) :
    ε ^ 2 * Real.log Real.goldenRatio / 128 * (N : ℝ) ^ (-(1 / 2 + ε)) ≤ 1 - β := by
  have hc3 : 3 ≤ χ.conductor := χ.three_le_conductor_of_ne_one hχ
  have hc0 : (0 : ℝ) < χ.conductor := by exact_mod_cast (by omega : 0 < χ.conductor)
  have hcN : (χ.conductor : ℝ) ≤ N :=
    Nat.cast_le.mpr (Nat.le_of_dvd (NeZero.pos N) χ.conductor_dvd_level)
  have hphi : 0 ≤ ε ^ 2 * Real.log Real.goldenRatio / 128 := by
    have := Real.log_pos Real.one_lt_goldenRatio
    positivity
  have hrpow : (N : ℝ) ^ (-(1 / 2 + ε)) ≤ (χ.conductor : ℝ) ^ (-(1 / 2 + ε)) :=
    Real.rpow_le_rpow_of_nonpos hc0 hcN (by linarith)
  exact (mul_le_mul_of_nonneg_left hrpow hphi).trans
    (χ.mul_rpow_conductor_le_one_sub_of_LFunction_eq_zero hε hq hχ hβ)

/-- **Uniform existential `N^{-(1/2 + ε)}` zero-gap bound** across all levels and nonprincipal
quadratic characters. -/
theorem exists_pos_mul_rpow_le_one_sub_of_LFunction_eq_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsQuadratic → χ ≠ 1 → ∀ β : ℝ, χ.LFunction β = 0 →
        c * (N : ℝ) ^ (-(1 / 2 + ε)) ≤ 1 - β :=
  ⟨ε ^ 2 * Real.log Real.goldenRatio / 128,
    by have := Real.log_pos Real.one_lt_goldenRatio; positivity,
    fun _ _ χ hq hχ _ hβ ↦ χ.mul_rpow_le_one_sub_of_LFunction_eq_zero hε hq hχ hβ⟩

/-- **Effective `N⁻¹` distance of a quadratic real zero from `1`.** For every nonprincipal
quadratic Dirichlet character `χ` of level `N` and every real zero `β` of `L(s, χ)`,
`log ((1 + √5) / 2) / (512 N) ≤ 1 - β`. -/
theorem div_level_le_one_sub_of_LFunction_eq_zero (hq : χ.IsQuadratic) (hχ : χ ≠ 1) {β : ℝ}
    (hβ : χ.LFunction β = 0) :
    Real.log Real.goldenRatio / (512 * N) ≤ 1 - β := by
  -- Apply `mul_rpow_le_one_sub_of_LFunction_eq_zero` at `ε = 1 / 2`.
  have h := χ.mul_rpow_le_one_sub_of_LFunction_eq_zero (ε := 1 / 2) (by norm_num) hq hχ hβ
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  convert h using 1
  rw [show -(1 / 2 + (1 / 2 : ℝ)) = -1 by ring, Real.rpow_neg_one]
  field_simp
  ring

end ZeroGap

end DirichletCharacter

namespace TauCeti.Multiquadratic

/-- **Effective `|d|^{-(1/2 + ε)}` distance of a real zero from `1` for `ℚ(√d)`.** For any `ε > 0`,
any squarefree integer `d ≠ 1`, and any real zero `β` of `L(s, χ_d)` (where `χ_d` is the primitive
quadratic character of `fundamentalDiscriminant d`),
`(ε² log φ / 128) · 4^{-(1/2 + ε)} · |d|^{-(1/2 + ε)} ≤ 1 - β`. -/
theorem mul_rpow_natAbs_le_one_sub_of_LFunction_eq_zero {ε : ℝ} (hε : 0 < ε) {d : ℤ}
    [NeZero (fundamentalDiscriminant d).natAbs] (hsf : Squarefree d) (hd1 : d ≠ 1) {β : ℝ}
    (hβ : (fundamentalDiscriminantCharCast ℂ (fundamentalDiscriminant d)
      (isFundamentalDiscr_fundamentalDiscriminant hsf)).LFunction β = 0) :
    ε ^ 2 * Real.log Real.goldenRatio / 128 * (4 : ℝ) ^ (-(1 / 2 + ε)) *
      (d.natAbs : ℝ) ^ (-(1 / 2 + ε)) ≤ 1 - β := by
  have hD : Int.IsFundamentalDiscr (fundamentalDiscriminant d) :=
    isFundamentalDiscr_fundamentalDiscriminant hsf
  have hD1 : fundamentalDiscriminant d ≠ 1 := by
    have := hsf.ne_zero
    rw [fundamentalDiscriminant_def]
    split_ifs <;> omega
  have hχ_ne : fundamentalDiscriminantCharCast ℂ (fundamentalDiscriminant d) hD ≠ 1 :=
    (fundamentalDiscriminantCharCast_eq_one_iff hD).not.mpr hD1
  have hgap := (fundamentalDiscriminantCharCast ℂ (fundamentalDiscriminant d) hD)
    |>.mul_rpow_le_one_sub_of_LFunction_eq_zero
      hε (fundamentalDiscriminantCharCast_isQuadratic hD) hχ_ne hβ
  have hD_pos : (0 : ℝ) < (fundamentalDiscriminant d).natAbs :=
    Nat.cast_pos.mpr (NeZero.pos _)
  have hd_pos : (0 : ℝ) < d.natAbs := Nat.cast_pos.mpr (Int.natAbs_pos.mpr hsf.ne_zero)
  have hle : ((fundamentalDiscriminant d).natAbs : ℝ) ≤ 4 * (d.natAbs : ℝ) := by
    have hZ : (fundamentalDiscriminant d).natAbs ≤ 4 * d.natAbs := by
      rw [fundamentalDiscriminant_def]
      split_ifs <;> [omega; simp [Int.natAbs_mul]]
    exact_mod_cast hZ
  have hrpow : (4 : ℝ) ^ (-(1 / 2 + ε)) * (d.natAbs : ℝ) ^ (-(1 / 2 + ε)) ≤
      ((fundamentalDiscriminant d).natAbs : ℝ) ^ (-(1 / 2 + ε)) := by
    rw [← Real.mul_rpow (by norm_num) hd_pos.le]
    exact Real.rpow_le_rpow_of_nonpos hD_pos hle (by linarith)
  have hcoeff : 0 ≤ ε ^ 2 * Real.log Real.goldenRatio / 128 := by
    have := Real.log_pos Real.one_lt_goldenRatio
    positivity
  calc ε ^ 2 * Real.log Real.goldenRatio / 128 * (4 : ℝ) ^ (-(1 / 2 + ε)) *
        (d.natAbs : ℝ) ^ (-(1 / 2 + ε))
      = ε ^ 2 * Real.log Real.goldenRatio / 128 *
          ((4 : ℝ) ^ (-(1 / 2 + ε)) * (d.natAbs : ℝ) ^ (-(1 / 2 + ε))) := by ring
    _ ≤ ε ^ 2 * Real.log Real.goldenRatio / 128 *
          ((fundamentalDiscriminant d).natAbs : ℝ) ^ (-(1 / 2 + ε)) :=
        mul_le_mul_of_nonneg_left hrpow hcoeff
    _ ≤ 1 - β := hgap

/-- **Uniform existential `|d|^{-(1/2 + ε)}` zero-gap bound** over all squarefree integers
`d ≠ 1`. -/
theorem exists_pos_mul_rpow_natAbs_le_one_sub_of_LFunction_eq_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ (d : ℤ) [NeZero (fundamentalDiscriminant d).natAbs] (hsf : Squarefree d),
      d ≠ 1 → ∀ β : ℝ,
        (fundamentalDiscriminantCharCast ℂ (fundamentalDiscriminant d)
          (isFundamentalDiscr_fundamentalDiscriminant hsf)).LFunction β = 0 →
          c * (d.natAbs : ℝ) ^ (-(1 / 2 + ε)) ≤ 1 - β :=
  ⟨ε ^ 2 * Real.log Real.goldenRatio / 128 * (4 : ℝ) ^ (-(1 / 2 + ε)),
    by have := Real.log_pos Real.one_lt_goldenRatio; positivity,
    fun _ _ hsf hd1 _ hβ ↦ mul_rpow_natAbs_le_one_sub_of_LFunction_eq_zero hε hsf hd1 hβ⟩

end TauCeti.Multiquadratic

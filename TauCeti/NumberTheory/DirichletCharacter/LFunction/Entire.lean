/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Analytic.Order
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Data.Nat.ChineseRemainder

/-!
# Dirichlet L-functions with the pole removed, and quadratic twists

For a Dirichlet character `χ` modulo `N`, `DirichletCharacter.entireLFunction χ` (written `E_χ`)
is `L(s, χ)` if `χ` is not principal and the entire continuation of `(s - 1) L(s, χ)` (Mathlib's
`DirichletCharacter.LFunctionTrivChar₁`) if it is. `DirichletCharacter.regularizedLFunction χ`
(written `f_χ`) is `E_χ`, divided by `s` when `χ` is principal: it is holomorphic on `Re s > 0` and
has the size of `L(s, χ)` for large `|s|`.

`E_χ` is entire and has no zero on `Re s ≥ 1`; for `Re s > 1`,
`∑ χ(n) Λ(n) n^{-s} = δ_χ / (s - 1) - E_χ'(s) / E_χ(s)` with `δ_χ = 1` for principal `χ` and `0`
otherwise; and the residue of `E_χ' / E_χ` at any point is the order of vanishing of `E_χ` there.

The *Legendre twist* `DirichletCharacter.legendreTwist χ d` of a character `χ` modulo `N` by an
odd prime `d` is the character `n ↦ χ(n) (n / d)` modulo `N * d`. When `d` does not divide `N` it
is not principal, so its `E` is its L-function.

## Main definitions

* `DirichletCharacter.entireLFunction`: `E_χ`.
* `DirichletCharacter.regularizedLFunction`: `f_χ`.
* `DirichletCharacter.legendreTwist`: the Legendre twist of a character.

## Main results

* `DirichletCharacter.differentiable_entireLFunction`,
  `DirichletCharacter.entireLFunction_ne_zero_of_one_le_re`: ShortGRH roadmap
  ZeroFreeRegionsAndPrimesInShortWindows 1.1 (a).
* `DirichletCharacter.LSeriesHasSum_twist_vonMangoldt`: 1.1 (b).
* `DirichletCharacter.tendsto_sub_mul_logDeriv_entireLFunction`: 1.1 (c).
* `DirichletCharacter.legendreTwist_apply`, `DirichletCharacter.legendreTwist_ne_one`,
  `DirichletCharacter.entireLFunction_legendreTwist`: 1.1 (d).

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC): `New.entireL` and `New.quadTwist` in
`src/Lib/General/NumberTheory/ImaginaryQuadraticField.lean`,
`New.regularL` and `New.differentiableAt_regularL` in
`src/Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean`, and `New.quadTwist_apply`,
`New.quadTwist_ne_one`, `New.analyticAt_entireL`, `New.entireL_ne_zero`,
`New.LSeriesHasSum_mul_vonMangoldt` and `New.tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt`
in `src/Lib/Analytic/EntireLFunction.lean`.
-/

public section

open Complex Filter ArithmeticFunction
open scoped Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}

open Classical in
/-- `E_χ`: the L-function `L(s, χ)` if `χ` is not principal, and the entire continuation of
`(s - 1) L(s, χ)` if `χ` is principal. -/
noncomputable def entireLFunction : ℂ → ℂ :=
  if χ = 1 then LFunctionTrivChar₁ N else χ.LFunction

theorem entireLFunction_of_ne_one (hχ : χ ≠ 1) : χ.entireLFunction = χ.LFunction := by
  simp [entireLFunction, hχ]

theorem entireLFunction_one : (1 : DirichletCharacter ℂ N).entireLFunction = LFunctionTrivChar₁ N :=
  by simp [entireLFunction]

/-- `E_χ(s) = (s - 1) L(s, χ)` for principal `χ` and `s ≠ 1`. -/
theorem entireLFunction_one_apply (hs : s ≠ 1) :
    (1 : DirichletCharacter ℂ N).entireLFunction s =
      (s - 1) * (1 : DirichletCharacter ℂ N).LFunction s := by
  rw [entireLFunction_one, LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar]

/-- `E_χ` is entire. -/
theorem differentiable_entireLFunction : Differentiable ℂ χ.entireLFunction := by
  rw [entireLFunction]
  split_ifs with hχ
  exacts [differentiable_LFunctionTrivChar₁ N, differentiable_LFunction hχ]

@[fun_prop]
theorem analyticAt_entireLFunction (s : ℂ) : AnalyticAt ℂ χ.entireLFunction s :=
  χ.differentiable_entireLFunction.analyticAt s

/-- `E_χ` has no zero on `Re s ≥ 1`. -/
theorem entireLFunction_ne_zero_of_one_le_re (hs : 1 ≤ s.re) : χ.entireLFunction s ≠ 0 := by
  rw [entireLFunction]
  split_ifs with hχ
  · obtain rfl | hs_ne := eq_or_ne s 1
    · exact LFunctionTrivChar₁_apply_one_ne_zero N
    · rw [LFunctionTrivChar₁, Function.update_of_ne hs_ne]
      exact mul_ne_zero (sub_ne_zero.2 hs_ne) (LFunction_ne_zero_of_one_le_re 1 (.inr hs_ne) hs)
  · exact LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs

open Classical in
/-- For `Re s > 1`, `∑ χ(n) Λ(n) n^{-s} = δ_χ / (s - 1) - E_χ'(s) / E_χ(s)`, where `δ_χ` is `1`
if `χ` is principal and `0` otherwise. -/
theorem LSeriesHasSum_twist_vonMangoldt (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ χ n * Λ n) s
      ((if χ = 1 then 1 else 0) / (s - 1) - logDeriv χ.entireLFunction s) := by
  refine LSeriesHasSum_iff.2 ⟨χ.LSeriesSummable_twist_vonMangoldt hs, ?_⟩
  have hs_ne : s ≠ 1 := ne_of_apply_ne re hs.ne'
  have h_series : LSeries (fun n ↦ χ n * Λ n) s = -deriv χ.LFunction s / χ.LFunction s := by
    rw [χ.deriv_LFunction_eq_deriv_LSeries hs, χ.LFunction_eq_LSeries hs]
    exact χ.LSeries_twist_vonMangoldt_eq hs
  have hL_ne : χ.LFunction s ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inr hs_ne) hs.le
  rw [h_series, entireLFunction, logDeriv_apply]
  obtain rfl | hχ := eq_or_ne χ 1
  · rw [ite_eq_left rfl, ite_eq_left rfl, deriv_LFunctionTrivChar₁_apply_of_ne_one N hs_ne,
      LFunctionTrivChar₁, Function.update_of_ne hs_ne, LFunctionTrivChar]
    field_simp [sub_ne_zero.2 hs_ne]
    ring
  · simp [hχ, neg_div]

theorem analyticOrderAt_entireLFunction_ne_top (s : ℂ) : analyticOrderAt χ.entireLFunction s ≠ ⊤ :=
  -- An entire function of infinite order at a point is zero, but `E_χ(1) ≠ 0`.
  fun h_top ↦ χ.entireLFunction_ne_zero_of_one_le_re (s := 1) le_rfl
    (congrFun ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s (by fun_prop)).1 h_top) 1)

/-- The residue of `E_χ' / E_χ` at any point `s` is the order of vanishing of `E_χ` at `s`: so
`E_χ' / E_χ` has at most simple poles. -/
theorem tendsto_sub_mul_logDeriv_entireLFunction (s : ℂ) :
    Tendsto (fun z ↦ (z - s) * logDeriv χ.entireLFunction z) (𝓝[≠] s)
      (𝓝 (analyticOrderNatAt χ.entireLFunction s : ℂ)) := by
  -- Near `s`, `E_χ = (z - s) ^ n • g` with `g s ≠ 0`, so `E_χ' / E_χ = n / (z - s) + g' / g`.
  set n := analyticOrderNatAt χ.entireLFunction s
  obtain ⟨g, hg, hg_ne, h_eq⟩ :
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ g s ≠ 0 ∧
        χ.entireLFunction =ᶠ[𝓝 s] fun z ↦ (z - s) ^ n • g z :=
    (χ.analyticAt_entireLFunction s).analyticOrderAt_ne_top.1
      (χ.analyticOrderAt_entireLFunction_ne_top s)
  have h_lim : Tendsto (fun z ↦ n + (z - s) * logDeriv g z) (𝓝[≠] s) (𝓝 (n : ℂ)) := by
    have h_cont : ContinuousAt (logDeriv g) s := (hg.deriv.div hg hg_ne).continuousAt
    have := ((tendsto_id.sub_const s).mul h_cont).mono_left (nhdsWithin_le_nhds (s := {s}ᶜ))
    simpa using this.const_add (n : ℂ)
  refine h_lim.congr' ?_
  filter_upwards [nhdsWithin_le_nhds h_eq.deriv, nhdsWithin_le_nhds h_eq,
    nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hg_ne),
    nhdsWithin_le_nhds hg.eventually_analyticAt, self_mem_nhdsWithin]
    with z hz_deriv hz hgz hg_an (hzs : z ≠ s)
  have h_mul : logDeriv (fun w ↦ (w - s) ^ n * g w) z =
      logDeriv (fun w ↦ (w - s) ^ n) z + logDeriv g z :=
    logDeriv_mul z (pow_ne_zero n (sub_ne_zero.2 hzs)) hgz (by fun_prop) hg_an.differentiableAt
  calc n + (z - s) * logDeriv g z = (z - s) * (n / (z - s) + logDeriv g z) := by
        field_simp [sub_ne_zero.2 hzs]
    _ = (z - s) * logDeriv (fun w ↦ (w - s) ^ n * g w) z := by
        rw [h_mul, logDeriv_fun_pow (by fun_prop)]
        simp [logDeriv_apply, div_eq_mul_inv]
    _ = (z - s) * logDeriv χ.entireLFunction z := by
        simp only [logDeriv_apply, hz, hz_deriv, smul_eq_mul]

/-! ### The regularized L-function -/

open Classical in
/-- `f_χ`: `E_χ(s)` if `χ` is not principal, and `E_χ(s) / s` if it is; so
`f_χ(s) = L(s, χ₀) (s - 1) / s` for principal `χ₀` and `s ≠ 1`. -/
noncomputable def regularizedLFunction (s : ℂ) : ℂ :=
  χ.entireLFunction s / if χ = 1 then s else 1

theorem regularizedLFunction_of_ne_one (hχ : χ ≠ 1) :
    χ.regularizedLFunction = χ.LFunction := by
  ext s
  simp [regularizedLFunction, hχ, entireLFunction_of_ne_one]

theorem regularizedLFunction_one_apply (s : ℂ) :
    (1 : DirichletCharacter ℂ N).regularizedLFunction s =
      (1 : DirichletCharacter ℂ N).entireLFunction s / s := by
  simp [regularizedLFunction]

/-- `f_χ` is holomorphic on `Re s > 0`. -/
theorem differentiableAt_regularizedLFunction (hs : 0 < s.re) :
    DifferentiableAt ℂ χ.regularizedLFunction s := by
  classical
  have h_denom : DifferentiableAt ℂ (fun z : ℂ ↦ if χ = 1 then z else 1) s := by
    split_ifs <;> fun_prop
  have h_ne : (if χ = 1 then s else 1) ≠ 0 := by
    split_ifs
    exacts [ne_zero_of_re_pos hs, one_ne_zero]
  exact (χ.analyticAt_entireLFunction s).differentiableAt.div h_denom h_ne

open Classical in
/-- For `Re s > 1`, `f_χ(s) = L(s, χ) (s - δ_χ) / s`. -/
theorem regularizedLFunction_eq_LSeries (hs : 1 < s.re) :
    χ.regularizedLFunction s = LSeries (fun n ↦ χ n) s / s * (s - if χ = 1 then 1 else 0) := by
  have hs_zero : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  rw [regularizedLFunction, entireLFunction, ← χ.LFunction_eq_LSeries hs]
  split_ifs with hχ
  · rw [hχ, LFunctionTrivChar₁, Function.update_of_ne (ne_of_apply_ne re hs.ne')]
    ring
  · field

/-- `f_χ` has no zero on `Re s ≥ 1`. -/
theorem regularizedLFunction_ne_zero_of_one_le_re (hs : 1 ≤ s.re) :
    χ.regularizedLFunction s ≠ 0 := by
  refine div_ne_zero (χ.entireLFunction_ne_zero_of_one_le_re hs) ?_
  split_ifs
  exacts [ne_zero_of_re_pos (by linarith), one_ne_zero]

/-! ### Legendre twists -/

section LegendreTwist

variable (d : ℕ) [Fact d.Prime]

/-- The *Legendre twist* of a character `χ` modulo `N` by a prime `d`: the character
`n ↦ χ(n) (n / d)` modulo `N * d`. -/
noncomputable def legendreTwist : DirichletCharacter ℂ (N * d) :=
  χ.changeLevel (dvd_mul_right N d) *
    changeLevel (dvd_mul_left d N) ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))

omit [NeZero N] in
/-- The Legendre twist takes the value `χ(n) (n / d)` at an integer `n`. -/
theorem legendreTwist_apply (n : ℤ) : χ.legendreTwist d n = χ n * legendreSym d n := by
  -- Both sides vanish unless `n` is prime to `N` and to `d`; then the change of level keeps values.
  rw [show (legendreSym d n : ℂ) =
    (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) n from rfl]
  by_cases h_cop : IsCoprime n (N * d : ℕ)
  · rw [legendreTwist, MulChar.mul_apply, changeLevel_eq_cast_of_dvd' _ _ h_cop,
      changeLevel_eq_cast_of_dvd' _ _ h_cop]
  · rw [(apply_eq_zero_iff (χ.legendreTwist d) n).2 h_cop, zero_eq_mul, apply_eq_zero_iff,
      apply_eq_zero_iff]
    rwa [Nat.cast_mul, IsCoprime.mul_right_iff, not_and_or] at h_cop

omit [NeZero N] in
/-- For an odd prime `d` not dividing `N`, the Legendre twist of any character modulo `N` by `d`
is not principal: at an integer that is `1` modulo `N` and a non-residue modulo `d` it is `-1`. -/
theorem legendreTwist_ne_one (hd : d ≠ 2) (hN : N.Coprime d) : χ.legendreTwist d ≠ 1 := by
  intro h_one
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod d) (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨n, (hn_N : n ≡ 1 [MOD N]), (hn_d : n ≡ a.val [MOD d])⟩ := Nat.chineseRemainder hN 1 a.val
  have hn_one : (n : ZMod N) = 1 := by simpa [← ZMod.natCast_eq_natCast_iff] using hn_N
  have hn_a : (n : ZMod d) = a := by simpa [← ZMod.natCast_eq_natCast_iff] using hn_d
  have h_val : χ.legendreTwist d n = -1 := by
    simpa [hn_one, legendreSym, hn_a, ha] using χ.legendreTwist_apply d n
  have h_sq : χ.legendreTwist d n * χ.legendreTwist d n = χ.legendreTwist d n := by
    simp [← MulChar.mul_apply, h_one]
  norm_num [h_val] at h_sq

/-- For an odd prime `d` not dividing `N`, `E` of the Legendre twist is its L-function. -/
theorem entireLFunction_legendreTwist (hd : d ≠ 2) (hN : N.Coprime d) :
    (χ.legendreTwist d).entireLFunction = (χ.legendreTwist d).LFunction :=
  entireLFunction_of_ne_one _ (χ.legendreTwist_ne_one d hd hN)

end LegendreTwist

end DirichletCharacter

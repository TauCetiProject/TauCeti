/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Analytic.Order
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LegendreTwist
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Contour.Residue.LogDeriv

/-!
# Dirichlet L-functions with the pole removed

For a Dirichlet character `χ` modulo `N`, `DirichletCharacter.entireLFunction χ` (written `E_χ`)
is `L(s, χ)` if `χ` is not principal and the entire continuation of `(s - 1) L(s, χ)` (Mathlib's
`DirichletCharacter.LFunctionTrivChar₁`) if it is. `DirichletCharacter.regularizedLFunction χ`
(written `f_χ`) is `E_χ`, divided by `s` when `χ` is principal: it is holomorphic on `Re s > 0` and
has the size of `L(s, χ)` for large `|s|`.

`E_χ` is entire and has no zero on `Re s ≥ 1`; for `Re s > 1`,
`∑ χ(n) Λ(n) n^{-s} = δ_χ / (s - 1) - E_χ'(s) / E_χ(s)` with `δ_χ = 1` for principal `χ` and `0`
otherwise; and the residue of `E_χ' / E_χ` at any point is the order of vanishing of `E_χ` there.

For an odd prime `d` not dividing `N`, the Legendre twist `DirichletCharacter.legendreTwist χ d`
is not principal, so its `E` is its L-function.

## Main definitions

* `DirichletCharacter.regularizedLFunction`: `f_χ`. The function `E_χ` itself,
  `DirichletCharacter.entireLFunction`, is defined in
  `TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic`.

## Main results

* `DirichletCharacter.differentiable_entireLFunction`,
  `DirichletCharacter.entireLFunction_ne_zero_of_one_le_re`: `E_χ` is entire and has no zero on
  `Re s ≥ 1`.
* `DirichletCharacter.LSeriesHasSum_twist_vonMangoldt`: the Dirichlet series of `χ Λ` is
  `δ_χ / (s - 1) - E_χ' / E_χ` on `Re s > 1`.
* `DirichletCharacter.tendsto_sub_mul_logDeriv_entireLFunction`: the residue of `E_χ' / E_χ` at
  `s` is the order of vanishing of `E_χ` at `s`.
* `DirichletCharacter.entireLFunction_legendreTwist`: `E` of a Legendre twist by an odd prime not
  dividing the level is its L-function.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC): `New.entireL` in `src/Lib/General/NumberTheory/ImaginaryQuadraticField.lean`,
`New.regularL` and `New.differentiableAt_regularL` in
`src/Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean`, and `New.analyticAt_entireL`,
`New.entireL_ne_zero`,
`New.LSeriesHasSum_mul_vonMangoldt` and `New.tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt`
in `src/Lib/Analytic/EntireLFunction.lean`.
-/

public section

open Complex Filter ArithmeticFunction
open scoped Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}

/-- `E_χ(s) = (s - 1) L(s, χ)` for principal `χ` and `s ≠ 1`. -/
theorem entireLFunction_one_apply (hs : s ≠ 1) :
    (1 : DirichletCharacter ℂ N).entireLFunction s =
      (s - 1) * (1 : DirichletCharacter ℂ N).LFunction s := by
  rw [entireLFunction_one, LFunctionTrivChar₁_apply_of_ne_one N hs, LFunctionTrivChar]

/-- `E_χ` is entire. -/
@[fun_prop]
theorem differentiable_entireLFunction : Differentiable ℂ χ.entireLFunction := by
  obtain rfl | hχ := eq_or_ne χ 1
  · rw [entireLFunction_one]
    exact differentiable_LFunctionTrivChar₁ N
  · rw [entireLFunction_of_ne_one hχ]
    exact differentiable_LFunction hχ

@[fun_prop]
theorem analyticAt_entireLFunction (s : ℂ) : AnalyticAt ℂ χ.entireLFunction s :=
  χ.differentiable_entireLFunction.analyticAt s

/-- `E_χ` has no zero on `Re s ≥ 1`. -/
theorem entireLFunction_ne_zero_of_one_le_re (hs : 1 ≤ s.re) : χ.entireLFunction s ≠ 0 := by
  obtain rfl | hχ := eq_or_ne χ 1
  · rw [entireLFunction_one]
    obtain rfl | hs_ne := eq_or_ne s 1
    · exact LFunctionTrivChar₁_apply_one_ne_zero N
    · rw [LFunctionTrivChar₁_apply_of_ne_one N hs_ne]
      exact mul_ne_zero (sub_ne_zero.2 hs_ne) (LFunction_ne_zero_of_one_le_re 1 (.inr hs_ne) hs)
  · rw [entireLFunction_of_ne_one hχ]
    exact LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs

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
  rw [h_series, logDeriv_apply]
  obtain rfl | hχ := eq_or_ne χ 1
  · rw [entireLFunction_one, ite_eq_left rfl, deriv_LFunctionTrivChar₁_apply_of_ne_one N hs_ne,
      LFunctionTrivChar₁_apply_of_ne_one N hs_ne, LFunctionTrivChar]
    field_simp [sub_ne_zero.2 hs_ne]
    ring
  · simp [hχ, neg_div, entireLFunction_of_ne_one hχ]

theorem analyticOrderAt_entireLFunction_ne_top (s : ℂ) : analyticOrderAt χ.entireLFunction s ≠ ⊤ :=
  -- An entire function of infinite order at a point is zero, but `E_χ(1) ≠ 0`.
  fun h_top ↦ χ.entireLFunction_ne_zero_of_one_le_re (s := 1) le_rfl
    (congrFun ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s (by fun_prop)).1 h_top) 1)

/-- The residue of `E_χ' / E_χ` at any point `s` is the order of vanishing of `E_χ` at `s`: so
`E_χ' / E_χ` has at most simple poles. -/
theorem tendsto_sub_mul_logDeriv_entireLFunction (s : ℂ) :
    Tendsto (fun z ↦ (z - s) * logDeriv χ.entireLFunction z) (𝓝[≠] s)
      (𝓝 (analyticOrderNatAt χ.entireLFunction s : ℂ)) := by
  have hm : MeromorphicAt χ.entireLFunction s := (χ.analyticAt_entireLFunction s).meromorphicAt
  have h_ord : meromorphicOrderAt χ.entireLFunction s =
      ((analyticOrderNatAt χ.entireLFunction s : ℤ) : WithTop ℤ) := by
    rw [(χ.analyticAt_entireLFunction s).meromorphicOrderAt_eq,
      ← Nat.cast_analyticOrderNatAt (χ.analyticOrderAt_entireLFunction_ne_top s), ENat.map_natCast]
  have h := TauCeti.Contour.tendsto_sub_mul_nhds_residue hm.logDeriv
    (TauCeti.Contour.neg_one_le_meromorphicOrderAt_logDeriv hm)
  rwa [TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt hm h_ord, Int.cast_natCast] at h

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

@[simp]
theorem regularizedLFunction_one_apply (s : ℂ) :
    (1 : DirichletCharacter ℂ N).regularizedLFunction s =
      (1 : DirichletCharacter ℂ N).entireLFunction s / s := by
  simp [regularizedLFunction]

/-- `f_χ` is holomorphic away from `0`, and everywhere if `χ` is not principal. -/
theorem differentiableAt_regularizedLFunction (hs : s ≠ 0 ∨ χ ≠ 1) :
    DifferentiableAt ℂ χ.regularizedLFunction s := by
  classical
  have h_denom : DifferentiableAt ℂ (fun z : ℂ ↦ if χ = 1 then z else 1) s := by
    split_ifs <;> fun_prop
  have h_ne : (if χ = 1 then s else 1) ≠ 0 := by
    split_ifs with hχ
    exacts [hs.resolve_right (not_not.2 hχ), one_ne_zero]
  exact (χ.analyticAt_entireLFunction s).differentiableAt.div h_denom h_ne

open Classical in
/-- For `Re s > 1`, `f_χ(s) = L(s, χ) (s - δ_χ) / s`. -/
theorem regularizedLFunction_eq_LSeries (hs : 1 < s.re) :
    χ.regularizedLFunction s = LSeries (fun n ↦ χ n) s / s * (s - if χ = 1 then 1 else 0) := by
  have hs_zero : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  rw [regularizedLFunction, ← χ.LFunction_eq_LSeries hs]
  obtain rfl | hχ := eq_or_ne χ 1
  · rw [entireLFunction_one, ite_eq_left rfl, ite_eq_left rfl,
      LFunctionTrivChar₁_apply_of_ne_one N (ne_of_apply_ne re hs.ne')]
    ring
  · rw [entireLFunction_of_ne_one hχ, ite_eq_right hχ, ite_eq_right hχ]
    field

/-- `f_χ` has no zero on `Re s ≥ 1`. -/
theorem regularizedLFunction_ne_zero_of_one_le_re (hs : 1 ≤ s.re) :
    χ.regularizedLFunction s ≠ 0 := by
  refine div_ne_zero (χ.entireLFunction_ne_zero_of_one_le_re hs) ?_
  split_ifs
  exacts [ne_zero_of_re_pos (by linarith), one_ne_zero]

/-! ### Legendre twists -/

section LegendreTwist

variable (d : ℕ) [Fact d.Prime]

/-- For an odd prime `d` not dividing `N`, `E` of the Legendre twist is its L-function. -/
theorem entireLFunction_legendreTwist (hd : d ≠ 2) (hN : N.Coprime d) :
    (χ.legendreTwist d).entireLFunction = (χ.legendreTwist d).LFunction :=
  entireLFunction_of_ne_one (χ.legendreTwist_ne_one d hd hN)

end LegendreTwist

end DirichletCharacter

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.SpecialFunctions.Pow.EulerFactor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel

/-!
# Logarithmic derivatives under level change for Dirichlet `L`-functions

Raising the level of a Dirichlet character `ψ` from `M` to a multiple `N` multiplies `ψ.LFunction`
by finitely many deleted Euler factors. Away from the principal pole (`s ≠ 1 ∨ ψ ≠ 1`) and away
from zeros, `logDeriv (changeLevel hMN ψ).LFunction s - logDeriv ψ.LFunction s` is the sum of the
logarithmic derivatives of those deleted Euler factors. On the closed half-plane `1 ≤ Re s`, this
difference has norm at most `log N` (including at `s = 1` for principal characters, where both
logarithmic derivatives vanish by totalization).

## Main results

* `DirichletCharacter.logDeriv_LFunction_changeLevel_sub`: exact deleted-Euler-factor formula for
  the difference of logarithmic derivatives under level change.
* `DirichletCharacter.norm_logDeriv_LFunction_changeLevel_sub_le`: uniform `log N` norm bound on
  `1 ≤ Re s`.

## References

* David Loeffler and Michael Stoll, `DirichletCharacter.LFunction_changeLevel` in
  `Mathlib.NumberTheory.LSeries.DirichletContinuation`.
* Michael Stoll, David Loeffler, and Terence Tao,
  `DirichletCharacter.LFunction_ne_zero_of_one_le_re` in
  `Mathlib.NumberTheory.LSeries.Nonvanishing`.
-/

public section

open Finset Complex

namespace DirichletCharacter

/-- Exact logarithmic-derivative formula for changing level: away from the principal pole
(`s ≠ 1 ∨ ψ ≠ 1`), if neither the deleted Euler factors nor `ψ.LFunction` vanish at `s`, then
`logDeriv (changeLevel hMN ψ).LFunction s - logDeriv ψ.LFunction s` equals the sum of the
logarithmic derivatives of the deleted Euler factors. -/
theorem logDeriv_LFunction_changeLevel_sub {M N : ℕ} [NeZero M] [NeZero N]
    (ψ : DirichletCharacter ℂ M) (hMN : M ∣ N) {s : ℂ} (h : s ≠ 1 ∨ ψ ≠ 1)
    (hPs : (∏ p ∈ N.primeFactors, (1 - ψ p * (p : ℂ) ^ (-s))) ≠ 0)
    (hψ : ψ.LFunction s ≠ 0) :
    logDeriv (changeLevel hMN ψ).LFunction s - logDeriv ψ.LFunction s =
      ∑ p ∈ N.primeFactors, logDeriv (fun z : ℂ ↦ 1 - ψ p * (p : ℂ) ^ (-z)) s := by
  let f (p : ℕ) (z : ℂ) := 1 - ψ p * (p : ℂ) ^ (-z)
  have hdf (p : ℕ) (hp : p ∈ N.primeFactors) : Differentiable ℂ (f p) :=
    Complex.differentiable_one_sub_mul_cpow_neg
      (mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero) _
  have hPs' : (∏ p ∈ N.primeFactors, f p) s ≠ 0 := by simpa [f, Finset.prod_apply] using hPs
  have hnef (p : ℕ) (hp : p ∈ N.primeFactors) : f p s ≠ 0 :=
    prod_ne_zero_iff.mp hPs p hp
  have hPdiff : Differentiable ℂ (∏ p ∈ N.primeFactors, f p) :=
    Differentiable.finsetProd fun p hp ↦ hdf p hp
  rw [(logDeriv_congr_nhds (LFunction_changeLevel_eventuallyEq_nhds ψ hMN h)).eq_of_nhds,
    logDeriv_mul s hPs' hψ (hPdiff s) (ψ.differentiableAt_LFunction s h), add_sub_cancel_right]
  exact logDeriv_prod hnef fun p hp ↦ hdf p hp s

/-- **Deleted Euler factors in the logarithmic derivative under level change.** On the closed
half-plane `1 ≤ re s`, raising the level of a character `ψ` modulo `M` to a multiple `N` changes
`logDeriv` by at most `log N` in norm. At `s = 1` for `ψ = 1`, both `L`-functions fail to be
differentiable so both logarithmic derivatives vanish by Lean's totalization. -/
theorem norm_logDeriv_LFunction_changeLevel_sub_le {M N : ℕ} [NeZero M] [NeZero N]
    (ψ : DirichletCharacter ℂ M) (hMN : M ∣ N) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖logDeriv (changeLevel hMN ψ).LFunction s - logDeriv ψ.LFunction s‖ ≤ Real.log N := by
  by_cases h1 : s = 1 ∧ ψ = 1
  · obtain ⟨rfl, rfl⟩ := h1
    have hch : changeLevel hMN (1 : DirichletCharacter ℂ M) = 1 := map_one _
    have hnd {K : ℕ} [NeZero K] : ¬ DifferentiableAt ℂ (1 : DirichletCharacter ℂ K).LFunction 1 :=
      mt ((1 : DirichletCharacter ℂ K).differentiableAt_LFunction_iff 1).mp (by simp)
    rw [hch, logDeriv_eq_zero_of_not_differentiableAt _ _ hnd,
      logDeriv_eq_zero_of_not_differentiableAt _ _ hnd, sub_self, norm_zero]
    exact Real.log_nonneg (Nat.one_le_cast.mpr NeZero.one_le)
  have h : s ≠ 1 ∨ ψ ≠ 1 := not_and_or.mp h1
  have hPs : (∏ p ∈ N.primeFactors, (1 - ψ p * (p : ℂ) ^ (-s))) ≠ 0 :=
    prod_one_sub_mul_prime_cpow_ne_zero (N := N) ψ (zero_lt_one.trans_le hs).ne'
  rw [logDeriv_LFunction_changeLevel_sub ψ hMN h hPs (LFunction_ne_zero_of_one_le_re ψ h.symm hs)]
  refine (norm_sum_le _ _).trans ((sum_le_sum fun p hp ↦ ?_).trans (Nat.sum_primeFactors_log_le N))
  simpa using Complex.norm_logDeriv_one_sub_mul_ofReal_cpow_neg_le (q := p)
    (mod_cast (Nat.prime_of_mem_primeFactors hp).two_le) (ψ.norm_le_one p) hs

end DirichletCharacter

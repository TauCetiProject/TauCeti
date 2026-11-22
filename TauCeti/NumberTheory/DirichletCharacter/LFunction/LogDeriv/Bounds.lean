/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Principal
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Hadamard

/-!
# Vertical-strip bounds for logarithmic derivatives of Dirichlet L-functions

On the vertical strip `1 < Re s ≤ 2` (`s = 1 + η + i u`, `0 < η ≤ 1`), Hadamard factorization
and level change give explicit upper bounds on `-Re (L'/L)(1 + η + i u, χ)` for nonprincipal
characters:

* `DirichletCharacter.exists_neg_re_logDeriv_LFunction_one_add_le_of_ne_one`: for every
  nonprincipal character `ψ ≠ 1` modulo `q` (primitive or imprimitive),
  `-Re (L'/L)(1 + η + i u, ψ) ≤ (3 / 2) * log q + C * log (|u| + 3)`.
* `DirichletCharacter.exists_neg_re_logDeriv_LFunction_one_add_zero_le`: for a nonprincipal
  primitive character `χ` with a zero `χ.LFunction (β + i u) = 0` (`0 < β`),
  `-Re (L'/L)(1 + η + i u, χ) ≤ -1 / (1 + η - β) + log q / 2 + C * log (|u| + 3)`.
* `DirichletCharacter.exists_sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le`: along the
  real axis `s = 1 + η`, any finite retained-zero sum over zeros in `0 < Re ρ` satisfies
  `∑ ρ ∈ S, m_ρ * Re (1 / (1 + η - ρ)) ≤ 1 / η + C * log (3 * q)`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §14.
-/

public section

open Complex Filter Set TauCeti TauCeti.LFunctions

namespace DirichletCharacter

/-- On the strip `1 < Re s ≤ 2` (`s = 1 + η + i u`), every nonprincipal Dirichlet L-function
satisfies `-Re (L'/L)(1 + η + i u, ψ) ≤ (3 / 2) * log q + C * log (|u| + 3)` for one absolute
constant `C > 0`. -/
theorem exists_neg_re_logDeriv_LFunction_one_add_le_of_ne_one :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q), ψ ≠ 1 →
      ∀ {η : ℝ}, 0 < η → η ≤ 1 → ∀ u : ℝ,
      -(logDeriv ψ.LFunction (1 + η + u * I)).re ≤
        (3 / 2) * Real.log q + C * Real.log (|u| + 3) := by
  obtain ⟨C, hC0, hγ⟩ := exists_norm_logDeriv_gammaFactor_le_log (a := 1) (b := 2) zero_lt_one
  refine ⟨C, hC0, fun {q} _ ψ hψ {η} hη hη1 u ↦ ?_⟩
  let q₀ : ℕ := ψ.conductor
  have : NeZero q₀ := ⟨Nat.ne_of_gt (Nat.pos_of_dvd_of_pos ψ.conductor_dvd_level (NeZero.pos q))⟩
  let ψ₀ : DirichletCharacter ℂ q₀ := ψ.primitiveCharacter
  have hψ₀_prim : ψ₀.IsPrimitive := ψ.primitiveCharacter_isPrimitive
  have hψ₀_ne : ψ₀ ≠ 1 := mt ψ.primitiveCharacter_eq_one_iff.mp hψ
  set s : ℂ := 1 + η + u * I
  have hs1 : 1 ≤ s.re := by simp [s]; linarith
  have hs2 : s.re ≤ 2 := by simp [s]; linarith
  have hch := norm_logDeriv_LFunction_changeLevel_sub_le ψ₀ ψ.conductor_dvd_level hs1 (.inl hψ₀_ne)
  rw [ψ.changeLevel_primitiveCharacter] at hch
  have hre_ch : -(logDeriv ψ.LFunction s).re ≤ -(logDeriv ψ₀.LFunction s).re + Real.log q := by
    rw [norm_sub_rev] at hch
    have hsub := (Complex.re_le_norm (logDeriv ψ₀.LFunction s - logDeriv ψ.LFunction s)).trans hch
    simp only [Complex.sub_re] at hsub
    linarith
  have hhad := ψ₀.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_add_gammaFactor
    hψ₀_prim hψ₀_ne (S := ∅) (by simp) hs1
  rw [Finset.sum_empty] at hhad
  have hq₀ : Real.log q₀ ≤ Real.log q := by
    refine Real.log_le_log (by exact_mod_cast NeZero.pos q₀) ?_
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) ψ.conductor_dvd_level
  have hγs : (logDeriv ψ₀.gammaFactor s).re ≤ C * Real.log (|u| + 3) := by
    simpa [s] using (Complex.re_le_norm _).trans (hγ ψ₀ s ⟨hs1, hs2⟩)
  linarith

/-- On the strip `1 < Re s ≤ 2` (`s = 1 + η + i u`), if `χ` is nonprincipal and primitive and
`χ.LFunction (β + i u) = 0` with `0 < β`, then
`-Re (L'/L)(1 + η + i u, χ) ≤ -1 / (1 + η - β) + log q / 2 + C * log (|u| + 3)` for one
absolute constant `C > 0`. -/
theorem exists_neg_re_logDeriv_LFunction_one_add_zero_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ {β u : ℝ}, 0 < β → χ.LFunction (β + u * I) = 0 →
      ∀ {η : ℝ}, 0 < η → η ≤ 1 →
      -(logDeriv χ.LFunction (1 + η + u * I)).re ≤
        -(1 / (1 + η - β)) + Real.log q / 2 + C * Real.log (|u| + 3) := by
  obtain ⟨C, hC0, hγ⟩ := exists_norm_logDeriv_gammaFactor_le_log (a := 1) (b := 2) zero_lt_one
  refine ⟨C, hC0, fun {q} _ χ hprim hne {β u} hβ hz {η} hη hη1 ↦ ?_⟩
  set s : ℂ := 1 + η + u * I
  set ρ : ℂ := β + u * I
  have hs1 : 1 ≤ s.re := by simp [s]; linarith
  have hs2 : s.re ≤ 2 := by simp [s]; linarith
  have hρpos : 0 < ρ.re := by simpa [ρ] using hβ
  have hhad := χ.re_one_div_sub_le_re_logDeriv_LFunction_add_gammaFactor hprim hne hρpos hz hs1
  have hsρ : s - ρ = ((1 + η - β : ℝ) : ℂ) := by apply Complex.ext <;> simp [s, ρ]
  rw [hsρ, one_div, ← ofReal_inv, ofReal_re, ← one_div] at hhad
  have hγs : (logDeriv χ.gammaFactor s).re ≤ C * Real.log (|u| + 3) := by
    simpa [s] using (Complex.re_le_norm _).trans (hγ χ s ⟨hs1, hs2⟩)
  linarith

/-- On the real segment `(1, 2]`, any finite multiplicity-weighted retained-zero sum over zeros in
`0 < Re ρ` of a nonprincipal primitive Dirichlet L-function is bounded by
`1 / η + C * log (3 * q)` for one absolute constant `C > 0`. -/
theorem exists_sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ {S : Finset ℂ}, (∀ ρ ∈ S, 0 < ρ.re) →
      ∀ {η : ℝ}, 0 < η → η ≤ 1 →
      ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((1 + η : ℂ) - ρ)).re ≤
        1 / η + C * Real.log (3 * q) := by
  obtain ⟨C₀, hC₀, hprin⟩ := exists_neg_re_logDeriv_LFunctionTrivChar_one_add_le
  refine ⟨C₀ + 3 / 2 + max gammaLogDerivBound 0, by positivity,
    fun {q} _ χ hprim hne {S} hS {η} hη hη1 ↦ ?_⟩
  have hhad := χ.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add
    hprim hne S hS (σ := 1 + η) ⟨by linarith, by linarith⟩
  have hmaj := χ.re_logDeriv_LFunction_le_neg_re_logDeriv_LFunctionTrivChar (σ := 1 + η)
    (by linarith)
  have h1 := hprin q hη hη1
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h1_le : 1 ≤ Real.log (3 * q) :=
    hlog3.le.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlogq_le : Real.log q ≤ Real.log (3 * q) :=
    Real.log_le_log (by positivity) (by linarith)
  have hC0_le :
      C₀ + max gammaLogDerivBound 0 ≤ (C₀ + max gammaLogDerivBound 0) * Real.log (3 * q) :=
    le_mul_of_one_le_right (by positivity) h1_le
  have hΓ_le : gammaLogDerivBound ≤ max gammaLogDerivBound 0 := le_max_left _ _
  simp only [Complex.ofReal_add, Complex.ofReal_one] at hhad hmaj
  linarith

end DirichletCharacter

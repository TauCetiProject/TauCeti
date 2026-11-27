/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.RemainderMellin
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.PoleRemoved

/-!
# Poles of the Riesz remainder Mellin expression for Dirichlet characters

On the open right half-plane the meromorphic Mellin expression has only simple poles,
precisely at the zeros of the Dirichlet L-function. Its residue at such a zero `ρ` is
`m / (ρ * (1 - ρ))`, where `m` is the zero multiplicity, so the residues at real poles are
positive. This sign prevents pole cancellation in positively weighted families.
On `Re s > 1`, the formulas for the principal and nonprincipal characters express the
Mellin expression using pole-cleared and ordinary logarithmic derivatives, respectively.
-/

public section

namespace DirichletCharacter

open TauCeti in
/-- On `Re s > 1`, the principal character's Riesz expression is the compensated difference
quotient of the negative logarithmic derivative of the pole-cleared function minus `1`. -/
theorem rieszRemainderMellin_LFunctionTrivChar (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    rieszRemainderMellin (LFunctionTrivChar q) s =
      ((-logDeriv (LFunctionTrivChar₁ q) s - 1) / s -
        (-logDeriv (LFunctionTrivChar₁ q) 1 - 1)) / (s - 1) := by
  have h₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have h₁ : s ≠ 1 := by rintro rfl; simp at hs
  have hL := (1 : DirichletCharacter ℂ q).LFunction_ne_zero_of_one_le_re (.inr h₁) hs.le
  have hmer := (1 : DirichletCharacter ℂ q).meromorphic_LFunction
  have ha := (1 : DirichletCharacter ℂ q).analyticAt_LFunction (.inl h₁)
  have h := (hmer.rieszRemainderMellin_eq_and_analyticAt h₀ h₁ ha hL).1
  rw [h, logDerivFinitePart_LFunctionTrivChar_one, meromorphicOrderAt_LFunctionTrivChar_one,
    logDeriv_LFunctionTrivChar₁_apply_of_ne_one h₁ hL]
  simp only [WithTop.untop₀_neg, WithTop.untop₀_one, Int.cast_neg, Int.cast_one]
  field_simp [h₀, sub_ne_zero.mpr h₁]
  ring

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- On the half-plane of absolute convergence, the nonprincipal character's correction
uses the ordinary logarithmic derivative at `1`. -/
theorem rieszRemainderMellin_LFunction_of_ne_one (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    TauCeti.rieszRemainderMellin χ.LFunction s =
      (s * logDeriv χ.LFunction 1 - logDeriv χ.LFunction s) / (s * (s - 1)) := by
  have hs₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs₁ : s ≠ 1 := by rintro rfl; simp at hs
  have h₁ := χ.analyticAt_LFunction (s := 1) (.inr hχ)
  have hne₁ := χ.LFunction_ne_zero_of_one_le_re (s := 1) (.inl hχ) (by simp)
  have hord := h₁.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hne₁
  have hpart := h₁.logDerivFinitePart_eq_logDeriv hne₁
  have h := (χ.meromorphic_LFunction.rieszRemainderMellin_eq_and_analyticAt hs₀ hs₁
    (χ.analyticAt_LFunction (.inl hs₁))
    (χ.LFunction_ne_zero_of_one_le_re (.inr hs₁) hs.le)).1
  simpa [hpart, hord] using h

/-- The Riesz remainder Mellin expression is analytic on `Re s ≥ 1`, including at `1`
where normalization removes the singularity of the defining quotient. -/
theorem analyticAt_rieszRemainderMellin_LFunction_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (TauCeti.rieszRemainderMellin χ.LFunction) s := by
  by_cases h₁ : s = 1
  · subst s
    exact χ.meromorphic_LFunction.analyticAt_rieszRemainderMellin_one
  · have h₀ : s ≠ 0 := by rintro rfl; norm_num at hs
    exact (χ.meromorphic_LFunction.rieszRemainderMellin_eq_and_analyticAt h₀ h₁
      (χ.analyticAt_LFunction (.inl h₁)) (χ.LFunction_ne_zero_of_one_le_re (.inr h₁) hs)).2

/-- A nonzero zero of the L-function gives a simple pole of the Riesz remainder Mellin expression,
with residue given by the multiplicity and the Riesz kernel. -/
theorem rieszRemainderMellin_LFunction_simplePole {ρ : ℂ} (h₀ : ρ ≠ 0)
    (hzero : 0 < meromorphicOrderAt χ.LFunction ρ) :
    meromorphicOrderAt (TauCeti.rieszRemainderMellin χ.LFunction) ρ = -1 ∧
      meromorphicTrailingCoeffAt (TauCeti.rieszRemainderMellin χ.LFunction) ρ =
        ((meromorphicOrderAt χ.LFunction ρ).untop₀ : ℂ) / (ρ * (1 - ρ)) := by
  obtain ⟨hz, hguard⟩ := χ.meromorphicOrderAt_LFunction_pos_iff.mp hzero
  have hre := χ.re_lt_one_of_LFunction_eq_zero hguard hz
  have h₁ : ρ ≠ 1 := by rintro rfl; simp at hre
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (χ.meromorphicOrderAt_LFunction_ne_top ρ)
  have hpos : 0 < n := by simpa [← hn] using hzero
  simpa [← hn] using
    χ.meromorphic_LFunction.rieszRemainderMellin_simplePole h₀ h₁ hn.symm hpos.ne'

/-- Away from `0`, the poles are precisely the zeros of the L-function. The original
principal-character pole at `1` is removed. -/
@[simp] theorem meromorphicOrderAt_rieszRemainderMellin_LFunction_neg_iff {ρ : ℂ} (h₀ : ρ ≠ 0) :
    meromorphicOrderAt (TauCeti.rieszRemainderMellin χ.LFunction) ρ < 0 ↔
      0 < meromorphicOrderAt χ.LFunction ρ := by
  constructor
  · contrapose!
    intro horder
    apply AnalyticAt.meromorphicOrderAt_nonneg
    by_cases h₁ : ρ = 1
    · subst ρ
      exact χ.meromorphic_LFunction.analyticAt_rieszRemainderMellin_one
    · have hne : χ.LFunction ρ ≠ 0 := fun heq ↦
        horder.not_gt (χ.meromorphicOrderAt_LFunction_pos_iff.mpr ⟨heq, .inl h₁⟩)
      exact (χ.meromorphic_LFunction.rieszRemainderMellin_eq_and_analyticAt h₀ h₁
        (χ.analyticAt_LFunction (.inl h₁)) hne).2
  · intro h
    rw [(χ.rieszRemainderMellin_LFunction_simplePole h₀ h).1]
    exact WithTop.coe_lt_coe.mpr (neg_one_lt_zero : (-1 : ℤ) < 0)

/-- Away from `0`, the residue of the Riesz remainder Mellin expression is the zero
multiplicity divided by `ρ * (1 - ρ)`, and is zero at points that are not zeros of `L`.
The natural analytic order at the principal character's pole is zero. -/
theorem residue_rieszRemainderMellin_LFunction {ρ : ℂ} (h₀ : ρ ≠ 0) :
    TauCeti.Contour.residue (TauCeti.rieszRemainderMellin χ.LFunction) ρ =
      (analyticOrderNatAt χ.LFunction ρ : ℂ) / (ρ * (1 - ρ)) := by
  rw [χ.meromorphic_LFunction.residue_rieszRemainderMellin h₀]
  by_cases h₁ : ρ = 1
  · simp [h₁]
  · rw [χ.meromorphicOrderAt_LFunction_eq_analyticOrderNatAt (.inl h₁), WithTop.untop₀_coe,
      Int.cast_natCast]

/-- Every real pole of the Mellin expression in the open right half-plane has a positive real
leading Laurent coefficient, which is its residue since the pole is simple. -/
theorem exists_pos_meromorphicTrailingCoeffAt_rieszRemainderMellin_LFunction {β : ℝ}
    (hβ : 0 < β) (hpole : meromorphicOrderAt (TauCeti.rieszRemainderMellin χ.LFunction) β < 0) :
    ∃ c : ℝ, 0 < c ∧
      meromorphicTrailingCoeffAt (TauCeti.rieszRemainderMellin χ.LFunction) β = (c : ℂ) := by
  have hzero := (χ.meromorphicOrderAt_rieszRemainderMellin_LFunction_neg_iff
    (Complex.ofReal_ne_zero.mpr hβ.ne')).mp hpole
  obtain ⟨hz, hguard⟩ := χ.meromorphicOrderAt_LFunction_pos_iff.mp hzero
  exact χ.meromorphic_LFunction.exists_pos_meromorphicTrailingCoeffAt_rieszRemainderMellin hβ
    (χ.re_lt_one_of_LFunction_eq_zero hguard hz) (χ.meromorphicOrderAt_LFunction_ne_top β) hzero

end DirichletCharacter

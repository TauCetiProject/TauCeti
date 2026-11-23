/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import TauCeti.Analysis.Complex.Conformal.Reflection.LogDeriv

/-!
# Conjugation of gamma logarithmic derivatives

Digamma and the logarithmic derivatives of the real and complex archimedean gamma factors
commute with conjugation. The identities hold at all points, including poles, since Mathlib's
total derivative commutes with conjugate reflection without a differentiability hypothesis.
They allow functional equations involving dual gamma factors to be read at conjugate points.
The proofs specialize `TauCeti.logDeriv_conj_eq_conj_logDeriv_of_ne_zero` to Mathlib's
`Gamma_conj`, `Gammaℝ_conj` and `Gammaℂ_conj` identities.
-/

public section

open ComplexConjugate

namespace Complex

/-- Digamma commutes with complex conjugation, including at gamma poles. -/
@[simp] theorem digamma_conj (s : ℂ) : digamma (conj s) = conj (digamma s) := by
  simp only [digamma_def]
  exact TauCeti.logDeriv_conj_eq_conj_logDeriv_of_ne_zero (u := 1) one_ne_zero
    isOpen_univ (fun z _ ↦ by simpa using Gamma_conj z) (Set.mem_univ s)

/-- The logarithmic derivative of the real-place gamma factor commutes with conjugation,
including at poles. -/
@[simp] theorem logDeriv_Gammaℝ_conj (s : ℂ) :
    logDeriv Gammaℝ (conj s) = conj (logDeriv Gammaℝ s) :=
  TauCeti.logDeriv_conj_eq_conj_logDeriv_of_ne_zero (u := 1) one_ne_zero
    isOpen_univ (fun z _ ↦ by simpa using Gammaℝ_conj z) (Set.mem_univ s)

/-- The logarithmic derivative of the complex-place gamma factor commutes with conjugation,
including at poles. -/
@[simp] theorem logDeriv_Gammaℂ_conj (s : ℂ) :
    logDeriv Gammaℂ (conj s) = conj (logDeriv Gammaℂ s) :=
  TauCeti.logDeriv_conj_eq_conj_logDeriv_of_ne_zero (u := 1) one_ne_zero
    isOpen_univ (fun z _ ↦ by simpa using Gammaℂ_conj z) (Set.mem_univ s)

end Complex

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Iterated derivatives of holomorphic functions of one complex variable

This file records that every iterated derivative of a complex differentiable function
`g : ℂ → E` is again complex differentiable (`Differentiable.iteratedDeriv`), the iterated form of
Mathlib's `Differentiable.deriv`, and that at a real point the iterated derivatives of a
holomorphic germ agree with the iterated real derivatives of its restriction to the real line
(`AnalyticAt.iteratedDeriv_comp_ofReal`). It also computes the norms of the real iterated
derivatives of the powers `z ^ m` (`TauCeti.Complex.norm_iteratedFDeriv_pow`).
-/

public section

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An iterated derivative of a complex differentiable function `g : ℂ → E` is complex
differentiable. This is the iterated form of `Differentiable.deriv`. -/
theorem Differentiable.iteratedDeriv {g : ℂ → E} (hg : Differentiable ℂ g) (k : ℕ) :
    Differentiable ℂ (iteratedDeriv k g) :=
  (hg.contDiff (n := ⊤)).differentiable_iteratedDeriv k (by simp)

/-- At a real point `t`, the iterated real derivatives of the restriction `s ↦ g s` of a
holomorphic function `g : ℂ → E` agree with its iterated complex derivatives. -/
theorem AnalyticAt.iteratedDeriv_comp_ofReal [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {g : ℂ → E} {t : ℝ} (hg : AnalyticAt ℂ g t) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ ↦ g s) t = iteratedDeriv k g t := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    have hd : deriv (fun s : ℝ ↦ g s) =ᶠ[𝓝 t] fun s : ℝ ↦ deriv g s := by
      filter_upwards [Complex.continuous_ofReal.continuousAt.eventually hg.eventually_analyticAt]
        with s hs
      have hcomp := (hs.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s
        Complex.ofRealCLM.hasDerivAt
      simpa [Function.comp_def] using hcomp.deriv
    rw [iteratedDeriv_succ', hd.iteratedDeriv_eq k, ih hg.deriv, ← iteratedDeriv_succ']

namespace TauCeti.Complex

/-- The real iterated derivatives of `z ^ m` have the norms of the complex ones:
`‖D^k (z ^ m)‖ = m (m - 1) ⋯ (m - k + 1) ‖z‖ ^ (m - k)`. -/
theorem norm_iteratedFDeriv_pow (k m : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ k (fun w : ℂ => w ^ m) z‖ = m.descFactorial k * ‖z‖ ^ (m - k) := by
  have h : ContDiffAt ℂ k (fun w : ℂ => w ^ m) z := by fun_prop
  rw [← h.restrictScalars_iteratedFDeriv (𝕜 := ℝ), Function.comp_apply,
    ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_pow, norm_mul, norm_pow, Complex.norm_natCast]

end TauCeti.Complex

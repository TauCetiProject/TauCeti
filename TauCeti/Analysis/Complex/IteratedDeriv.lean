/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Iterated derivatives of holomorphic functions of one complex variable

This file records that every iterated derivative of a complex differentiable function
`g : ℂ → E` is again complex differentiable (`Differentiable.iteratedDeriv`,
`DifferentiableOn.iteratedDeriv`), and that locally uniform convergence of holomorphic functions on
an open subset of `ℂ` passes to every iterated derivative
(`TendstoLocallyUniformlyOn.iteratedDeriv`). It also computes the norms of the real iterated
derivatives of the powers `z ^ m` (`TauCeti.Complex.norm_iteratedFDeriv_pow`).
-/

public section

open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An iterated derivative of a complex differentiable function `g : ℂ → E` is complex
differentiable. This is the iterated form of `Differentiable.deriv`. -/
theorem Differentiable.iteratedDeriv {g : ℂ → E} (hg : Differentiable ℂ g) (k : ℕ) :
    Differentiable ℂ (iteratedDeriv k g) :=
  (hg.contDiff (n := ⊤)).differentiable_iteratedDeriv k (by simp)

/-- An iterated derivative of a function complex differentiable on an open set `U ⊆ ℂ` is complex
differentiable on `U`. -/
theorem DifferentiableOn.iteratedDeriv {g : ℂ → E} {U : Set ℂ} (hg : DifferentiableOn ℂ g U)
    (hU : IsOpen U) (k : ℕ) : DifferentiableOn ℂ (iteratedDeriv k g) U := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hg
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv hU

/-- Locally uniform convergence of holomorphic functions on an open subset of `ℂ` implies locally
uniform convergence of every iterated derivative. -/
theorem TendstoLocallyUniformlyOn.iteratedDeriv {ι : Type*} {φ : Filter ι}
    {F : ι → ℂ → E} {f : ℂ → E} {U : Set ℂ} (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) (hU : IsOpen U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n ↦ iteratedDeriv k (F n)) (iteratedDeriv k f) φ U := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k ih =>
    simp only [iteratedDeriv_succ]
    exact ih.deriv (hF.mono fun n hn ↦ hn.iteratedDeriv hU k) hU

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

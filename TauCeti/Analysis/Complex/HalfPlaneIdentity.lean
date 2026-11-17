/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Identity theorems from a right half-plane

Functions holomorphic on the right half-plane `Re s > a` (or on a punctured complex plane `{w}ᶜ`)
that agree on some right half-plane `Re s > b` agree throughout their common domain. The codomain
is any complete complex normed space.
-/

public section

open Set

/-- **Identity theorem on a right half-plane.** Two functions holomorphic on `Re s > a` that
agree on some right half-plane `Re s > b` agree throughout `Re s > a`. -/
theorem DifferentiableOn.eqOn_of_eqOn_re_gt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f g : ℂ → E} {a b : ℝ}
    (hf : DifferentiableOn ℂ f {s | a < s.re}) (hg : DifferentiableOn ℂ g {s | a < s.re})
    (hfg : EqOn f g {s | b < s.re}) : EqOn f g {s | a < s.re} := by
  have hopen (c : ℝ) : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine (hf.analyticOnNhd (hopen a)).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd (hopen a)) (convex_halfSpace_re_gt a).isPreconnected
    (z₀ := ((max a b + 1 : ℝ) : ℂ)) ?_ (hfg.eventuallyEq_of_mem ((hopen b).mem_nhds ?_)) <;>
    simp <;> grind

/-- **Identity theorem on a punctured plane from a right half-plane.** Two functions holomorphic on
`{w}ᶜ` that agree on some right half-plane `Re s > b` agree throughout `{w}ᶜ`. -/
theorem DifferentiableOn.eqOn_compl_singleton_of_eqOn_re_gt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f g : ℂ → E} {w : ℂ} {b : ℝ}
    (hf : DifferentiableOn ℂ f {w}ᶜ) (hg : DifferentiableOn ℂ g {w}ᶜ)
    (hfg : EqOn f g {s | b < s.re}) : EqOn f g {w}ᶜ := by
  have hopen : IsOpen {s : ℂ | b < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn := (isConnected_compl_singleton_of_one_lt_rank
    (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) w).isPreconnected
  set z₀ : ℂ := ((max w.re b + 1 : ℝ) : ℂ)
  have hz₀_ne : z₀ ∈ ({w}ᶜ : Set ℂ) := by
    intro h
    have hre := congrArg Complex.re (mem_singleton_iff.mp h)
    simp only [z₀, Complex.ofReal_re] at hre
    linarith [le_max_left w.re b]
  have hz₀_gt : b < z₀.re := by
    simp only [z₀, Complex.ofReal_re]
    linarith [le_max_right w.re b]
  exact (hf.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd isOpen_compl_singleton) hconn hz₀_ne
    (hfg.eventuallyEq_of_mem (hopen.mem_nhds hz₀_gt))

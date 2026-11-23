/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Analytic.Uniqueness

/-!
# Identity theorems on right half-planes and punctured planes

Functions holomorphic on a right half-plane `Re s > a` or on a punctured complex plane `{w}ᶜ`
that agree on the intersection with `{s | b < s.re}` agree throughout their domain, by
`DifferentiableOn.eqOn_of_isOpen_of_isPreconnected_of_eventuallyEq`. The codomain is any complete
complex normed space.
-/

public section

open Set
open scoped Topology

/-- **Identity theorem on a right half-plane.** Two functions holomorphic on `Re s > a` that
agree on `{s | a < s.re} ∩ {s | b < s.re}` agree throughout `Re s > a`. -/
theorem DifferentiableOn.eqOn_of_eqOn_re_gt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f g : ℂ → E} {a b : ℝ}
    (hf : DifferentiableOn ℂ f {s | a < s.re}) (hg : DifferentiableOn ℂ g {s | a < s.re})
    (hfg : EqOn f g ({s | a < s.re} ∩ {s | b < s.re})) : EqOn f g {s | a < s.re} := by
  have hopenA : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hopenB : IsOpen {s : ℂ | b < s.re} := isOpen_lt continuous_const Complex.continuous_re
  let z₀ : ℂ := ((max a b + 1 : ℝ) : ℂ)
  have hz₀A : z₀ ∈ {s : ℂ | a < s.re} := by
    simp only [z₀, mem_ofPred_eq, Complex.ofReal_re]
    linarith [le_max_left a b]
  have hz₀B : z₀ ∈ {s : ℂ | b < s.re} := by
    simp only [z₀, mem_ofPred_eq, Complex.ofReal_re]
    linarith [le_max_right a b]
  exact hf.eqOn_of_isOpen_of_isPreconnected_of_eventuallyEq hg hopenA
    (convex_halfSpace_re_gt a).isPreconnected hz₀A
    (hfg.eventuallyEq_of_mem ((hopenA.inter hopenB).mem_nhds ⟨hz₀A, hz₀B⟩))

/-- **Identity theorem on a punctured plane from a right half-plane.** Two functions holomorphic on
`{w}ᶜ` that agree on `{w}ᶜ ∩ {s | b < s.re}` agree throughout `{w}ᶜ`. -/
theorem DifferentiableOn.eqOn_compl_singleton_of_eqOn_re_gt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f g : ℂ → E} {w : ℂ} {b : ℝ}
    (hf : DifferentiableOn ℂ f {w}ᶜ) (hg : DifferentiableOn ℂ g {w}ᶜ)
    (hfg : EqOn f g ({w}ᶜ ∩ {s | b < s.re})) : EqOn f g {w}ᶜ := by
  have hopenB : IsOpen {s : ℂ | b < s.re} := isOpen_lt continuous_const Complex.continuous_re
  let z₀ : ℂ := ((max w.re b + 1 : ℝ) : ℂ)
  have hz₀w : z₀ ∈ ({w}ᶜ : Set ℂ) := fun h => by
    have hre := congrArg Complex.re (mem_singleton_iff.mp h)
    simp only [z₀, Complex.ofReal_re] at hre
    linarith [le_max_left w.re b]
  have hz₀B : z₀ ∈ {s : ℂ | b < s.re} := by
    simp only [z₀, mem_ofPred_eq, Complex.ofReal_re]
    linarith [le_max_right w.re b]
  exact hf.eqOn_of_isOpen_of_isPreconnected_of_eventuallyEq hg isOpen_compl_singleton
    (isConnected_compl_singleton_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) w).isPreconnected
    hz₀w (hfg.eventuallyEq_of_mem ((isOpen_compl_singleton.inter hopenB).mem_nhds ⟨hz₀w, hz₀B⟩))

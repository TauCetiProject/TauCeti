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

Functions holomorphic on an open preconnected set `U` meeting some right half-plane `Re s > b`
(in particular on a right half-plane `Re s > a` or on a punctured complex plane `{w}ᶜ`) that agree
on `Re s > b` agree throughout `U`. The codomain is any complete complex normed space.
-/

public section

open Set

/-- **Identity theorem from a right half-plane on an open preconnected domain.** Two functions
holomorphic on an open preconnected set `U ⊆ ℂ` meeting `{s | b < s.re}` that agree on
`U ∩ {s | b < s.re}` agree throughout `U`. -/
theorem DifferentiableOn.eqOn_of_isOpen_of_isPreconnected_of_eqOn_re_gt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f g : ℂ → E} {U : Set ℂ} {b : ℝ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hU_open : IsOpen U) (hU_conn : IsPreconnected U)
    (hne : (U ∩ {s | b < s.re}).Nonempty)
    (hfg : EqOn f g (U ∩ {s | b < s.re})) : EqOn f g U := by
  obtain ⟨z₀, hz₀U, hz₀b⟩ := hne
  have hopen : IsOpen {s : ℂ | b < s.re} := isOpen_lt continuous_const Complex.continuous_re
  exact (hf.analyticOnNhd hU_open).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd hU_open) hU_conn hz₀U
    (hfg.eventuallyEq_of_mem ((hU_open.inter hopen).mem_nhds ⟨hz₀U, hz₀b⟩))

/-- **Identity theorem on a right half-plane.** Two functions holomorphic on `Re s > a` that
agree on `{s | a < s.re} ∩ {s | b < s.re}` agree throughout `Re s > a`. -/
theorem DifferentiableOn.eqOn_of_eqOn_re_gt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f g : ℂ → E} {a b : ℝ}
    (hf : DifferentiableOn ℂ f {s | a < s.re}) (hg : DifferentiableOn ℂ g {s | a < s.re})
    (hfg : EqOn f g ({s | a < s.re} ∩ {s | b < s.re})) : EqOn f g {s | a < s.re} := by
  refine hf.eqOn_of_isOpen_of_isPreconnected_of_eqOn_re_gt hg
    (isOpen_lt continuous_const Complex.continuous_re) (convex_halfSpace_re_gt a).isPreconnected
    ⟨((max a b + 1 : ℝ) : ℂ), ?_⟩ hfg
  simp only [mem_inter_iff, mem_ofPred_eq, Complex.ofReal_re]
  exact ⟨by linarith [le_max_left a b], by linarith [le_max_right a b]⟩

/-- **Identity theorem on a punctured plane from a right half-plane.** Two functions holomorphic on
`{w}ᶜ` that agree on `{w}ᶜ ∩ {s | b < s.re}` agree throughout `{w}ᶜ`. -/
theorem DifferentiableOn.eqOn_compl_singleton_of_eqOn_re_gt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f g : ℂ → E} {w : ℂ} {b : ℝ}
    (hf : DifferentiableOn ℂ f {w}ᶜ) (hg : DifferentiableOn ℂ g {w}ᶜ)
    (hfg : EqOn f g ({w}ᶜ ∩ {s | b < s.re})) : EqOn f g {w}ᶜ := by
  refine hf.eqOn_of_isOpen_of_isPreconnected_of_eqOn_re_gt hg isOpen_compl_singleton
    (isConnected_compl_singleton_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) w).isPreconnected
    ⟨((max w.re b + 1 : ℝ) : ℂ), ?_⟩ hfg
  refine ⟨fun h => ?_, ?_⟩
  · have hre := congrArg Complex.re (mem_singleton_iff.mp h)
    simp only [Complex.ofReal_re] at hre
    linarith [le_max_left w.re b]
  · simp only [mem_ofPred_eq, Complex.ofReal_re]
    linarith [le_max_right w.re b]

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Identity theorems for holomorphic functions on complex domains

Two functions holomorphic on an open preconnected subset `U ⊆ ℂ` that agree at points accumulating
at some point `z₀ ∈ U` agree throughout `U`
(`DifferentiableOn.eqOn_of_isOpen_of_isPreconnected_of_frequently_eq`).
In particular, functions holomorphic on a right half-plane `Re s > a` or on a punctured complex
plane `{w}ᶜ` that agree on the intersection with `{s | b < s.re}` agree throughout their domain.
The codomain is any complex normed space (without requiring completeness).
-/

public section

open Set
open scoped Topology

/-- **Identity theorem on an open preconnected domain from accumulating agreement.** Two functions
holomorphic on an open preconnected set `U ⊆ ℂ` that agree at points accumulating at some point
`z₀ ∈ U` agree throughout `U`. -/
theorem DifferentiableOn.eqOn_of_isOpen_of_isPreconnected_of_frequently_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℂ → E} {U : Set ℂ} {z₀ : ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hU_open : IsOpen U) (hU_conn : IsPreconnected U)
    (hz₀ : z₀ ∈ U) (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : Set.EqOn f g U := by
  let e : E →L[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  have heq : Set.EqOn (e ∘ f) (e ∘ g) U :=
    ((e.differentiable.comp_differentiableOn hf).analyticOnNhd
      hU_open).eqOn_of_preconnected_of_frequently_eq
      ((e.differentiable.comp_differentiableOn hg).analyticOnNhd hU_open)
      hU_conn hz₀ (hfg.mono fun z hz ↦ congrArg e hz)
  exact fun z hz ↦ UniformSpace.Completion.coe_injective E (heq hz)

/-- **Identity theorem on a right half-plane.** Two functions holomorphic on `Re s > a` that
agree on `{s | a < s.re} ∩ {s | b < s.re}` agree throughout `Re s > a`. -/
theorem DifferentiableOn.eqOn_of_eqOn_re_gt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f g : ℂ → E} {a b : ℝ}
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
  exact hf.eqOn_of_isOpen_of_isPreconnected_of_frequently_eq hg hopenA
    (convex_halfSpace_re_gt a).isPreconnected hz₀A
    ((hfg.eventuallyEq_of_mem ((hopenA.inter hopenB).mem_nhds ⟨hz₀A, hz₀B⟩)).filter_mono
      nhdsWithin_le_nhds).frequently

/-- **Identity theorem on a punctured plane from a right half-plane.** Two functions holomorphic on
`{w}ᶜ` that agree on `{w}ᶜ ∩ {s | b < s.re}` agree throughout `{w}ᶜ`. -/
theorem DifferentiableOn.eqOn_compl_singleton_of_eqOn_re_gt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f g : ℂ → E} {w : ℂ} {b : ℝ}
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
  exact hf.eqOn_of_isOpen_of_isPreconnected_of_frequently_eq hg isOpen_compl_singleton
    (isConnected_compl_singleton_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) w).isPreconnected
    hz₀w ((hfg.eventuallyEq_of_mem
      ((isOpen_compl_singleton.inter hopenB).mem_nhds ⟨hz₀w, hz₀B⟩)).filter_mono
      nhdsWithin_le_nhds).frequently

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive
import Mathlib.Analysis.Complex.HasPrimitives
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Local primitives of holomorphic functions and real `1`-forms

This file connects complex derivatives in `ℂ` with real `1`-form primitives on the real manifold
`ℂ`, independently of global de Rham exactness.

## Main declarations

* `TauCeti.isPrimitiveOn_toSpanSingleton_iff` -- the correspondence between complex primitives of
  `f` and real `1`-form primitives of `f(z) dz`.
* `TauCeti.forall_exists_isPrimitiveOn_toSpanSingleton_iff_differentiableOn` -- a `1`-form
  `z ↦ (v ↦ v • f z)` has local primitives on an open set `s ⊆ ℂ` if and only if `f` is
  holomorphic on `s`.
-/

public section

open Complex Metric Set
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A function `g : ℂ → E` is a primitive of the real `1`-form `z ↦ (v ↦ v • f z)` on `s` if and
only if `s` is open and `g` has complex derivative `f z` at every `z ∈ s`. -/
theorem TauCeti.isPrimitiveOn_toSpanSingleton_iff {f g : ℂ → E} {s : Set ℂ} :
    TauCeti.IsPrimitiveOn (I := 𝓘(ℝ, ℂ))
        ((fun z ↦ ContinuousAlternatingMap.ofSubsingleton ℝ ℂ E (0 : Fin 1)
          ((ContinuousLinearMap.toSpanSingleton ℂ (f z)).restrictScalars ℝ)) :
            TauCeti.RoughForm 𝓘(ℝ, ℂ) ℂ E 1) g s ↔
      IsOpen s ∧ ∀ z ∈ s, HasDerivAt g (f z) z := by
  rw [TauCeti.isPrimitiveOn_ofSubsingleton_iff]
  simp only [← TauCeti.hasDerivAt_iff_hasFDerivAt_restrictScalars]

/-- On an open subset `s ⊆ ℂ` with complete coefficients `E`, the real `1`-form
`z ↦ (v ↦ v • f z)` admits local primitives on `s` if and only if `f` is holomorphic on `s`. -/
theorem TauCeti.forall_exists_isPrimitiveOn_toSpanSingleton_iff_differentiableOn [CompleteSpace E]
    {f : ℂ → E} {s : Set ℂ} (hs : IsOpen s) :
    (∀ z ∈ s, ∃ (g : ℂ → E) (U : Set ℂ), z ∈ U ∧
      TauCeti.IsPrimitiveOn (I := 𝓘(ℝ, ℂ))
        ((fun w ↦ ContinuousAlternatingMap.ofSubsingleton ℝ ℂ E (0 : Fin 1)
          ((ContinuousLinearMap.toSpanSingleton ℂ (f w)).restrictScalars ℝ)) :
            TauCeti.RoughForm 𝓘(ℝ, ℂ) ℂ E 1) g U) ↔
      DifferentiableOn ℂ f s := by
  constructor
  · intro h z hz
    obtain ⟨g, U, hzU, hgU⟩ := h z hz
    rw [TauCeti.isPrimitiveOn_toSpanSingleton_iff] at hgU
    have hdiff : DifferentiableOn ℂ f U :=
      Complex.IsExactOn.differentiableOn hgU.1 ⟨g, hgU.2⟩
    exact ((hdiff z hzU).differentiableAt (hgU.1.mem_nhds hzU)).differentiableWithinAt
  · intro hf z hz
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hs z hz
    obtain ⟨g, hg⟩ := (hf.mono hball).isExactOn_ball
    exact ⟨g, ball z r, mem_ball_self hr,
      TauCeti.isPrimitiveOn_toSpanSingleton_iff.mpr ⟨isOpen_ball, hg⟩⟩

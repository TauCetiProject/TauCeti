/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import TauCeti.Geometry.Manifold.DeRham.SimplyConnected
import TauCeti.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Primitives of holomorphic functions on simply connected domains

This file connects complex derivatives in `ℂ` with real `1`-form primitives on the real manifold
`ℂ` and deduces global primitives on simply connected open subsets of `ℂ` (and open subsets whose
connected components are simply connected) for holomorphic functions and continuous conservative
functions.

## Main declarations

* `TauCeti.isPrimitiveOn_toSpanSingleton_iff` and
  `TauCeti.forall_exists_isPrimitiveOn_toSpanSingleton_iff_differentiableOn` -- the correspondence
  between complex primitives of `f` and real `1`-form primitives of `f(z) dz`.
* `DifferentiableOn.isExactOn_of_isSimplyConnected` and
  `DifferentiableOn.isExactOn_of_isSimplyConnected_connectedComponentIn` -- global primitives of
  holomorphic functions on simply connected open sets in `ℂ` and on open sets whose connected
  components are simply connected.
* `Complex.IsConservativeOn.isExactOn_of_isSimplyConnected` and
  `Complex.IsConservativeOn.isExactOn_of_isSimplyConnected_connectedComponentIn` -- Morera's
  theorem on simply connected open sets and open sets with simply connected components.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 8, Section 1 (monodromy and primitives on
  simply connected regions).
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

variable [CompleteSpace E]

/-- On an open subset `s ⊆ ℂ` with complete coefficients `E`, the real `1`-form
`z ↦ (v ↦ v • f z)` admits local primitives on `s` if and only if `f` is holomorphic on `s`. -/
theorem TauCeti.forall_exists_isPrimitiveOn_toSpanSingleton_iff_differentiableOn
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

/-- **Primitives on simply connected domains.** Every holomorphic function on a simply connected
open subset `s ⊆ ℂ` with complete coefficients has a complex primitive on `s`. -/
theorem DifferentiableOn.isExactOn_of_isSimplyConnected {f : ℂ → E} {s : Set ℂ}
    (hf : DifferentiableOn ℂ f s) (hs : IsOpen s) (hsc : IsSimplyConnected s) :
    Complex.IsExactOn f s := by
  have hloc :=
    (TauCeti.forall_exists_isPrimitiveOn_toSpanSingleton_iff_differentiableOn hs).mpr hf
  obtain ⟨g, hg⟩ := TauCeti.exists_isPrimitiveOn_of_isSimplyConnected hs hsc hloc
  exact ⟨g, (TauCeti.isPrimitiveOn_toSpanSingleton_iff.mp hg).2⟩

/-- Every holomorphic function on an open subset `s ⊆ ℂ` whose connected components are all simply
connected (with complete coefficients) has a complex primitive on `s`. -/
theorem DifferentiableOn.isExactOn_of_isSimplyConnected_connectedComponentIn {f : ℂ → E}
    {s : Set ℂ} (hf : DifferentiableOn ℂ f s) (hs : IsOpen s)
    (hsc : ∀ z ∈ s, IsSimplyConnected (connectedComponentIn s z)) :
    Complex.IsExactOn f s := by
  have hloc :=
    (TauCeti.forall_exists_isPrimitiveOn_toSpanSingleton_iff_differentiableOn hs).mpr hf
  obtain ⟨g, hg⟩ :=
    TauCeti.exists_isPrimitiveOn_of_isSimplyConnected_connectedComponentIn hs hsc hloc
  exact ⟨g, (TauCeti.isPrimitiveOn_toSpanSingleton_iff.mp hg).2⟩

/-- **Morera's theorem on simply connected domains.** A continuous function on a simply connected
open subset `s ⊆ ℂ` whose rectangle integrals vanish has a complex primitive on `s`. -/
theorem Complex.IsConservativeOn.isExactOn_of_isSimplyConnected {f : ℂ → E} {s : Set ℂ}
    (hf : Complex.IsConservativeOn f s) (hfc : ContinuousOn f s) (hs : IsOpen s)
    (hsc : IsSimplyConnected s) : Complex.IsExactOn f s :=
  ((Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hs).mp
    ⟨hf, hfc⟩).isExactOn_of_isSimplyConnected hs hsc

/-- A continuous function on an open subset `s ⊆ ℂ` whose connected components are simply connected
and whose rectangle integrals vanish has a complex primitive on `s`. -/
theorem Complex.IsConservativeOn.isExactOn_of_isSimplyConnected_connectedComponentIn
    {f : ℂ → E} {s : Set ℂ} (hf : Complex.IsConservativeOn f s) (hfc : ContinuousOn f s)
    (hs : IsOpen s) (hsc : ∀ z ∈ s, IsSimplyConnected (connectedComponentIn s z)) :
    Complex.IsExactOn f s :=
  ((Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hs).mp
    ⟨hf, hfc⟩).isExactOn_of_isSimplyConnected_connectedComponentIn hs hsc

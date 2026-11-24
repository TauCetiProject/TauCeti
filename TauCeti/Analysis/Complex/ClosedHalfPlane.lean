/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Holomorphic continuation to a neighbourhood of a closed half-plane

Tauberian theorems at the boundary of a half-plane, such as Newman's, ask for a function that is
holomorphic on some open set containing the closed half-plane `σ ≤ re s`. When the function is
already holomorphic on the open half-plane `σ < re s`, for example because it is a Laplace
transform or a Dirichlet series there, this hypothesis only concerns the boundary line: it holds
exactly when the function is analytic at every point of `re s = σ`
(`TauCeti.exists_isOpen_differentiableOn_iff_analyticAt`). The open set can then be taken to be
the set of points at which the function is analytic, which is open by Mathlib's
`isOpen_analyticAt`.

Limits at points of the closed half-plane taken within the open half-plane are well defined, since
the open half-plane accumulates at each of them (`TauCeti.nhdsWithin_setOfPred_lt_re_neBot`).
-/

public section

open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A function holomorphic on the open half-plane `σ < re s` is holomorphic on an open set
containing the closed half-plane `σ ≤ re s` if and only if it is analytic at every point of the
boundary line `re s = σ`. -/
theorem exists_isOpen_differentiableOn_iff_analyticAt {F : ℂ → E} {σ : ℝ}
    (hF : DifferentiableOn ℂ F {s | σ < s.re}) :
    (∃ Ω : Set ℂ, IsOpen Ω ∧ {s : ℂ | σ ≤ s.re} ⊆ Ω ∧ DifferentiableOn ℂ F Ω) ↔
      ∀ s : ℂ, s.re = σ → AnalyticAt ℂ F s := by
  refine ⟨fun ⟨Ω, hΩ, hcover, hFΩ⟩ s hs ↦ hFΩ.analyticAt (hΩ.mem_nhds (hcover hs.ge)),
    fun h ↦ ⟨{s | AnalyticAt ℂ F s}, isOpen_analyticAt ℂ F, fun s (hs : σ ≤ s.re) ↦ ?_,
      fun _ hs ↦ hs.differentiableAt.differentiableWithinAt⟩⟩
  rcases hs.eq_or_lt with hs | hs
  · exact h s hs.symm
  · exact hF.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

/-- The open half-plane `σ < re s` accumulates at every point of the closed half-plane
`σ ≤ re s`, in particular at every point of its boundary line. -/
theorem nhdsWithin_setOfPred_lt_re_neBot {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) :
    (𝓝[{z : ℂ | σ < z.re}] s).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.1 (by simpa using hs)

end TauCeti

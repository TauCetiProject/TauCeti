/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DiffContOnCl
public import TauCeti.Analysis.Complex.Wirtinger.Basic

/-!
# Holomorphy and the conjugate Wirtinger derivative

For a real-differentiable map between complex normed spaces, vanishing of the conjugate
Wirtinger derivative characterizes complex differentiability. The real-differentiability
hypothesis is essential because the totalized real derivative vanishes at nondifferentiable
points. In one variable the real differential has coefficients `wirtingerDeriv f x 1` and
`conjWirtingerDeriv f x 1` in the basis `dz`, `dbar z`; testing the latter coefficient alone
detects its vanishing.

These statements connect the real differential and its type decomposition with holomorphy. In
particular, two functions of one complex variable, continuous on the closure of an open set and real
differentiable on it, with the same conjugate Wirtinger derivative there, differ by a function
holomorphic on the set and continuous on its closure
(`TauCeti.diffContOnCl_sub_of_conjWirtingerDeriv_eq`).

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Chapter II.
-/

public noncomputable section

open Complex
open scoped ComplexConjugate

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A real-differentiable map between complex normed spaces is complex differentiable
exactly when its conjugate Wirtinger derivative vanishes. -/
theorem differentiableAt_iff_conjWirtingerDeriv_eq_zero {g : V → W} {x : V}
    (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℂ g x ↔ conjWirtingerDeriv g x = 0 := by
  constructor
  · exact fun h ↦ h.conjWirtingerDeriv_eq_zero
  · intro h
    apply (differentiableAt_iff_restrictScalars ℝ hg).mpr
    refine ⟨wirtingerDeriv g x, ?_⟩
    ext v
    simpa only [ContinuousLinearMap.coe_restrictScalars', h, zero_apply, add_zero] using
      wirtingerDeriv_add_conjWirtingerDeriv g x v

/-- For a real-differentiable function of one complex variable, the single equation
`conjWirtingerDeriv f x 1 = 0` characterizes complex differentiability. -/
theorem differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero {f : ℂ → W} {x : ℂ}
    (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℂ f x ↔ conjWirtingerDeriv f x 1 = 0 := by
  rw [differentiableAt_iff_conjWirtingerDeriv_eq_zero hf,
    conjWirtingerDeriv_eq_zero_iff_apply_one_eq_zero]

/-- Two functions, continuous on the closure of an open set `U ⊆ ℂ` and real differentiable on
`U`, with the same `∂/∂(conj z)` on `U`, differ by a function holomorphic on `U` and continuous on
its closure. -/
theorem diffContOnCl_sub_of_conjWirtingerDeriv_eq {U : Set ℂ} {u₁ u₂ : ℂ → W} (hU : IsOpen U)
    (hc₁ : ContinuousOn u₁ (closure U)) (hc₂ : ContinuousOn u₂ (closure U))
    (hd₁ : DifferentiableOn ℝ u₁ U) (hd₂ : DifferentiableOn ℝ u₂ U)
    (heq : ∀ z ∈ U, conjWirtingerDeriv u₁ z 1 = conjWirtingerDeriv u₂ z 1) :
    DiffContOnCl ℂ (u₁ - u₂) U := by
  refine ⟨fun z hz ↦ ?_, hc₁.sub hc₂⟩
  have h₁ := (hd₁ z hz).differentiableAt (hU.mem_nhds hz)
  have h₂ := (hd₂ z hz).differentiableAt (hU.mem_nhds hz)
  refine ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero (h₁.sub h₂)).mpr
    ?_).differentiableWithinAt
  rw [conjWirtingerDeriv_sub h₁ h₂, sub_apply, heq z hz, sub_self]

end TauCeti

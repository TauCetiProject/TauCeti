/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# The Cauchy–Riemann criterion in complex normed spaces

A real-differentiable map between complex normed spaces is complex-differentiable precisely
when its real derivative commutes with multiplication by `I`. Unlike the one-variable test
at `1` and `I`, this tests every vector in the domain. No finite-dimensionality is needed.

The proof uses Mathlib's `real_linearMap_map_smul_complex` on each complex line and its
`differentiableWithinAt_iff_restrictScalars` criterion to recover the complex derivative.
These results allow the same test to be applied to coordinate representatives of manifold maps.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Chapter I.
-/

public section

namespace TauCeti

open Complex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {s : Set E} {x : E}

/-- The Cauchy–Riemann criterion within a set with unique real derivatives: the real derivative
must commute with multiplication by `I` on every vector. -/
theorem differentiableWithinAt_complex_iff_map_I (hs : UniqueDiffWithinAt ℝ s x) :
    DifferentiableWithinAt ℂ f s x ↔ DifferentiableWithinAt ℝ f s x ∧
      ∀ v, fderivWithin ℝ f s x (I • v) = I • fderivWithin ℝ f s x v := by
  constructor
  · intro hf
    refine ⟨hf.restrictScalars ℝ, ?_⟩
    rw [← hf.restrictScalars_fderivWithin ℝ hs]
    intro v
    exact (fderivWithin ℂ f s x).map_smul I v
  · rintro ⟨hf, hI⟩
    let D := fderivWithin ℝ f s x
    have hsmul (c : ℂ) (v : E) : D (c • v) = c • D v := by
      let L : ℂ →ₗ[ℝ] F := D.toLinearMap.comp
        ((LinearMap.toSpanSingleton ℂ E v).restrictScalars ℝ)
      have hL : L I = I • L 1 := by simpa [L, D] using hI v
      simpa [L] using real_linearMap_map_smul_complex hL c 1
    let Dc : E →L[ℂ] F :=
      { toFun := D
        map_add' := D.map_add
        map_smul' := hsmul
        cont := D.continuous }
    exact (differentiableWithinAt_iff_restrictScalars ℝ hf hs).2 ⟨Dc, rfl⟩

/-- A map between complex normed spaces is complex-differentiable at a point exactly when it
is real-differentiable there and its real derivative commutes with multiplication by `I`. -/
theorem differentiableAt_complex_iff_map_I :
    DifferentiableAt ℂ f x ↔ DifferentiableAt ℝ f x ∧
      ∀ v, fderiv ℝ f x (I • v) = I • fderiv ℝ f x v := by
  simpa only [differentiableWithinAt_univ, fderivWithin_univ] using
    (differentiableWithinAt_complex_iff_map_I
    (f := f) (uniqueDiffWithinAt_univ (𝕜 := ℝ) (x := x)))

end TauCeti

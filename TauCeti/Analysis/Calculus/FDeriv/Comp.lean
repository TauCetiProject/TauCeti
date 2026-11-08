/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Derivatives under composition and changes of coordinates

By the chain rule, the differential of `f ∘ φ` at `b` is the differential of `f` at `φ b`
precomposed with that of `φ` at `b`. When the latter is invertible, one vanishes exactly when the
other does, so criticality does not depend on the coordinates.

At a fixed point of a map preserving the germ of `f`, the derivative of `f` is unchanged by
precomposition with the derivative of that map.

## Main results

* `HasFDerivAt.comp_eq_of_eventuallyEq`: invariance of a germ at a fixed point implies invariance
  of its derivative.
* `TauCeti.fderiv_comp_eq_zero_iff_of_isInvertible`: `b` is a critical point of `f ∘ φ` exactly
  when `φ b` is a critical point of `f`, if the differential of `φ` at `b` is invertible.
* `TauCeti.fderiv_comp_add_smul`: the derivative of `w ↦ f (c + a • w)` is `a` times that of `f`
  at `c + a • w`.
-/

public section

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- If a map fixes `x` and preserves the germ of `f` there, its derivative preserves the
derivative of `f` by precomposition. -/
theorem _root_.HasFDerivAt.comp_eq_of_eventuallyEq {f : E → F} {f' : E →L[𝕜] F}
    {φ : E → E} {φ' : E →L[𝕜] E} {x : E} (hf : HasFDerivAt f f' x)
    (hφ : HasFDerivAt φ φ' x) (hfix : φ x = x)
    (hinv : f ∘ φ =ᶠ[nhds x] f) : f'.comp φ' = f' := by
  have hfφ : HasFDerivAt f f' (φ x) := by simpa only [hfix] using hf
  exact (hfφ.comp x hφ).unique (hf.congr_of_eventuallyEq hinv)

/-- **Criticality does not depend on the coordinates.** If `f` is differentiable at `φ b`, `φ` is
differentiable at `b`, and the differential of `φ` at `b` is invertible, then `b` is a critical
point of `f ∘ φ` exactly when `φ b` is a critical point of `f`. -/
theorem fderiv_comp_eq_zero_iff_of_isInvertible {f : E → G} {φ : F → E} {b : F}
    (hf : DifferentiableAt 𝕜 f (φ b)) (hφ : DifferentiableAt 𝕜 φ b)
    (hinv : (fderiv 𝕜 φ b).IsInvertible) :
    fderiv 𝕜 (f ∘ φ) b = 0 ↔ fderiv 𝕜 f (φ b) = 0 := by
  obtain ⟨e, he⟩ := hinv
  -- The differential of `f ∘ φ` at `b` is that of `f` at `φ b` precomposed with the equivalence
  -- `e`, so one vanishes exactly when the other does.
  rw [fderiv_comp (x := b) hf hφ, ← he]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; ext u; simp⟩
  ext u
  simpa using congrArg (fun L : F →L[𝕜] G ↦ L (e.symm u)) h

/-- Precomposing a real-valued function with scalar multiplication scales the norm of its
Fréchet derivative by the absolute value of the scalar. -/
theorem norm_fderiv_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (a : ℝ) (x : E) :
    ‖fderiv ℝ (fun y ↦ f (a • y)) x‖ = |a| * ‖fderiv ℝ f (a • x)‖ := by
  rw [_root_.fderiv_comp_smul a, norm_smul, Real.norm_eq_abs]

/-- **The chain rule for an affine change of variables.** The derivative of `w ↦ f (c + a • w)`
at `w` is `a` times the derivative of `f` at `c + a • w`. Like `fderiv_comp_smul`, this needs no
differentiability of `f`. -/
theorem fderiv_comp_add_smul (f : E → F) (c : E) (a : 𝕜) (w : E) :
    fderiv 𝕜 (fun w ↦ f (c + a • w)) w = a • fderiv 𝕜 f (c + a • w) := by
  rw [_root_.fderiv_comp_smul (f := fun y ↦ f (c + y)), fderiv_comp_add_left]

end TauCeti

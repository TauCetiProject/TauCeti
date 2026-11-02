/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Critical points under a change of coordinates

By the chain rule, the differential of `f ∘ φ` at `b` is the differential of `f` at `φ b`
precomposed with that of `φ` at `b`. When the latter is invertible, one vanishes exactly when the
other does, so criticality does not depend on the coordinates.

## Main results

* `TauCeti.fderiv_comp_eq_zero_iff_of_isInvertible`: `b` is a critical point of `f ∘ φ` exactly
  when `φ b` is a critical point of `f`, if the differential of `φ` at `b` is invertible.
-/

public section

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

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

end TauCeti

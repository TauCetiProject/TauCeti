/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Regularity transport across `ULift.up`

Because `ContinuousLinearEquiv.ulift : ULift.{u} F ≃L[𝕜] F` is a continuous linear equivalence over
any nontrivially normed field `𝕜`, composing a map `f : E → F` on the left with `ULift.up.{u}`
preserves and reflects `C^n` regularity (`ContDiffWithinAt`, `ContDiffAt`, `ContDiffOn`, and
`ContDiff`) for every `n : ℕ∞ω`.

## Main results

* `contDiffWithinAt_ulift_up_iff`: `ContDiffWithinAt 𝕜 n (fun y ↦ ULift.up.{u} (f y)) s x ↔
  ContDiffWithinAt 𝕜 n f s x`.
* `contDiffAt_ulift_up_iff`: `ContDiffAt 𝕜 n (fun y ↦ ULift.up.{u} (f y)) x ↔
  ContDiffAt 𝕜 n f x`.
* `contDiffOn_ulift_up_iff`: `ContDiffOn 𝕜 n (fun y ↦ ULift.up.{u} (f y)) s ↔
  ContDiffOn 𝕜 n f s`.
* `contDiff_ulift_up_iff`: `ContDiff 𝕜 n (fun y ↦ ULift.up.{u} (f y)) ↔ ContDiff 𝕜 n f`.
-/

public section

open scoped ContDiff

section ULift

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞}

/-- Composing on the left with `ULift.up` preserves `ContDiffWithinAt`. -/
@[simp]
theorem contDiffWithinAt_ulift_up_iff {f : E → F} {s : Set E} {x : E} :
    ContDiffWithinAt 𝕜 n (fun y ↦ ULift.up.{u} (f y)) s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  (ContinuousLinearEquiv.ulift : ULift.{u} F ≃L[𝕜] F).symm.comp_contDiffWithinAt_iff
    (n := n) (f := f) (s := s) (x := x)

/-- Composing on the left with `ULift.up` preserves `ContDiffAt`. -/
@[simp]
theorem contDiffAt_ulift_up_iff {f : E → F} {x : E} :
    ContDiffAt 𝕜 n (fun y ↦ ULift.up.{u} (f y)) x ↔ ContDiffAt 𝕜 n f x :=
  (ContinuousLinearEquiv.ulift : ULift.{u} F ≃L[𝕜] F).symm.comp_contDiffAt_iff
    (n := n) (f := f) (x := x)

/-- Composing on the left with `ULift.up` preserves `ContDiffOn`. -/
@[simp]
theorem contDiffOn_ulift_up_iff {f : E → F} {s : Set E} :
    ContDiffOn 𝕜 n (fun y ↦ ULift.up.{u} (f y)) s ↔ ContDiffOn 𝕜 n f s :=
  (ContinuousLinearEquiv.ulift : ULift.{u} F ≃L[𝕜] F).symm.comp_contDiffOn_iff
    (n := n) (f := f) (s := s)

/-- Composing on the left with `ULift.up` preserves `ContDiff`. -/
@[simp]
theorem contDiff_ulift_up_iff {f : E → F} :
    ContDiff 𝕜 n (fun y ↦ ULift.up.{u} (f y)) ↔ ContDiff 𝕜 n f :=
  (ContinuousLinearEquiv.ulift : ULift.{u} F ≃L[𝕜] F).symm.comp_contDiff_iff (n := n) (f := f)

end ULift

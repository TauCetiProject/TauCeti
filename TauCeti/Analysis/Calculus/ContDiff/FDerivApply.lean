/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Directional derivatives of `C^n` maps on open sets

A map that is `C^n` on an open set `s` has `C^m` directional derivatives `x ↦ fderiv 𝕜 f x v` on
`s` whenever `m + 1 ≤ n` (`ContDiffOn.fderiv_apply_of_isOpen`). This is the form in which partial
derivatives of a smooth coefficient or cutoff are used, without passing through the full
derivative field `fderiv 𝕜 f`.

For a globally `C^n` map with `n ≠ 0`, each directional derivative `x ↦ fderiv 𝕜 f x v` is
continuous (`ContDiff.continuous_fderiv_apply_const`). This is the fixed-direction form of
Mathlib's `ContDiff.continuous_fderiv_apply`, which treats the direction as a variable.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {s : Set E} {m n : WithTop ℕ∞}

/-- A map that is `C^n` on an open set has `C^m` directional derivatives there when
`m + 1 ≤ n`. -/
theorem ContDiffOn.fderiv_apply_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hmn : m + 1 ≤ n) (v : E) : ContDiffOn 𝕜 m (fun x => fderiv 𝕜 f x v) s :=
  (hf.fderiv_of_isOpen hs hmn).clm_apply contDiffOn_const

/-- A `C^n` map with `n ≠ 0` has continuous directional derivatives `x ↦ fderiv 𝕜 f x v`. -/
theorem ContDiff.continuous_fderiv_apply_const (hf : ContDiff 𝕜 n f) (hn : n ≠ 0) (v : E) :
    Continuous fun x => fderiv 𝕜 f x v :=
  (hf.continuous_fderiv hn).clm_apply continuous_const

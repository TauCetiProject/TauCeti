/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Directional derivatives of `C^n` maps on open sets

A map that is `C^n` on an open set `s` has `C^m` directional derivatives `x ↦ fderiv 𝕜 f x v` on
`s` whenever `m + 1 ≤ n` (`ContDiffOn.fderiv_apply_of_isOpen`). This is the form in which partial
derivatives of a smooth coefficient or cutoff are used, without passing through the full
derivative field `fderiv 𝕜 f`. At each point of `s`, the derivative of order `i` of
`x ↦ fderiv 𝕜 f x v` is bounded by `‖v‖` times the derivative of `f` of order `i + 1`
(`ContDiffOn.norm_iteratedFDeriv_fderiv_apply_le`), so bounds on the derivatives of `f` pass to its
directional derivatives.

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

/-- **Derivatives of a directional derivative.** If `f` is `C^{k+1}` on an open set `s`, then at
each `x ∈ s` the derivative of order `i ≤ k` of `x ↦ ∂ᵥf(x) = fderiv 𝕜 f x v` is bounded by
`‖v‖` times the derivative of `f` of order `i + 1`. -/
theorem ContDiffOn.norm_iteratedFDeriv_fderiv_apply_le {k : ℕ} (hf : ContDiffOn 𝕜 (k + 1) f s)
    (hs : IsOpen s) (v : E) {i : ℕ} (hi : i ≤ k) {x : E} (hx : x ∈ s) :
    ‖iteratedFDeriv 𝕜 i (fun y => fderiv 𝕜 f y v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv 𝕜 (i + 1) f x‖ :=
  (norm_iteratedFDeriv_clm_apply_const
    ((hf.fderiv_of_isOpen hs le_rfl).contDiffAt (hs.mem_nhds hx)) (by exact_mod_cast hi)).trans_eq
    (by rw [norm_iteratedFDeriv_fderiv])

/-- A `C^n` map with `n ≠ 0` has continuous directional derivatives `x ↦ fderiv 𝕜 f x v`. -/
theorem ContDiff.continuous_fderiv_apply_const (hf : ContDiff 𝕜 n f) (hn : n ≠ 0) (v : E) :
    Continuous fun x => fderiv 𝕜 f x v :=
  (hf.continuous_fderiv hn).clm_apply continuous_const

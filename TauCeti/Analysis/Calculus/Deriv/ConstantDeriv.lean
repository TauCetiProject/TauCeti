/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.RCLike.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Functions with constant derivative are affine

A differentiable function `f : 𝕜 → G`, for `𝕜 = ℝ` or `𝕜 = ℂ`, whose derivative is the constant
`c` everywhere satisfies `f x = f y + (x - y) • c`. This is the affine counterpart of Mathlib's
`is_const_of_deriv_eq_zero`, from which it follows by subtracting the line `x ↦ x • c`.

## Main result

* `Differentiable.eq_add_sub_smul_of_deriv_eq`
-/

public section

namespace TauCeti

variable {𝕜 G : Type*} [RCLike 𝕜] [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : 𝕜 → G}

/-- A differentiable function whose derivative is the constant `c` everywhere is affine:
`f x = f y + (x - y) • c`. -/
theorem _root_.Differentiable.eq_add_sub_smul_of_deriv_eq (hf : Differentiable 𝕜 f) {c : G}
    (hc : ∀ x, deriv f x = c) (x y : 𝕜) : f x = f y + (x - y) • c := by
  have hd (w : 𝕜) : HasDerivAt (fun w ↦ f w - w • c) (deriv f w - (1 : 𝕜) • c) w :=
    (hf w).hasDerivAt.sub ((hasDerivAt_id w).smul_const c)
  have h := is_const_of_deriv_eq_zero (fun w ↦ (hd w).differentiableAt)
    (fun w ↦ by rw [(hd w).deriv, hc w, one_smul, sub_self]) x y
  rw [sub_eq_iff_eq_add] at h
  rw [h, sub_smul]
  abel

end TauCeti

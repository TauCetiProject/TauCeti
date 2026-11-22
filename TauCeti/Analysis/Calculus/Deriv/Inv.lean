/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Differentiability of inverted translations

In a nontrivially normed field `𝕜`, the shifted inversion `w ↦ a₀ + w⁻¹` is differentiable on `{0}ᶜ`
(`TauCeti.differentiableOn_add_inv`).

## Main results

* `TauCeti.differentiableOn_add_inv`: `w ↦ a₀ + w⁻¹` is differentiable on `{0}ᶜ`.
-/

public section

namespace TauCeti

/-- In a nontrivially normed field, `w ↦ a₀ + w⁻¹` is differentiable on `{0}ᶜ`. -/
theorem differentiableOn_add_inv {𝕜 : Type*} [NontriviallyNormedField 𝕜] (a₀ : 𝕜) :
    DifferentiableOn 𝕜 (fun w : 𝕜 ↦ a₀ + w⁻¹) {0}ᶜ :=
  (differentiableOn_const a₀).add fun _ hw ↦
    (differentiableAt_inv_iff.mpr hw).differentiableWithinAt

end TauCeti

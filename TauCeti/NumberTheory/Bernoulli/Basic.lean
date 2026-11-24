/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Bernoulli

/-!
# Evaluation of `bernoulli 12`

Mathlib records `bernoulli 0` through `bernoulli 6` in `Mathlib.NumberTheory.Bernoulli`. This file
evaluates `B₁₂ = -691 / 2730`, which is used to compute the positive-degree `q`-expansion
coefficients of the normalised weight-`12` Eisenstein series `E₁₂`.

## Main results

* `TauCeti.bernoulli_twelve`: `bernoulli 12 = -691 / 2730`.
-/

public section

namespace TauCeti

/- `bernoulli` is computed through `bernoulli'`, which is defined by well-founded recursion, so
neither `norm_num` nor elaborator-side `decide` can evaluate it; the kernel can. -/

/-- The twelfth Bernoulli number `B₁₂ = -691 / 2730`. -/
@[simp]
theorem bernoulli_twelve : bernoulli 12 = -691 / 2730 := by decide +kernel

end TauCeti

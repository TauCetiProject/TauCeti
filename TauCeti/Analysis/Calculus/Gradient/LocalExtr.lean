/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Fermat's rule for gradients

At a local extremum of a real function on a real Hilbert space, a gradient vanishes. This is
Mathlib's Fréchet-derivative form of Fermat's rule (`IsLocalMax.hasFDerivAt_eq_zero`,
`IsLocalMin.hasFDerivAt_eq_zero`) read through the Riesz isometry `InnerProductSpace.toDual`.

## Main statements

* `IsLocalMax.hasGradientAt_eq_zero`, `IsLocalMin.hasGradientAt_eq_zero`.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {f : F → ℝ} {a g : F}

/-- **Fermat's rule** for gradients: a gradient of a real function at a local minimum is
zero. -/
theorem IsLocalMin.hasGradientAt_eq_zero (h : IsLocalMin f a) (hf : HasGradientAt f g a) :
    g = 0 := by
  simpa using h.hasFDerivAt_eq_zero hf.hasFDerivAt

/-- **Fermat's rule** for gradients: a gradient of a real function at a local maximum is
zero. -/
theorem IsLocalMax.hasGradientAt_eq_zero (h : IsLocalMax f a) (hf : HasGradientAt f g a) :
    g = 0 := by
  simpa using h.hasFDerivAt_eq_zero hf.hasFDerivAt

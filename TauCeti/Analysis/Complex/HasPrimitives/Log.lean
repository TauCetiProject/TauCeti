/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Primitives of holomorphic functions via complex logarithms

This file records exactness results for holomorphic functions whose primitives come from
`Complex.log`.

## Main declarations

* `TauCeti.isExactOn_inv_slitPlane`: exactness of `z ↦ z⁻¹` on `Complex.slitPlane` via
  `Complex.log`.
-/

public section

/-- The holomorphic function `z ↦ z⁻¹` has a complex primitive on `Complex.slitPlane`, namely
the principal branch `Complex.log`. -/
theorem TauCeti.isExactOn_inv_slitPlane : Complex.IsExactOn (fun z : ℂ ↦ z⁻¹) Complex.slitPlane :=
  ⟨Complex.log, fun _ hz ↦ Complex.hasDerivAt_log hz⟩

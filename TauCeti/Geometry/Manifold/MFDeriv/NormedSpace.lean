/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Vanishing of the derivative of a vector-valued function

For a function `g` from a manifold to a normed space `F`, Mathlib has two derivatives at `x`:
`mfderiv I 𝓘(𝕜, F) g x`, with values in the tangent space `TangentSpace 𝓘(𝕜, F) (g x)`, and
`mvfderiv I g x`, with values in `F` itself. They differ by the identification of the tangent space
with `F`, so one vanishes exactly when the other does.

## Main results

* `TauCeti.mvfderiv_eq_zero_iff`: `mvfderiv I g x = 0 ↔ mfderiv I 𝓘(𝕜, F) g x = 0`.
-/

public section

open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of a vector-valued function, read in the target space, vanishes exactly when
its manifold derivative does. -/
theorem mvfderiv_eq_zero_iff {g : M → F} {x : M} :
    mvfderiv I g x = 0 ↔ mfderiv I 𝓘(𝕜, F) g x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [mvfderiv, h]⟩
  ext u
  simpa [mvfderiv] using congrArg (fun L ↦ L u) h

end TauCeti

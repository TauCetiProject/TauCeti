/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Directional derivatives through continuous bilinear maps

The directional Leibniz rule follows by applying the one-variable bilinear rule along the
line through the base point. It requires only directional derivatives of the two factors.
-/

public section

/-- The directional Leibniz rule for an arbitrary continuous bilinear map. -/
theorem HasLineDerivAt.clm_bilin {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H] (B : F →L[𝕜] G →L[𝕜] H)
    {f : E → F} {g : E → G} {f' : F} {g' : G} {x v : E}
    (hf : HasLineDerivAt 𝕜 f f' x v) (hg : HasLineDerivAt 𝕜 g g' x v) :
    HasLineDerivAt 𝕜 (fun y => B (f y) (g y)) (B f' (g x) + B (f x) g') x v := by
  rw [HasLineDerivAt] at hf hg ⊢
  simpa only [Function.comp_apply, zero_smul, add_zero] using
    (B.hasFDerivAt.comp_hasDerivAt 0 hf).clm_apply hg

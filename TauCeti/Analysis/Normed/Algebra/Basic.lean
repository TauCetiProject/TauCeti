/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Rational scalars on real normed algebras

Much of Mathlib's API for `NormedSpace.exp` (for example `NormedSpace.exp_continuous`) assumes a
normed `ℚ`-algebra. This file names the restriction of scalars that makes every real normed
algebra a normed `ℚ`-algebra, so that files working with real Banach algebras can enable it
locally.
-/

public section

namespace TauCeti

variable {R : Type*} [SeminormedRing R] [NormedAlgebra ℝ R]

/-- A real normed algebra regarded as a rational normed algebra, by restricting scalars along
`ℚ → ℝ`.

This is not a global instance: algebras such as `ℂ` already carry a `ℚ`-algebra structure
(for example through Mathlib's `normedAlgebraRat`) that is not reducibly defeq to this one, so
a global instance would create a diamond. Enable it where needed with
`attribute [local instance] TauCeti.normedAlgebraRatOfReal`. -/
noncomputable abbrev normedAlgebraRatOfReal : NormedAlgebra ℚ R :=
  .restrictScalars ℚ ℝ R

end TauCeti

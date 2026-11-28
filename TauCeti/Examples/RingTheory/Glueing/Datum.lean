/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Field.Rat
public import TauCeti.RingTheory.Glueing.Datum

/-!
# Checks for `GlueingDatum`

* Positive section check: `((1, 2), (1, 2))` satisfies the cocycle condition for the trivial
  glueing datum of `ℚ × ℚ` over `ℚ`.
* Sign / cocycle check: `((1, 2), (2, 1))` does *not* lie in the sections of the glueing datum of
  `ℚ × ℚ` over `ℚ`.
-/

public section

open TensorProduct

namespace TauCeti.GlueingDatumChecks

/-- Positive section check: `((1, 2), (1, 2))` lies in sections of `ℚ × ℚ` over `ℚ`. -/
example : (((1 : ℚ) ⊗ₜ[ℚ] ((1 : ℚ), (2 : ℚ)), (1 : ℚ) ⊗ₜ[ℚ] ((1 : ℚ), (2 : ℚ))) :
      (ℚ ⊗[ℚ] (ℚ × ℚ)) × (ℚ ⊗[ℚ] (ℚ × ℚ))) ∈
    (GlueingDatum.ofModule ℚ ℚ ℚ ℚ (ℚ × ℚ)).sections ℚ := by simp

/-- Cocycle non-membership check: `((1, 2), (2, 1))` does not lie in sections. -/
example : (((1 : ℚ) ⊗ₜ[ℚ] ((1 : ℚ), (2 : ℚ)), (1 : ℚ) ⊗ₜ[ℚ] ((2 : ℚ), (1 : ℚ))) :
      (ℚ ⊗[ℚ] (ℚ × ℚ)) × (ℚ ⊗[ℚ] (ℚ × ℚ))) ∉
    (GlueingDatum.ofModule ℚ ℚ ℚ ℚ (ℚ × ℚ)).sections ℚ := fun hmem ↦ by
  simp only [GlueingDatum.mem_sections_iff, GlueingDatum.ofModule_ψ₁_tmul,
    GlueingDatum.ofModule_ψ₂_tmul, one_smul] at hmem
  simpa using congrArg (TensorProduct.lid ℚ (ℚ × ℚ)) hmem

end TauCeti.GlueingDatumChecks

end

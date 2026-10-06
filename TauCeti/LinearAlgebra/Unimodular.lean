/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Unimodular

/-!
# Unit rescaling of unimodular vectors

Multiplication by a unit preserves unimodularity in any module over a semiring.
Thus each unit multiple of a unimodular vector can be used as a generator when constructing
projective orbit morphisms.
-/

public section

namespace TauCeti.Module

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Multiplication by a unit preserves unimodularity. -/
theorem isUnimodular_units_smul (c : Rˣ) {m : M} (hm : Module.IsUnimodular R m) :
    Module.IsUnimodular R (c • m) := by
  obtain ⟨f, hf⟩ := Module.isUnimodular_iff.mp hm
  apply Module.isUnimodular_iff.mpr
  refine ⟨(LinearMap.mulRight R (↑c⁻¹ : R)).comp f, ?_⟩
  simp [LinearMap.mulRight_apply, Units.smul_def, hf]

end TauCeti.Module

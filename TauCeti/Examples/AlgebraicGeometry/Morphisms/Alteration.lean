/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.AlgebraicGeometry.Morphisms.Alteration

/-!
# An alteration of degree two

The morphism `Spec ℂ ⟶ Spec ℝ` is finite and surjective, hence an alteration
(`TauCeti.AlgebraicGeometry.isAlteration_of_isFinite`). Its generic degree is `[ℂ : ℝ] = 2`: the
predicate `IsAlteration` admits finite covers of degree greater than one.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

/-- `Spec ℂ ⟶ Spec ℝ` is an alteration. -/
theorem isAlteration_Spec_algebraMap_real_complex :
    IsAlteration (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  infer_instance

end TauCeti.AlgebraicGeometry

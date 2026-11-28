/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.BorelSpace
public import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Unique

/-!
# `GL₁` of the adeles and the ideles

For `n = 1`, the matrix-units topology and Borel structure of `GL₁(𝔸_F)` agree with those of the
ideles `𝔸_Fˣ`, through the entry of a `1 × 1` matrix.
-/

public section

namespace TauCeti.Examples

open NumberField

variable (F : Type*) [Field F] [NumberField F]

/-- `GL₁(𝔸_F)` and the ideles are isomorphic topological groups, through the matrix entry. -/
noncomputable example : GL (Fin 1) (AdeleRing (𝓞 F) F) ≃ₜ* IdeleGroup (𝓞 F) F :=
  Matrix.GeneralLinearGroup.uniqueContinuousMulEquiv _ _

/-- The same map is a measurable equivalence for the Borel structures of `GL₁(𝔸_F)` and of the
ideles. -/
noncomputable example : GL (Fin 1) (AdeleRing (𝓞 F) F) ≃ᵐ IdeleGroup (𝓞 F) F :=
  (Matrix.GeneralLinearGroup.uniqueContinuousMulEquiv _ _).toHomeomorph.toMeasurableEquiv

/-- The measurable equivalence reads off the matrix entry. -/
example (g : GL (Fin 1) (AdeleRing (𝓞 F) F)) :
    ((Matrix.GeneralLinearGroup.uniqueContinuousMulEquiv _ _).toHomeomorph.toMeasurableEquiv g :
        AdeleRing (𝓞 F) F) =
      (g : Matrix (Fin 1) (Fin 1) (AdeleRing (𝓞 F) F)) 0 0 := by
  simp [ContinuousMulEquiv.toHomeomorph_eq_coe]

end TauCeti.Examples

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.SymmetricProduct
import Mathlib.Tactic.Ring

/-!
# Inner-product properties of the symmetric exterior product

On finite-dimensional real inner product spaces `E` and `F`, taking the Hilbert-space adjoint
commutes with the symmetric exterior product `exteriorPower.symmMap₂`:
`(f ∧ g)* = f* ∧ g*` (`exteriorPower.adjoint_symmMap₂`).
-/

public section

open scoped RealInnerProductSpace

noncomputable section

namespace exteriorPower

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Taking the adjoint commutes with `exteriorPower.symmMap₂`: `(f ∧ g)* = f* ∧ g*`. -/
@[simp]
theorem adjoint_symmMap₂ (f g : E →ₗ[ℝ] F) :
    LinearMap.adjoint (symmMap₂ f g) = symmMap₂ (LinearMap.adjoint f) (LinearMap.adjoint g) := by
  refine linearMap_ext_inner_ιMulti_two fun α β γ δ ↦ ?_
  rw [LinearMap.adjoint_inner_left]
  -- `symmMap₂` uses `Submodule.module` rather than `NormedSpace.toModule` on `⋀[ℝ]^2 F`;
  -- instantiate `real_inner_smul_right` / `inner_add_right` concretely.
  have hsmul (x y : ⋀[ℝ]^2 F) (c : ℝ) : ⟪x, c • y⟫ = c * ⟪x, y⟫ :=
    real_inner_smul_right x y c
  have hadd (x y z : ⋀[ℝ]^2 F) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ :=
    inner_add_right x y z
  simp only [symmMap₂_apply_ιMulti, real_inner_smul_left, hsmul,
    inner_add_left, hadd, inner_ιMulti_two, LinearMap.adjoint_inner_left]
  simp only [real_inner_comm (f _), real_inner_comm (g _)]
  ring

end exteriorPower

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Determinant
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Operations
public import TauCeti.LinearAlgebra.Determinant.ConstantRank
public import TauCeti.LinearAlgebra.Determinant.ProjectiveOperations

/-!
# Determinant characters of restrictions, sums, twists and duals

For continuous representations on finite projective modules, the determinant character
`TauCeti.ContinuousRep.det` satisfies:

* `det (Res_φ ρ) = det ρ ∘ φ` (`ContinuousRep.det_res`);
* `det (ρ × σ) = det ρ · det σ` (`ContinuousRep.det_prod`);
* `det (ρ(χ)) = det ρ · χ^d` when `M` has constant rank `d` (`ContinuousRep.det_twist`);
* `det (ρ^∨) = (det ρ)⁻¹` (`ContinuousRep.det_dual`).

The determinant of a product uses `LinearMap.projectiveDet_prodMap`, that of a dual
`LinearMap.projectiveDet_dualMap`, and that of a twist `LinearMap.projectiveDet_smul`.
-/

public section

open Module

namespace TauCeti.ContinuousRep

variable {Γ A M N : Type*} [Group Γ] [TopologicalSpace Γ] [CommRing A]
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [Module.Finite A M] [Module.Projective A M]
  [AddCommGroup N] [Module A N] [TopologicalSpace N] [Module.Finite A N] [Module.Projective A N]

/-- **The determinant of a restriction** is the restriction of the determinant. -/
@[simp]
theorem det_res {Γ' : Type*} [Group Γ'] [TopologicalSpace Γ'] (ρ : ContinuousRep Γ A M)
    (φ : Γ' →ₜ* Γ) : (ρ.res φ).det = ρ.det.comp φ.toMonoidHom := by
  ext g
  simp

/-- **The determinant of a direct sum** is the product of the determinants. -/
@[simp]
theorem det_prod (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) :
    (ρ.prod σ).det = ρ.det * σ.det := by
  ext g
  simp only [coe_det_apply, MonoidHom.mul_apply, Units.val_mul]
  rw [show ρ.prod σ g = (ρ g).prodMap (σ g) from LinearMap.ext fun x ↦ by simp [prod_apply]]
  exact LinearMap.projectiveDet_prodMap (ρ g) (σ g)

/-- **The determinant of a twist**: on a module of constant rank `d`, twisting by `χ` multiplies
the determinant character by `χ ^ d`. -/
theorem det_twist [TopologicalSpace A] [ContinuousSMul A M] {d : ℕ}
    (hd : ∀ p, rankAtStalk (R := A) M p = d) (ρ : ContinuousRep Γ A M) (χ : Γ →ₜ* Aˣ) :
    (ρ.twist χ).det = ρ.det * (χ : Γ →* Aˣ) ^ d := by
  ext g
  rw [coe_det_apply, show (ρ.twist χ) g = (χ g : A) • ρ g from LinearMap.ext fun x ↦ by simp,
    LinearMap.projectiveDet_smul hd, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul,
    Units.val_pow_eq_pow_val, coe_det_apply, mul_comm]
  rfl

/-- **The determinant of the contragredient** is the inverse of the determinant character. -/
@[simp]
theorem det_dual [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology A M]
    [ContinuousInv Γ] [TopologicalSpace (Module.Dual A M)] [IsModuleTopology A (Module.Dual A M)]
    (ρ : ContinuousRep Γ A M) : ρ.dual.det = ρ.det⁻¹ := by
  ext g
  rw [coe_det_apply, dual_apply, ← LinearMap.dualMap_def, LinearMap.projectiveDet_dualMap,
    ← coe_det_apply, map_inv, MonoidHom.inv_apply]

end TauCeti.ContinuousRep

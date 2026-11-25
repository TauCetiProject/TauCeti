/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import TauCeti.LinearAlgebra.Eigenspace.Transport

/-!
# Eigenvalues of linear automorphisms

The eigenvalues of the inverse of a linear automorphism are the inverses of its eigenvalues, and
transport along a linear equivalence preserves eigenvalues.

## Main declarations

* `LinearMap.GeneralLinearGroup.hasEigenvalue_inv_iff`: `μ` is an eigenvalue of `g⁻¹` exactly
  when `μ⁻¹` is an eigenvalue of `g`.
* `LinearMap.GeneralLinearGroup.hasEigenvalue_congrLinearEquiv_iff`: transport along a linear
  equivalence preserves eigenvalues.
-/

public section

namespace LinearMap.GeneralLinearGroup

open Module

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- `μ` is an eigenvalue of the inverse of `g` exactly when `μ⁻¹` is an eigenvalue of `g`. -/
@[simp]
theorem hasEigenvalue_inv_iff (g : GeneralLinearGroup K V) (μ : Kˣ) :
    Module.End.HasEigenvalue ((g⁻¹ : GeneralLinearGroup K V) : End K V) μ ↔
      Module.End.HasEigenvalue (g : End K V) (μ⁻¹ : Kˣ) := by
  -- An eigenvector of `g` for `μ⁻¹` is an eigenvector of `g⁻¹` for `μ`, and conversely.
  suffices key : ∀ (g : GeneralLinearGroup K V) (μ : Kˣ),
      Module.End.HasEigenvalue (g : End K V) (μ⁻¹ : Kˣ) →
        Module.End.HasEigenvalue ((g⁻¹ : GeneralLinearGroup K V) : End K V) μ by
    refine ⟨fun h ↦ ?_, key g μ⟩
    simpa using key g⁻¹ μ⁻¹ (by simpa using h)
  intro g μ h
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  refine Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv.2⟩
  have h1 : ((g⁻¹ : GeneralLinearGroup K V) : End K V) ((g : End K V) v) = v := by
    rw [← mul_apply_eq_comp, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq_self]
  rw [hv.apply_eq_smul, map_smul] at h1
  calc ((g⁻¹ : GeneralLinearGroup K V) : End K V) v
      = (μ : K) • ((μ⁻¹ : Kˣ) : K) • ((g⁻¹ : GeneralLinearGroup K V) : End K V) v := by
        rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
    _ = (μ : K) • v := by rw [h1]

/-- Transport along a linear equivalence preserves eigenvalues. -/
theorem hasEigenvalue_congrLinearEquiv_iff (e : V ≃ₗ[K] W) (g : GeneralLinearGroup K V)
    (μ : K) :
    Module.End.HasEigenvalue (congrLinearEquiv e g : End K W) μ ↔
      Module.End.HasEigenvalue (g : End K V) μ := by
  rw [Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff,
    TauCeti.eigenspace_eq_comap_of_intertwine (e := e) (g := (congrLinearEquiv e g : End K W))
      (fun x ↦ by simp) μ, ne_eq, ne_eq, Submodule.comap_equiv_eq_map_symm,
    Submodule.map_eq_bot_iff]

end LinearMap.GeneralLinearGroup

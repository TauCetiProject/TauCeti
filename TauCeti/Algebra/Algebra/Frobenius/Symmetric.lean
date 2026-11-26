/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Basic

/-!
# Symmetric algebras and inner Nakayama automorphisms

A finite-dimensional Frobenius algebra is symmetric precisely when its Nakayama automorphism
is inner. We use the inverse Nakayama automorphism, so the unit also describes the change from
the given Frobenius functional to a symmetric one.

## References

* T. Y. Lam, *Lectures on modules and rings*, Section 16.
-/

public section

namespace TauCeti

/-- An algebra is symmetric Frobenius if it admits a symmetric Frobenius functional. -/
def IsSymmetricFrobenius (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] : Prop :=
  ∃ φ : A →ₗ[k] k, φ.IsSymmetricFrobeniusFunctional

/-- The existence characterization of a symmetric Frobenius algebra. -/
theorem isSymmetricFrobenius_iff (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] :
    IsSymmetricFrobenius k A ↔ ∃ φ : A →ₗ[k] k, φ.IsSymmetricFrobeniusFunctional :=
  Iff.rfl

end TauCeti

namespace LinearMap

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  {φ : A →ₗ[k] k}

/-- A Frobenius algebra is symmetric exactly when its inverse Nakayama automorphism is inner. -/
theorem IsFrobeniusFunctional.isSymmetricFrobenius_iff_nakayamaAut_symm_eq_conj
    (hφ : φ.IsFrobeniusFunctional) :
    TauCeti.IsSymmetricFrobenius k A ↔
      ∃ u : Aˣ, ∀ a : A, hφ.nakayamaAut.symm a = (u : A) * a * ↑u⁻¹ := by
  rw [TauCeti.isSymmetricFrobenius_iff]
  constructor
  · rintro ⟨ψ, hψ⟩
    obtain ⟨u, hu⟩ := hφ.exists_unit_apply_eq_apply_mul hψ.isFrobeniusFunctional
    refine ⟨u, fun b => ?_⟩
    have he : hφ.nakayamaAut.symm b * (u : A) = (u : A) * b := by
      apply hφ.toDualEquiv.injective
      ext a
      simp only [toDualEquiv_apply_apply, mul_assoc]
      calc
        φ (hφ.nakayamaAut.symm b * (↑u * a)) = φ ((↑u * a) * b) := by
          simpa using (hφ.apply_mul_nakayamaAut (hφ.nakayamaAut.symm b) (↑u * a)).symm
        _ = ψ (a * b) := by rw [mul_assoc, ← hu]
        _ = ψ (b * a) := hψ.apply_mul_comm a b
        _ = φ (↑u * (b * a)) := hu _
    simpa [mul_assoc] using congrArg (fun x => x * (↑u⁻¹ : A)) he
  · rintro ⟨u, hu⟩
    refine ⟨φ.comp (LinearMap.mulLeft k (u : A)), hφ.comp_mulLeft_unit u, fun a b => ?_⟩
    simp only [comp_apply, mulLeft_apply]
    calc
      φ (↑u * (a * b)) = φ (hφ.nakayamaAut.symm b * (↑u * a)) := by
        simpa only [mul_assoc, AlgEquiv.apply_symm_apply] using
          hφ.apply_mul_nakayamaAut (hφ.nakayamaAut.symm b) (↑u * a)
      _ = φ (↑u * (b * a)) := by rw [hu]; simp [mul_assoc]

end LinearMap

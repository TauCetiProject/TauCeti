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

variable {k A : Type*}

/-- Multiplication by a unit preserves Frobenius functionals. -/
theorem IsFrobeniusFunctional.comp_mulLeft_unit [CommSemiring k] [Semiring A] [Algebra k A]
    {φ : A →ₗ[k] k} (hφ : φ.IsFrobeniusFunctional) (u : Aˣ) :
    (φ.comp (LinearMap.mulLeft k (u : A))).IsFrobeniusFunctional := by
  refine isFrobeniusFunctional_iff.mpr ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have h : (u : A) * a = 0 := hφ.eq_zero_of_forall_left fun b => by
      simpa only [comp_apply, mulLeft_apply, mul_assoc] using ha b
    simpa using congrArg (fun x => (↑u⁻¹ : A) * x) h
  · exact hφ.eq_zero_of_forall_right fun a => by
      simpa [← mul_assoc] using
        hb ((↑u⁻¹ : A) * a)

variable [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  {φ ψ : A →ₗ[k] k}

/-- Any two Frobenius functionals differ by left multiplication by a unit. -/
theorem IsFrobeniusFunctional.exists_unit_apply_eq_apply_mul
    (hφ : φ.IsFrobeniusFunctional) (hψ : ψ.IsFrobeniusFunctional) :
    ∃ u : Aˣ, ∀ x : A, ψ x = φ ((u : A) * x) := by
  let a := hφ.toDualEquiv.symm ψ
  have ha (x : A) : φ (a * x) = ψ x := by
    simpa only [toDualEquiv_apply_apply] using
      DFunLike.congr_fun (hφ.toDualEquiv.apply_symm_apply ψ) x
  have he : (fun x : A => a * x) = hφ.toDualEquiv.symm ∘ hψ.toDualEquiv := by
    funext x
    apply hφ.toDualEquiv.injective
    ext y
    simp only [Function.comp_apply, LinearEquiv.apply_symm_apply,
      toDualEquiv_apply_apply, mul_assoc, ha]
  have hu : IsUnit a := IsUnit.isUnit_iff_mulLeft_bijective.mpr <| by
    rw [he]
    exact hφ.toDualEquiv.symm.bijective.comp hψ.toDualEquiv.bijective
  obtain ⟨u, hu⟩ := hu
  exact ⟨u, fun x => by rw [hu]; exact (ha x).symm⟩

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

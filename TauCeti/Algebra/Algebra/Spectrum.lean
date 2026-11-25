/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Spectra under unit-reflecting algebra homomorphisms, of `1 + k a`, and of integral elements

Every algebra homomorphism `φ` satisfies `spectrum R (φ a) ⊆ spectrum R a`
(`AlgHom.spectrum_apply_subset`). When `φ` also reflects units, the inclusion is an equality.
This is the algebraic form of spectral permanence: it holds for the inclusion of an
inverse-closed subalgebra, and for the complexification of real operators.

More generally, if units in the image of `Φ` lift to source units, an algebra homomorphism `χ`
killing the kernel of `Φ` satisfies `spectrum R (χ a) ⊆ spectrum R (Φ a)`
(`AlgHom.spectrum_apply_subset_of_ker_le`); in particular a scalar-valued such `χ` takes values
in the image spectrum (`AlgHom.apply_mem_spectrum_of_ker_le`). This is the algebraic input to
extending characters from dense homomorphic images of Banach algebras.

Over a field, `1 + k a` is invertible exactly when `1 + k x` does not vanish on the spectrum of
`a` (`spectrum.isUnit_one_add_smul_iff`): for `k ≠ 0` the spectrum of `1 + k a` is the image of
that of `a` under `x ↦ 1 + k x`.

An integral element over a field has finite spectrum (`IsIntegral.finite_spectrum`): its spectrum
consists of roots of a monic annihilating polynomial. In particular every element of a
finite-dimensional algebra over a field has finite spectrum
(`spectrum.finite_of_finiteDimensional`).

## References

* G. K. Pedersen, *Analysis Now*, §4.2, Exercises 11–12, for the scalar character argument.
-/

public section

namespace AlgHom

variable {F R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  [FunLike F A B] [AlgHomClass F R A B]

/-- An algebra homomorphism which reflects units preserves spectra. -/
@[simp]
theorem spectrum_apply_eq (φ : F) [IsLocalHom φ] (a : A) :
    spectrum R (φ a) = spectrum R a := by
  ext r
  simp only [spectrum.mem_iff, ← isUnit_map_iff φ (algebraMap R A r - a), map_sub,
    AlgHomClass.commutes]

/-- If units in the image of `Φ` lift to units, then a homomorphism `χ` killing the kernel of `Φ`
can only shrink spectra relative to `Φ`. -/
theorem spectrum_apply_subset_of_ker_le {G C : Type*} [Ring C] [Algebra R C] [FunLike G A C]
    [AlgHomClass G R A C] (Φ : F)
    (hUnits : ∀ a : A, IsUnit (Φ a) → ∃ b : A, IsUnit b ∧ Φ b = Φ a)
    (χ : G) (hχ : RingHom.ker Φ ≤ RingHom.ker χ) (a : A) :
    spectrum R (χ a) ⊆ spectrum R (Φ a) := by
  intro r hr
  rw [spectrum.mem_iff] at hr ⊢
  intro h
  obtain ⟨b, hb, hbΦ⟩ := hUnits (algebraMap R A r - a) (by simpa [AlgHomClass.commutes] using h)
  have hk : b - (algebraMap R A r - a) ∈ RingHom.ker χ := hχ (by simp [RingHom.mem_ker, hbΦ])
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hk
  exact hr (by simpa [hk, AlgHomClass.commutes] using hb.map χ)

/-- A scalar-valued homomorphism killing the kernel takes its value in the image spectrum
whenever units in the image lift to units. -/
theorem apply_mem_spectrum_of_ker_le {R A B F G : Type*} [CommRing R] [Nontrivial R] [Ring A]
    [Algebra R A] [Ring B] [Algebra R B] [FunLike F A B] [AlgHomClass F R A B] [FunLike G A R]
    [AlgHomClass G R A R] (Φ : F)
    (hUnits : ∀ a : A, IsUnit (Φ a) → ∃ b : A, IsUnit b ∧ Φ b = Φ a)
    (χ : G) (hχ : RingHom.ker Φ ≤ RingHom.ker χ) (a : A) :
    χ a ∈ spectrum R (Φ a) :=
  spectrum_apply_subset_of_ker_le Φ hUnits χ hχ a (by simp [spectrum.mem_iff])

end AlgHom

open Polynomial in
/-- An integral element of an algebra over a field has finite spectrum. -/
theorem IsIntegral.finite_spectrum {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {a : A}
    (ha : IsIntegral 𝕜 a) : (spectrum 𝕜 a).Finite := by
  nontriviality A
  obtain ⟨p, hp, hpa⟩ := ha
  refine (Polynomial.finite_setOfPred_isRoot hp.ne_zero).subset fun k hk ↦ ?_
  have := spectrum.subset_polynomial_aeval a p ⟨k, hk, rfl⟩
  rw [← aeval_def] at hpa
  rw [hpa, spectrum.zero_eq, Set.mem_singleton_iff] at this
  exact this

namespace spectrum

/-- Over a field, `1 + k a` is invertible exactly when `1 + k x` does not vanish on the spectrum
of `a`. -/
theorem isUnit_one_add_smul_iff {R A : Type*} [Field R] [Ring A] [Algebra R A] {a : A} {k : R} :
    IsUnit (1 + k • a) ↔ ∀ x ∈ spectrum R a, 1 + k * x ≠ 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  -- The spectrum of `1 + k a` is the image of that of `a` under `x ↦ 1 + k x`.
  have hσ : spectrum R (1 + k • a) = (fun x ↦ 1 + k * x) '' spectrum R a := by
    have h₁ := singleton_add_eq (Units.mk0 k hk • a) (1 : R)
    have h₂ := unit_smul_eq_smul a (Units.mk0 k hk)
    simp only [map_one, Units.smul_mk0] at h₁ h₂
    rw [← h₁, h₂, Set.singleton_add, ← Set.image_smul, Set.image_image]
    simp only [smul_eq_mul]
  rw [← zero_notMem_iff R, hσ]
  simp

/-- An element of a finite-dimensional algebra over a field has finite spectrum. -/
theorem finite_of_finiteDimensional {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    [FiniteDimensional 𝕜 A] (a : A) : (spectrum 𝕜 a).Finite :=
  (IsIntegral.of_finite 𝕜 a).finite_spectrum

end spectrum

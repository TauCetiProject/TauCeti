/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
# Spectra under unit-reflecting algebra homomorphisms

Every algebra homomorphism `φ` satisfies `spectrum R (φ a) ⊆ spectrum R a`
(`AlgHom.spectrum_apply_subset`). When `φ` also reflects units, the inclusion is an equality.
This is the algebraic form of spectral permanence: it holds for the inclusion of an
inverse-closed subalgebra, and for the complexification of real operators.

More generally, if units in the image of `Φ` lift to source units, an algebra homomorphism `χ`
killing the kernel of `Φ` satisfies `spectrum R (χ a) ⊆ spectrum R (Φ a)`
(`AlgHom.spectrum_apply_subset_of_ker_le`); in particular a scalar-valued such `χ` takes values
in the image spectrum (`AlgHom.apply_mem_spectrum_of_ker_le`). This is the algebraic input to
extending characters from dense homomorphic images of Banach algebras.

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

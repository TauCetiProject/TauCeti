/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Scaling
public import TauCeti.NumberTheory.IntegralLattice.Dyadic.DensityExponent.JordanSplitting
public import TauCeti.NumberTheory.IntegralLattice.Dyadic.DensityExponent.Scaling
public import TauCeti.NumberTheory.IntegralLattice.Localization.Operations
public import TauCeti.NumberTheory.IntegralLattice.JordanSplitting

/-!
# Dyadic density exponents under a form twist by two

Twisting an integral lattice's form by `2` shifts its dyadic Jordan constituents up one
scale. Their ranks and scale-relative parity types are unchanged. We identify the profile
of the twisted lattice with the shift of the original profile, so the profile-level scaling
formulas compute the exponents of the actual lattice. In particular `N_M` is unchanged and
`N_Q` and `N` both increase by the scale-shift correction.

This operation changes the form, not the carrier: it is distinct from dilating the lattice
inside its rational ambient space. The results apply to nondegenerate lattices of any
signature, including rank zero.

## References

* S. Cho, *Group schemes and local densities of quadratic lattices in residue characteristic 2*,
  Compositio Math. 151 (2015), Definition 2.1, Section 2.3, and Lemma 5.1.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §91C.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R M : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
  {B : BilinForm R M} {π : R} {N : ℕ → Submodule R M}

/-- The profile of a Jordan splitting multiplied by its uniformizer is the shift of the
original profile. In particular the parity of each constituent is measured at its new scale,
not by divisibility by the uniformizer alone. -/
theorem IsJordanSplitting.dyadicJordanProfile_smul_uniformizer
    (h : B.IsJordanSplitting π N) (hB : B.IsSymm) (hπ : π ≠ 0) (hπ' : ¬IsUnit π) :
    h.smul_uniformizer.dyadicJordanProfile (hB.smul π) hπ hπ' =
      (h.dyadicJordanProfile hB hπ hπ').shift := by
  ext i
  · cases i with
    | zero => simp
    | succ i => simp
  · cases i with
    | zero =>
      rw [h.smul_uniformizer.mem_dyadicJordanProfile_typeI_iff_exists]
      simp
    | succ i =>
      rw [h.smul_uniformizer.mem_dyadicJordanProfile_typeI_iff_exists,
        TauCeti.DyadicJordanProfile.mem_shift_typeI_succ_iff,
        h.mem_dyadicJordanProfile_typeI_iff_exists]
      simp only [LinearMap.smul_apply, smul_eq_mul, pow_succ' π (i + 1),
        mul_dvd_mul_iff_left hπ]

end LinearMap.BilinForm

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (L : IntegralLattice V) [L.IsNondegenerate]

/-- Twisting a nondegenerate integral lattice's form by `2` shifts every dyadic Jordan scale
up one, preserving the constituent ranks and parity types. -/
@[simp]
theorem dyadicJordanProfile_smul_two :
    ((2 : ℤ) • L).dyadicJordanProfile = L.dyadicJordanProfile.shift := by
  obtain ⟨N, hN⟩ := L.exists_isJordanSplitting_localIntegralForm 2 L.form_nondegenerate
  have hN' : (((2 : ℤ) • L).localIntegralForm 2).IsJordanSplitting 2
      (fun | 0 => ⊥ | i + 1 => N i) := by
    rw [localIntegralForm_smul]
    -- The carriers agree; reconcile their inherited tensor-product instances.
    convert! hN.smul_uniformizer using 1
  rw [dyadicJordanProfile_eq hN', dyadicJordanProfile_eq hN]
  refine (hN'.dyadicJordanProfile_eq_of_equivalent _ _ _ hN.smul_uniformizer
    ((L.isSymm_localIntegralForm 2).smul (2 : ℤ_[2])) ?_).trans ?_
  · exact ⟨{ toLinearEquiv := LinearEquiv.refl _ _
             map_app' x y := by simp }⟩
  · exact hN.dyadicJordanProfile_smul_uniformizer (L.isSymm_localIntegralForm 2)
      two_ne_zero PadicInt.not_isUnit_two

/-- Cho's exponent `N_Q` increases by the scale-shift correction under a form twist by `2`. -/
theorem nQ_dyadicJordanProfile_smul_two :
    ((2 : ℤ) • L).dyadicJordanProfile.nQ =
      L.dyadicJordanProfile.nQ + L.dyadicJordanProfile.shiftCorrection := by
  rw [dyadicJordanProfile_smul_two, DyadicJordanProfile.nQ_shift]

/-- Cho's density exponent `N` increases by the scale-shift correction under a form twist
by `2`. -/
theorem densityExponent_dyadicJordanProfile_smul_two :
    ((2 : ℤ) • L).dyadicJordanProfile.densityExponent =
      L.dyadicJordanProfile.densityExponent + L.dyadicJordanProfile.shiftCorrection := by
  rw [dyadicJordanProfile_smul_two, DyadicJordanProfile.densityExponent_shift]

end TauCeti.IntegralLattice

end

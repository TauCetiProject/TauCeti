/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Basic
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import TauCeti.Data.Int.MulPred
import TauCeti.NumberTheory.IntegralLattice.Localization.Unimodular
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Characteristic vectors of a localized lattice

A characteristic vector `w` of an integral lattice `L` satisfies `B(x, x) ≡ B(x, w)` modulo `2`
for every `x ∈ L`. At the dyadic prime this congruence persists after localization: `1 ⊗ w` is a
characteristic vector of the integral form on `ℤ_[2] ⊗[ℤ] L`. Since squaring is the identity
modulo `2` in `ℤ_[2]`, it suffices to test the characteristic condition on a basis, and there it
is the integral congruence cast into `ℤ_[2]`. Conversely, when `L` has odd discriminant its dyadic
localization is unimodular and therefore admits a `2`-adic characteristic vector, whose coordinates
truncate modulo `2` to an integral characteristic vector of `L`.

## Main results

* `TauCeti.IntegralLattice.IsCharacteristicVector.isCharacteristic_localIntegralForm`: a
  characteristic vector of a lattice is characteristic for its dyadic localization.
* `TauCeti.IntegralLattice.exists_isCharacteristicVector_of_odd_discriminant`: every integral
  lattice of odd discriminant admits an integral characteristic vector.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- **Integral characteristic vectors stay characteristic at `2`.** If `w` is a characteristic
vector of `L`, then `1 ⊗ w` is a characteristic vector of the dyadic localization of `L`. -/
theorem IsCharacteristicVector.isCharacteristic_localIntegralForm {L : IntegralLattice V} {w : L}
    (hw : L.IsCharacteristicVector w) :
    (L.localIntegralForm 2).IsCharacteristic ((1 : ℤ_[2]) ⊗ₜ w) := by
  let b := finBasis ℤ L
  refine ((L.isSymm_localIntegralForm 2).isCharacteristic_iff_forall_basis
    PadicInt.two_dvd_sq_sub_self (b.baseChange ℤ_[2])).mpr fun i ↦ ?_
  have h := LinearMap.BilinForm.isCharacteristic_iff.mp
    ((L.isCharacteristicVector_iff_isCharacteristic w).mp hw) (b i)
  simpa only [Basis.baseChange_apply, localIntegralForm_tmul, one_mul, Int.cast_sub,
    Int.cast_ofNat] using Int.cast_dvd_cast (α := ℤ_[2]) _ _ h

/-- Every integral lattice of odd discriminant admits an integral characteristic vector. -/
theorem exists_isCharacteristicVector_of_odd_discriminant {L : IntegralLattice V}
    (hL : Odd L.discriminant) : ∃ w : L, L.IsCharacteristicVector w := by
  classical
  have hunit : IsUnit (L.determinant : ℤ_[2]) :=
    (L.isUnit_determinant_two_iff_odd_discriminant).mpr hL
  have := L.isPerfPair_localIntegralForm_of_isUnit_determinant 2 hunit
  obtain ⟨w₂, hw₂⟩ :=
    (L.isSymm_localIntegralForm 2).exists_isCharacteristic PadicInt.two_dvd_sq_sub_self
  let b := Module.finBasis ℤ L
  let b₂ := b.baseChange ℤ_[2]
  let m : Fin (finrank ℤ L) → ℤ := fun i ↦ ((b₂.repr w₂ i).appr 1 : ℤ)
  refine ⟨∑ i, m i • b i, (L.isCharacteristicVector_iff_isCharacteristic _).mpr ?_⟩
  refine (L.isSymm_integralForm.isCharacteristic_iff_forall_basis Int.two_dvd_sq_sub_self b).mpr
    fun j ↦ ?_
  have hdvd_diff : (2 : ℤ_[2]) ∣
      L.localIntegralForm 2 w₂ (b₂ j) - (L.integralForm (∑ i, m i • b i) (b j) : ℤ_[2]) := by
    rw [← b₂.sum_repr w₂]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Int.cast_sum, Int.cast_mul, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ ↦ ?_
    have hbij : L.localIntegralForm 2 (b₂ i) (b₂ j) = (L.integralForm (b i) (b j) : ℤ_[2]) := by
      simp [b₂]
    rw [hbij, ← sub_mul]
    exact dvd_mul_of_dvd_left (by simpa [m] using PadicInt.dvd_sub_appr (b₂.repr w₂ i) 1) _
  have hbj : L.localIntegralForm 2 (b₂ j) (b₂ j) = (L.integralForm (b j) (b j) : ℤ_[2]) := by
    simp [b₂]
  have hdvd₂ : (2 : ℤ_[2]) ∣
      ((L.integralForm (∑ i, m i • b i) (b j) - L.integralForm (b j) (b j) : ℤ) : ℤ_[2]) := by
    have hsub := dvd_sub (LinearMap.BilinForm.isCharacteristic_iff.mp hw₂ (b₂ j)) hdvd_diff
    rwa [hbj, sub_sub_sub_cancel_left, ← Int.cast_sub] at hsub
  exact_mod_cast (PadicInt.pow_p_dvd_int_iff (p := 2) 1 _).mp (by simpa using hdvd₂)

end TauCeti.IntegralLattice

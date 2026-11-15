/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Basic
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Characteristic vectors of a localized lattice

A characteristic vector `w` of an integral lattice `L` satisfies `B(x, x) ≡ B(x, w)` modulo `2`
for every `x ∈ L`. At the dyadic prime this congruence persists after localization: `1 ⊗ w` is a
characteristic vector of the integral form on `ℤ_[2] ⊗[ℤ] L`. Since squaring is the identity
modulo `2` in `ℤ_[2]`, it suffices to test the characteristic condition on a basis, and there it
is the integral congruence cast into `ℤ_[2]`.

## Main results

* `TauCeti.IntegralLattice.IsCharacteristicVector.isCharacteristic_localIntegralForm`: a
  characteristic vector of a lattice is characteristic for its dyadic localization.

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

end TauCeti.IntegralLattice

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
public import TauCeti.LinearAlgebra.BilinearForm.LocalRing
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Basic
public import TauCeti.NumberTheory.IntegralLattice.Localization.Ideals
public import TauCeti.NumberTheory.IntegralLattice.Localization.Unimodular
import TauCeti.LinearAlgebra.BilinearForm.Even.Basic
import TauCeti.NumberTheory.IntegralLattice.Localization.Characteristic
import TauCeti.NumberTheory.Padics.BilinearForm.Unimodular
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Lattices unimodular at `2`

A lattice whose determinant is a unit at `2` has a unimodular dyadic localization. Over `ℤ_[2]`
such forms are classified by their rank, their type (even or odd), their determinant square class
and their oddity, the norm of a characteristic vector modulo `8`
(`LinearMap.BilinForm.IsSymm.equivalent_iff_two_dvd_iff_and_isSquare_det_mul_det_and_eight_dvd`).
This file transfers that classification to lattices: evenness of a lattice is evenness of its
dyadic localization
(`TauCeti.IntegralLattice.isEven_iff_forall_two_dvd_localIntegralForm_apply_self`), and
characteristic vectors of the lattice stay characteristic after localization
(`TauCeti.IntegralLattice.IsCharacteristicVector.isCharacteristic_localIntegralForm`), so the
invariants can be read off the lattice itself. For even lattices the oddity
is automatically `0`, and the localizations are classified by rank and determinant square class,
as at odd primes (`TauCeti.IntegralLattice.localIntegralForm_equivalent_iff`). The oddity cannot
be dropped: the lattices `⟨1, 1⟩` and `⟨3, 3⟩` are odd, with the same rank and square determinants,
but only the first represents `1` over `ℤ_[2]`. Nor can the type: the hyperbolic plane and
`⟨1, -1⟩` have rank two, determinant `-1` and oddity `0`, but only the second is odd.

An even lattice unimodular at `2` has even rank and splits off a rank-two perfect summand
orthogonally after localization.

## Main results

* `TauCeti.IntegralLattice.IsEven.even_finrank_of_isUnit_determinant`: an even lattice of odd
  determinant has even rank.
* `TauCeti.IntegralLattice.exists_binary_isPerfPair_isCompl_orthogonal_localIntegralForm`: an even
  lattice unimodular at `2` splits off a perfect binary summand after localization.
* `TauCeti.IntegralLattice.localIntegralForm_two_equivalent_iff`: lattices with determinants that
  are units at `2` have isometric dyadic localizations exactly when their ranks, types,
  determinant square classes and oddities agree;
  `TauCeti.IntegralLattice.localIntegralForm_two_equivalent_iff_of_isCharacteristicVector` reads
  the oddity off integral characteristic vectors.
* `TauCeti.IntegralLattice.localIntegralForm_two_equivalent_iff_of_isEven`: for even lattices the
  rank and the determinant square class suffice.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Chapter IX.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

namespace TauCeti.IntegralLattice

open Module

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- **An even lattice of odd determinant has even rank.** Its dyadic localization is a perfect
pairing whose self-pairings are all divisible by `2`, and such a form has even rank. -/
theorem IsEven.even_finrank_of_isUnit_determinant {L : IntegralLattice V} (heven : L.IsEven)
    (hdet : IsUnit (L.determinant : ℤ_[2])) : Even (finrank ℤ L) := by
  have := L.isPerfPair_localIntegralForm_of_isUnit_determinant 2 hdet
  have h := (L.isSymm_localIntegralForm 2).even_finrank_of_isPerfPair (L.localIntegralForm 2)
    fun x hx ↦ PadicInt.not_isUnit_two
      (isUnit_of_dvd_unit (heven.two_dvd_localIntegralForm_apply_self x) hx)
  rwa [Module.finrank_baseChange] at h

/-- **An even lattice unimodular at `2` splits off a perfect binary summand.** If the rank is at
least two, the dyadic localization has a rank-two submodule carrying a perfect restriction of the
local integral form and complementary to its orthogonal complement. -/
theorem exists_binary_isPerfPair_isCompl_orthogonal_localIntegralForm
    (L : IntegralLattice V) (hrank : 2 ≤ finrank ℤ L) (heven : L.IsEven)
    (hdet : IsUnit (L.determinant : ℤ_[2])) :
    ∃ S : Submodule ℤ_[2] (L.LocalCarrier 2),
      finrank ℤ_[2] S = 2 ∧ ((L.localIntegralForm 2).restrict S).IsPerfPair ∧
        IsCompl S ((L.localIntegralForm 2).orthogonal S) := by
  have hrank' : finrank ℤ L = (finrank ℤ L - 2) + 2 := (Nat.sub_add_cancel hrank).symm
  let c := (Module.finBasis ℤ L).reindex (finCongr hrank')
  let b := c.baseChange ℤ_[2]
  have hdet' : IsUnit ((L.localIntegralForm 2).toMatrix b).det := by
    exact L.det_toMatrix_localIntegralForm 2 c ▸ hdet
  exact LinearMap.BilinForm.IsSymm.exists_binary_isPerfPair_isCompl_orthogonal
    (L.localIntegralForm 2) (L.isSymm_localIntegralForm 2) b
      heven.two_dvd_localIntegralForm_apply_self (mem_nonunits_iff.mp PadicInt.p_nonunit) hdet'

/-- **Classification of localizations unimodular at `2`.** Let `L` and `M` be lattices whose
determinants are units at `2`, and let `w` and `w'` be characteristic vectors of their dyadic
localizations. The localizations are integrally isometric exactly when the ranks agree, `L` is even
if and only if `M` is, the product of the determinants is a square in `ℤ_[2]`, and
`B(w, w) ≡ B(w', w')` modulo `8`, that is, the oddities agree. The lattices need not be globally
unimodular. -/
theorem localIntegralForm_two_equivalent_iff (L : IntegralLattice V) (M : IntegralLattice W)
    (hL : IsUnit (L.determinant : ℤ_[2])) (hM : IsUnit (M.determinant : ℤ_[2]))
    {w : L.LocalCarrier 2} {w' : M.LocalCarrier 2}
    (hw : (L.localIntegralForm 2).IsCharacteristic w)
    (hw' : (M.localIntegralForm 2).IsCharacteristic w') :
    (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) ↔
      finrank ℤ L = finrank ℤ M ∧ (L.IsEven ↔ M.IsEven) ∧
        IsSquare ((L.determinant : ℤ_[2]) * (M.determinant : ℤ_[2])) ∧
        (8 : ℤ_[2]) ∣ M.localIntegralForm 2 w' w' - L.localIntegralForm 2 w w := by
  classical
  -- Once the ranks agree, compare Gram matrices in base-changed bases of the same size.
  have key (hn : finrank ℤ L = finrank ℤ M) :
      (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) ↔ (L.IsEven ↔ M.IsEven) ∧
        IsSquare ((L.determinant : ℤ_[2]) * (M.determinant : ℤ_[2])) ∧
        (8 : ℤ_[2]) ∣ M.localIntegralForm 2 w' w' - L.localIntegralForm 2 w w := by
    let b := Module.finBasis ℤ L
    let c := (Module.finBasis ℤ M).reindex (finCongr hn.symm)
    have hdetL := L.det_toMatrix_localIntegralForm 2 b
    have hdetM := M.det_toMatrix_localIntegralForm 2 c
    rw [isEven_iff_forall_two_dvd_localIntegralForm_apply_self,
      isEven_iff_forall_two_dvd_localIntegralForm_apply_self, ← hdetL, ← hdetM]
    have hLsymm := L.isSymm_localIntegralForm 2
    exact hLsymm.equivalent_iff_two_dvd_iff_and_isSquare_det_mul_det_and_eight_dvd
      (M.isSymm_localIntegralForm 2) (b.baseChange ℤ_[2]) (c.baseChange ℤ_[2])
      (hdetL.symm ▸ hL) (hdetM.symm ▸ hM) hw hw'
  refine ⟨fun h ↦ ?_, fun ⟨hn, h⟩ ↦ (key hn).mpr h⟩
  have hn := (L.localIntegralForm_equivalent_imp M 2 h).1
  exact ⟨hn, (key hn).mp h⟩

/-- **Classification of localizations unimodular at `2`, with integral characteristic vectors.**
If `w` and `w'` are characteristic vectors of `L` and `M`, whose determinants are units at `2`, then
the dyadic localizations are integrally isometric exactly when the ranks agree, `L` is even if and
only if `M` is, the product of the determinants is a square in `ℤ_[2]`, and the norms of `w` and
`w'` agree modulo `8`. -/
theorem localIntegralForm_two_equivalent_iff_of_isCharacteristicVector (L : IntegralLattice V)
    (M : IntegralLattice W) (hL : IsUnit (L.determinant : ℤ_[2]))
    (hM : IsUnit (M.determinant : ℤ_[2])) {w : L} {w' : M} (hw : L.IsCharacteristicVector w)
    (hw' : M.IsCharacteristicVector w') :
    (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) ↔
      finrank ℤ L = finrank ℤ M ∧ (L.IsEven ↔ M.IsEven) ∧
        IsSquare ((L.determinant : ℤ_[2]) * (M.determinant : ℤ_[2])) ∧
        L.integralNorm w ≡ M.integralNorm w' [ZMOD 8] := by
  -- `8 = 2 ^ 3` divides an integer in `ℤ_[2]` exactly when it divides it in `ℤ`.
  have h8 := PadicInt.pow_p_dvd_int_iff (p := 2) 3 (M.integralForm w' w' - L.integralForm w w)
  norm_num at h8
  rw [L.localIntegralForm_two_equivalent_iff M hL hM hw.isCharacteristic_localIntegralForm
    hw'.isCharacteristic_localIntegralForm, Int.modEq_iff_dvd, L.integralNorm_apply,
    M.integralNorm_apply, ← h8]
  simp only [localIntegralForm_tmul, one_mul]

/-- **Classification of even localizations unimodular at `2`.** Even lattices whose determinants
are units at `2` have integrally isometric dyadic localizations exactly when their ranks agree and
the product of their determinants is a square in `ℤ_[2]`. The lattices need not be globally
unimodular. -/
theorem localIntegralForm_two_equivalent_iff_of_isEven (L : IntegralLattice V)
    (M : IntegralLattice W) (hLeven : L.IsEven) (hMeven : M.IsEven)
    (hL : IsUnit (L.determinant : ℤ_[2])) (hM : IsUnit (M.determinant : ℤ_[2])) :
    (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) ↔
      finrank ℤ L = finrank ℤ M ∧
        IsSquare ((L.determinant : ℤ_[2]) * (M.determinant : ℤ_[2])) := by
  -- For even lattices `0` is characteristic, so the oddities agree automatically.
  rw [L.localIntegralForm_two_equivalent_iff M hL hM
    (LinearMap.BilinForm.isCharacteristic_zero_iff.mpr hLeven.two_dvd_localIntegralForm_apply_self)
    (LinearMap.BilinForm.isCharacteristic_zero_iff.mpr hMeven.two_dvd_localIntegralForm_apply_self)]
  simp [hLeven, hMeven]

end TauCeti.IntegralLattice

end

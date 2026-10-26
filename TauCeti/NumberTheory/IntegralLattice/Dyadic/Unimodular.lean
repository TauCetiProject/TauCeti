/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.LocalRing
public import TauCeti.NumberTheory.IntegralLattice.Localization.Ideals
public import TauCeti.NumberTheory.IntegralLattice.Localization.Unimodular
import TauCeti.LinearAlgebra.BilinearForm.Even.Henselian
import TauCeti.LinearAlgebra.BilinearForm.Even.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Henselian.Basic

/-!
# Even lattices unimodular at `2`

An even integral lattice whose determinant is a unit at `2` has an even unimodular localization.
It therefore splits off a rank-two perfect summand orthogonally. Over `ℤ_[2]`, whose residue field
has two elements and in which `-3` is not a square, the classification of even unimodular forms
(`LinearMap.BilinForm.IsSymm.equivalent_iff_isSquare_det_mul_det_of_even`) then shows that such
localizations are classified by their rank and determinant square class, as at odd primes
(`TauCeti.IntegralLattice.localIntegralForm_equivalent_iff`). Evenness cannot be dropped: the odd
lattices `⟨1, 1⟩` and `⟨3, 3⟩` have the same rank and square determinants, but only the first
represents `1` over `ℤ_[2]`.

## Main results

* `TauCeti.IntegralLattice.IsEven.two_dvd_localIntegralForm_apply_self`: the dyadic localization
  of an even lattice is even.
* `TauCeti.IntegralLattice.IsEven.even_finrank_of_isUnit_determinant`: an even lattice of odd
  determinant has even rank.
* `TauCeti.IntegralLattice.exists_binary_isPerfPair_isCompl_orthogonal_localIntegralForm`: an even
  lattice unimodular at `2` splits off a perfect binary summand after localization.
* `TauCeti.IntegralLattice.localIntegralForm_two_equivalent_iff_of_isEven`: even lattices with
  determinants that are units at `2` have isometric dyadic localizations exactly when their ranks
  and determinant square classes agree.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Chapter IX.
-/

public section

namespace TauCeti.IntegralLattice

open Module

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- **The dyadic localization of an even lattice is even.** Every value `B(x, x)` of the localized
integral form of an even lattice at `2` is divisible by `2` in `ℤ_[2]`. -/
theorem IsEven.two_dvd_localIntegralForm_apply_self {L : IntegralLattice V} (heven : L.IsEven)
    (x : L.LocalCarrier 2) : (2 : ℤ_[2]) ∣ L.localIntegralForm 2 x x := by
  rw [← Ideal.mem_span_singleton]
  exact (L.isEven_iff_localNormIdeal_le_span_two.mp heven)
    ((L.localIntegralForm 2).self_mem_normIdeal x)

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
  classical
  refine ⟨L.localIntegralForm_equivalent_imp M 2, fun ⟨hn, hsq⟩ ↦ ?_⟩
  -- `-3` is not a square in `ℤ_[2]`, since it is not a square modulo `8`.
  have h3 : ¬ IsSquare (-3 : ℤ_[2]) := by
    rintro ⟨x, hx⟩
    have h8 := congrArg (PadicInt.toZModPow 3) hx
    rw [map_mul, map_neg, map_ofNat] at h8
    revert h8
    generalize PadicInt.toZModPow 3 x = y
    revert y
    decide
  let b := Module.finBasis ℤ L
  let c := (Module.finBasis ℤ M).reindex (finCongr hn.symm)
  have hdetL := L.det_toMatrix_localIntegralForm 2 b
  have hdetM := M.det_toMatrix_localIntegralForm 2 c
  refine ((L.isSymm_localIntegralForm 2).equivalent_iff_isSquare_det_mul_det_of_even
    (PadicInt.card_residueField 2) h3 (M.isSymm_localIntegralForm 2)
    hLeven.two_dvd_localIntegralForm_apply_self hMeven.two_dvd_localIntegralForm_apply_self
    (b.baseChange ℤ_[2]) (c.baseChange ℤ_[2]) (hdetL.symm ▸ hL) (hdetM.symm ▸ hM)).mpr ?_
  rwa [hdetL, hdetM]

end TauCeti.IntegralLattice

end

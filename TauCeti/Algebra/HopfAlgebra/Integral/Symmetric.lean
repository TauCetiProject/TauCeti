/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Symmetric
public import TauCeti.Algebra.HopfAlgebra.Antipode
public import TauCeti.Algebra.HopfAlgebra.Integral.Modular

/-!
# Symmetric finite-dimensional Hopf algebras

A finite-dimensional Hopf algebra over a field is symmetric if and only if it is unimodular and
the square of its antipode is inner. The proof uses a nonzero right cointegral as a Frobenius
functional and identifies its inverse Nakayama automorphism with the square of the antipode in
the unimodular case.

## References

* K. Erdmann, Ø. Solberg and X. Wang, *On the structure and cohomology ring of connected Hopf
  algebras*, J. Algebra 527 (2019), 366–398, arXiv:1710.11558, Theorem 2.2(c).
-/

public section

open Coalgebra HopfAlgebra

namespace TauCeti.HopfAlgebra

variable {k H : Type*} [Field k] [Ring H] [HopfAlgebra k H] [FiniteDimensional k H]

/-- A finite-dimensional Hopf algebra is symmetric if and only if it is unimodular and the
square of its antipode is inner. -/
theorem symmetric_iff_unimodular_and_antipodeSquare_inner :
    IsSymmetricFrobenius k H ↔ IsUnimodular k H ∧ AntipodeSquareIsInner k H := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero k H
  have hi := LinearMap.isRightInvariantIntegral_iff_isRightCointegral.mpr hφ
  have hF := hi.isFrobeniusFunctional h0
  constructor
  · intro hsym
    obtain ⟨ψ, hψ⟩ := isSymmetricFrobenius_iff k H |>.mp hsym
    obtain ⟨⟨t, ht⟩, htψ, -⟩ := hψ.isFrobeniusFunctional.existsUnique_leftIntegral_apply_eq_one
    have hα : modularCharacter k H = counit := by
      ext h
      rw [← hψ.isFrobeniusFunctional.apply_mul_eq_modularCharacter ht htψ,
        hψ.apply_mul_comm, mem_leftIntegral_iff.mp ht, map_smul, htψ, smul_eq_mul, mul_one]
    have hu : IsUnimodular k H := isUnimodular_iff_modularCharacter_eq_counit.mpr hα
    refine ⟨hu, (antipodeSquareIsInner_iff k H).mpr ?_⟩
    obtain ⟨u, hu'⟩ := hF.isSymmetricFrobenius_iff_nakayamaAut_symm_eq_conj.mp hsym
    exact ⟨u, fun x => (hi.nakayamaAut_symm_eq_antipode_antipode h0 hu x).symm.trans (hu' x)⟩
  · rintro ⟨hu, hinner⟩
    apply hF.isSymmetricFrobenius_iff_nakayamaAut_symm_eq_conj.mpr
    obtain ⟨u, hu'⟩ := (antipodeSquareIsInner_iff k H).mp hinner
    exact ⟨u, fun x => (hi.nakayamaAut_symm_eq_antipode_antipode h0 hu x).trans (hu' x)⟩

end TauCeti.HopfAlgebra

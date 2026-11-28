/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.Basic
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Integral points of norm one in CM number fields

The algebraic integers of norm one from a CM number field to its maximal real subfield are
exactly the roots of unity. Thus triviality of an infinity type or a residue character on
integral points of the norm-one torus can be tested on the roots of unity.

This is Kronecker's theorem applied after transporting CM conjugation through each complex
embedding. The application to cyclotomic CM fields is the step
`New.Data.exists_zeta_pow_eq_of_isIntegral` in lsernau/grh-lean,
`grh/src/New/Derivatives/Field/ChosenPlaces.lean` (`72fead1`).
-/

public section

namespace NumberField.IsCMField

/-- An element of a CM number field is a root of unity if and only if it is integral and
its product with its complex conjugate is one. -/
theorem isOfFinOrder_iff_isIntegral_and_mul_complexConj_eq_one
    {K : Type*} [Field K] [NumberField K] [IsCMField K] {x : K} :
    IsOfFinOrder x ↔ IsIntegral ℤ x ∧ x * complexConj K x = 1 := by
  constructor
  · intro hx
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hx
    exact ⟨hx.isIntegral, mul_complexConj_eq_one_of_pow_eq hn.ne' hpow (by simp)⟩
  · rintro ⟨hInt, hNorm⟩
    have habs (φ : K →+* ℂ) : ‖φ x‖ = 1 := by
      have h := congrArg φ hNorm
      rw [map_mul, complexEmbedding_complexConj, map_one, Complex.mul_conj] at h
      have hsq : Complex.normSq (φ x) = 1 :=
        Complex.ofReal_injective (h.trans Complex.ofReal_one.symm)
      rw [Complex.normSq_eq_norm_sq] at hsq
      nlinarith [norm_nonneg (φ x)]
    obtain ⟨n, hn, hpow⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ hInt habs
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow⟩

end NumberField.IsCMField

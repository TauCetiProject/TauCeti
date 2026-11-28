/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.RamificationInertia.Inertia
import TauCeti.FieldTheory.Galois.Basic
import TauCeti.FieldTheory.Galois.Restriction
import TauCeti.NumberTheory.NumberField.Frobenius.Restriction
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Frobenius on an imaginary quadratic subfield

At a prime of residue degree two in an imaginary quadratic field, Frobenius acts by complex
conjugation. This also identifies the restriction of odd powers of Frobenius from a larger field.
-/

public section

open scoped NumberField
open NumberField NumberField.IsCMField

namespace IsArithFrobAt

/-- At a prime whose contraction to an imaginary quadratic subfield has residue degree two
over `ℤ`, odd powers of arithmetic Frobenius restrict to complex conjugation on that subfield. -/
theorem restrictNormal_pow_eq_complexConj {K E : Type*} [Field K] [CharZero K] [IsCMField K]
    [Algebra.IsQuadraticExtension ℚ K] [Field E] [CharZero E] [Algebra K E] [IsScalarTower ℚ K E]
    {Q : Ideal (𝓞 E)} [Q.IsPrime] {φ : E ≃ₐ[ℚ] E} (hφ : IsArithFrobAt ℤ φ Q)
    (hf : (Q.under (𝓞 K)).inertiaDeg ℤ = 2) {n : ℕ} (hn : Odd n) :
    (φ ^ n).restrictNormal K = (complexConj K).restrictScalars ℚ := by
  have : NumberField K := ⟨⟩
  have hφK := (Ideal.isArithFrobAt_ringOfIntegers_rat_iff (φ.restrictNormal K) (Q.under (𝓞 K))).mp
    ((Ideal.isArithFrobAt_ringOfIntegers_rat_iff φ Q).mpr hφ).restrictNormal
  have hdiv := Ideal.inertiaDeg_dvd_orderOf (Q.under (𝓞 K)) hφK
  rw [hf] at hdiv
  have hc : (complexConj K).restrictScalars ℚ ≠ 1 := fun h ↦
    complexConj_ne_one K (AlgEquiv.restrictScalars_injective ℚ h)
  refine (Algebra.IsQuadraticExtension.algEquiv_eq_one_or_eq ℚ K hc _).resolve_left ?_
  intro h
  rw [← AlgEquiv.restrictNormalHom_apply_eq_restrictNormal ℚ K E, map_pow,
    AlgEquiv.restrictNormalHom_apply_eq_restrictNormal] at h
  exact hn.not_two_dvd_nat (hdiv.trans (orderOf_dvd_iff_pow_eq_one.mpr h))

end IsArithFrobAt

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation

/-!
# Rescaling Weierstrass factors

This file shares the algebraic normalization arguments used by disc and entire preparation.
Over an ultrametric normed commutative ring, a polynomial with unit leading coefficient
can be made monic by rescaling its restricted-unit cofactor. Conversely, if the product
has constant coefficient one, a monic preparation can be rescaled so that both factors have
constant coefficient one. Comparison and uniqueness use monic Weierstrass uniqueness.
No entire-convergence or completeness hypothesis is needed for these rescalings.

The construction is extracted from the normalized entire preparation development,
following R. F. Coleman, *p-adic Banach spaces and families of modular forms*, Appendix A3.
-/

public section

namespace TauCeti.PowerSeries

open _root_.PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : ℝ} {d : ℕ}
  {f : R⟦X⟧} {P P' ω : Polynomial R} {U U' e : IsRestricted.subring (R := R) c}

/-- Move an invertible leading coefficient from a polynomial to its restricted-unit factor. -/
private theorem exists_monic_of_isUnit_leadingCoeff (ha : IsUnit P.leadingCoeff)
    (hd : P.natDegree = d) (hU : IsUnit U) (hf : f = (P : R⟦X⟧) * (U : R⟦X⟧)) :
    ∃ e : IsRestricted.subring (R := R) c, IsUnit e ∧
      (ha.unit⁻¹ • P).IsMonicOfDegree d ∧ (e : R⟦X⟧) = P.leadingCoeff • (U : R⟦X⟧) ∧
      (e : R⟦X⟧) * ((ha.unit⁻¹ • P : Polynomial R) : R⟦X⟧) = f := by
  set u := ha.unit
  have hu : (u : R) = P.leadingCoeff := ha.unit_spec
  refine ⟨algebraMap R _ u * U, (u.isUnit.map (algebraMap R _)).mul hU,
    ⟨by rw [Polynomial.natDegree_smul_of_smul_regular P (IsSMulRegular.all _), hd],
      Polynomial.monic_of_isUnit_leadingCoeff_inv_smul ha⟩, ?_, ?_⟩
  · rw [Subring.coe_mul, coe_algebraMap_isRestrictedSubring, Algebra.algebraMap_self_apply,
      hu, smul_eq_C_mul]
  · rw [Subring.coe_mul, coe_algebraMap_isRestrictedSubring, Algebra.algebraMap_self_apply,
      ← smul_eq_C_mul, Units.smul_def, Polynomial.coe_smul,
      smul_mul_smul_comm, u.mul_inv, one_smul, mul_comm]
    exact hf.symm

/-- A polynomial-times-restricted-unit factorization of the distinguished degree rescales
any monic preparation, provided its leading coefficient is a unit. -/
theorem IsMulDistinguished.eq_smul_and_smul_eq (hf : IsMulDistinguished c d f)
    (hc : 0 < c) (ha : IsUnit P.leadingCoeff) (hd : P.natDegree = d) (hU : IsUnit U)
    (hPU : f = (P : R⟦X⟧) * (U : R⟦X⟧)) (he : IsUnit e) (hω : ω.IsMonicOfDegree d)
    (heω : (e : R⟦X⟧) * (ω : R⟦X⟧) = f) :
    P = P.leadingCoeff • ω ∧ P.leadingCoeff • (U : R⟦X⟧) = (e : R⟦X⟧) := by
  obtain ⟨e', he', hω', he'U, he'P⟩ := exists_monic_of_isUnit_leadingCoeff ha hd hU hPU
  obtain ⟨rfl, rfl⟩ := hf.eq_and_eq_of_mul_eq_of_mul_eq hc he' he hω' hω he'P heω
  refine ⟨?_, he'U.symm⟩
  rw [Units.smul_def, smul_smul, ha.mul_val_inv, one_smul]

/-- Polynomial-times-restricted-unit preparations with constant-one polynomial factors
and invertible leading coefficients are unique at the distinguished degree. -/
theorem IsMulDistinguished.eq_and_eq_of_normalized_mul_eq (hf : IsMulDistinguished c d f)
    (hc : 0 < c) (ha : IsUnit P.leadingCoeff) (ha' : IsUnit P'.leadingCoeff)
    (hd : P.natDegree = d) (hd' : P'.natDegree = d)
    (hP0 : P.coeff 0 = 1) (hP0' : P'.coeff 0 = 1) (hU : IsUnit U) (hU' : IsUnit U')
    (hPU : f = (P : R⟦X⟧) * (U : R⟦X⟧)) (hPU' : f = (P' : R⟦X⟧) * (U' : R⟦X⟧)) :
    P = P' ∧ U = U' := by
  obtain ⟨e', he', hω', he'U, he'P⟩ := exists_monic_of_isUnit_leadingCoeff ha' hd' hU' hPU'
  obtain ⟨hP, hG⟩ := hf.eq_smul_and_smul_eq hc ha hd hU hPU he' hω' he'P
  set ω := ha'.unit⁻¹ • P' with hω
  -- The constant coefficient of the common monic polynomial is inverse to both leading
  -- coefficients, so the two rescaling constants agree even over a ring with zero divisors.
  have h1 : P.leadingCoeff * ω.coeff 0 = 1 := by
    rw [← smul_eq_mul, ← Polynomial.coeff_smul, ← hP, hP0]
  have h2 : P'.leadingCoeff * ω.coeff 0 = 1 := by
    rw [hω, Units.smul_def, Polynomial.coeff_smul, smul_eq_mul, ← mul_assoc,
      ha'.mul_val_inv, one_mul, hP0']
  have heq : P.leadingCoeff = P'.leadingCoeff :=
    calc P.leadingCoeff = P.leadingCoeff * (P'.leadingCoeff * ω.coeff 0) := by rw [h2, mul_one]
      _ = P'.leadingCoeff * (P.leadingCoeff * ω.coeff 0) := by ring
      _ = P'.leadingCoeff := by rw [h1, mul_one]
  refine ⟨?_, Subtype.ext ?_⟩
  · rw [hP, heq, hω, Units.smul_def, smul_smul, ha'.mul_val_inv, one_smul]
  · rw [he'U, ← heq] at hG
    exact ha.smul_left_cancel.mp hG

/-- Rescale monic restricted-unit factors of a constant-one series so that both factors
have constant coefficient one. The resulting cofactor is explicitly a scalar multiple of
the original, allowing additional convergence properties to be transported by callers. -/
theorem exists_normalized_factors_of_mul_eq (he : IsUnit e) (hω : ω.IsMonicOfDegree d)
    (heω : (e : R⟦X⟧) * (ω : R⟦X⟧) = f) (hf0 : constantCoeff f = 1) :
    ∃ (a : Rˣ) (U : IsRestricted.subring (R := R) c),
      (a • ω).coeff 0 = 1 ∧ (a • ω).natDegree = d ∧ IsUnit (a • ω).leadingCoeff ∧
      constantCoeff (U : R⟦X⟧) = 1 ∧ IsUnit U ∧
      f = ((a • ω : Polynomial R) : R⟦X⟧) * (U : R⟦X⟧) ∧
      (U : R⟦X⟧) = ((a⁻¹ : Rˣ) : R) • (e : R⟦X⟧) := by
  have h0 : constantCoeff (e : R⟦X⟧) * ω.coeff 0 = 1 := by
    rw [← hf0, ← heω, map_mul, ← Polynomial.coeff_coe, coeff_zero_eq_constantCoeff_apply]
  let a : Rˣ := ⟨constantCoeff (e : R⟦X⟧), ω.coeff 0, h0, by rw [mul_comm]; exact h0⟩
  let U : IsRestricted.subring (R := R) c := algebraMap R _ (a⁻¹ : Rˣ) * e
  have hU : (U : R⟦X⟧) = ((a⁻¹ : Rˣ) : R) • (e : R⟦X⟧) := by
    rw [Subring.coe_mul, coe_algebraMap_isRestrictedSubring, Algebra.algebraMap_self_apply,
      smul_eq_C_mul]
  refine ⟨a, U, ?_, ?_, ?_, ?_, ((a⁻¹).isUnit.map (algebraMap R _)).mul he, ?_, hU⟩
  · rw [Units.smul_def, Polynomial.coeff_smul, smul_eq_mul]; exact h0
  · rw [Polynomial.natDegree_smul_of_smul_regular ω (IsSMulRegular.all _), hω.natDegree_eq]
  · rw [Polynomial.leadingCoeff_smul_of_smul_regular ω (IsSMulRegular.all _),
      hω.leadingCoeff_eq, Units.smul_def, smul_eq_mul, mul_one]
    exact a.isUnit
  · rw [hU, smul_eq_C_mul, map_mul, constantCoeff_C, mul_comm]
    exact a.mul_inv
  · rw [hU, Units.smul_def, Polynomial.coe_smul, smul_mul_smul_comm, a.mul_inv,
      one_smul, mul_comm, heω]

end TauCeti.PowerSeries

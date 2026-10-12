/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Discriminants of products of nonmonic polynomials

The discriminant of a product of two positive-degree polynomials over a domain is the
product of their discriminants and the square of their resultant. Unlike the monic
product law, this applies to primitive polynomials over polynomial coefficient rings,
where leading coefficients need not be units.

Positive degrees are essential with the convention `Polynomial.discr_C = 1`: multiplying
by a constant instead obeys the scaling law `TauCeti.discr_C_mul`.

This extends `Polynomial.Monic.discr_mul` and supplies the discriminant identity for
products of primitive basis members in McCallum projection, where the coefficient ring
is a multivariate polynomial ring.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), Section 2 (discriminants and resultants of a polynomial basis).
-/

public section

universe u

namespace Polynomial

/-- The discriminant product law for positive-degree polynomials over an integral domain.
No monicity, separability, or characteristic assumption is required. -/
theorem discr_mul_of_natDegree_pos {R : Type u} [CommRing R] [IsDomain R]
    (f g : R[X]) (hf : 0 < f.natDegree) (hg : 0 < g.natDegree) :
    (f * g).discr = f.discr * g.discr * (f.resultant g) ^ 2 := by
  -- Normalize over a field, where both leading coefficients can be inverted.
  have field_case {K : Type u} [Field K] (f g : K[X])
      (hf : 0 < f.natDegree) (hg : 0 < g.natDegree) :
      (f * g).discr = f.discr * g.discr * (f.resultant g) ^ 2 := by
    have hf0 : f ≠ 0 := by rintro rfl; simp at hf
    have hg0 : g ≠ 0 := by rintro rfl; simp at hg
    let a := f.leadingCoeff
    let b := g.leadingCoeff
    have ha : a ≠ 0 := leadingCoeff_ne_zero.mpr hf0
    have hb : b ≠ 0 := leadingCoeff_ne_zero.mpr hg0
    let p := f * C a⁻¹
    let q := g * C b⁻¹
    have hp : p.Monic := monic_mul_leadingCoeff_inv hf0
    have hq : q.Monic := monic_mul_leadingCoeff_inv hg0
    have hfp : f = C a * p := by simp [p, mul_left_comm, ← C_mul, ha]
    have hgq : g = C b * q := by simp [q, mul_left_comm, ← C_mul, hb]
    have hpd : p.natDegree = f.natDegree := natDegree_mul_C (inv_ne_zero ha)
    have hqd : q.natDegree = g.natDegree := natDegree_mul_C (inv_ne_zero hb)
    have hprod : f * g = C (a * b) * (p * q) := by rw [hfp, hgq, C_mul]; ring
    have hexpa : 2 * (p.natDegree + q.natDegree) - 2 =
        (2 * p.natDegree - 2) + 2 * q.natDegree := by omega
    have hexpb : 2 * (p.natDegree + q.natDegree) - 2 =
        (2 * q.natDegree - 2) + 2 * p.natDegree := by omega
    rw [hprod, TauCeti.discr_C_mul _ (mul_ne_zero ha hb), hp.natDegree_mul hq,
      hp.discr_mul hq]
    conv_rhs => rw [hfp, hgq]
    rw [TauCeti.discr_C_mul _ ha, TauCeti.discr_C_mul _ hb,
      natDegree_C_mul ha, natDegree_C_mul hb,
      resultant_C_mul_left, resultant_C_mul_right]
    simp only [mul_pow]
    conv_lhs => arg 1; arg 1; rw [hexpa, pow_add]
    conv_lhs => arg 1; arg 2; rw [hexpb, pow_add]
    simp only [← pow_mul]
    ring
  -- The fraction-field embedding preserves degrees, discriminants, and resultants.
  let φ := algebraMap R (FractionRing R)
  have hφ : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  apply hφ
  have h := field_case (f.map φ) (g.map φ)
    (by simpa only [natDegree_map_eq_of_injective hφ] using hf)
    (by simpa only [natDegree_map_eq_of_injective hφ] using hg)
  simpa only [← Polynomial.map_mul, discr_map_of_natDegree_eq φ
    (natDegree_map_eq_of_injective hφ _), resultant_map_map,
    natDegree_map_eq_of_injective hφ, map_mul, map_pow] using h

end Polynomial

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.IsConjRoot
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.FieldTheory.IntermediateField.Adjoin.Inv

/-!
# Minimal polynomials of inverses and reciprocal algebraic numbers

The minimal polynomial of the inverse of a nonzero element `x` is the reverse
`P* = X ^ d P(1 / X)` of the minimal polynomial `P` of `x`, divided by its constant coefficient
`P(0)`.

Over an integrally closed domain `R` with fraction field `K`, an integral element `x ≠ 0` is
conjugate over `K` to its inverse exactly when its minimal polynomial `P` over `R` is reciprocal up
to sign: `P* = P` or `P* = -P`. Then `P(0) = ±1`, the inverse `x⁻¹` is again integral over `R`,
and the roots of `P` in any field are closed under inversion. The sign `P* = -P` only occurs for
`P = X - 1`, as soon as `2 ≠ 0` in `R`.

For `R = ℤ` and `K = ℚ` this describes the reciprocal algebraic integers: the conjugates of a
Salem number are closed under inversion, while Smyth's lower bound for the Mahler measure concerns
the nonreciprocal algebraic integers.

## Main results

* `TauCeti.minpoly.inv`: `minpoly K x⁻¹ = C (P(0))⁻¹ * P*` for `x ≠ 0`, where `P = minpoly K x`.
* `TauCeti.isConjRoot_inv_iff_reverse_minpoly_eq_or_eq_neg`: over an integrally closed domain
  `R` with fraction field `K`, an integral `x ≠ 0` is conjugate over `K` to `x⁻¹` exactly when
  `P* = P` or `P* = -P`, where `P = minpoly R x`.
* `IsConjRoot.isIntegral_of_isIntegrallyClosed`: a conjugate over `K` of an element integral over
  `R` is integral over `R`; in particular a reciprocal algebraic integer is a unit.
* `IsConjRoot.coeff_zero_minpoly_eq_one_or_eq_neg_one`: a reciprocal integral `x ≠ 0` has
  `P(0) = ±1`.
* `IsConjRoot.inv_mem_aroots_minpoly`: the roots of the minimal polynomial of a reciprocal
  integral element are closed under inversion.
* `TauCeti.minpoly.reverse_eq_neg_iff`: `P* = -P` exactly when `P = X - 1`, provided `2 ≠ 0`.

## References

* C. Smyth, *The Mahler measure of algebraic numbers: a survey* (2008), §5.1.
-/

public section

open Polynomial

namespace TauCeti

namespace minpoly

/-- The minimal polynomial of the inverse of a nonzero element `x` is the reverse of the minimal
polynomial of `x`, divided by its constant coefficient. When `x` is not algebraic, both sides
vanish. -/
theorem inv {K L : Type*} [Field K] [Field L] [Algebra K L] {x : L} (hx : x ≠ 0) :
    minpoly K x⁻¹ = C ((minpoly K x).coeff 0)⁻¹ * (minpoly K x).reverse := by
  by_cases hint : IsIntegral K x
  swap
  · have hint' : ¬IsIntegral K x⁻¹ := fun h ↦ hint (by simpa using h.inv)
    simp [_root_.minpoly.eq_zero hint, _root_.minpoly.eq_zero hint']
  have h0 := _root_.minpoly.coeff_zero_ne_zero hint hx
  have hmonic : (C ((minpoly K x).coeff 0)⁻¹ * (minpoly K x).reverse).Monic := by
    rw [Monic, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff,
      trailingCoeff_eq_coeff_zero h0, inv_mul_cancel₀ h0]
  have hroot : aeval x⁻¹ (minpoly K x).reverse = 0 := by
    rw [aeval_def, eval₂_inv_reverse_eq_zero_iff _ _ hx, ← aeval_def, _root_.minpoly.aeval]
  refine (eq_of_monic_of_dvd_of_natDegree_le (_root_.minpoly.monic hint.inv) hmonic
    (_root_.minpoly.dvd K _ (by rw [map_mul, hroot, mul_zero])) ?_).symm
  rw [natDegree_C_mul (inv_ne_zero h0), reverse_natDegree,
    natTrailingDegree_eq_zero.mpr (.inr h0), Nat.sub_zero, natDegree_inv]

/-- If `2 ≠ 0` in the domain `R`, the minimal polynomial `P` of an integral element of a domain
satisfies `P* = -P` only for `P = X - 1`. Over `ZMod 2` the reciprocal minimal polynomial
`X ^ 2 + X + 1` is a counterexample. -/
theorem reverse_eq_neg_iff {R L : Type*} [CommRing R] [IsDomain R] [CommRing L] [IsDomain L]
    [Algebra R L] {x : L} (hx : IsIntegral R x) (h2 : (2 : R) ≠ 0) :
    (minpoly R x).reverse = -minpoly R x ↔ minpoly R x = X - 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- `P(1) = P*(1) = -P(1)`, so `X - 1` is a monic factor of the irreducible `P`.
    have h1 : (minpoly R x).IsRoot 1 := by
      have h1 := congrArg (eval 1) h
      rw [eval_one_reverse, eval_neg, eq_neg_iff_add_eq_zero, ← two_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_left h2
    have hq := (mul_divByMonic_eq_iff_isRoot.mpr h1).symm
    have hqm : (minpoly R x /ₘ (X - C 1)).Monic :=
      (monic_X_sub_C 1).of_mul_monic_left (hq ▸ _root_.minpoly.monic hx)
    obtain hu | hu := (_root_.minpoly.irreducible hx).isUnit_or_isUnit hq
    · exact absurd hu (not_isUnit_X_sub_C 1)
    · rw [hq, hqm.isUnit_iff.mp hu, mul_one, C_1]
  · rw [h, show (X - 1 : R[X]) = X ^ 1 - C 1 by simp, reverse_X_pow_sub_C, C_1]
    ring

end minpoly

section IsIntegrallyClosed

variable {R K L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] {x : L}

/-- Over an integrally closed domain `R` with fraction field `K`, a conjugate over `K` of an
element integral over `R` is again integral over `R`. -/
theorem _root_.IsConjRoot.isIntegral_of_isIntegrallyClosed {y : L} (h : IsConjRoot K x y)
    (hx : IsIntegral R x) : IsIntegral R y := by
  refine ⟨minpoly R x, minpoly.monic hx, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap K, ← minpoly.isIntegrallyClosed_eq_field_fractions' K hx]
  exact h.aeval_eq_zero

/-- Over an integrally closed domain `R` with fraction field `K`, a nonzero element `x` integral
over `R` is conjugate over `K` to `x⁻¹` exactly when its minimal polynomial `P` over `R` is
reciprocal up to sign: `P* = P` or `P* = -P`, where `P*` is the reverse of `P`. -/
theorem isConjRoot_inv_iff_reverse_minpoly_eq_or_eq_neg (hx : IsIntegral R x) (hx0 : x ≠ 0) :
    IsConjRoot K x x⁻¹ ↔
      (minpoly R x).reverse = minpoly R x ∨ (minpoly R x).reverse = -minpoly R x := by
  have hP := minpoly.monic hx
  have h0 := minpoly.coeff_zero_ne_zero (hx.tower_top (A := K)) hx0
  -- Over a field, `P = C c⁻¹ * P*` and `P* = C c * P` are equivalent for `c ≠ 0`.
  have key (P : K[X]) {c : K} (hc : c ≠ 0) : P = C c⁻¹ * P.reverse ↔ P.reverse = C c * P := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · conv_rhs => rw [h]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
    · rw [h, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
  rw [isConjRoot_def, TauCeti.minpoly.inv hx0, key _ h0,
    minpoly.isIntegrallyClosed_eq_field_fractions' K hx, coeff_map,
    reverse_map_of_isUnit_leadingCoeff (by rw [hP.leadingCoeff]; exact isUnit_one), ← map_C,
    ← Polynomial.map_mul, (map_injective _ (IsFractionRing.injective R K)).eq_iff,
    hP.reverse_eq_C_coeff_zero_mul_iff]

/-- If a nonzero element `x` integral over an integrally closed domain `R` is conjugate to `x⁻¹`
over the fraction field, then the constant coefficient of its minimal polynomial over `R` is
`1` or `-1`. -/
theorem _root_.IsConjRoot.coeff_zero_minpoly_eq_one_or_eq_neg_one (h : IsConjRoot K x x⁻¹)
    (hx : IsIntegral R x) (hx0 : x ≠ 0) :
    (minpoly R x).coeff 0 = 1 ∨ (minpoly R x).coeff 0 = -1 := by
  have h1 : (minpoly R x).reverse.coeff 0 = 1 := by
    rw [coeff_zero_reverse, (minpoly.monic hx).leadingCoeff]
  obtain hr | hr := (isConjRoot_inv_iff_reverse_minpoly_eq_or_eq_neg hx hx0).mp h
  · exact .inl (hr ▸ h1)
  · rw [hr, coeff_neg, neg_eq_iff_eq_neg] at h1
    exact .inr h1

/-- If an element `x` integral over an integrally closed domain `R` is conjugate to `x⁻¹` over
the fraction field, then the roots of its minimal polynomial over `R`, in any field, are closed
under inversion. -/
theorem _root_.IsConjRoot.inv_mem_aroots_minpoly {M : Type*} [Field M] [Algebra R M]
    (h : IsConjRoot K x x⁻¹) (hx : IsIntegral R x) {z : M} (hz : z ∈ (minpoly R x).aroots M) :
    z⁻¹ ∈ (minpoly R x).aroots M := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simpa using hz
  rw [mem_aroots'] at hz ⊢
  rcases eq_or_ne x 0 with rfl | hx0
  · -- The minimal polynomial of `0` is `X`, whose only root is `0`.
    have hX : minpoly R (0 : L) = X := map_injective _ (IsFractionRing.injective R K) <| by
      rw [← minpoly.isIntegrallyClosed_eq_field_fractions' K hx, minpoly.zero, Polynomial.map_X]
    rw [hX, aeval_X] at hz
    exact absurd hz.2 hz0
  have hrev : aeval z⁻¹ (minpoly R x).reverse = 0 := by
    rw [aeval_def, eval₂_inv_reverse_eq_zero_iff _ _ hz0, ← aeval_def, hz.2]
  refine ⟨hz.1, ?_⟩
  obtain hr | hr := (isConjRoot_inv_iff_reverse_minpoly_eq_or_eq_neg hx hx0).mp h
  · rwa [hr] at hrev
  · rwa [hr, map_neg, neg_eq_zero] at hrev

end IsIntegrallyClosed

/-! ### Examples -/

/-- `1` is its own inverse, and its minimal polynomial `X - 1` over `ℤ` has reverse
`-(X - 1)`. -/
example : (minpoly ℤ (1 : ℚ)).reverse = -minpoly ℤ (1 : ℚ) := by
  have h : minpoly ℤ (1 : ℚ) = X - 1 := by
    simpa using minpoly.eq_X_sub_C_of_algebraMap_inj 1 (algebraMap ℤ ℚ).injective_int
  exact (TauCeti.minpoly.reverse_eq_neg_iff isIntegral_one two_ne_zero).mpr h

/-- `2` is not conjugate to `1 / 2`: the constant coefficient of its minimal polynomial `X - 2`
over `ℤ` is `-2`. -/
example : ¬IsConjRoot ℚ (2 : ℚ) 2⁻¹ := by
  have h : minpoly ℤ (2 : ℚ) = X - C 2 := by
    simpa using minpoly.eq_X_sub_C_of_algebraMap_inj (2 : ℤ) (algebraMap ℤ ℚ).injective_int
  intro hc
  have := hc.coeff_zero_minpoly_eq_one_or_eq_neg_one (R := ℤ)
    ⟨X - C 2, monic_X_sub_C 2, by simp⟩ two_ne_zero
  rw [h] at this
  simp at this

/-- Lehmer's polynomial is reciprocal. -/
example : (X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 : ℤ[X]).reverse =
    X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 := by
  have hdeg : (X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 : ℤ[X]).natDegree =
      10 := by compute_degree!
  have hX : reflect 10 (X : ℤ[X]) = X ^ 9 := by simpa using reflect_monomial (R := ℤ) 10 1
  rw [reverse, hdeg]
  simp [reflect_add, reflect_sub, revAt_le, hX]
  ring

/-- `X ^ 3 - X - 1` is not reciprocal up to sign: its reverse is `1 - X ^ 2 - X ^ 3`. -/
example : (X ^ 3 - X - 1 : ℤ[X]).reverse = 1 - X ^ 2 - X ^ 3 ∧
    (X ^ 3 - X - 1 : ℤ[X]).reverse ≠ X ^ 3 - X - 1 ∧
    (X ^ 3 - X - 1 : ℤ[X]).reverse ≠ -(X ^ 3 - X - 1) := by
  have hdeg : (X ^ 3 - X - 1 : ℤ[X]).natDegree = 3 := by compute_degree!
  have hrev : (X ^ 3 - X - 1 : ℤ[X]).reverse = 1 - X ^ 2 - X ^ 3 := by
    have hX : reflect 3 (X : ℤ[X]) = X ^ 2 := by simpa using reflect_monomial (R := ℤ) 3 1
    rw [reverse, hdeg]
    simp [reflect_sub, revAt_le, hX]
  refine ⟨hrev, fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [hrev] using congrArg (eval 0) h
  · simpa [hrev] using congrArg (eval 1) h

end TauCeti

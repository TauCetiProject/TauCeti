/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Basic
import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula

/-!
# Hermitian coordinates

Let `q > 1`. Functions `x` and `y` of a field `F ⊇ K` are **Hermitian coordinates** with
parameter `q` when `x` is transcendental over `K`, `F = K(x, y)`, and

`y ^ q + y = x ^ (q + 1)`.

When `q` is a power of the characteristic and `K = 𝔽_{q²}`, `F` is the Hermitian function field
(Stichtenoth, Section 6.4), the standard example of a function field with a large
automorphism group; its translation automorphisms are constructed in
`TauCeti.FieldTheory.FunctionField.Hermitian.Translation`.

This file computes the degree `[F : K(x)] = q`, with no assumption on `K` or on the
characteristic. At a pole `P` of `x` the equation forces a pole of `y`, and comparing orders
gives `q · ord_P y = (q + 1) · ord_P x`. So `q` divides the order of every pole of `x`, hence the
degree of the pole divisor of `x`, which is `[F : K(x)]` (Stichtenoth, Theorem 1.4.11). As `y` is
a root of the monic polynomial `T ^ q + T - x ^ (q + 1)` of degree `q`, the degree is exactly `q`
and this polynomial is the minimal polynomial of `y` over `K(x)`.

## Main definitions

* `TauCeti.IsHermitianCoordinates`: `x` is transcendental, `F = K(x, y)` and
  `y ^ q + y = x ^ (q + 1)`.

## Main results

* `TauCeti.IsHermitianCoordinates.transcendental_y`: `y` is transcendental over `K`.
* `TauCeti.IsHermitianCoordinates.isFunctionField`: `F / K` is an algebraic function field.
* `TauCeti.IsHermitianCoordinates.mul_ord_y_eq`: `q · ord_P y = (q + 1) · ord_P x` at every pole
  `P` of `x`.
* `TauCeti.IsHermitianCoordinates.finrank_adjoin_x`: `[F : K(x)] = q`.
* `TauCeti.IsHermitianCoordinates.minpoly_adjoin_x`: the minimal polynomial of `y` over `K(x)` is
  `T ^ q + T - x ^ (q + 1)`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section 6.4 and Theorem 1.4.11.
-/

public section

open Polynomial
open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **Hermitian coordinates** with parameter `q`: `x` is transcendental over `K`, `x` and `y`
generate `F`, and `y ^ q + y = x ^ (q + 1)`. -/
structure IsHermitianCoordinates (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F]
    (q : ℕ) (x y : F) : Prop where
  /-- `x` is transcendental over `K`. -/
  transcendental_x : Transcendental K x
  /-- `x` and `y` generate `F` over `K`. -/
  adjoin_eq_top : K⟮x, y⟯ = ⊤
  /-- The Hermitian equation. -/
  equation : y ^ q + y = x ^ (q + 1)

namespace IsHermitianCoordinates

variable {q : ℕ} {x y : F} (h : IsHermitianCoordinates K q x y)
include h

/-- The second Hermitian coordinate is transcendental over the constant field. -/
theorem transcendental_y : Transcendental K y := by
  intro hy
  apply h.transcendental_x
  have hx : IsAlgebraic K (x ^ (q + 1)) := h.equation ▸ (hy.pow q).add hy
  exact hx.of_pow (by omega)

/-- `y` generates `F` over `K(x)`. -/
theorem adjoin_adjoin_eq_top : K⟮x⟯⟮y⟯ = ⊤ :=
  IntermediateField.restrictScalars_injective K <| by
    rw [IntermediateField.adjoin_simple_adjoin_simple, h.adjoin_eq_top,
      IntermediateField.restrictScalars_top]

omit h in
/-- The polynomial `T ^ q + T - x ^ (q + 1)` over `K(x)` is monic of degree `q` for `q > 1`. -/
private theorem monic_poly (hq : 1 < q) :
    (X ^ q + X - C (IntermediateField.AdjoinSimple.gen K x ^ (q + 1))).Monic := by
  rw [add_sub_assoc]
  refine monic_X_pow_add ?_
  exact (degree_X_sub_C_le _).trans_lt (by exact_mod_cast hq)

omit h in
private theorem natDegree_poly (hq : 1 < q) :
    (X ^ q + X - C (IntermediateField.AdjoinSimple.gen K x ^ (q + 1))).natDegree = q := by
  rw [add_sub_assoc, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact (degree_X_sub_C_le _).trans_lt (by exact_mod_cast hq)

private theorem aeval_poly :
    aeval y (X ^ q + X - C (IntermediateField.AdjoinSimple.gen K x ^ (q + 1))) = 0 := by
  simp [h.equation]

/-- `y` is integral over `K(x)`. -/
theorem isIntegral_adjoin_x (hq : 1 < q) : IsIntegral K⟮x⟯ y :=
  ⟨_, monic_poly hq, by rw [← aeval_def]; exact h.aeval_poly⟩

/-- `F` is finite over `K(x)`. -/
theorem finiteDimensional_adjoin_x (hq : 1 < q) : FiniteDimensional K⟮x⟯ F := by
  have := IntermediateField.adjoin.finiteDimensional (h.isIntegral_adjoin_x hq)
  rw [h.adjoin_adjoin_eq_top] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

/-- A field with Hermitian coordinates is an algebraic function field. -/
theorem isFunctionField (hq : 1 < q) : IsFunctionField K F :=
  have := h.finiteDimensional_adjoin_x hq
  h.transcendental_x.isFunctionField_adjoin.finite_extension

/-- At a pole `P` of `x`, the function `y` has a pole as well, and
`q · ord_P y = (q + 1) · ord_P x`. -/
theorem mul_ord_y_eq (hq : 1 < q) {P : Place K F} (hP : P.ord x < 0) :
    (q : ℤ) * P.ord y = (q + 1) * P.ord x := by
  have hx0 : x ≠ 0 := h.transcendental_x.ne_zero
  have hrhs : P.ord (y ^ q + y) = (q + 1) * P.ord x := by
    rw [h.equation, P.ord_pow]
    push_cast
    ring
  -- `y` is not regular at `P`, since `y ^ q + y` has a pole there.
  have hy : P.ord y < 0 := by
    by_contra hy
    have hmem : y ^ q + y ∈ P.integers := by
      have hy' : y ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (not_lt.mp hy)
      exact add_mem (pow_mem hy' q) hy'
    have := P.mem_integers_iff_ord_nonneg.mp hmem
    rw [hrhs] at this
    nlinarith
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  have hlt : P.ord (y ^ q) < P.ord y := by
    rw [P.ord_pow]
    have : (1 : ℤ) < q := by exact_mod_cast hq
    nlinarith
  rw [← hrhs, P.ord_add_eq_min_of_ord_ne (pow_ne_zero q hy0) hy0 hlt.ne, min_eq_left hlt.le,
    P.ord_pow]

/-- `q` divides the pole order `max (-ord_P x) 0` of `x` at every place. -/
private theorem dvd_ord_x (hq : 1 < q) (P : Place K F) : (q : ℤ) ∣ -P.ord x ⊔ 0 := by
  by_cases hP : P.ord x < 0
  · rw [max_eq_left (by omega), dvd_neg]
    have hcop : IsCoprime (q : ℤ) (q + 1) := ⟨-1, 1, by ring⟩
    exact hcop.dvd_of_dvd_mul_left ⟨P.ord y, (h.mul_ord_y_eq hq hP).symm⟩
  · rw [max_eq_right (by omega)]
    exact dvd_zero _

/-- **The degree of `x`**: `[F : K(x)] = q`. -/
theorem finrank_adjoin_x (hq : 1 < q) : Module.finrank K⟮x⟯ F = q := by
  classical
  have hF := h.isFunctionField hq
  have := h.finiteDimensional_adjoin_x hq
  have hx0 : x ≠ 0 := h.transcendental_x.ne_zero
  -- The degree of the pole divisor of `x` is `[F : K(x)]`, and every coefficient is divisible
  -- by `q`.
  have hdeg := Divisor.degree_poles hF (Units.mk0 x hx0) h.transcendental_x
  rw [Units.val_mk0] at hdeg
  have hdvd : (q : ℤ) ∣ Module.finrank K⟮x⟯ F := by
    rw [← hdeg, Divisor.degree_apply]
    refine Finset.dvd_sum fun P _ ↦ Dvd.dvd.mul_right ?_ _
    rw [← WeilDivisor.coeff, Divisor.coeff_poles]
    exact h.dvd_ord_x hq P
  have hge : q ≤ Module.finrank K⟮x⟯ F :=
    Nat.le_of_dvd Module.finrank_pos (by exact_mod_cast hdvd)
  -- `y` generates `F` over `K(x)` and is a root of a polynomial of degree `q`.
  have hle : Module.finrank K⟮x⟯ F ≤ q := by
    rw [← IntermediateField.finrank_top', ← h.adjoin_adjoin_eq_top,
      IntermediateField.adjoin.finrank (h.isIntegral_adjoin_x hq),
      ← natDegree_poly (K := K) (x := x) hq]
    exact natDegree_le_of_dvd (minpoly.dvd _ _ h.aeval_poly)
      (monic_poly (K := K) (x := x) hq).ne_zero
  omega

/-- **The minimal polynomial of `y` over `K(x)`** is `T ^ q + T - x ^ (q + 1)`. -/
theorem minpoly_adjoin_x (hq : 1 < q) :
    minpoly K⟮x⟯ y = X ^ q + X - C (IntermediateField.AdjoinSimple.gen K x ^ (q + 1)) := by
  have hint := h.isIntegral_adjoin_x hq
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (monic_poly hq)
    (minpoly.dvd _ _ h.aeval_poly) ?_).symm
  rw [natDegree_poly hq, ← IntermediateField.adjoin.finrank hint, h.adjoin_adjoin_eq_top,
    IntermediateField.finrank_top', h.finrank_adjoin_x hq]

end IsHermitianCoordinates

end TauCeti

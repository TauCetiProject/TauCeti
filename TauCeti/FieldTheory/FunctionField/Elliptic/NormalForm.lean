/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import TauCeti.FieldTheory.FunctionField.Elliptic.WeierstrassEquation

/-!
# Completing the square in a genus-one function field

When two is invertible in the constant field, completing the square puts the Weierstrass
equation supplied by Riemann–Roch in the form `Y² = X³ + a₂X² + a₄X + a₆`.  The coordinate
change preserves the pole orders two and three at the chosen rational place, so the resulting
coordinates still generate the function field.  The change of the Weierstrass curve itself is
Mathlib's `WeierstrassCurve.toCharNeTwoNF`.

This is the characteristic-not-two normal-form part of Stichtenoth, Proposition 6.1.2.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Springer, 2009,
  Proposition 6.1.2.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Springer, 2009,
  Chapter III, Section 1.
-/

public section

namespace TauCeti

open AlgebraicGeometry WeierstrassCurve

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

private theorem completedSquare (a₂ a₄ a₆ c d x y : F) :
    (y + c * x + d) ^ 2 -
        (x ^ 3 + (a₂ + c ^ 2) * x ^ 2 + (a₄ + 2 * c * d) * x + (a₆ + d ^ 2)) =
      y ^ 2 + (2 * c) * x * y + (2 * d) * y -
        (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) := by
  ring

private theorem charNeTwoNFCoefficients (W : WeierstrassCurve k) (h2 : (2 : k) ≠ 0) :
    letI : Invertible (2 : k) := invertibleOfNonzero h2
    let c := W.a₁ / 2
    let d := W.a₃ / 2
    (W.toCharNeTwoNF • W).a₂ = W.a₂ + c ^ 2 ∧
      (W.toCharNeTwoNF • W).a₄ = W.a₄ + 2 * c * d ∧
      (W.toCharNeTwoNF • W).a₆ = W.a₆ + d ^ 2 := by
  let : Invertible (2 : k) := invertibleOfNonzero h2
  dsimp
  constructor
  · simp [variableChange_a₂, WeierstrassCurve.toCharNeTwoNF, invOf_eq_inv]
    field_simp [h2]
    ring
  constructor
  · simp [variableChange_a₄, WeierstrassCurve.toCharNeTwoNF, invOf_eq_inv]
    field_simp [h2]
    ring
  · simp [variableChange_a₆, WeierstrassCurve.toCharNeTwoNF, invOf_eq_inv]
    field_simp [h2]
    ring

namespace Place.IsWeierstrassCoordinates

variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}

/-- Completing the square in Weierstrass coordinates preserves the pole orders and gives
Mathlib's characteristic-not-two normal form. -/
theorem toCharNeTwoNF (h : P.IsWeierstrassCoordinates W x y) (h2 : (2 : k) ≠ 0) :
    letI : Invertible (2 : k) := invertibleOfNonzero h2
    P.IsWeierstrassCoordinates (W.toCharNeTwoNF • W)
      x (y + algebraMap k F (W.a₁ / 2) * x + algebraMap k F (W.a₃ / 2)) := by
  let : Invertible (2 : k) := invertibleOfNonzero h2
  let c : k := W.a₁ / 2
  let d : k := W.a₃ / 2
  have hyc : P.ord (y + algebraMap k F c * x) = -3 := by
    rcases eq_or_ne c 0 with hc | hc
    · simpa [hc] using h.ord_y
    · have hc' : algebraMap k F c ≠ 0 := (map_ne_zero _).mpr hc
      have hcx : P.ord (algebraMap k F c * x) = -2 := by
        rw [P.ord_mul hc' h.x_ne_zero, P.ord_algebraMap, h.ord_x]
        omega
      rw [P.ord_add_eq_min_of_ord_ne h.y_ne_zero (mul_ne_zero hc' h.x_ne_zero)
        (by rw [h.ord_y, hcx]; omega), h.ord_y, hcx]
      decide
  have hyc0 : y + algebraMap k F c * x ≠ 0 := by
    intro heq
    simp [heq] at hyc
  have hycd : P.ord (y + algebraMap k F c * x + algebraMap k F d) = -3 := by
    rcases eq_or_ne d 0 with hd | hd
    · simpa [hd] using hyc
    · rw [P.ord_add_eq_min_of_ord_ne hyc0 ((map_ne_zero _).mpr hd)
        (by rw [hyc, P.ord_algebraMap]; omega), hyc, P.ord_algebraMap]
      decide
  refine ⟨h.ord_x, h.ord_x_nonneg, ?_, ?_, ?_⟩
  · exact hycd
  · intro Q hQ
    have hxQ : x ∈ Q.integers := Q.mem_integers_iff_ord_nonneg.mpr (h.ord_x_nonneg Q hQ)
    have hyQ : y ∈ Q.integers := Q.mem_integers_iff_ord_nonneg.mpr (h.ord_y_nonneg Q hQ)
    have hcQ : algebraMap k F c ∈ Q.integers := Q.algebraMap_mem_integers c
    have hdQ : algebraMap k F d ∈ Q.integers := Q.algebraMap_mem_integers d
    exact Q.mem_integers_iff_ord_nonneg.mp (by exact add_mem (add_mem hyQ (mul_mem hcQ hxQ)) hdQ)
  · have hEq := h.equation
    rw [Affine.equation_iff] at hEq ⊢
    obtain ⟨ha₂, ha₄, ha₆⟩ := charNeTwoNFCoefficients W h2
    have hc : W.a₁ = 2 * c := by
      dsimp [c]
      field_simp [h2]
    have hd : W.a₃ = 2 * d := by
      dsimp [d]
      field_simp [h2]
    simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at hEq ⊢
    rw [ha₂, ha₄, ha₆]
    rw [hc, hd] at hEq
    simp only [a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF, map_zero, zero_mul,
      add_zero, map_add, map_pow, map_mul, map_ofNat] at *
    linear_combination completedSquare (algebraMap k F W.a₂) (algebraMap k F W.a₄)
      (algebraMap k F W.a₆) (algebraMap k F c) (algebraMap k F d) x y + hEq

end Place.IsWeierstrassCoordinates

namespace Place

/-- At every degree-one place of a genus-one function field in characteristic other than two,
there are Weierstrass coordinates in the normal form `Y² = X³ + a₂X² + a₄X + a₆`.
Their pole orders are two and three, so they generate the function field. -/
theorem exists_isWeierstrassCoordinates_isCharNeTwoNF_of_genus_eq_one
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hg : genus k F = 1) (h2 : (2 : k) ≠ 0) {P : Place k F} (hP : P.degree = 1) :
    ∃ (W : WeierstrassCurve k) (x y : F), W.IsCharNeTwoNF ∧
      P.IsWeierstrassCoordinates W x y := by
  obtain ⟨W, x, y, h⟩ := P.exists_isWeierstrassCoordinates_of_genus_eq_one hF hex hg hP
  let : Invertible (2 : k) := invertibleOfNonzero h2
  refine ⟨W.toCharNeTwoNF • W, x,
    y + algebraMap k F (W.a₁ / 2) * x + algebraMap k F (W.a₃ / 2), ?_, ?_⟩
  · infer_instance
  · exact h.toCharNeTwoNF h2

end Place

/-- An elliptic function field in characteristic other than two has a rational place with
Weierstrass coordinates in the form `Y² = X³ + a₂X² + a₄X + a₆`. -/
theorem IsEllipticFunctionField.exists_isWeierstrassCoordinates_isCharNeTwoNF
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (he : IsEllipticFunctionField k F) (h2 : (2 : k) ≠ 0) :
    ∃ (P : Place k F) (W : WeierstrassCurve k) (x y : F),
      P.degree = 1 ∧ W.IsCharNeTwoNF ∧ P.IsWeierstrassCoordinates W x y := by
  obtain ⟨P, hP⟩ := he.exists_place_degree_eq_one hF hex
  obtain ⟨W, x, y, hW, h⟩ :=
    P.exists_isWeierstrassCoordinates_isCharNeTwoNF_of_genus_eq_one hF hex he.genus_eq_one
      h2 hP
  exact ⟨P, W, x, y, hP, hW, h⟩

end TauCeti

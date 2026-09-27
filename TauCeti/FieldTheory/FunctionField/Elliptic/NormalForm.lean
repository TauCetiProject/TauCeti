/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import TauCeti.FieldTheory.FunctionField.Elliptic.VariableChange

/-!
# Normal forms of genus-one function fields

When two is invertible in the constant field, completing the square puts the Weierstrass
equation supplied by Riemann–Roch in the form `Y² = X³ + a₂X² + a₄X + a₆`.  The coordinate
change preserves the pole orders two and three at the chosen rational place, so the resulting
coordinates still generate the function field.  The change of the Weierstrass curve itself is
Mathlib's `WeierstrassCurve.toCharNeTwoNF`.

In characteristic two, Mathlib's `WeierstrassCurve.toCharTwoNF` gives either
`Y² + XY = X³ + a₂X² + a₆` or `Y² + a₃Y = X³ + a₄X + a₆`. Transport under an admissible
variable change preserves the same pole orders, so these normal forms also have coordinates
that generate the function field. These statements concern equations and pole orders;
nonsingularity is a separate assertion.

These are the normal-form coordinate changes of Stichtenoth, Proposition 6.1.2.

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

namespace Place.IsWeierstrassCoordinates

variable {P : Place k F} {W : WeierstrassCurve k} {x y : F}

/-- Completing the square in Weierstrass coordinates preserves the pole orders and gives
Mathlib's characteristic-not-two normal form. -/
theorem toCharNeTwoNF (h : P.IsWeierstrassCoordinates W x y) (h2 : (2 : k) ≠ 0) :
    letI : Invertible (2 : k) := invertibleOfNonzero h2
    P.IsWeierstrassCoordinates (W.toCharNeTwoNF • W)
      x (y + algebraMap k F (W.a₁ / 2) * x + algebraMap k F (W.a₃ / 2)) := by
  let : Invertible (2 : k) := invertibleOfNonzero h2
  -- The inverse of Mathlib's change fixes `x` and adds `(a₁x + a₃)/2` to `y`.
  simpa [WeierstrassCurve.toCharNeTwoNF, VariableChange.inv_def, invOf_eq_inv,
    div_eq_mul_inv, mul_comm] using h.variableChange W.toCharNeTwoNF

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

/-- At every degree-one place of a genus-one function field in characteristic two,
there are Weierstrass coordinates in one of Mathlib's two characteristic-two normal forms.
Their pole orders are two and three, so they generate the function field. -/
theorem exists_isWeierstrassCoordinates_isCharTwoNF_of_genus_eq_one
    [CharP k 2] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hg : genus k F = 1) {P : Place k F} (hP : P.degree = 1) :
    ∃ (W : WeierstrassCurve k) (x y : F), W.IsCharTwoNF ∧
      P.IsWeierstrassCoordinates W x y := by
  obtain ⟨W, x, y, h⟩ := P.exists_isWeierstrassCoordinates_of_genus_eq_one hF hex hg hP
  obtain ⟨C, hC⟩ := W.exists_variableChange_isCharTwoNF
  exact ⟨_, _, _, hC, h.variableChange C⟩

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

/-- An elliptic function field in characteristic two has a rational place with Weierstrass
coordinates in the form `Y² + XY = X³ + a₂X² + a₆` or `Y² + a₃Y = X³ + a₄X + a₆`. -/
theorem IsEllipticFunctionField.exists_isWeierstrassCoordinates_isCharTwoNF
    [CharP k 2] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (he : IsEllipticFunctionField k F) :
    ∃ (P : Place k F) (W : WeierstrassCurve k) (x y : F),
      P.degree = 1 ∧ W.IsCharTwoNF ∧ P.IsWeierstrassCoordinates W x y := by
  obtain ⟨P, hP⟩ := he.exists_place_degree_eq_one hF hex
  obtain ⟨W, x, y, hW, h⟩ :=
    P.exists_isWeierstrassCoordinates_isCharTwoNF_of_genus_eq_one hF hex he.genus_eq_one hP
  exact ⟨P, W, x, y, hP, hW, h⟩

end TauCeti

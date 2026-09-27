/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.VariableChange
public import TauCeti.FieldTheory.FunctionField.Elliptic.WeierstrassEquation

/-!
# Admissible changes of Weierstrass coordinates

An admissible change of variables over the constant field preserves the pole orders two and
three of Weierstrass coordinates, and their regularity away from the chosen place. Consequently
at a degree-one place of a function field, normalizing the equation also gives normalized
generators of the field.
The equation transport uses `WeierstrassCurve.Affine.variableChange_equation`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Springer, 2009,
  Proposition 6.1.2.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Springer, 2009,
  Chapter III, Section 1.
-/

public section

namespace TauCeti.Place.IsWeierstrassCoordinates

open WeierstrassCurve

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  {P : Place k F} {W : WeierstrassCurve k} {x y : F}

private theorem ord_scaled_x_add (h : P.IsWeierstrassCoordinates W x y)
    (a : kˣ) (b : k) :
    P.ord (algebraMap k F (a : k) * x + algebraMap k F b) = -2 := by
  have ha : algebraMap k F (a : k) ≠ 0 := (map_ne_zero _).mpr a.ne_zero
  have hx : P.ord (algebraMap k F (a : k) * x) = -2 := by
    rw [P.ord_mul ha h.x_ne_zero, P.ord_algebraMap, h.ord_x, zero_add]
  by_cases hb : b = 0
  · simpa [hb] using hx
  · rw [P.ord_add_eq_min_of_ord_ne (mul_ne_zero ha h.x_ne_zero)
      ((map_ne_zero _).mpr hb) (by rw [hx, P.ord_algebraMap]; decide), hx,
      P.ord_algebraMap]
    decide

private theorem ord_scaled_y_add (h : P.IsWeierstrassCoordinates W x y)
    (a : kˣ) (b c : k) :
    P.ord (algebraMap k F (a : k) * y + algebraMap k F b * x + algebraMap k F c) = -3 := by
  have ha : algebraMap k F (a : k) ≠ 0 := (map_ne_zero _).mpr a.ne_zero
  have hy : P.ord (algebraMap k F (a : k) * y) = -3 := by
    rw [P.ord_mul ha h.y_ne_zero, P.ord_algebraMap, h.ord_y, zero_add]
  have hyb : P.ord (algebraMap k F (a : k) * y + algebraMap k F b * x) = -3 := by
    by_cases hb : b = 0
    · simpa [hb] using hy
    · have hb' : algebraMap k F b ≠ 0 := (map_ne_zero _).mpr hb
      have hx : P.ord (algebraMap k F b * x) = -2 := by
        rw [P.ord_mul hb' h.x_ne_zero, P.ord_algebraMap, h.ord_x, zero_add]
      rw [P.ord_add_eq_min_of_ord_ne (mul_ne_zero ha h.y_ne_zero)
        (mul_ne_zero hb' h.x_ne_zero) (by rw [hy, hx]; decide), hy, hx]
      decide
  have hyb0 : algebraMap k F (a : k) * y + algebraMap k F b * x ≠ 0 := by
    intro heq
    simp [heq] at hyb
  by_cases hc : c = 0
  · simpa [hc] using hyb
  · rw [P.ord_add_eq_min_of_ord_ne hyb0 ((map_ne_zero _).mpr hc)
      (by rw [hyb, P.ord_algebraMap]; decide), hyb, P.ord_algebraMap]
    decide

/-- An admissible change of variables over the constant field preserves Weierstrass
coordinates. The coordinates on `C • W` are obtained by applying the inverse change. -/
theorem variableChange (h : P.IsWeierstrassCoordinates W x y) (C : VariableChange k) :
    P.IsWeierstrassCoordinates (C • W)
      (algebraMap k F ((C⁻¹).u : k) ^ 2 * x + algebraMap k F (C⁻¹).r)
      (algebraMap k F ((C⁻¹).u : k) ^ 3 * y +
        algebraMap k F ((C⁻¹).u : k) ^ 2 * algebraMap k F (C⁻¹).s * x +
          algebraMap k F (C⁻¹).t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hx := h.ord_scaled_x_add ((C⁻¹).u ^ 2) (C⁻¹).r
    rw [Units.val_pow_eq_pow_val, map_pow] at hx
    exact hx
  · intro Q hQ
    apply Q.mem_integers_iff_ord_nonneg.mp
    exact add_mem (mul_mem (pow_mem (Q.algebraMap_mem_integers _) _)
      (Q.mem_integers_iff_ord_nonneg.mpr (h.ord_x_nonneg Q hQ)))
      (Q.algebraMap_mem_integers _)
  · have hy := h.ord_scaled_y_add ((C⁻¹).u ^ 3)
      (((C⁻¹).u : k) ^ 2 * (C⁻¹).s) (C⁻¹).t
    rw [Units.val_pow_eq_pow_val, map_pow, map_mul, map_pow] at hy
    exact hy
  · intro Q hQ
    apply Q.mem_integers_iff_ord_nonneg.mp
    exact add_mem (add_mem
      (mul_mem (pow_mem (Q.algebraMap_mem_integers _) _)
        (Q.mem_integers_iff_ord_nonneg.mpr (h.ord_y_nonneg Q hQ)))
      (mul_mem (mul_mem (pow_mem (Q.algebraMap_mem_integers _) _)
        (Q.algebraMap_mem_integers _))
        (Q.mem_integers_iff_ord_nonneg.mpr (h.ord_x_nonneg Q hQ))))
      (Q.algebraMap_mem_integers _)
  · have heq := (Affine.variableChange_equation ((C • W).baseChange F)
      ((C⁻¹).map (algebraMap k F)) x y).mpr
      (by simpa only [baseChange, map_variableChange, inv_smul_smul] using h.equation)
    simpa only [VariableChange.map_u, VariableChange.map_r, VariableChange.map_s,
      VariableChange.map_t, Units.coe_map, MonoidHom.coe_ofClass] using heq

end TauCeti.Place.IsWeierstrassCoordinates

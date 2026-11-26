/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.Basic
public import Mathlib.Algebra.Ring.Invertible

/-!
# The hyperbola `x² - y² = a` as a node chart

When `2` is invertible in `R`, the change of coordinates `u = x - y`, `v = x + y` turns the
hyperbola `x² - y² = a` into the node chart `uv = a`, with inverse `x = (u + v) / 2`,
`y = (v - u) / 2`. So `R[x, y] ⧸ (x² - y² - a)` is a node chart over `R` itself: for a discrete
valuation ring `R` with uniformizer `π`, the curve `x² - y² = π` is the chart `uv = π`, with
no extension of the base needed.

## Main results

* `TauCeti.NodeAlgebra.equivQuotientSqSubSq`: the isomorphism
  `R[u, v] ⧸ (uv - a) ≃ₐ[R] R[x, y] ⧸ (x² - y² - a)` sending `u ↦ x - y` and `v ↦ x + y`, with
  inverse `x ↦ (u + v) / 2`, `y ↦ (v - u) / 2` (`TauCeti.NodeAlgebra.equivQuotientSqSubSq_symm_mk`).

## References

* [Stacks Project, Lemma 55.14.2, Tag 0CDD](https://stacks.math.columbia.edu/tag/0CDD): the
  étale local structure of a node over a discrete valuation ring.
-/

public section

noncomputable section

namespace TauCeti.NodeAlgebra

open MvPolynomial

variable {R : Type*} [CommRing R] (a : R) [Invertible (2 : R)]

/-- The point `x = (u + v) / 2`, `y = (v - u) / 2` of the node chart `uv = a`. -/
private abbrev hyperbolaCoord : Fin 2 → NodeAlgebra R a :=
  ![algebraMap R _ ⅟2 * (coord a 0 + coord a 1), algebraMap R _ ⅟2 * (coord a 1 - coord a 0)]

/-- The coordinate change `x = (u + v) / 2`, `y = (v - u) / 2` from the hyperbola
`x² - y² = a` to the node chart `uv = a`. -/
private def ofQuotientSqSubSq :
    (MvPolynomial (Fin 2) R ⧸ Ideal.span {X 0 ^ 2 - X 1 ^ 2 - C a}) →ₐ[R] NodeAlgebra R a :=
  Ideal.Quotient.liftₐ _ (aeval (hyperbolaCoord a))
    (by
      intro p hp
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      have h₂ := congrArg (algebraMap R (NodeAlgebra R a)) (invOf_mul_self (2 : R))
      rw [map_mul, map_ofNat, map_one] at h₂
      have huv := coord_zero_mul_coord_one a
      simp only [map_mul, map_sub, map_pow, aeval_X, aeval_C, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      -- With `h = ⅟2`, `x² - y² - a = uv (2h - 1)(2h + 1) + (uv - a)`.
      linear_combination aeval (hyperbolaCoord a) c *
        (coord a 0 * coord a 1 * (algebraMap R _ ⅟2 * 2 + 1) * h₂ + huv))

private lemma ofQuotientSqSubSq_mk (p : MvPolynomial (Fin 2) R) :
    ofQuotientSqSubSq a (Ideal.Quotient.mk _ p) = aeval (hyperbolaCoord a) p :=
  Ideal.Quotient.liftₐ_apply _ _ _ _

/-- **The hyperbola `x² - y² = a` is a node chart**: when `2` is invertible in `R`, the
coordinates `u = x - y` and `v = x + y` identify `R[u, v] ⧸ (uv - a)` with
`R[x, y] ⧸ (x² - y² - a)`. -/
def equivQuotientSqSubSq :
    NodeAlgebra R a ≃ₐ[R] MvPolynomial (Fin 2) R ⧸ Ideal.span {X 0 ^ 2 - X 1 ^ 2 - C a} :=
  AlgEquiv.ofAlgHom
    (lift a (Ideal.Quotient.mk _ (X 0 - X 1)) (Ideal.Quotient.mk _ (X 0 + X 1)) (by
      rw [← map_mul, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, algebraMap_eq]
      convert Ideal.mem_span_singleton_self _ using 1
      ring))
    (ofQuotientSqSubSq a)
    (by
      refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i ↦ ?_)
      have h₂ := congrArg
        (algebraMap R (MvPolynomial (Fin 2) R ⧸ Ideal.span {X 0 ^ 2 - X 1 ^ 2 - C a}))
        (invOf_mul_self (2 : R))
      rw [map_mul, map_ofNat, map_one] at h₂
      fin_cases i <;>
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ofQuotientSqSubSq_mk, aeval_X,
          map_mul, map_add, map_sub, AlgHom.commutes, lift_coord_zero, lift_coord_one,
          AlgHom.coe_id, id_eq, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
          Matrix.cons_val_one]
      · linear_combination Ideal.Quotient.mk _ (X 0) * h₂
      · linear_combination Ideal.Quotient.mk _ (X 1) * h₂)
    (by
      have h₂ := congrArg (algebraMap R (NodeAlgebra R a)) (invOf_mul_self (2 : R))
      rw [map_mul, map_ofNat, map_one] at h₂
      ext
      · simp only [AlgHom.comp_apply, lift_coord_zero, map_sub, ofQuotientSqSubSq_mk, aeval_X,
          Matrix.cons_val_zero, Matrix.cons_val_one, AlgHom.coe_id, id_eq]
        linear_combination coord a 0 * h₂
      · simp only [AlgHom.comp_apply, lift_coord_one, map_add, ofQuotientSqSubSq_mk, aeval_X,
          Matrix.cons_val_zero, Matrix.cons_val_one, AlgHom.coe_id, id_eq]
        linear_combination coord a 1 * h₂)

/-- The isomorphism sends `u` to `x - y`. -/
@[simp]
theorem equivQuotientSqSubSq_coord_zero :
    equivQuotientSqSubSq a (coord a 0) = Ideal.Quotient.mk _ (X 0 - X 1) := by
  rw [equivQuotientSqSubSq, AlgEquiv.ofAlgHom_apply, lift_coord_zero]

/-- The isomorphism sends `v` to `x + y`. -/
@[simp]
theorem equivQuotientSqSubSq_coord_one :
    equivQuotientSqSubSq a (coord a 1) = Ideal.Quotient.mk _ (X 0 + X 1) := by
  rw [equivQuotientSqSubSq, AlgEquiv.ofAlgHom_apply, lift_coord_one]

/-- The inverse isomorphism evaluates a polynomial at `x = (u + v) / 2` and `y = (v - u) / 2`. -/
@[simp]
theorem equivQuotientSqSubSq_symm_mk (p : MvPolynomial (Fin 2) R) :
    (equivQuotientSqSubSq a).symm (Ideal.Quotient.mk _ p) =
      aeval ![algebraMap R _ ⅟2 * (coord a 0 + coord a 1),
        algebraMap R _ ⅟2 * (coord a 1 - coord a 0)] p := by
  rw [equivQuotientSqSubSq, AlgEquiv.ofAlgHom_symm_apply, ofQuotientSqSubSq_mk]

end TauCeti.NodeAlgebra

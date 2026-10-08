/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing
public import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# Variable changes on the homogeneous coordinate ring of a Weierstrass curve

An admissible change of variables `C = (u, r, s, t)` carries a point `(x, y)` of `C • W` to the
point `(u²x + r, u³y + u²sx + t)` of `W`. In homogeneous coordinates this is the linear map
`[X : Y : Z] ↦ [u²X + rZ : u²sX + u³Y + tZ : Z]` with matrix `C.toMatrix`. Substituting it into the
homogeneous Weierstrass polynomial of `W` gives `u⁶` times that of `C • W`, so it induces an
`R`-algebra isomorphism of homogeneous coordinate rings
`variableChangeEquiv W C : R[X, Y, Z] ⧸ (W) ≃ₐ[R] R[X, Y, Z] ⧸ (C • W)` which preserves the grading
by total degree. Its `Proj` is the isomorphism between the projective Weierstrass models of `C • W`
and `W`.

## Main definitions

* `WeierstrassCurve.VariableChange.toMatrix`: the matrix of a change of variables acting on
  homogeneous coordinates `[X : Y : Z]`.
* `WeierstrassCurve.Projective.variableChangeEquiv`: the induced isomorphism of homogeneous
  coordinate rings.

## Main results

* `WeierstrassCurve.VariableChange.toMatrix_mul`: `toMatrix` is an anti-homomorphism, matching the
  action `(C * C') • W = C • C' • W`.
* `WeierstrassCurve.VariableChange.toMatrix_map`: `toMatrix` commutes with mapping along a ring
  homomorphism.
* `WeierstrassCurve.VariableChange.toMatrix_injective` and
  `WeierstrassCurve.VariableChange.toMatrix_inj`: a change of variables is determined by its
  matrix.
* `WeierstrassCurve.Projective.equation_variableChange`: `P` solves the projective Weierstrass
  equation of `C • W` exactly when `C.toMatrix *ᵥ P` solves that of `W`.
* `WeierstrassCurve.Projective.linearSubst_polynomial`: the substitution multiplies the
  homogeneous Weierstrass polynomial by `u⁶`.
* `WeierstrassCurve.Projective.variableChangeEquiv_one` and
  `WeierstrassCurve.Projective.variableChangeEquiv_mul`: the isomorphisms are compatible with the
  identity and with products of changes of variables.
* `WeierstrassCurve.Projective.variableChangeEquiv_mem_grading`: the isomorphism preserves the
  grading.
* `WeierstrassCurve.Projective.evalZero_variableChangeEquiv`: the point `[0 : 1 : 0]` of `C • W` is
  carried to the point `[0 : u³ : 0] = [0 : 1 : 0]` of `W`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.1][silverman2009]
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2.

## Provenance

`toMatrix_injective` is adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/ComparisonInjective.lean`: it is the last step
of the proof of `projModelVCIso_injective'`, which recovers `u` from `u²` and `u³`, and `s` from
`u²` and `u²s`, by cancelling the unit `u²`, and concludes by `VariableChange.ext`. The source has
no matrix of a change of variables and applies this step to coefficients it has read off the
affine coordinate ring; here it is stated for the entries of `toMatrix`.
-/

public section

open MvPolynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

namespace VariableChange

/-- The matrix of the change of variables `C = (u, r, s, t)` acting on homogeneous coordinates:
`[X : Y : Z] ↦ [u²X + rZ : u²sX + u³Y + tZ : Z]`, the homogenisation of
`(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
def toMatrix (C : VariableChange R) : Matrix (Fin 3) (Fin 3) R :=
  !![(C.u : R) ^ 2, 0, C.r; (C.u : R) ^ 2 * C.s, (C.u : R) ^ 3, C.t; 0, 0, 1]

/-- The entries of the matrix `C.toMatrix` of a change of variables. -/
theorem toMatrix_def (C : VariableChange R) :
    C.toMatrix = !![(C.u : R) ^ 2, 0, C.r; (C.u : R) ^ 2 * C.s, (C.u : R) ^ 3, C.t; 0, 0, 1] :=
  (rfl)

@[simp]
theorem toMatrix_one : toMatrix (1 : VariableChange R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, one_def]

/-- `toMatrix` reverses products: a point of `(C * C') • W = C • C' • W` is first carried to
`C' • W` by `C`, and then to `W` by `C'`. -/
@[simp]
theorem toMatrix_mul (C C' : VariableChange R) : toMatrix (C * C') = toMatrix C' * toMatrix C := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, mul_def, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

theorem toMatrix_mul_toMatrix_inv (C : VariableChange R) : toMatrix C * toMatrix C⁻¹ = 1 := by
  rw [← toMatrix_mul, inv_mul_cancel, toMatrix_one]

theorem toMatrix_inv_mul_toMatrix (C : VariableChange R) : toMatrix C⁻¹ * toMatrix C = 1 := by
  rw [← toMatrix_mul, mul_inv_cancel, toMatrix_one]

/-- The matrix of a change of variables mapped along a ring homomorphism `f` is the matrix of the
original change of variables with `f` applied to its entries. -/
@[simp]
theorem toMatrix_map {S : Type*} [CommRing S] (C : VariableChange R) (f : R →+* S) :
    (C.map f).toMatrix = C.toMatrix.map f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix]

/-- A change of variables `C = (u, r, s, t)` is determined by its matrix `C.toMatrix`. -/
theorem toMatrix_injective :
    Function.Injective (toMatrix : VariableChange R → Matrix (Fin 3) (Fin 3) R) := by
  intro C C' h
  -- the entries `u²`, `r`, `u²s`, `u³` and `t` of the two matrices agree
  simp only [toMatrix_def, Equiv.apply_eq_iff_eq, Matrix.vecCons_inj, and_true, true_and] at h
  obtain ⟨⟨h00, h02⟩, h10, h11, h12⟩ := h
  -- `u = u³ / u²`, and then `s = u²s / u²`
  have hu : (C.u : R) = C'.u :=
    (C.u.isUnit.pow 2).mul_left_cancel (by linear_combination h11 - (C'.u : R) * h00)
  exact VariableChange.ext (Units.ext hu) h02
    ((C.u.isUnit.pow 2).mul_left_cancel (by rw [h10, h00])) h12

/-- Two changes of variables have the same matrix exactly when they are equal. -/
@[simp]
theorem toMatrix_inj {C C' : VariableChange R} : C.toMatrix = C'.toMatrix ↔ C = C' :=
  toMatrix_injective.eq_iff

end VariableChange

namespace Projective

variable (W : WeierstrassCurve R) (C : VariableChange R)

/-- The change of variables multiplies the homogeneous Weierstrass polynomial by `u⁶`:
`W(u²X + rZ, u²sX + u³Y + tZ, Z) = u⁶ (C • W)(X, Y, Z)`. -/
theorem linearSubst_polynomial :
    linearSubst C.toMatrix W.toProjective.polynomial =
      MvPolynomial.C ((C.u : R) ^ 6) * (C • W).toProjective.polynomial := by
  -- the coefficients of `C • W`, with the factors `u⁻ⁱ` cleared
  have h₁ : (C.u : R) * (C • W).a₁ = W.a₁ + 2 * C.s := by
    simp only [variableChange_a₁, Units.mul_inv_cancel_left]
  have h₂ : (C.u : R) ^ 2 * (C • W).a₂ = W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2 := by
    simp only [variableChange_a₂, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv_cancel_left]
  have h₃ : (C.u : R) ^ 3 * (C • W).a₃ = W.a₃ + C.r * W.a₁ + 2 * C.t := by
    simp only [variableChange_a₃, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv_cancel_left]
  have h₄ : (C.u : R) ^ 4 * (C • W).a₄ = W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂
      - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2 - 2 * C.s * C.t := by
    simp only [variableChange_a₄, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv_cancel_left]
  have h₆ : (C.u : R) ^ 6 * (C • W).a₆ = W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3
      - C.t * W.a₃ - C.t ^ 2 - C.r * C.t * W.a₁ := by
    simp only [variableChange_a₆, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv_cancel_left]
  replace h₁ := congr((MvPolynomial.C $h₁ : MvPolynomial (Fin 3) R))
  replace h₂ := congr((MvPolynomial.C $h₂ : MvPolynomial (Fin 3) R))
  replace h₃ := congr((MvPolynomial.C $h₃ : MvPolynomial (Fin 3) R))
  replace h₄ := congr((MvPolynomial.C $h₄ : MvPolynomial (Fin 3) R))
  replace h₆ := congr((MvPolynomial.C $h₆ : MvPolynomial (Fin 3) R))
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at h₁ h₂ h₃ h₄ h₆
  simp [polynomial, VariableChange.toMatrix, Fin.sum_univ_three]
  linear_combination -(MvPolynomial.C (C.u : R) ^ 5 * X 0 * X 1 * X 2) * h₁
    + MvPolynomial.C (C.u : R) ^ 4 * X 0 ^ 2 * X 2 * h₂
    - MvPolynomial.C (C.u : R) ^ 3 * X 1 * X 2 ^ 2 * h₃
    + MvPolynomial.C (C.u : R) ^ 2 * X 0 * X 2 ^ 2 * h₄ + X 2 ^ 3 * h₆

/-- The linear substitution along `C.toMatrix`, an `R`-algebra automorphism of `R[X, Y, Z]` with
inverse the substitution along `C⁻¹.toMatrix`. -/
private noncomputable def linearSubstEquiv : MvPolynomial (Fin 3) R ≃ₐ[R] MvPolynomial (Fin 3) R :=
  AlgEquiv.ofAlgHom (linearSubst C.toMatrix) (linearSubst C⁻¹.toMatrix)
    (by rw [← linearSubst_mul, VariableChange.toMatrix_inv_mul_toMatrix, linearSubst_one])
    (by rw [← linearSubst_mul, VariableChange.toMatrix_mul_toMatrix_inv, linearSubst_one])

private theorem linearSubstEquiv_apply (p : MvPolynomial (Fin 3) R) :
    linearSubstEquiv C p = linearSubst C.toMatrix p :=
  rfl

/-- The isomorphism of homogeneous coordinate rings `R[X, Y, Z] ⧸ (W) ≃ₐ[R] R[X, Y, Z] ⧸ (C • W)`
induced by the change of variables `C`: the class of `p(X, Y, Z)` goes to the class of
`p(u²X + rZ, u²sX + u³Y + tZ, Z)`. -/
noncomputable def variableChangeEquiv :
    W.toProjective.CoordinateRing ≃ₐ[R] (C • W).toProjective.CoordinateRing :=
  Ideal.quotientEquivAlg _ _ (linearSubstEquiv C) <| by
    rw [Ideal.map_span, Set.image_singleton, RingHom.coe_coe, linearSubstEquiv_apply,
      linearSubst_polynomial, Ideal.span_singleton_mul_left_unit
      ((C.u.isUnit.pow 6).map MvPolynomial.C)]

@[simp]
theorem variableChangeEquiv_mk (p : MvPolynomial (Fin 3) R) :
    variableChangeEquiv W C (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (linearSubst C.toMatrix p) :=
  (rfl)

@[simp]
theorem variableChangeEquiv_symm_mk (p : MvPolynomial (Fin 3) R) :
    (variableChangeEquiv W C).symm (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (linearSubst C⁻¹.toMatrix p) :=
  (rfl)

/-- The identity change of variables induces the canonical isomorphism
`R[X, Y, Z] ⧸ (W) ≃ₐ[R] R[X, Y, Z] ⧸ (1 • W)` coming from `1 • W = W`. -/
@[simp]
theorem variableChangeEquiv_one :
    variableChangeEquiv W 1 = Ideal.quotientEquivAlgOfEq R (by rw [one_smul]) := by
  ext x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- The isomorphism induced by a product `C * C'` is the isomorphism induced by `C'` followed by
the one induced by `C`, up to the canonical isomorphism coming from `C • C' • W = (C * C') • W`. -/
@[simp]
theorem variableChangeEquiv_mul (C' : VariableChange R) :
    variableChangeEquiv W (C * C') =
      ((variableChangeEquiv W C').trans (variableChangeEquiv (C' • W) C)).trans
        (Ideal.quotientEquivAlgOfEq R (by rw [mul_smul])) := by
  ext x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [linearSubst_mul_apply]

/-- The isomorphism of homogeneous coordinate rings preserves the grading by total degree. -/
theorem variableChangeEquiv_mem_grading {n : ℕ} {x : W.toProjective.CoordinateRing}
    (hx : x ∈ W.toProjective.grading n) :
    variableChangeEquiv W C x ∈ (C • W).toProjective.grading n := by
  obtain ⟨p, hp, rfl⟩ := W.toProjective.mem_grading_iff.mp hx
  rw [variableChangeEquiv_mk]
  exact mk_mem_grading _ (hp.linearSubst _)

/-- The inverse isomorphism of homogeneous coordinate rings preserves the grading by total
degree. -/
theorem variableChangeEquiv_symm_mem_grading {n : ℕ} {x : (C • W).toProjective.CoordinateRing}
    (hx : x ∈ (C • W).toProjective.grading n) :
    (variableChangeEquiv W C).symm x ∈ W.toProjective.grading n := by
  obtain ⟨p, hp, rfl⟩ := (C • W).toProjective.mem_grading_iff.mp hx
  rw [variableChangeEquiv_symm_mk]
  exact mk_mem_grading _ (hp.linearSubst _)

open Matrix in
/-- A point representative `P` solves the projective Weierstrass equation of `C • W` exactly when
its image `C.toMatrix *ᵥ P = [u²P₀ + rP₂ : u²sP₀ + u³P₁ + tP₂ : P₂]` solves that of `W`. -/
theorem equation_variableChange (P : Fin 3 → R) :
    (C • W).toProjective.Equation P ↔ W.toProjective.Equation (C.toMatrix *ᵥ P) := by
  rw [Projective.Equation, Projective.Equation, ← eval_linearSubst, linearSubst_polynomial,
    eval_mul, eval_C, (C.u.isUnit.pow 6).mul_right_eq_zero]

open Matrix in
/-- Evaluating at `[0 : 1 : 0]` after the change of variables is evaluating at
`[0 : u³ : 0]`: on the degree-`n` part it multiplies the value at `[0 : 1 : 0]` by `(u³)ⁿ`. -/
theorem evalZero_variableChangeEquiv {n : ℕ} {x : W.toProjective.CoordinateRing}
    (hx : x ∈ W.toProjective.grading n) :
    (C • W).toProjective.evalZero (variableChangeEquiv W C x) =
      ((C.u : R) ^ 3) ^ n * W.toProjective.evalZero x := by
  obtain ⟨p, hp, rfl⟩ := W.toProjective.mem_grading_iff.mp hx
  have h : C.toMatrix *ᵥ ![0, 1, 0] = ((C.u : R) ^ 3 • (1 : Matrix (Fin 3) (Fin 3) R)) *ᵥ
      ![0, 1, 0] := by
    ext i
    fin_cases i <;> simp [VariableChange.toMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [variableChangeEquiv_mk, evalZero_mk, evalZero_mk, eval_linearSubst, h, ← eval_linearSubst,
    hp.linearSubst_smul, linearSubst_one, AlgHom.id_apply, smul_eq_C_mul, eval_mul, eval_C]

end Projective

end WeierstrassCurve

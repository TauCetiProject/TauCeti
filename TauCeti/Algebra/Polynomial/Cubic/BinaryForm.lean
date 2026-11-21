/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.Algebra.Polynomial.Homogenize
public import TauCeti.RingTheory.MvPolynomial.LinearSubst
import Mathlib.Tactic.LinearCombination

/-!
# Binary cubic forms and the twisted action of `GL₂`

Mathlib's `Cubic R` records four coefficients `a, b, c, d`. Read homogeneously, they are the
binary cubic form `f(x, y) = a x³ + b x² y + c x y² + d y³`, the homogenization
`(Cubic.toPoly P).homogenize 3` in `MvPolynomial (Fin 2) R`. Binary cubic forms parametrize cubic
rings (Delone–Faddeev), and integral forms ordered by discriminant count cubic fields
(Davenport–Heilbronn). This file equips the carrier `Cubic R` with its linear substitutions and with
the twisted left action of `GL₂(R)`

`(g • f)(x, y) = (det g)⁻¹ f((x, y) g)`,

where `(x, y) g = (g₀₀ x + g₁₀ y, g₀₁ x + g₁₁ y)` is the row vector times the matrix. The action is
defined on coefficients, so it makes sense over every commutative ring, including small finite
fields where a form is not determined by its values, and no division by `2` or `3` occurs.

## Main definitions

* `Cubic.polynomialAction M P`: the form `f((x, y) M)`, for an arbitrary `2 × 2` matrix `M`.
* The instance `MulAction (GL (Fin 2) R) (Cubic R)`: the twisted action
  `g • P = (det g)⁻¹ · Cubic.polynomialAction g P`.

## Main results

* `Cubic.homogenize_toPoly_polynomialAction`, `Cubic.homogenize_toPoly_smul`: on binary forms the
  substitution is `TauCeti.polynomialAction`, and the twisted action is its multiple by
  `(det g)⁻¹`.
* `Cubic.polynomialAction_mul`: substitution is a left action of the monoid of `2 × 2` matrices.
* `Cubic.discr_polynomialAction`: `disc (f ∘ M) = (det M)⁶ disc f`, a polynomial identity over
  every commutative ring.
* `Cubic.discr_smul`: `disc (g • f) = (det g)² disc f`.
* `Cubic.scalar_smul`: the scalar matrix `u` multiplies every coefficient by `u`.
* `Cubic.map_smul`: the action commutes with base change along ring homomorphisms.
* The instance `FaithfulSMul (GL (Fin 2) R) (Cubic R)`: only the identity fixes every form.

## References

* M. Bhargava, A. Shankar, J. Tsimerman, *On the Davenport–Heilbronn theorems and second order
  terms*, Invent. Math. 193 (2013), §2.
* M. M. Wood, *Parametrizing quartic algebras over an arbitrary base*, Algebra Number Theory 5
  (2011), §2.
-/

public section

open Matrix

namespace Cubic

section Substitution

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The binary form of `P`: the homogenization `a X₀³ + b X₀² X₁ + c X₀ X₁² + d X₁³` of
`Cubic.toPoly P` in degree three. -/
theorem homogenize_toPoly (P : Cubic R) :
    P.toPoly.homogenize 3 = MvPolynomial.C P.a * MvPolynomial.X 0 ^ 3 +
      MvPolynomial.C P.b * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 +
        MvPolynomial.C P.c * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 +
          MvPolynomial.C P.d * MvPolynomial.X 1 ^ 3 := by
  simp [toPoly, mul_assoc]

/-- The linear substitution `v ↦ P (v ᵥ* M)` of the binary cubic form `P` by the `2 × 2` matrix
`M`, computed on coefficients: with `(x, y) M = (M₀₀ x + M₁₀ y, M₀₁ x + M₁₁ y)`, it expands
`P (M₀₀ x + M₁₀ y, M₀₁ x + M₁₁ y)`. -/
def polynomialAction (M : Matrix (Fin 2) (Fin 2) R) (P : Cubic R) : Cubic R where
  a := P.a * M 0 0 ^ 3 + P.b * M 0 0 ^ 2 * M 0 1 + P.c * M 0 0 * M 0 1 ^ 2 + P.d * M 0 1 ^ 3
  b := 3 * P.a * M 0 0 ^ 2 * M 1 0 + P.b * (M 0 0 ^ 2 * M 1 1 + 2 * M 0 0 * M 1 0 * M 0 1) +
    P.c * (2 * M 0 0 * M 0 1 * M 1 1 + M 1 0 * M 0 1 ^ 2) + 3 * P.d * M 0 1 ^ 2 * M 1 1
  c := 3 * P.a * M 0 0 * M 1 0 ^ 2 + P.b * (2 * M 0 0 * M 1 0 * M 1 1 + M 1 0 ^ 2 * M 0 1) +
    P.c * (M 0 0 * M 1 1 ^ 2 + 2 * M 1 0 * M 0 1 * M 1 1) + 3 * P.d * M 0 1 * M 1 1 ^ 2
  d := P.a * M 1 0 ^ 3 + P.b * M 1 0 ^ 2 * M 1 1 + P.c * M 1 0 * M 1 1 ^ 2 + P.d * M 1 1 ^ 3

@[simp]
theorem polynomialAction_a (M : Matrix (Fin 2) (Fin 2) R) (P : Cubic R) :
    (polynomialAction M P).a =
      P.a * M 0 0 ^ 3 + P.b * M 0 0 ^ 2 * M 0 1 + P.c * M 0 0 * M 0 1 ^ 2 + P.d * M 0 1 ^ 3 :=
  (rfl)

@[simp]
theorem polynomialAction_b (M : Matrix (Fin 2) (Fin 2) R) (P : Cubic R) :
    (polynomialAction M P).b =
      3 * P.a * M 0 0 ^ 2 * M 1 0 + P.b * (M 0 0 ^ 2 * M 1 1 + 2 * M 0 0 * M 1 0 * M 0 1) +
        P.c * (2 * M 0 0 * M 0 1 * M 1 1 + M 1 0 * M 0 1 ^ 2) + 3 * P.d * M 0 1 ^ 2 * M 1 1 :=
  (rfl)

@[simp]
theorem polynomialAction_c (M : Matrix (Fin 2) (Fin 2) R) (P : Cubic R) :
    (polynomialAction M P).c =
      3 * P.a * M 0 0 * M 1 0 ^ 2 + P.b * (2 * M 0 0 * M 1 0 * M 1 1 + M 1 0 ^ 2 * M 0 1) +
        P.c * (M 0 0 * M 1 1 ^ 2 + 2 * M 1 0 * M 0 1 * M 1 1) + 3 * P.d * M 0 1 * M 1 1 ^ 2 :=
  (rfl)

@[simp]
theorem polynomialAction_d (M : Matrix (Fin 2) (Fin 2) R) (P : Cubic R) :
    (polynomialAction M P).d =
      P.a * M 1 0 ^ 3 + P.b * M 1 0 ^ 2 * M 1 1 + P.c * M 1 0 * M 1 1 ^ 2 + P.d * M 1 1 ^ 3 :=
  (rfl)

/-- `Cubic.polynomialAction M` is the substitution `X₀ ↦ M₀₀ X₀ + M₁₀ X₁`, `X₁ ↦ M₀₁ X₀ + M₁₁ X₁`
of the binary form, that is `TauCeti.polynomialAction M`. -/
theorem homogenize_toPoly_polynomialAction (M : Matrix (Fin 2) (Fin 2) R) (P : Cubic R) :
    (polynomialAction M P).toPoly.homogenize 3 =
      TauCeti.polynomialAction M (P.toPoly.homogenize 3) := by
  simp only [homogenize_toPoly, map_add, map_mul, map_pow, TauCeti.polynomialAction_X,
    Fin.sum_univ_two, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, polynomialAction_a,
    polynomialAction_b, polynomialAction_c, polynomialAction_d, map_ofNat]
  ring

@[simp]
theorem polynomialAction_one (P : Cubic R) : polynomialAction 1 P = P := by
  ext <;> simp

/-- Substitution by `M * N` substitutes by `N` and then by `M`: `P ((v M) N) = P (v (M N))`, so
linear substitution is a left action of the monoid of `2 × 2` matrices. -/
theorem polynomialAction_mul (M N : Matrix (Fin 2) (Fin 2) R) (P : Cubic R) :
    polynomialAction (M * N) P = polynomialAction M (polynomialAction N P) := by
  ext <;> simp only [polynomialAction_a, polynomialAction_b, polynomialAction_c,
    polynomialAction_d, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Linear substitution commutes with base change of the coefficients. -/
theorem map_polynomialAction (φ : R →+* S) (M : Matrix (Fin 2) (Fin 2) R) (P : Cubic R) :
    (polynomialAction M P).map φ = polynomialAction (φ.mapMatrix M) (P.map φ) := by
  ext <;> simp [map, map_ofNat]

end Substitution

section Discriminant

variable {R : Type*} [CommRing R]

/-- **Discriminant covariance of linear substitution.** For every `2 × 2` matrix `M`,
`disc (P ∘ M) = (det M)⁶ disc P`. This is a polynomial identity in the coefficients of `P` and the
entries of `M`, so it holds over every commutative ring. -/
@[simp]
theorem discr_polynomialAction (M : Matrix (Fin 2) (Fin 2) R) (P : Cubic R) :
    (polynomialAction M P).discr = M.det ^ 6 * P.discr := by
  simp only [discr, polynomialAction_a, polynomialAction_b, polynomialAction_c, polynomialAction_d,
    det_fin_two]
  ring

end Discriminant

section TwistedAction

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The twisted left action `(g • P)(v) = (det g)⁻¹ P (v ᵥ* g)` of `GL₂(R)` on binary cubic
forms, computed on coefficients from `Cubic.polynomialAction`. The twist by `(det g)⁻¹` makes a
scalar matrix `u` act as multiplication by `u` and gives `disc (g • P) = (det g)² disc P`. -/
instance instSMulGL : SMul (GL (Fin 2) R) (Cubic R) where
  smul g P :=
    let u : R := ↑(GeneralLinearGroup.det g)⁻¹
    let Q := polynomialAction (g : Matrix (Fin 2) (Fin 2) R) P
    ⟨u * Q.a, u * Q.b, u * Q.c, u * Q.d⟩

variable (g : GL (Fin 2) R) (P : Cubic R)

@[simp]
theorem smul_a : (g • P).a = ↑(GeneralLinearGroup.det g)⁻¹ * (polynomialAction g P).a :=
  (rfl)

@[simp]
theorem smul_b : (g • P).b = ↑(GeneralLinearGroup.det g)⁻¹ * (polynomialAction g P).b :=
  (rfl)

@[simp]
theorem smul_c : (g • P).c = ↑(GeneralLinearGroup.det g)⁻¹ * (polynomialAction g P).c :=
  (rfl)

@[simp]
theorem smul_d : (g • P).d = ↑(GeneralLinearGroup.det g)⁻¹ * (polynomialAction g P).d :=
  (rfl)

/-- The twisted substitution is a left action: `(g * h) • P = g • h • P`. -/
instance instMulActionGL : MulAction (GL (Fin 2) R) (Cubic R) where
  one_smul P := by ext <;> simp
  mul_smul g h P := by
    ext <;> simp only [smul_a, smul_b, smul_c, smul_d, Units.val_mul, polynomialAction_mul,
      map_mul, mul_inv, polynomialAction_a, polynomialAction_b, polynomialAction_c,
      polynomialAction_d] <;> ring

/-- The twisted action on binary forms: `g • P` is `(det g)⁻¹ · TauCeti.polynomialAction g P`. -/
theorem homogenize_toPoly_smul :
    (g • P).toPoly.homogenize 3 = MvPolynomial.C (↑(GeneralLinearGroup.det g)⁻¹ : R) *
      TauCeti.polynomialAction (g : Matrix (Fin 2) (Fin 2) R) (P.toPoly.homogenize 3) := by
  rw [← homogenize_toPoly_polynomialAction, homogenize_toPoly, homogenize_toPoly]
  simp only [smul_a, smul_b, smul_c, smul_d, map_mul]
  ring

/-- **Discriminant covariance of the twisted action:** `disc (g • P) = (det g)² disc P`. -/
@[simp]
theorem discr_smul :
    (g • P).discr = (GeneralLinearGroup.det g : R) ^ 2 * P.discr := by
  set u : R := ↑(GeneralLinearGroup.det g)⁻¹
  set δ : R := ↑(GeneralLinearGroup.det g)
  have hu : u * δ = 1 := Units.inv_mul _
  have h : (g • P).discr = u ^ 4 * (polynomialAction g P).discr := by
    simp only [discr, smul_a, smul_b, smul_c, smul_d]
    ring
  rw [h, discr_polynomialAction, ← GeneralLinearGroup.val_det_apply]
  calc u ^ 4 * (δ ^ 6 * P.discr) = (u * δ) ^ 4 * (δ ^ 2 * P.discr) := by ring
    _ = δ ^ 2 * P.discr := by rw [hu, one_pow, one_mul]

/-- A scalar matrix `u` acts by multiplying every coefficient by `u`: the substitution contributes
`u³` and the twist `u⁻²`. -/
@[simp]
theorem scalar_smul (u : Rˣ) :
    GeneralLinearGroup.scalar (Fin 2) u • P = ⟨u * P.a, u * P.b, u * P.c, u * P.d⟩ := by
  have hu (x : R) : ((u⁻¹ : Rˣ) : R) ^ 2 * (x * u ^ 3) = u * x := by
    calc ((u⁻¹ : Rˣ) : R) ^ 2 * (x * u ^ 3) = ((u⁻¹ : Rˣ) * u : R) ^ 2 * (u * x) := by ring
      _ = u * x := by rw [Units.inv_mul, one_pow, one_mul]
  ext <;> simp [← pow_succ, ← pow_succ', hu]

/-- The twisted action commutes with base change of the coefficients along a ring
homomorphism. -/
protected theorem map_smul (φ : R →+* S) :
    (g • P).map φ = GeneralLinearGroup.map φ g • P.map φ := by
  have hsub : polynomialAction (GeneralLinearGroup.map φ g : Matrix (Fin 2) (Fin 2) S) (P.map φ) =
      (polynomialAction g P).map φ := by
    rw [map_polynomialAction, GeneralLinearGroup.val_map_apply, RingHom.mapMatrix_apply]
  rw [Cubic.ext_iff]
  simp only [smul_a, smul_b, smul_c, smul_d, GeneralLinearGroup.map_det, hsub]
  simp [map]

/-- An element of `GL₂(R)` fixing every binary cubic form is the identity. -/
private theorem eq_one_of_forall_smul_eq (h : ∀ P : Cubic R, g • P = P) : g = 1 := by
  -- The forms `x³` and `y³` make the diagonal entries units; `x² y` and `x y²` then kill the
  -- off-diagonal entries and pin the diagonal ones to `1`.
  set u : R := ↑(GeneralLinearGroup.det g)⁻¹
  have hu : u * (g 0 0 * g 1 1 - g 0 1 * g 1 0) = 1 := by
    rw [← det_fin_two, ← GeneralLinearGroup.val_det_apply]
    exact Units.inv_mul _
  have h₁ := congrArg Cubic.a (h ⟨1, 0, 0, 0⟩)
  have h₂ := congrArg Cubic.d (h ⟨0, 0, 0, 1⟩)
  have h₃ := congrArg Cubic.a (h ⟨0, 1, 0, 0⟩)
  have h₄ := congrArg Cubic.b (h ⟨0, 1, 0, 0⟩)
  have h₅ := congrArg Cubic.d (h ⟨0, 0, 1, 0⟩)
  have h₆ := congrArg Cubic.c (h ⟨0, 0, 1, 0⟩)
  simp only [smul_a, smul_b, smul_c, smul_d, polynomialAction_a, polynomialAction_b,
    polynomialAction_c, polynomialAction_d, zero_mul, one_mul, zero_add,
    add_zero] at h₁ h₂ h₃ h₄ h₅ h₆
  have h01 : g 0 1 = 0 := by linear_combination g 0 0 * h₃ - g 0 1 * h₁
  have h10 : g 1 0 = 0 := by linear_combination g 1 1 * h₅ - g 1 0 * h₂
  rw [h01, h10] at hu h₄ h₆
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using (by linear_combination h₄ - g 0 0 * hu : g 0 0 = 1)
  · simpa using h01
  · simpa using h10
  · simpa using (by linear_combination h₆ - g 1 1 * hu : g 1 1 = 1)

/-- The twisted action is faithful over every commutative ring, including finite fields where
distinct forms can define the same function. -/
instance instFaithfulSMulGL : FaithfulSMul (GL (Fin 2) R) (Cubic R) where
  eq_of_smul_eq_smul {g₁ g₂} h := by
    have := eq_one_of_forall_smul_eq (g₂⁻¹ * g₁) fun P => by rw [mul_smul, h, inv_smul_smul]
    rwa [inv_mul_eq_one, eq_comm] at this

end TwistedAction

end Cubic

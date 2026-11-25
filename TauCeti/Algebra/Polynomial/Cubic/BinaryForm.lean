/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Algebra.Polynomial.Cubic.Basic
public import TauCeti.RingTheory.MvPolynomial.LinearSubst
import Mathlib.Tactic.LinearCombination

/-!
# The twisted action of `GL₂` on binary cubic forms

A cubic `P = ⟨a, b, c, d⟩ : Cubic R` over a commutative ring `R`, with its leading coefficient
allowed to vanish, is read as the binary cubic form
`f(u, v) = a u³ + b u² v + c u v² + d v³`; as a polynomial in `MvPolynomial (Fin 2) R` this is
Mathlib's homogenization `P.toPoly.homogenize 3`, with `u = X 0` and `v = X 1`. Invertible
`2 × 2` matrices act on these forms on the left by the determinant-twisted substitution in row
variables,
```
(g • f)(u, v) = det(g)⁻¹ f((u, v) g),
```
so that `g • (h • f) = (g * h) • f`. For `g = !![p, q; r, s]` the coefficients of `g • P` are
`det(g)⁻¹` times
```
a' = f(p, q) = a p³ + b p² q + c p q² + d q³
b' = 3 a p² r + b (p² s + 2 p q r) + c (2 p q s + q² r) + 3 d q² s
c' = 3 a p r² + b (2 p r s + q r²) + c (p s² + 2 q r s) + 3 d q s²
d' = f(r, s) = a r³ + b r² s + c r s² + d s³.
```
This is the action under which integral binary cubic forms correspond to cubic rings: the twist
makes the scalar matrix `λ • 1` act by multiplication by `λ`, and it makes Mathlib's
discriminant `Cubic.discr`, the invariant `b²c² − 4ac³ − 4b³d − 27a²d² + 18abcd`, covariant of
weight two:
```
disc(g • f) = det(g)² disc(f).
```
These are polynomial identities in the coefficients and the matrix entries, so they hold over
every commutative ring, with no inversion of `2` or `3`. Mapping coefficients along a ring
homomorphism commutes with the action, which transports orbit data between a ring and its
localizations and completions.

## Main definitions

* `Cubic.polynomialAction M P`: the form `f((u, v) M)`, for an arbitrary `2 × 2` matrix `M`.
* The instance `MulAction (GL (Fin 2) R) (Cubic R)`: the twisted action
  `(g • f)(u, v) = det(g)⁻¹ f((u, v) g)`, that is `det(g)⁻¹ · Cubic.polynomialAction g P`
  (`Cubic.smul_eq_polynomialAction`).

## Main results

* `Cubic.smul_a`, `Cubic.smul_b`, `Cubic.smul_c`, `Cubic.smul_d`: the coefficients of `g • P`.
* `Cubic.homogenize_toPoly_smul`: the action is the substitution `X ↦ gᵀ X` of
  `MvPolynomial.linearSubst`, twisted by `det(g)⁻¹`; `Cubic.eval_homogenize_toPoly_smul` is its
  pointwise form `(g • f)(x) = det(g)⁻¹ f(x ᵥ* g)`.
* `Cubic.homogenize_toPoly_injective` and `Cubic.isHomogeneous_iff_exists_homogenize_toPoly`:
  cubics are exactly the binary cubic forms, as homogeneous polynomials of degree three.
* `Cubic.homogenize_toPoly_polynomialAction`: on binary forms `Cubic.polynomialAction` is
  `TauCeti.polynomialAction`.
* `Cubic.polynomialAction_mul`: substitution is a left action of the monoid of `2 × 2` matrices.
* `Cubic.discr_polynomialAction`: `disc (f ∘ M) = (det M)⁶ disc f` for every `2 × 2` matrix.
* `Cubic.discr_smul`: `(g • P).discr = det(g)² * P.discr`.
* `Cubic.discr_smul_eq_zero_iff`: the action preserves vanishing of the discriminant.
* `Cubic.scalar_smul`: the scalar matrix `u • 1` acts by multiplying every coefficient by `u`.
* `Cubic.smul_map`: mapping coefficients along a ring homomorphism is equivariant for
  `Matrix.GeneralLinearGroup.map`.
* The instance `FaithfulSMul (GL (Fin 2) R) (Cubic R)`: only the identity fixes every form.

## References

* M. Bhargava, A. Shankar, J. Tsimerman, *On the Davenport–Heilbronn theorems and second order
  terms*, Invent. Math. **193** (2013), §2.
* W. T. Gan, B. Gross and G. Savin, *Fourier coefficients of modular forms on `G₂`*, Duke Math.
  J. **115** (2002), 105–169.
* M. M. Wood, *Parametrizing quartic algebras over an arbitrary base*, Algebra Number Theory
  **5** (2011), 1069–1094, §2.
-/

public section

open Matrix MvPolynomial

namespace Cubic

section BinaryForm

variable {R : Type*} [CommSemiring R]

/-- The binary cubic form of a cubic: homogenizing `P.toPoly` in degree three gives
`a u³ + b u² v + c u v² + d v³`, with `u = X 0` and `v = X 1`. -/
theorem homogenize_toPoly (P : Cubic R) :
    P.toPoly.homogenize 3 = C P.a * X 0 ^ 3 + C P.b * X 0 ^ 2 * X 1 +
      C P.c * X 0 * X 1 ^ 2 + C P.d * X 1 ^ 3 := by
  simp [toPoly, mul_assoc]

/-- A cubic is determined by its binary cubic form. -/
theorem homogenize_toPoly_injective :
    Function.Injective fun P : Cubic R ↦ P.toPoly.homogenize 3 := fun P Q h ↦
  (toPoly_injective P Q).1 <| by
    rw [← Polynomial.aeval_homogenize_X_one P.toPoly Polynomial.natDegree_cubic_le,
      ← Polynomial.aeval_homogenize_X_one Q.toPoly Polynomial.natDegree_cubic_le]
    exact congrArg _ h

/-- The binary cubic forms are exactly the homogeneous polynomials of degree three in two
variables. -/
theorem isHomogeneous_iff_exists_homogenize_toPoly {p : MvPolynomial (Fin 2) R} :
    p.IsHomogeneous 3 ↔ ∃ P : Cubic R, P.toPoly.homogenize 3 = p := by
  refine ⟨fun hp ↦ ?_, fun ⟨P, hP⟩ ↦ hP ▸ Polynomial.isHomogeneous_homogenize _⟩
  have hdeg : (aeval ![(Polynomial.X : Polynomial R), 1] p).degree ≤ 3 := by
    rw [p.as_sum, map_sum]
    refine Polynomial.degree_le_of_natDegree_le <|
      Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm ↦ ?_
    have hm3 := hp (mem_support_iff.mp hm)
    simp [Finsupp.weight_apply, Finsupp.sum_fintype] at hm3
    simpa [aeval_monomial, Finsupp.prod_fintype, ← Polynomial.C_eq_algebraMap] using
      (Polynomial.natDegree_C_mul_X_pow_le (p.coeff m) (m 0)).trans (by omega)
  exact ⟨equiv.symm ⟨_, hdeg⟩, Polynomial.homogenize_eq_of_isHomogeneous hp
    (congrArg Subtype.val (equiv.apply_symm_apply ⟨_, hdeg⟩)).symm⟩

end BinaryForm

section MatrixSubstitution

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

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
    Fin.sum_univ_two, algHom_C, algebraMap_eq, polynomialAction_a, polynomialAction_b,
    polynomialAction_c, polynomialAction_d, map_ofNat]
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

end MatrixSubstitution

variable {R : Type*} [CommRing R]

/-- The twisted action of `GL (Fin 2) R` on cubics read as binary cubic forms:
`(g • f)(u, v) = det(g)⁻¹ f((u, v) g)` for `f(u, v) = a u³ + b u² v + c u v² + d v³`, the
variables `(u, v)` forming a row vector. The coefficients are `Cubic.smul_a`, `Cubic.smul_b`,
`Cubic.smul_c` and `Cubic.smul_d`; the substitution is `Cubic.homogenize_toPoly_smul`. -/
instance instSMulGeneralLinearGroup : SMul (GL (Fin 2) R) (Cubic R) where
  smul g P :=
    ⟨↑(GeneralLinearGroup.det g)⁻¹ *
        (P.a * g 0 0 ^ 3 + P.b * g 0 0 ^ 2 * g 0 1 + P.c * g 0 0 * g 0 1 ^ 2 + P.d * g 0 1 ^ 3),
      ↑(GeneralLinearGroup.det g)⁻¹ *
        (3 * P.a * g 0 0 ^ 2 * g 1 0 + P.b * (g 0 0 ^ 2 * g 1 1 + 2 * g 0 0 * g 0 1 * g 1 0) +
          P.c * (2 * g 0 0 * g 0 1 * g 1 1 + g 0 1 ^ 2 * g 1 0) + 3 * P.d * g 0 1 ^ 2 * g 1 1),
      ↑(GeneralLinearGroup.det g)⁻¹ *
        (3 * P.a * g 0 0 * g 1 0 ^ 2 + P.b * (2 * g 0 0 * g 1 0 * g 1 1 + g 0 1 * g 1 0 ^ 2) +
          P.c * (g 0 0 * g 1 1 ^ 2 + 2 * g 0 1 * g 1 0 * g 1 1) + 3 * P.d * g 0 1 * g 1 1 ^ 2),
      ↑(GeneralLinearGroup.det g)⁻¹ *
        (P.a * g 1 0 ^ 3 + P.b * g 1 0 ^ 2 * g 1 1 + P.c * g 1 0 * g 1 1 ^ 2 + P.d * g 1 1 ^ 3)⟩

section Coefficients

variable (g : GL (Fin 2) R) (P : Cubic R)

/-- The `u³` coefficient of `g • P` is `det(g)⁻¹ f(p, q)` for the first row `(p, q)` of `g`. -/
@[simp]
theorem smul_a : (g • P).a = ↑(GeneralLinearGroup.det g)⁻¹ *
    (P.a * g 0 0 ^ 3 + P.b * g 0 0 ^ 2 * g 0 1 + P.c * g 0 0 * g 0 1 ^ 2 + P.d * g 0 1 ^ 3) :=
  rfl

/-- The `u² v` coefficient of `g • P`. -/
@[simp]
theorem smul_b : (g • P).b = ↑(GeneralLinearGroup.det g)⁻¹ *
    (3 * P.a * g 0 0 ^ 2 * g 1 0 + P.b * (g 0 0 ^ 2 * g 1 1 + 2 * g 0 0 * g 0 1 * g 1 0) +
      P.c * (2 * g 0 0 * g 0 1 * g 1 1 + g 0 1 ^ 2 * g 1 0) + 3 * P.d * g 0 1 ^ 2 * g 1 1) :=
  rfl

/-- The `u v²` coefficient of `g • P`. -/
@[simp]
theorem smul_c : (g • P).c = ↑(GeneralLinearGroup.det g)⁻¹ *
    (3 * P.a * g 0 0 * g 1 0 ^ 2 + P.b * (2 * g 0 0 * g 1 0 * g 1 1 + g 0 1 * g 1 0 ^ 2) +
      P.c * (g 0 0 * g 1 1 ^ 2 + 2 * g 0 1 * g 1 0 * g 1 1) + 3 * P.d * g 0 1 * g 1 1 ^ 2) :=
  rfl

/-- The `v³` coefficient of `g • P` is `det(g)⁻¹ f(r, s)` for the second row `(r, s)` of `g`. -/
@[simp]
theorem smul_d : (g • P).d = ↑(GeneralLinearGroup.det g)⁻¹ *
    (P.a * g 1 0 ^ 3 + P.b * g 1 0 ^ 2 * g 1 1 + P.c * g 1 0 * g 1 1 ^ 2 + P.d * g 1 1 ^ 3) :=
  rfl

end Coefficients

/-- The twisted substitution `(g • f)(u, v) = det(g)⁻¹ f((u, v) g)` is a left action:
`g • (h • f) = (g * h) • f`. -/
instance instMulActionGeneralLinearGroup : MulAction (GL (Fin 2) R) (Cubic R) where
  one_smul P := by
    ext <;> simp
  mul_smul g h P := by
    have hdet : (↑(GeneralLinearGroup.det (g * h))⁻¹ : R) =
        ↑(GeneralLinearGroup.det g)⁻¹ * ↑(GeneralLinearGroup.det h)⁻¹ := by
      simp [mul_comm]
    ext <;>
    · simp only [smul_a, smul_b, smul_c, smul_d, hdet, Units.val_mul, Matrix.mul_apply,
        Fin.sum_univ_two]
      ring

section Substitution

/-- The twisted action is `det(g)⁻¹` times the untwisted substitution `Cubic.polynomialAction g`
on every coefficient. -/
theorem smul_eq_polynomialAction (g : GL (Fin 2) R) (P : Cubic R) :
    g • P = ⟨↑(GeneralLinearGroup.det g)⁻¹ * (polynomialAction (g : Matrix (Fin 2) (Fin 2) R) P).a,
      ↑(GeneralLinearGroup.det g)⁻¹ * (polynomialAction (g : Matrix (Fin 2) (Fin 2) R) P).b,
      ↑(GeneralLinearGroup.det g)⁻¹ * (polynomialAction (g : Matrix (Fin 2) (Fin 2) R) P).c,
      ↑(GeneralLinearGroup.det g)⁻¹ * (polynomialAction (g : Matrix (Fin 2) (Fin 2) R) P).d⟩ := by
  ext <;> simp only [smul_a, smul_b, smul_c, smul_d, polynomialAction_a, polynomialAction_b,
    polynomialAction_c, polynomialAction_d] <;> ring

/-- The action of `g` is the substitution `X ↦ gᵀ X` of the variables, that is
`(u, v) ↦ (u, v) g` in row variables, followed by multiplication by `det(g)⁻¹`. -/
theorem homogenize_toPoly_smul (g : GL (Fin 2) R) (P : Cubic R) :
    (g • P).toPoly.homogenize 3 = C (↑(GeneralLinearGroup.det g)⁻¹ : R) *
      linearSubst (g : Matrix (Fin 2) (Fin 2) R)ᵀ (P.toPoly.homogenize 3) := by
  simp only [homogenize_toPoly, map_add, map_mul, map_pow, algHom_C, algebraMap_eq, linearSubst_X,
    Fin.sum_univ_two, transpose_apply, smul_a, smul_b, smul_c, smul_d, map_ofNat]
  ring

/-- Pointwise form of `Cubic.homogenize_toPoly_smul`:
`(g • f)(x) = det(g)⁻¹ f(x ᵥ* g)` for every row vector `x`. -/
theorem eval_homogenize_toPoly_smul (g : GL (Fin 2) R) (P : Cubic R) (x : Fin 2 → R) :
    eval x ((g • P).toPoly.homogenize 3) =
      ↑(GeneralLinearGroup.det g)⁻¹ * eval (x ᵥ* (g : Matrix (Fin 2) (Fin 2) R))
        (P.toPoly.homogenize 3) := by
  rw [homogenize_toPoly_smul, eval_mul, eval_C, eval_linearSubst, mulVec_transpose]

end Substitution

section Discriminant

/-- **Covariance of the discriminant.** The discriminant of a binary cubic form is a relative
invariant of weight two for the twisted action: `disc(g • f) = det(g)² disc(f)`. -/
@[simp]
theorem discr_smul (g : GL (Fin 2) R) (P : Cubic R) :
    (g • P).discr = ↑(GeneralLinearGroup.det g) ^ 2 * P.discr := by
  -- Untwisted, the substitution multiplies the discriminant by `det(g) ^ 6`; each of the four
  -- coefficients carries one factor `det(g)⁻¹`, and the discriminant has degree four.
  have hP : (g • P).discr = (↑(GeneralLinearGroup.det g)⁻¹ * ↑(GeneralLinearGroup.det g)) ^ 4 *
      (↑(GeneralLinearGroup.det g) ^ 2 * P.discr) := by
    rw [GeneralLinearGroup.val_det_apply, det_fin_two]
    simp only [discr, smul_a, smul_b, smul_c, smul_d]
    ring
  rw [hP, Units.inv_mul, one_pow, one_mul]

/-- The action preserves vanishing of the discriminant. -/
theorem discr_smul_eq_zero_iff (g : GL (Fin 2) R) (P : Cubic R) :
    (g • P).discr = 0 ↔ P.discr = 0 := by
  rw [discr_smul, ((GeneralLinearGroup.det g).isUnit.pow 2).mul_right_eq_zero]

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

/-- The scalar matrix `u • 1` multiplies every coefficient by `u`: its substitution multiplies a
cubic form by `u³` and its determinant is `u²`. -/
theorem scalar_smul (u : Rˣ) (P : Cubic R) :
    GeneralLinearGroup.scalar (Fin 2) u • P = ⟨↑u * P.a, ↑u * P.b, ↑u * P.c, ↑u * P.d⟩ := by
  have hu : (↑u⁻¹ : R) ^ 2 * ↑u ^ 3 = ↑u := by
    rw [show (↑u⁻¹ : R) ^ 2 * ↑u ^ 3 = (↑u⁻¹ * ↑u) ^ 2 * ↑u by ring, Units.inv_mul, one_pow,
      one_mul]
  ext
  · simp; linear_combination P.a * hu
  · simp; linear_combination P.b * hu
  · simp; linear_combination P.c * hu
  · simp; linear_combination P.d * hu

/-- Mapping coefficients along a ring homomorphism is equivariant for the action, through the
entrywise map `GL (Fin 2) R →* GL (Fin 2) S`. -/
@[simp]
theorem smul_map {S : Type*} [CommRing S] (f : R →+* S) (g : GL (Fin 2) R) (P : Cubic R) :
    GeneralLinearGroup.map f g • P.map f = (g • P).map f := by
  have hdet : (↑(GeneralLinearGroup.det (GeneralLinearGroup.map f g))⁻¹ : S) =
      f ↑(GeneralLinearGroup.det g)⁻¹ := by
    simp [GeneralLinearGroup.map_det]
  ext <;> simp [map, hdet, map_ofNat]

/-- An element of `GL₂(R)` fixing every binary cubic form is the identity. -/
private theorem eq_one_of_forall_smul_eq (g : GL (Fin 2) R) (h : ∀ P : Cubic R, g • P = P) :
    g = 1 := by
  -- The forms `u³` and `v³` make the diagonal entries units; `u² v` and `u v²` then kill the
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
  simp only [smul_a, smul_b, smul_c, smul_d, zero_mul, mul_zero, one_mul, zero_add,
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
instance instFaithfulSMulGeneralLinearGroup : FaithfulSMul (GL (Fin 2) R) (Cubic R) where
  eq_of_smul_eq_smul {g₁ g₂} h := by
    have := eq_one_of_forall_smul_eq (g₂⁻¹ * g₁) fun P => by rw [mul_smul, h, inv_smul_smul]
    rwa [inv_mul_eq_one, eq_comm] at this

section Examples

/-- The form `u³ - v³` has discriminant `-27` over every commutative ring. -/
example : (⟨1, 0, 0, -1⟩ : Cubic R).discr = -27 := by
  simp [discr]

/-- The form `u v (u - v)` has discriminant `1`. -/
example : (⟨0, 1, -1, 0⟩ : Cubic R).discr = 1 := by
  simp [discr]

/-- The unipotent matrix `!![1, 1; 0, 1]` takes `u³ - v³` to `-3 u² v - 3 u v² - v³`. -/
example : (ModularGroup.T : GL (Fin 2) ℤ) • (⟨1, 0, 0, -1⟩ : Cubic ℤ) = ⟨0, -3, -3, -1⟩ := by
  ext <;> simp

end Examples

end Cubic

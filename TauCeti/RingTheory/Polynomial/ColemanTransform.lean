/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import TauCeti.LinearAlgebra.Matrix.Charpoly.Resultant
import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse
import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Coleman's spectral transform at a prescribed rank

Let `P` be a polynomial with `P(0) = 1` and degree at most `n`, thought of as the Fredholm
determinant `det (1 - T u)` of an operator `u` of rank `n`, and let `B` be a polynomial of degree at
most `m`. Coleman's transform

`D_{n,m}(B, P)(T) = Res_X (X ^ n P(1 / X), 1 - T B(X))`

is the Fredholm determinant `det (1 - T B(u))`. It is computed with Mathlib's degree-bounded
resultant `Polynomial.resultant`, over the polynomial ring in `T`.

The rank `n` is part of the data and is not recovered from `P`: an eigenvalue `0` of `u` is
invisible in `det (1 - T u)` but becomes the eigenvalue `B(0)` of `B(u)`. Accordingly, raising `n`
by one multiplies the transform by `1 - B(0) T` (`TauCeti.colemanDBounded_succ`), and for a finite
matrix the rank to use is its size, not the degree of `det (1 - T A)`
(`Matrix.charpolyRev_aeval_eq_colemanDBounded`). The degree bound `m` of `B` plays no role once
`P(0) = 1` (`TauCeti.colemanDBounded_of_natDegree_le`).

All statements hold over an arbitrary commutative ring, including rings with nilpotents: they are
universal polynomial identities, not statements about values at field-valued points.

## Main definitions

* `TauCeti.colemanDBounded n m B P`: the transform `D_{n,m}(B, P)` at rank `n` and degree bound `m`.
* `TauCeti.colemanD B P`: the transform at the minimal rank `P.natDegree` and the minimal degree
  bound `B.natDegree`.

## Main results

* `Matrix.charpolyRev_aeval_eq_colemanDBounded`: spectral mapping for a square matrix `A` of size
  `n`, `det (1 - T B(A)) = D_{n,m}(B, det (1 - T A))`.
* `TauCeti.colemanDBounded_mul`: ranks add and the transform is multiplicative in `P`.
* `TauCeti.colemanDBounded_succ`, `TauCeti.colemanDBounded_one_right`: padding the rank.
* `TauCeti.colemanDBounded_add_of_coeff_zero`: if `B(0) = 0`, the transform is independent of the
  rank.
* `TauCeti.colemanDBounded_of_natDegree_le`, `TauCeti.colemanD_eq_colemanDBounded`: independence
  of the degree bound of `B`.
* `TauCeti.colemanDBounded_eq_colemanD`: comparison with the minimal-rank transform.
* `TauCeti.colemanDBounded_map`: compatibility with ring homomorphisms of the coefficients.
* `TauCeti.colemanDBounded_X_left`: for `B = X` the transform returns `P`.
* `TauCeti.coeff_zero_colemanDBounded`: the constant coefficient is `P(0) ^ m`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A3.
-/

public section

open Polynomial

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Coleman's transform `D_{n,m}(B, P)(T) = Res_X (X ^ n P(1 / X), 1 - T B(X))` at rank `n` and
degree bound `m`. The resultant is taken over the polynomial ring `R[T]`, with the degree bounds `n`
for the reflection of `P` and `m` for `1 - T B(X)`.

When `P = det (1 - T A)` for a square matrix `A` of size `n` and `B` has degree at most `m`, this is
`det (1 - T B(A))` (`Matrix.charpolyRev_aeval_eq_colemanDBounded`). -/
noncomputable def colemanDBounded (n m : ℕ) (B P : R[X]) : R[X] :=
  ((P.reflect n).map C).resultant (1 - C X * B.map C) n m

theorem colemanDBounded_def (n m : ℕ) (B P : R[X]) :
    colemanDBounded n m B P = ((P.reflect n).map C).resultant (1 - C X * B.map C) n m := (rfl)

/-- Coleman's transform at the minimal rank `P.natDegree` and degree bound `B.natDegree`.
For a finite matrix with a zero eigenvalue the rank must instead be the size of the matrix; see
`TauCeti.colemanDBounded_eq_colemanD`. -/
noncomputable def colemanD (B P : R[X]) : R[X] :=
  colemanDBounded P.natDegree B.natDegree B P

theorem colemanD_def (B P : R[X]) :
    colemanD B P = colemanDBounded P.natDegree B.natDegree B P := (rfl)

/-- The polynomial `1 - T B(X)` in `R[T][X]` has degree at most that of `B`. -/
private theorem natDegree_one_sub_C_X_mul_map_C_le (B : R[X]) {m : ℕ} (hB : B.natDegree ≤ m) :
    (1 - C X * B.map C : R[X][X]).natDegree ≤ m :=
  (natDegree_sub_le _ _).trans <| max_le (by simp) <|
    (natDegree_C_mul_le _ _).trans <| (natDegree_map_le).trans hB

private theorem natDegree_map_C_reflect_le {n : ℕ} {P : R[X]} (hP : P.natDegree ≤ n) :
    ((P.reflect n).map C : R[X][X]).natDegree ≤ n :=
  natDegree_map_le.trans <| natDegree_reflect_le.trans <| max_le le_rfl hP

private theorem coeff_zero_one_sub_C_X_mul_map_C (B : R[X]) :
    (1 - C X * B.map C : R[X][X]).coeff 0 = 1 - C (B.coeff 0) * X := by
  rw [coeff_sub, coeff_one_zero, coeff_C_mul, coeff_map, mul_comm]

private theorem coeff_map_C_reflect_self (n : ℕ) (P : R[X]) :
    ((P.reflect n).map C).coeff n = C (P.coeff 0) := by
  simp [coeff_reflect]

/-- At rank zero the transform is the constant `P(0) ^ m`. -/
@[simp]
theorem colemanDBounded_zero_rank (m : ℕ) (B P : R[X]) :
    colemanDBounded 0 m B P = C (P.coeff 0) ^ m := by
  simp [colemanDBounded_def, coeff_reflect]

/-- For `B = 0` the transform is the constant `P(0) ^ m`. -/
@[simp]
theorem colemanDBounded_zero_left (n m : ℕ) (P : R[X]) :
    colemanDBounded n m 0 P = C (P.coeff 0) ^ m := by
  rw [colemanDBounded_def, Polynomial.map_zero, mul_zero, sub_zero, resultant_one_right,
    coeff_map_C_reflect_self]

/-- The constant coefficient of the transform is `P(0) ^ m`. In particular it is `1` when
`P(0) = 1`. -/
@[simp]
theorem coeff_zero_colemanDBounded (n m : ℕ) (B P : R[X]) :
    (colemanDBounded n m B P).coeff 0 = P.coeff 0 ^ m := by
  have hC : (evalRingHom (0 : R)).comp C = RingHom.id R := by ext; simp
  have h₁ : ((P.reflect n).map C).map (evalRingHom (0 : R)) = P.reflect n := by
    rw [Polynomial.map_map, hC, Polynomial.map_id]
  have h₂ : (1 - C X * B.map C : R[X][X]).map (evalRingHom (0 : R)) = 1 := by simp
  rw [coeff_zero_eq_eval_zero, ← coe_evalRingHom, colemanDBounded_def, ← resultant_map_map, h₁,
    h₂, resultant_one_right, coeff_reflect, revAt_le le_rfl, Nat.sub_self]

/-- The transform commutes with ring homomorphisms applied to the coefficients. -/
theorem colemanDBounded_map (φ : R →+* S) (n m : ℕ) (B P : R[X]) :
    colemanDBounded n m (B.map φ) (P.map φ) = (colemanDBounded n m B P).map φ := by
  have hC : (mapRingHom φ).comp C = C.comp φ := by ext; simp
  have h := resultant_map_map ((P.reflect n).map C) (1 - C X * B.map C) n m (mapRingHom φ)
  rw [coe_mapRingHom] at h
  rw [colemanDBounded_def, colemanDBounded_def, ← h]
  congr 1
  · rw [Polynomial.map_map, hC, ← Polynomial.map_map, reflect_map]
  · rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, Polynomial.map_map,
      Polynomial.map_map, hC, coe_mapRingHom, map_X]

/-- Ranks add, and the transform is multiplicative in `P`. -/
theorem colemanDBounded_mul {n₁ n₂ m : ℕ} {B P₁ P₂ : R[X]} (hP₁ : P₁.natDegree ≤ n₁)
    (hP₂ : P₂.natDegree ≤ n₂) (hB : B.natDegree ≤ m) :
    colemanDBounded (n₁ + n₂) m B (P₁ * P₂) =
      colemanDBounded n₁ m B P₁ * colemanDBounded n₂ m B P₂ := by
  simp only [colemanDBounded_def]
  rw [reflect_mul _ _ hP₁ hP₂, Polynomial.map_mul,
    resultant_mul_left_of_natDegree_le (natDegree_map_C_reflect_le hP₁)
      (natDegree_map_C_reflect_le hP₂) (natDegree_one_sub_C_X_mul_map_C_le B hB)]

/-- At rank one, the transform of `P = 1` is `1 - B(0) T`: the eigenvalue `0` of `u` becomes the
eigenvalue `B(0)` of `B(u)`. -/
theorem colemanDBounded_one_one {m : ℕ} {B : R[X]} (hB : B.natDegree ≤ m) :
    colemanDBounded 1 m B 1 = 1 - C (B.coeff 0) * X := by
  have h := resultant_X_pow_left (1 - C X * B.map C : R[X][X]) 1 m
    (natDegree_one_sub_C_X_mul_map_C_le B hB)
  rw [pow_one, pow_one, coeff_zero_one_sub_C_X_mul_map_C] at h
  rw [colemanDBounded_def, reflect_one, pow_one, map_X, h]

/-- The transform of `P = 1` at rank `n` is `(1 - B(0) T) ^ n`. -/
theorem colemanDBounded_one_right (n : ℕ) {m : ℕ} {B : R[X]} (hB : B.natDegree ≤ m) :
    colemanDBounded n m B 1 = (1 - C (B.coeff 0) * X) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← mul_one (1 : R[X]), colemanDBounded_mul (by simp) (by simp) hB, mul_one, ih,
      colemanDBounded_one_one hB, pow_succ]

/-- Raising the rank by one multiplies the transform by `1 - B(0) T`. -/
theorem colemanDBounded_succ {n m : ℕ} {B P : R[X]} (hP : P.natDegree ≤ n)
    (hB : B.natDegree ≤ m) :
    colemanDBounded (n + 1) m B P = (1 - C (B.coeff 0) * X) * colemanDBounded n m B P := by
  rw [← mul_one P, colemanDBounded_mul hP (by simp) hB, mul_one, colemanDBounded_one_one hB,
    mul_comm]

/-- If `B(0) = 0`, the transform does not depend on the rank `n ≥ deg P`. -/
theorem colemanDBounded_add_of_coeff_zero {n m : ℕ} {B P : R[X]} (hP : P.natDegree ≤ n)
    (hB : B.natDegree ≤ m) (hB0 : B.coeff 0 = 0) (k : ℕ) :
    colemanDBounded (n + k) m B P = colemanDBounded n m B P := by
  rw [← mul_one P, colemanDBounded_mul hP (by simp) hB, colemanDBounded_one_right k hB, hB0,
    map_zero, zero_mul, sub_zero, one_pow, mul_one, mul_one]

/-- If `P(0) = 1`, the transform does not depend on the bound `m ≥ deg B`. -/
theorem colemanDBounded_of_natDegree_le {n m m' : ℕ} {B P : R[X]} (hP0 : P.coeff 0 = 1)
    (hB : B.natDegree ≤ m) (hm : m ≤ m') :
    colemanDBounded n m' B P = colemanDBounded n m B P := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [colemanDBounded_def, resultant_add_right_deg _ _ _ _ _
    (natDegree_one_sub_C_X_mul_map_C_le B hB), coeff_map_C_reflect_self, hP0, map_one, one_pow,
    one_mul, colemanDBounded_def]

/-- If `P(0) = 1`, the minimal-rank transform may be computed with any bound `m ≥ deg B`. -/
theorem colemanD_eq_colemanDBounded {m : ℕ} {B P : R[X]} (hP0 : P.coeff 0 = 1)
    (hB : B.natDegree ≤ m) :
    colemanD B P = colemanDBounded P.natDegree m B P :=
  (colemanDBounded_of_natDegree_le hP0 le_rfl hB).symm

/-- If `P(0) = 1`, the transform at a rank `n ≥ deg P` is the minimal-rank transform times
`(1 - B(0) T) ^ (n - deg P)`, one factor for each zero eigenvalue added by the padding. -/
theorem colemanDBounded_eq_colemanD {n m : ℕ} {B P : R[X]} (hP : P.natDegree ≤ n)
    (hB : B.natDegree ≤ m) (hP0 : P.coeff 0 = 1) :
    colemanDBounded n m B P = (1 - C (B.coeff 0) * X) ^ (n - P.natDegree) * colemanD B P := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hP
  have h := colemanDBounded_mul (P₁ := P) (P₂ := 1) le_rfl (by simp : (1 : R[X]).natDegree ≤ k) hB
  rw [mul_one] at h
  rw [h, colemanDBounded_one_right k hB, Nat.add_sub_cancel_left,
    colemanD_eq_colemanDBounded hP0 hB, mul_comm]

/-- For `B = X` and `deg P ≤ 1`, a direct `2 × 2` Sylvester determinant. -/
private theorem colemanDBounded_X_left_of_natDegree_le_one {P : R[X]} (hP : P.natDegree ≤ 1) :
    colemanDBounded 1 1 X P = P := by
  have hr : ((P.reflect 1).map C : R[X][X]) = C (C (P.coeff 1)) + C (C (P.coeff 0)) * X := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hP]
    simp [add_comm]
  have hg : (1 - C X * (X : R[X]).map C : R[X][X]) = C 1 + C (-X) * X := by
    rw [map_X, C_1, C_neg]
    ring
  rw [colemanDBounded_def, hr, hg]
  conv_rhs => rw [eq_X_add_C_of_natDegree_le_one hP]
  simp [resultant, sylvester, Matrix.det_fin_two, Fin.addCases, coeff_C, coeff_X, coeff_one]
  ring

/-- For `B = X`, the transform at degree bound `1` and any rank `n ≥ deg P` is `P` itself:
`det (1 - T u)` is recovered from `u = X(u)`. -/
theorem colemanDBounded_X_left {n : ℕ} {P : R[X]} (hP : P.natDegree ≤ n) :
    colemanDBounded n 1 X P = P := by
  induction P using induction_of_Splits_of_injective_of_surjective generalizing n with
  | Splits K P hsplit =>
    -- pad down to the actual degree, then factor `P` into linear factors
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hP
    have h := colemanDBounded_mul (P₁ := P) (P₂ := 1) le_rfl
      (by simp : (1 : K[X]).natDegree ≤ k) natDegree_X_le
    rw [mul_one] at h
    rw [h, colemanDBounded_one_right k natDegree_X_le, coeff_X_zero, map_zero, zero_mul, sub_zero,
      one_pow, mul_one]
    have hprod (s : Multiset K) :
        colemanDBounded (Multiset.card s) 1 X (s.map (X - C ·)).prod = (s.map (X - C ·)).prod := by
      induction s using Multiset.induction_on with
      | empty => simp
      | cons a s ih =>
        rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm,
          colemanDBounded_mul (natDegree_X_sub_C_le a)
            (natDegree_multiset_prod_X_sub_C_eq_card s).le natDegree_X_le,
          colemanDBounded_X_left_of_natDegree_le_one (natDegree_X_sub_C_le a), ih]
    have hP' := hsplit.eq_prod_roots
    rw [hsplit.natDegree_eq_card_roots]
    generalize P.roots = s at hP' ⊢
    generalize P.leadingCoeff = c at hP'
    subst hP'
    rw [← zero_add (Multiset.card s), colemanDBounded_mul (natDegree_C c).le
      (natDegree_multiset_prod_X_sub_C_eq_card s).le natDegree_X_le, hprod,
      colemanDBounded_zero_rank, coeff_C_zero, pow_one]
  | injective R S φ hφ P IH =>
    apply map_injective φ hφ
    rw [← colemanDBounded_map, map_X]
    exact IH (natDegree_map_le.trans hP)
  | surjective R S φ hφ P IH =>
    obtain ⟨P, rfl, hdeg⟩ := exists_natDegree_eq_of_mem_lifts (Polynomial.map_surjective φ hφ P)
    rw [← map_X φ, colemanDBounded_map, IH P (hdeg ▸ hP)]

/-- The rank matters: for `B = 1` and `P = 1`, rank one gives `1 - T` and the minimal rank zero
gives `1`. -/
example : colemanDBounded 1 0 (1 : ℤ[X]) 1 = 1 - X ∧ colemanD (1 : ℤ[X]) 1 = 1 := by
  refine ⟨?_, by simp [colemanD_def]⟩
  simpa using colemanDBounded_one_one (B := (1 : ℤ[X])) (m := 0) (by simp)

end TauCeti

namespace Matrix

open TauCeti

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Spectral mapping for Coleman's transform: for a square matrix `A` and a polynomial `B` of
degree at most `m`, `det (1 - T B(A)) = D_{n,m}(B, det (1 - T A))`, where the rank `n` is the size
of `A`. -/
theorem charpolyRev_aeval_eq_colemanDBounded (A : Matrix ι ι R) {m : ℕ} {B : R[X]}
    (hB : B.natDegree ≤ m) :
    (aeval A B).charpolyRev = colemanDBounded (Fintype.card ι) m B A.charpolyRev := by
  rw [colemanDBounded_def, charpolyRev_eq_reflect A, reflect_reflect, ← charpoly_map,
    ← det_aeval_eq_resultant_charpoly _ _ (natDegree_one_sub_C_X_mul_map_C_le B hB), charpolyRev,
    map_sub, map_one, map_mul, aeval_C, ← map_aeval, Algebra.smul_def]

end Matrix

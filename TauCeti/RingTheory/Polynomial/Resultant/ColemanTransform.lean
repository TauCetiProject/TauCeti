/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Tactic.ComputeDegree

/-!
# Coleman's spectral transform of prescribed rank

Let `P` be a polynomial with `P(0) = 1` and `deg P ≤ n`, and let `B` be a polynomial with
`deg B ≤ m`. Coleman's transform of prescribed rank is

`D_(n,m)(B, P)(T) = Res_X(reflect n P (X), 1 - T B(X))`,

the resultant being taken with the degree bounds `n` and `m`. If `P = ∏ᵢ (1 - αᵢ X)` is the
determinant `det(1 - X A)` of an `n × n` matrix `A` with eigenvalues `αᵢ` (some of which may
vanish), then `reflect n P = ∏ᵢ (X - αᵢ)` and `D_(n,m)(B, P) = ∏ᵢ (1 - B(αᵢ) T)` is the
determinant `det(1 - T B(A))`. The rank `n` must therefore be the dimension, not the degree
of `P`: every zero eigenvalue contributes a factor `1 - B(0) T`. This transform is the finite
model for the spectral mapping theorem `det(1 - T B(u)) = D(B, det(1 - T u))` for compact
operators `u` over nonarchimedean coefficient rings.

All identities here hold over an arbitrary commutative ring, including rings with nilpotents.

## Main definitions

* `TauCeti.colemanDBounded n m B P`: the transform `D_(n,m)(B, P)`.
* `TauCeti.colemanD B P`: the transform at the minimal rank `deg P` and degree bound `deg B`.

## Main results

* `TauCeti.colemanDBounded_of_natDegree_le`: independence of the degree bound `m` once it
  bounds `deg B`.
* `TauCeti.colemanDBounded_mul`: multiplicativity in `P`, with addition of ranks.
* `TauCeti.colemanDBounded_succ` and `TauCeti.colemanDBounded_add`: raising the rank multiplies
  by powers of `1 - B(0) T`; `TauCeti.colemanDBounded_add_of_coeff_zero`: the rank does not
  matter when `B(0) = 0`.
* `TauCeti.colemanDBounded_multiset_prod`: `D_(n,m)(B, ∏ (1 - αᵢ X)) = ∏ (1 - B(αᵢ) T)`.
* `TauCeti.colemanDBounded_map`: compatibility with coefficient ring homomorphisms.
* `TauCeti.colemanDBounded_X`: `D_(n,m)(X, P) = P`.
* `TauCeti.colemanD_eq_colemanDBounded`: comparison of the minimal-rank and bounded transforms.

## References

* R. F. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  417–479, Appendix A3.
-/

public section

open Polynomial

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S]

/-- *Coleman's transform of prescribed rank* `D_(n,m)(B, P)(T) = Res_X(reflect n P, 1 - T B)`,
the resultant of `reflect n P` and `1 - T B(X)` taken with the degree bounds `n` and `m`.
For `P = ∏ᵢ (1 - αᵢ X)` with `n` factors it is `∏ᵢ (1 - B(αᵢ) T)`
(`colemanDBounded_multiset_prod`). It is meaningful when `P(0) = 1`, `deg P ≤ n` and
`deg B ≤ m`. -/
noncomputable def colemanDBounded (n m : ℕ) (B P : R[X]) : R[X] :=
  ((reflect n P).map C).resultant (1 - C X * B.map C) n m

/-- Coleman's transform is the resultant of `reflect n P` and `1 - T B(X)` with degree bounds
`n` and `m`. -/
theorem colemanDBounded_def (n m : ℕ) (B P : R[X]) :
    colemanDBounded n m B P = ((reflect n P).map C).resultant (1 - C X * B.map C) n m :=
  (rfl)

variable {n n' m m' : ℕ} {B P Q : R[X]}

private theorem natDegree_one_sub_C_X_mul_map_C_le (hB : B.natDegree ≤ m) :
    (1 - C X * B.map C : R[X][X]).natDegree ≤ m := by
  refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
  exact (natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hB)

private theorem natDegree_map_C_reflect_le (hP : P.natDegree ≤ n) :
    ((reflect n P).map C : R[X][X]).natDegree ≤ n :=
  natDegree_map_le.trans (natDegree_reflect_le.trans (max_le le_rfl hP))

private theorem coeff_map_C_reflect_self (hP0 : P.coeff 0 = 1) :
    ((reflect n P).map C : R[X][X]).coeff n = 1 := by
  simp [coeff_reflect, hP0]

private theorem natDegree_map_C_reflect [Nontrivial R] (hP : P.natDegree ≤ n)
    (hP0 : P.coeff 0 = 1) : ((reflect n P).map C : R[X][X]).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_map_C_reflect_le hP)
    (by simp [coeff_map_C_reflect_self hP0])

/-- Evaluating Coleman's transform at `T = t` gives the resultant of `reflect n P` and
`1 - t B`. -/
theorem eval_colemanDBounded (t : R) :
    (colemanDBounded n m B P).eval t = (reflect n P).resultant (1 - C t * B) n m := by
  rw [colemanDBounded_def, ← coe_evalRingHom, ← resultant_map_map]
  congr 1
  · rw [Polynomial.map_map, show (evalRingHom t).comp C = RingHom.id R by ext; simp, map_id]
  · simp [Polynomial.map_map, show (evalRingHom t).comp C = RingHom.id R by ext; simp]

/-- Coleman's transform is normalised: its constant coefficient is `P(0) ^ m = 1`. -/
@[simp]
theorem coeff_zero_colemanDBounded (hP0 : P.coeff 0 = 1) :
    (colemanDBounded n m B P).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_colemanDBounded, map_zero, zero_mul, sub_zero,
    resultant_one_right, coeff_reflect, revAt_le le_rfl, Nat.sub_self, hP0, one_pow]

/-- Coleman's transform commutes with coefficient ring homomorphisms. -/
theorem colemanDBounded_map (φ : R →+* S) :
    (colemanDBounded n m B P).map φ = colemanDBounded n m (B.map φ) (P.map φ) := by
  have hC : (mapRingHom φ).comp C = C.comp φ := by ext; simp
  rw [colemanDBounded_def, colemanDBounded_def, ← coe_mapRingHom, ← resultant_map_map]
  congr 1
  · rw [Polynomial.map_map, hC, ← Polynomial.map_map, coe_mapRingHom, reflect_map]
  · rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, Polynomial.map_map, hC,
      ← Polynomial.map_map, coe_mapRingHom, map_X]

/-- Coleman's transform does not depend on the degree bound `m`, once it bounds `deg B`. -/
theorem colemanDBounded_of_natDegree_le (hB : B.natDegree ≤ m) (hm : m ≤ m')
    (hP0 : P.coeff 0 = 1) : colemanDBounded n m' B P = colemanDBounded n m B P := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [colemanDBounded_def, colemanDBounded_def,
    resultant_add_right_deg _ _ _ _ _ (natDegree_one_sub_C_X_mul_map_C_le hB),
    coeff_map_C_reflect_self hP0, one_pow, one_mul]

/-- Coleman's transform is multiplicative in `P`, the ranks adding. -/
theorem colemanDBounded_mul (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n')
    (hP0 : P.coeff 0 = 1) (hQ0 : Q.coeff 0 = 1) (hB : B.natDegree ≤ m) :
    colemanDBounded (n + n') m B (P * Q) =
      colemanDBounded n m B P * colemanDBounded n' m B Q := by
  nontriviality R
  have h := resultant_mul_left ((reflect n P).map C) ((reflect n' Q).map C) _ m
    (natDegree_one_sub_C_X_mul_map_C_le hB)
  rw [natDegree_map_C_reflect hP hP0, natDegree_map_C_reflect hQ hQ0] at h
  rw [colemanDBounded_def, colemanDBounded_def, colemanDBounded_def, reflect_mul _ _ hP hQ,
    Polynomial.map_mul, h]

/-- At `P = 1`, Coleman's transform of rank `n` is `(1 - B(0) T) ^ n`: each of the `n` zero
eigenvalues contributes a factor `1 - B(0) T`. -/
theorem colemanDBounded_one (hB : B.natDegree ≤ m) :
    colemanDBounded n m B 1 = (1 - C (B.coeff 0) * X) ^ n := by
  rw [colemanDBounded_def, reflect_one, Polynomial.map_pow, map_X,
    resultant_X_pow_left _ _ _ (natDegree_one_sub_C_X_mul_map_C_le hB), coeff_sub, coeff_one_zero,
    coeff_C_mul, coeff_map, mul_comm]

/-- Raising the rank by `k` multiplies Coleman's transform by `(1 - B(0) T) ^ k`. -/
theorem colemanDBounded_add (k : ℕ) (hP : P.natDegree ≤ n) (hB : B.natDegree ≤ m)
    (hP0 : P.coeff 0 = 1) :
    colemanDBounded (n + k) m B P = (1 - C (B.coeff 0) * X) ^ k * colemanDBounded n m B P := by
  rw [← mul_one P, colemanDBounded_mul hP (by simp) hP0 (by simp) hB, colemanDBounded_one hB,
    mul_one, mul_comm]

/-- The padding identity `D_(n+1,m)(B, P) = (1 - B(0) T) D_(n,m)(B, P)`. -/
theorem colemanDBounded_succ (hP : P.natDegree ≤ n) (hB : B.natDegree ≤ m)
    (hP0 : P.coeff 0 = 1) :
    colemanDBounded (n + 1) m B P = (1 - C (B.coeff 0) * X) * colemanDBounded n m B P := by
  rw [colemanDBounded_add 1 hP hB hP0, pow_one]

/-- When `B(0) = 0`, Coleman's transform does not depend on the rank. -/
theorem colemanDBounded_add_of_coeff_zero (k : ℕ) (hP : P.natDegree ≤ n)
    (hB : B.natDegree ≤ m) (hP0 : P.coeff 0 = 1) (hB0 : B.coeff 0 = 0) :
    colemanDBounded (n + k) m B P = colemanDBounded n m B P := by
  rw [colemanDBounded_add k hP hB hP0, hB0, map_zero, zero_mul, sub_zero, one_pow, one_mul]

/-- Coleman's transform of the linear factor `1 - a X` of rank one is `1 - B(a) T`. -/
theorem colemanDBounded_one_sub_C_mul_X (a : R) (hB : B.natDegree ≤ m) :
    colemanDBounded 1 m B (1 - C a * X) = 1 - C (B.eval a) * X := by
  have h : reflect 1 (1 - C a * X) = X - C a := by
    rw [reflect_sub, reflect_one, ← pow_one X, reflect_C_mul_X_pow]
    simp
  rw [colemanDBounded_def, h, Polynomial.map_sub, map_X, map_C,
    resultant_X_sub_C_left _ _ _ (natDegree_one_sub_C_X_mul_map_C_le hB)]
  rw [eval_sub, eval_one, eval_mul, eval_C, eval_map, eval₂_at_apply, mul_comm]

/-- Spectral mapping for split `P`: if `P = ∏ (1 - αᵢ X)` over a multiset of `n` scalars `αᵢ`,
then `D_(n,m)(B, P) = ∏ (1 - B(αᵢ) T)`. -/
theorem colemanDBounded_multiset_prod (s : Multiset R) (hB : B.natDegree ≤ m) :
    colemanDBounded (Multiset.card s) m B (s.map fun a ↦ 1 - C a * X).prod =
      (s.map fun a ↦ 1 - C (B.eval a) * X).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [colemanDBounded_one hB]
  | cons a s ih =>
    have hdeg : (s.map fun a ↦ 1 - C a * X).prod.natDegree ≤ Multiset.card s := by
      refine natDegree_multiset_prod_le _ |>.trans ?_
      rw [Multiset.map_map]
      refine (Multiset.sum_le_card_nsmul _ 1 ?_).trans (by simp)
      simp only [Multiset.mem_map, Function.comp_apply, forall_exists_index, and_imp]
      rintro _ b - rfl
      compute_degree
    have hcoeff : (s.map fun a ↦ 1 - C a * X).prod.coeff 0 = 1 := by
      refine coeff_zero_multiset_prod _ |>.trans (Multiset.prod_eq_one fun x hx ↦ ?_)
      obtain ⟨_, hf, rfl⟩ := Multiset.mem_map.1 hx
      obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 hf
      simp
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, add_comm,
      colemanDBounded_mul (by compute_degree) hdeg (by simp) hcoeff hB,
      colemanDBounded_one_sub_C_mul_X a hB, ih, Multiset.map_cons, Multiset.prod_cons]

/-- For constant `B = b`, Coleman's transform of rank `n` is `(1 - b T) ^ n`, whatever `P`. -/
theorem colemanDBounded_C (b : R) (hP0 : P.coeff 0 = 1) :
    colemanDBounded n m (C b) P = (1 - C b * X) ^ n := by
  rw [colemanDBounded_def, map_C, ← C_mul, ← C_1, ← C_sub, resultant_C_right,
    coeff_map_C_reflect_self hP0, one_pow, one_mul, mul_comm X]

/-- At `B = 0`, Coleman's transform is `1`. -/
@[simp]
theorem colemanDBounded_zero (hP0 : P.coeff 0 = 1) : colemanDBounded n m 0 P = 1 := by
  have h := colemanDBounded_C (n := n) (m := m) (0 : R) hP0
  rwa [map_zero, zero_mul, sub_zero, one_pow] at h

/-- At `B = X`, Coleman's transform returns `P`: `D_(n,m)(X, P) = P`. -/
theorem colemanDBounded_X (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1) (hm : 1 ≤ m) :
    colemanDBounded n m X P = P := by
  rw [colemanDBounded_of_natDegree_le natDegree_X_le hm hP0]
  -- Over the Laurent polynomials, where `T` is invertible, `1 - T X = -T (X - T⁻¹)`, and the
  -- resultant becomes `T ^ n * (reflect n P)(T⁻¹) = P(T)`.
  let φ : R[X] →+* LaurentPolynomial R := Polynomial.toLaurent
  refine (Polynomial.toLaurent_injective : Function.Injective φ) ?_
  have hφ : ∀ p : R[X], φ p = eval₂ LaurentPolynomial.C (LaurentPolynomial.T 1) p := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial k a => simp [φ, ← C_mul_X_pow_eq_monomial, LaurentPolynomial.T_pow]
  have hg : (1 - C X * (X : R[X]).map C : R[X][X]).map φ =
      C (-LaurentPolynomial.T 1) * (X - C (⅟(LaurentPolynomial.T 1))) := by
    rw [mul_sub, ← C_mul, neg_mul, mul_invOf_self]
    simp [φ]
    ring
  rw [colemanDBounded_def, ← resultant_map_map, hg, resultant_C_mul_right,
    resultant_X_sub_C_right _ _ _ ((natDegree_map_le).trans (natDegree_map_C_reflect_le hP)),
    Polynomial.map_map, eval_map, hφ, ← eval₂_reflect_mul_pow _ _ n P hP]
  have hC : φ.comp C = LaurentPolynomial.C := by ext; simp [φ]
  rw [hC, ← mul_assoc, ← mul_pow, neg_mul_neg, mul_one, mul_comm]

/-- *Coleman's transform at minimal rank*: `colemanDBounded` at the rank `deg P` and degree bound
`deg B`. A finite matrix must instead use `colemanDBounded` at its dimension, which may exceed
`deg P` because of zero eigenvalues (`colemanDBounded_eq_pow_mul_colemanD`). -/
noncomputable def colemanD (B P : R[X]) : R[X] :=
  colemanDBounded P.natDegree B.natDegree B P

/-- The minimal-rank transform is `colemanDBounded` at rank `deg P` and degree bound `deg B`. -/
theorem colemanD_def (B P : R[X]) : colemanD B P = colemanDBounded P.natDegree B.natDegree B P :=
  (rfl)

/-- The minimal-rank transform is `colemanDBounded` at rank `deg P` and any degree bound
`m ≥ deg B`. -/
theorem colemanD_eq_colemanDBounded (hB : B.natDegree ≤ m) (hP0 : P.coeff 0 = 1) :
    colemanD B P = colemanDBounded P.natDegree m B P := by
  rw [colemanD_def, colemanDBounded_of_natDegree_le le_rfl hB hP0]

/-- The transform of rank `n ≥ deg P` is the minimal-rank transform times
`(1 - B(0) T) ^ (n - deg P)`. -/
theorem colemanDBounded_eq_pow_mul_colemanD (hP : P.natDegree ≤ n) (hB : B.natDegree ≤ m)
    (hP0 : P.coeff 0 = 1) :
    colemanDBounded n m B P = (1 - C (B.coeff 0) * X) ^ (n - P.natDegree) * colemanD B P := by
  rw [colemanD_eq_colemanDBounded hB hP0, ← colemanDBounded_add _ le_rfl hB hP0,
    Nat.add_sub_cancel' hP]

end TauCeti

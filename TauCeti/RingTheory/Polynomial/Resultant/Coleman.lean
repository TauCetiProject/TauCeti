/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.LinearAlgebra.Matrix.Polynomial
import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Coleman's finite spectral transform

Let `R` be a commutative ring, `P B : R[X]` with `P.coeff 0 = 1`, `P.natDegree ≤ n` and
`B.natDegree ≤ m`. Coleman's transform of rank `n` is the polynomial

`D_(n,m)(B, P)(T) = Res_X (reflect n P (X), 1 - T B(X))`,

a resultant over `R[T]` with the degree bounds `n` and `m` (`Polynomial.colemanDBounded`).
If `P = ∏ (1 - αᵢ T)` is a product of `n` linear factors, then `reflect n P = ∏ (X - αᵢ)` and
`D_(n,m)(B, P) = ∏ (1 - B(αᵢ) T)` (`Polynomial.colemanDBounded_prod_one_sub_C_mul_X`). Thus, for
`P = det (1 - T A)` with `A` an `n × n` matrix, the transform is meant to compute
`det (1 - T B(A))` from `P` alone, without access to `A` or to its eigenvalues. This is the
polynomial form of the spectral mapping for Fredholm determinants of compact operators.

The rank is part of the data. The reversal is taken in the specified degree `n`, not in the
actual degree of `P`, so that zero eigenvalues are kept: raising the rank by one multiplies by
the factor `1 - B(0) T` of a new zero eigenvalue (`Polynomial.colemanDBounded_succ`). The rank is
therefore irrelevant when `B(0) = 0` (`Polynomial.colemanDBounded_add_of_coeff_zero`), and the
minimal-rank transform `Polynomial.colemanD` then agrees with every bounded one
(`Polynomial.colemanD_eq_colemanDBounded`). The bound `m` is irrelevant once it bounds the
degree of `B` (`Polynomial.colemanDBounded_of_natDegree_le`).

## Main results

* `Polynomial.colemanDBounded_of_natDegree_le`: independence of the degree bound for `B`.
* `Polynomial.colemanDBounded_succ`, `Polynomial.colemanDBounded_add`: padding the rank.
* `Polynomial.colemanDBounded_mul`: multiplicativity in `P`, with addition of ranks.
* `Polynomial.colemanDBounded_map`: compatibility with coefficient ring homomorphisms.
* `Polynomial.natDegree_colemanDBounded_le`, `Polynomial.coeff_zero_colemanDBounded`: the transform
  of rank `n` has degree at most `n` and constant coefficient one.
* `Polynomial.colemanDBounded_prod_one_sub_C_mul_X`: the transform of a product of linear
  factors.
* `Polynomial.colemanDBounded_X_left`, `Polynomial.colemanDBounded_zero_left`,
  `Polynomial.colemanDBounded_one_right`: the values `D(T, P) = P`, `D(0, P) = 1` and
  `D(B, 1) = (1 - B(0) T) ^ n`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A3.
-/

public section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Coleman's transform of rank `n`: for `P` with `P.coeff 0 = 1` and `P.natDegree ≤ n`, and `B`
with `B.natDegree ≤ m`, the polynomial `Res_X (reflect n P (X), 1 - T B(X))` in `T`, a resultant
over `R[T]` with degree bounds `n` and `m`. If `P = ∏ (1 - αᵢ T)` over `n` factors, it is
`∏ (1 - B(αᵢ) T)`. The resultant is defined for all `B`, `P`, `n` and `m`; the hypotheses are
those under which it has this meaning. -/
noncomputable def colemanDBounded (B P : R[X]) (n m : ℕ) : R[X] :=
  resultant ((P.reflect n).map C) (1 - C X * B.map C) n m

/-- Coleman's transform at the minimal rank `P.natDegree` and degree bound `B.natDegree`. -/
noncomputable def colemanD (B P : R[X]) : R[X] :=
  colemanDBounded B P P.natDegree B.natDegree

theorem colemanDBounded_def (B P : R[X]) (n m : ℕ) :
    colemanDBounded B P n m = resultant ((P.reflect n).map C) (1 - C X * B.map C) n m := by
  rw [colemanDBounded]

theorem colemanD_def (B P : R[X]) :
    colemanD B P = colemanDBounded B P P.natDegree B.natDegree := by
  rw [colemanD]

section Auxiliary

variable {B P : R[X]} {n : ℕ}

private theorem natDegree_map_reflect_le (hP : P.natDegree ≤ n) :
    ((P.reflect n).map C).natDegree ≤ n :=
  natDegree_map_le.trans (natDegree_reflect_le.trans (max_le le_rfl hP))

private theorem coeff_map_reflect_self (P : R[X]) (n : ℕ) :
    ((P.reflect n).map C).coeff n = C (P.coeff 0) := by
  rw [coeff_map, coeff_reflect, revAt_le le_rfl, Nat.sub_self]

private theorem natDegree_one_sub_C_X_mul_le (B : R[X]) :
    (1 - C X * B.map C).natDegree ≤ B.natDegree :=
  (natDegree_sub_le _ _).trans (max_le (by simp)
    ((natDegree_C_mul_le _ _).trans natDegree_map_le))

private theorem coeff_zero_one_sub_C_X_mul (B : R[X]) :
    (1 - C X * B.map C).coeff 0 = 1 - C (B.coeff 0) * X := by
  rw [coeff_sub, coeff_one_zero, coeff_C_mul, coeff_map, mul_comm]

end Auxiliary

variable {B P : R[X]} {n m : ℕ}

/-- Raising the degree bound for `B` does not change Coleman's transform. -/
theorem colemanDBounded_add_right_deg (hB : B.natDegree ≤ m) (hP0 : P.coeff 0 = 1) (k : ℕ) :
    colemanDBounded B P n (m + k) = colemanDBounded B P n m := by
  rw [colemanDBounded, resultant_add_right_deg _ _ _ _ _
    ((natDegree_one_sub_C_X_mul_le B).trans hB)]
  simp [hP0, colemanDBounded]

/-- Coleman's transform does not depend on the chosen bound for the degree of `B`. -/
theorem colemanDBounded_of_natDegree_le (hB : B.natDegree ≤ m) (hP0 : P.coeff 0 = 1) :
    colemanDBounded B P n m = colemanDBounded B P n B.natDegree := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hB
  exact colemanDBounded_add_right_deg le_rfl hP0 k

/-- Padding the rank by one multiplies Coleman's transform by `1 - B(0) T`, the factor of an
additional zero eigenvalue. -/
theorem colemanDBounded_succ (hP : P.natDegree ≤ n) (hB : B.natDegree ≤ m) :
    colemanDBounded B P (n + 1) m = (1 - C (B.coeff 0) * X) * colemanDBounded B P n m := by
  have hX : P.reflect (n + 1) = X * P.reflect n := by
    simpa [reflect_one, add_comm 1 n] using reflect_mul (1 : R[X]) P (F := 1) (by simp) hP
  -- the resultant with `X` at degree bound one is the constant coefficient
  have hXres : X.resultant (1 - C X * B.map C) 1 m = 1 - C (B.coeff 0) * X := by
    have h := resultant_X_pow_left _ 1 m ((natDegree_one_sub_C_X_mul_le B).trans hB)
    rwa [pow_one, pow_one, coeff_zero_one_sub_C_X_mul] at h
  rw [colemanDBounded, hX, Polynomial.map_mul, map_X, add_comm n 1,
    resultant_mul_left_of_natDegree_le natDegree_X_le (natDegree_map_reflect_le hP)
      ((natDegree_one_sub_C_X_mul_le B).trans hB), hXres, colemanDBounded]

/-- Padding the rank by `k` multiplies Coleman's transform by `(1 - B(0) T) ^ k`. -/
theorem colemanDBounded_add (hP : P.natDegree ≤ n) (hB : B.natDegree ≤ m) (k : ℕ) :
    colemanDBounded B P (n + k) m = (1 - C (B.coeff 0) * X) ^ k * colemanDBounded B P n m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, colemanDBounded_succ (hP.trans (Nat.le_add_right n k)) hB, ih, pow_succ',
      mul_assoc]

/-- When `B(0) = 0`, Coleman's transform does not depend on the rank. -/
theorem colemanDBounded_add_of_coeff_zero (hP : P.natDegree ≤ n) (hB : B.natDegree ≤ m)
    (hB0 : B.coeff 0 = 0) (k : ℕ) :
    colemanDBounded B P (n + k) m = colemanDBounded B P n m := by
  simp [colemanDBounded_add hP hB, hB0]

/-- When `B(0) = 0`, every bounded Coleman transform equals the minimal-rank transform. -/
theorem colemanD_eq_colemanDBounded (hP : P.natDegree ≤ n) (hB : B.natDegree ≤ m)
    (hP0 : P.coeff 0 = 1) (hB0 : B.coeff 0 = 0) :
    colemanDBounded B P n m = colemanD B P := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hP
  rw [colemanDBounded_add_of_coeff_zero le_rfl hB hB0, colemanDBounded_of_natDegree_le hB hP0,
    colemanD]

/-- Coleman's transform is multiplicative in `P`, the ranks adding. -/
theorem colemanDBounded_mul {P₁ P₂ : R[X]} {n₁ n₂ : ℕ} (hP₁ : P₁.natDegree ≤ n₁)
    (hP₂ : P₂.natDegree ≤ n₂) (hB : B.natDegree ≤ m) :
    colemanDBounded B (P₁ * P₂) (n₁ + n₂) m =
      colemanDBounded B P₁ n₁ m * colemanDBounded B P₂ n₂ m := by
  rw [colemanDBounded, reflect_mul _ _ hP₁ hP₂, Polynomial.map_mul,
    resultant_mul_left_of_natDegree_le (natDegree_map_reflect_le hP₁)
      (natDegree_map_reflect_le hP₂) ((natDegree_one_sub_C_X_mul_le B).trans hB),
    colemanDBounded, colemanDBounded]

/-- Coleman's transform commutes with coefficient ring homomorphisms. -/
@[simp]
theorem colemanDBounded_map (φ : R →+* S) (B P : R[X]) (n m : ℕ) :
    (colemanDBounded B P n m).map φ = colemanDBounded (B.map φ) (P.map φ) n m := by
  rw [colemanDBounded, colemanDBounded, ← coe_mapRingHom, ← resultant_map_map]
  congr 1
  · simp only [coe_mapRingHom, reflect_map, Polynomial.map_map, mapRingHom_comp_C]
  · simp [Polynomial.map_map, mapRingHom_comp_C]

/-- Coleman's transform of rank `n` is a polynomial of degree at most `n`. -/
theorem natDegree_colemanDBounded_le (B P : R[X]) (n m : ℕ) :
    (colemanDBounded B P n m).natDegree ≤ n := by
  -- the first `n` columns of the Sylvester matrix hold the coefficients of `1 - T B`, which are
  -- of degree at most one in `T`; the other `m` columns hold constants
  have key := Matrix.natDegree_det_le_of_natDegree_le
    (sylvester ((P.reflect n).map C) (1 - C X * B.map C) n m)
    (fun j ↦ Fin.addCases (fun _ ↦ 1) (fun _ ↦ 0) j) fun i j ↦ by
      induction j using Fin.addCases with
      | left j =>
        simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
        split_ifs
        · rw [coeff_sub, coeff_C_mul, coeff_map]
          refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
          · rw [coeff_one]
            split_ifs <;> simp
          · exact natDegree_mul_le.trans (by rw [natDegree_C, add_zero]; exact natDegree_X_le)
        · simp
      | right j =>
        simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
        split_ifs <;> simp
  rw [colemanDBounded, resultant]
  simpa [Fin.sum_univ_add] using key

/-- Coleman's transform has constant coefficient one. -/
theorem coeff_zero_colemanDBounded (hP0 : P.coeff 0 = 1) (B : R[X]) (n m : ℕ) :
    (colemanDBounded B P n m).coeff 0 = 1 := by
  -- `simp` cannot rewrite the arguments of `resultant`, whose degree bounds are `optParam`s
  -- depending on them, so the evaluations at `T = 0` are computed separately
  have hC : (evalRingHom (0 : R)).comp C = RingHom.id R := by ext; simp
  have hf : ((P.reflect n).map C).map (evalRingHom 0) = P.reflect n := by
    simp [Polynomial.map_map, hC]
  have hg : (1 - C X * B.map C).map (evalRingHom (0 : R)) = 1 := by simp
  rw [coeff_zero_eq_eval_zero, ← coe_evalRingHom, colemanDBounded, ← resultant_map_map, hf, hg,
    resultant_one_right]
  simp [coeff_reflect, hP0]

/-- With `B = T`, Coleman's transform returns `P`: the eigenvalues are unchanged. -/
@[simp]
theorem colemanDBounded_X_left (hP : P.natDegree ≤ n) : colemanDBounded X P n 1 = P := by
  rw [colemanDBounded, map_X, resultant_one_sub_C_mul_X_right _ _ (natDegree_map_reflect_le hP),
    reflect_map, reflect_reflect, eval_map, eval₂_C_X]

/-- With `B = 0`, Coleman's transform is one. -/
@[simp]
theorem colemanDBounded_zero_left (hP0 : P.coeff 0 = 1) (n m : ℕ) :
    colemanDBounded 0 P n m = 1 := by
  rw [colemanDBounded, Polynomial.map_zero, mul_zero, sub_zero, resultant_one_right,
    coeff_map_reflect_self, hP0, C_1, one_pow]

/-- With `P = 1`, all `n` eigenvalues are zero, and Coleman's transform is `(1 - B(0) T) ^ n`. -/
@[simp]
theorem colemanDBounded_one_right (hB : B.natDegree ≤ m) (n : ℕ) :
    colemanDBounded B 1 n m = (1 - C (B.coeff 0) * X) ^ n := by
  rw [colemanDBounded, reflect_one, Polynomial.map_pow, map_X,
    resultant_X_pow_left _ _ _ ((natDegree_one_sub_C_X_mul_le B).trans hB),
    coeff_zero_one_sub_C_X_mul]

/-- Coleman's transform of a single factor `1 - α T` is `1 - B(α) T`. -/
theorem colemanDBounded_one_sub_C_mul_X (hB : B.natDegree ≤ m) (α : R) :
    colemanDBounded B (1 - C α * X) 1 m = 1 - C (B.eval α) * X := by
  have hr : (1 - C α * X).reflect 1 = X - C α := by simp
  rw [colemanDBounded, hr, Polynomial.map_sub, map_X, map_C,
    resultant_X_sub_C_left _ _ _ ((natDegree_one_sub_C_X_mul_le B).trans hB), eval_sub, eval_one,
    eval_mul, eval_C, eval_map, eval₂_hom, mul_comm]

/-- If `P = ∏ (1 - αᵢ T)` has one factor for each unit of rank, Coleman's transform is
`∏ (1 - B(αᵢ) T)`: it replaces each inverse root `αᵢ` by `B(αᵢ)`. -/
theorem colemanDBounded_prod_one_sub_C_mul_X {ι : Type*} (s : Finset ι) (α : ι → R)
    (hB : B.natDegree ≤ m) :
    colemanDBounded B (∏ i ∈ s, (1 - C (α i) * X)) s.card m =
      ∏ i ∈ s, (1 - C (B.eval (α i)) * X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [colemanDBounded_one_right hB]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      add_comm, colemanDBounded_mul (natDegree_one_sub_C_mul_X_le _) ?_ hB,
      colemanDBounded_one_sub_C_mul_X hB, ih]
    exact (natDegree_prod_le _ _).trans
      (by simpa using Finset.sum_le_sum fun i _ ↦ natDegree_one_sub_C_mul_X_le (α i))

end Polynomial

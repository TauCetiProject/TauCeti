/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Topology.Algebra.MvPolynomial
import TauCeti.Algebra.Polynomial.Degree.Operations
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.LinearAlgebra.Matrix.Charpoly.Resultant
import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse
import TauCeti.LinearAlgebra.Matrix.Polynomial
import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Coleman's finite spectral transform

Let `R` be a commutative ring, `P B : R[X]` with `P.coeff 0 = 1`, `P.natDegree ≤ n` and
`B.natDegree ≤ m`. Coleman's transform of rank `n` is the polynomial

`D_(n,m)(B, P)(T) = Res_X (reflect n P (X), 1 - T B(X))`,

a resultant over `R[T]` with the degree bounds `n` and `m` (`Polynomial.colemanDBounded`).
If `P = ∏ (1 - αᵢ T)` is a product of `n` linear factors, then `reflect n P = ∏ (X - αᵢ)` and
`D_(n,m)(B, P) = ∏ (1 - B(αᵢ) T)` (`Polynomial.colemanDBounded_prod_one_sub_C_mul_X`). For
`P = det (1 - T A)` with `A` an `n × n` matrix over any commutative ring, the transform computes
`det (1 - T B(A))` from `P` alone, without access to `A` or to its eigenvalues
(`Matrix.colemanDBounded_charpolyRev`). This is the polynomial form of the spectral mapping
for Fredholm determinants of compact operators.

The rank is part of the data. The reversal is taken in the specified degree `n`, not in the
actual degree of `P`, so that zero eigenvalues are kept: raising the rank by one multiplies by
the factor `1 - B(0) T` of a new zero eigenvalue (`Polynomial.colemanDBounded_succ`). The rank is
therefore irrelevant when `B(0) = 0` (`Polynomial.colemanDBounded_add_of_coeff_zero`), and the
minimal-rank transform `Polynomial.colemanD` then agrees with every bounded one
(`Polynomial.colemanD_eq_colemanDBounded`). The bound `m` is irrelevant once it bounds the
degree of `B` (`Polynomial.colemanDBounded_of_natDegree_le`).

Evaluating the transform at a scalar `t` gives the resultant over `R` of `reflect n P` and
`1 - t B` (`Polynomial.eval_colemanDBounded`). For a polynomial `Q` with `Q(0) = 1` and invertible
leading coefficient, and `c` the inverse of that coefficient, the polynomial `B = 1 - c Q*` built
from the reversal `Q* = Q.reverse` vanishes at `0` and sends every inverse root of `Q` to `1`.
Accordingly `D(B, Q) = (1 - T) ^ deg Q` (`Polynomial.colemanDSeries_one_sub_C_mul_reverse_self`),
while the value at `T = 1` of the transform of any `F` is the resultant of the monic polynomial
`c Q` and `F` (`Polynomial.eval_one_colemanDBounded_one_sub_C_mul_reflect`), a unit exactly when
`Q` and `F` are coprime (`Polynomial.isUnit_eval_one_colemanDBounded_one_sub_C_mul_reverse_iff`).
So if a Fredholm determinant factors as `Q S`, its transform along `B` is `(1 - T) ^ deg Q` times
the transform of `S`. For a polynomial `S` with `S(0) = 1` the latter is a unit at `T = 1` exactly
when `Q` and `S` are coprime: a coprime polynomial factor becomes a zero of order `deg Q` at one.

When `B(0) = 0`, the `k`-th coefficient of `D_(n,m)(B, P)` only involves the coefficients of `P`
of index at most `k m` (`Polynomial.coeff_colemanDBounded_congr`): in the Leibniz expansion of
the Sylvester matrix, a term contributing to `Tᵏ` moves exactly `k` of the first `n` columns down,
each by at most `m` rows, so the columns carrying the coefficients of `P` move up by at most `k m`
rows in total. Hence Coleman's transform extends to a power series input `F`: the series
`Polynomial.colemanDSeries B F` has as `k`-th coefficient that of `D_(N,m)(B, trunc (N + 1) F)`
for any `N ≥ k m`. It is multiplicative in `F` (`Polynomial.colemanDSeries_mul`), agrees with the
polynomial transform on polynomials (`Polynomial.colemanDSeries_coe`), and each of its
coefficients is a polynomial, hence continuous, function of finitely many coefficients of `F`
(`Polynomial.continuous_coeff_colemanDSeries`). This is the transform computing Fredholm
determinants of polynomials in compact operators.

## Main results

* `Polynomial.colemanDBounded_of_natDegree_le`: independence of the degree bound for `B`.
* `Polynomial.colemanDBounded_succ`, `Polynomial.colemanDBounded_add`: padding the rank.
* `Polynomial.colemanDBounded_mul`: multiplicativity in `P`, with addition of ranks.
* `Polynomial.colemanDBounded_map`: compatibility with coefficient ring homomorphisms.
* `Polynomial.natDegree_colemanDBounded_le`, `Polynomial.coeff_zero_colemanDBounded`: the transform
  of rank `n` has degree at most `n` and constant coefficient one.
* `Polynomial.colemanDBounded_prod_one_sub_C_mul_X`: the transform of a product of linear
  factors.
* `Matrix.colemanDBounded_charpolyRev`: finite matrix spectral mapping,
  `D_(n,m)(B, det (1 - T A)) = det (1 - T B(A))` for an `n × n` matrix `A`.
* `Polynomial.colemanDBounded_X_left`, `Polynomial.colemanDBounded_zero_left`,
  `Polynomial.colemanDBounded_one_right`: the values `D(T, P) = P`, `D(0, P) = 1` and
  `D(B, 1) = (1 - B(0) T) ^ n`.
* `Polynomial.eval_colemanDBounded`: the value at `t` is `Res_(n,m)(reflect n P, 1 - t B)`.
* `Polynomial.colemanDBounded_one_sub_C_mul_reflect_self`: `D_(n,n)(1 - c P*, P) = (1 - T) ^ n`
  for the reversal `P* = reflect n P`.
* `Polynomial.eval_one_colemanDBounded_one_sub_C_mul_reflect`: the value at `T = 1` of
  `D_(n,d)(1 - c Q*, F)` is `Res_(d,n)(c Q, F)` for `Q* = reflect d Q`.
* `Polynomial.isUnit_eval_one_colemanDBounded_one_sub_C_mul_reverse_iff`: for `c` inverting the
  leading coefficient of `Q`, that value is a unit exactly when `Q` and `F` are coprime.
* `Polynomial.coeff_prod_sylvester_colemanDBounded`: the terms of the Leibniz expansion of the
  Sylvester matrix defining the transform when `B(0) = 0`.
* `Polynomial.coeff_colemanDBounded_congr`: locality of the coefficients in `P` when `B(0) = 0`.
* `Polynomial.colemanDSeries`: Coleman's transform of a power series along a polynomial `B`, with
  `Polynomial.coeff_colemanDSeries_eq_coeff_colemanDBounded`, `Polynomial.coeff_colemanDSeries`,
  `Polynomial.colemanDSeries_coe`, `Polynomial.colemanDSeries_mul` and
  `Polynomial.continuous_coeff_colemanDSeries`.
* `Polynomial.colemanDSeries_one_sub_C_mul_reverse_self`: `D(1 - c Q*, Q) = (1 - T) ^ deg Q` when
  `Q(0) = 1` and `c` inverts the leading coefficient of `Q`.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendices A3–A4.
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

variable {B P : R[X]} {n m : ℕ}

/-- The kernel `1 - T B(X)` of Coleman's transform has degree in `X` at most any bound for the
degree of `B`. -/
theorem natDegree_one_sub_C_X_mul_map_le (hB : B.natDegree ≤ m) :
    (1 - C X * B.map C).natDegree ≤ m :=
  (natDegree_one_sub_C_mul_le _ _).trans (natDegree_map_le.trans hB)

/-- Raising the degree bound for `B` does not change Coleman's transform. -/
theorem colemanDBounded_add_right_deg (hB : B.natDegree ≤ m) (hP0 : P.coeff 0 = 1) (k : ℕ) :
    colemanDBounded B P n (m + k) = colemanDBounded B P n m := by
  rw [colemanDBounded, resultant_add_right_deg _ _ _ _ _ (natDegree_one_sub_C_X_mul_map_le hB)]
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
    have h := resultant_X_pow_left _ 1 m (natDegree_one_sub_C_X_mul_map_le hB)
    rw [pow_one, pow_one] at h
    simp [h, X_mul_C]
  rw [colemanDBounded, hX, Polynomial.map_mul, map_X, add_comm n 1,
    resultant_mul_left_of_natDegree_le natDegree_X_le
      (natDegree_map_reflect_le_of_natDegree_le C hP)
      (natDegree_one_sub_C_X_mul_map_le hB),
    hXres, colemanDBounded]

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

/-- When `B(0) = 0`, the minimal-rank transform equals every bounded Coleman transform. -/
theorem colemanD_eq_colemanDBounded (hP : P.natDegree ≤ n) (hB : B.natDegree ≤ m)
    (hP0 : P.coeff 0 = 1) (hB0 : B.coeff 0 = 0) :
    colemanD B P = colemanDBounded B P n m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hP
  rw [colemanDBounded_add_of_coeff_zero le_rfl hB hB0, colemanDBounded_of_natDegree_le hB hP0,
    colemanD]

/-- Coleman's transform is multiplicative in `P`, the ranks adding. -/
theorem colemanDBounded_mul {P₁ P₂ : R[X]} {n₁ n₂ : ℕ} (hP₁ : P₁.natDegree ≤ n₁)
    (hP₂ : P₂.natDegree ≤ n₂) (hB : B.natDegree ≤ m) :
    colemanDBounded B (P₁ * P₂) (n₁ + n₂) m =
      colemanDBounded B P₁ n₁ m * colemanDBounded B P₂ n₂ m := by
  rw [colemanDBounded, reflect_mul _ _ hP₁ hP₂, Polynomial.map_mul,
    resultant_mul_left_of_natDegree_le
      (natDegree_map_reflect_le_of_natDegree_le C hP₁)
      (natDegree_map_reflect_le_of_natDegree_le C hP₂)
      (natDegree_one_sub_C_X_mul_map_le hB),
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

/-- The value of Coleman's transform at `t` is the resultant over `R` of the reversal of `P` and
`1 - t B`, with the same degree bounds. -/
theorem eval_colemanDBounded (B P : R[X]) (n m : ℕ) (t : R) :
    (colemanDBounded B P n m).eval t = resultant (P.reflect n) (1 - C t * B) n m := by
  -- `simp` cannot rewrite the arguments of `resultant`, whose degree bounds are `optParam`s
  -- depending on them, so the evaluations at `T = t` are computed separately
  have hC : (evalRingHom t).comp C = RingHom.id R := by ext; simp
  have hf : ((P.reflect n).map C).map (evalRingHom t) = P.reflect n := by
    simp [Polynomial.map_map, hC]
  have hg : (1 - C X * B.map C).map (evalRingHom t) = 1 - C t * B := by
    simp [Polynomial.map_map, hC]
  rw [← coe_evalRingHom, colemanDBounded, ← resultant_map_map, hf, hg]

/-- Coleman's transform has constant coefficient one. -/
@[simp]
theorem coeff_zero_colemanDBounded (hP0 : P.coeff 0 = 1) (B : R[X]) (n m : ℕ) :
    (colemanDBounded B P n m).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_colemanDBounded, C_0, zero_mul, sub_zero, resultant_one_right]
  simp [coeff_reflect, hP0]

/-- With `B = T`, Coleman's transform returns `P`: the eigenvalues are unchanged. -/
@[simp]
theorem colemanDBounded_X_left (hP : P.natDegree ≤ n) : colemanDBounded X P n 1 = P := by
  rw [colemanDBounded, map_X,
    resultant_one_sub_C_mul_X_right _ _ (natDegree_map_reflect_le_of_natDegree_le C hP),
    reflect_map, reflect_reflect, eval_map, eval₂_C_X]

/-- With `B = 0`, Coleman's transform is one. -/
@[simp]
theorem colemanDBounded_zero_left (hP0 : P.coeff 0 = 1) (n m : ℕ) :
    colemanDBounded 0 P n m = 1 := by
  rw [colemanDBounded, Polynomial.map_zero, mul_zero, sub_zero, resultant_one_right,
    coeff_map, coeff_reflect_self, hP0, C_1, one_pow]

/-- With `P = 1`, all `n` eigenvalues are zero, and Coleman's transform is `(1 - B(0) T) ^ n`. -/
@[simp]
theorem colemanDBounded_one_right (hB : B.natDegree ≤ m) (n : ℕ) :
    colemanDBounded B 1 n m = (1 - C (B.coeff 0) * X) ^ n := by
  rw [colemanDBounded, reflect_one, Polynomial.map_pow, map_X,
    resultant_X_pow_left _ _ _ (natDegree_one_sub_C_X_mul_map_le hB)]
  simp [X_mul_C]

/-- Coleman's transform of a single factor `1 - α T` is `1 - B(α) T`. -/
theorem colemanDBounded_one_sub_C_mul_X (hB : B.natDegree ≤ m) (α : R) :
    colemanDBounded B (1 - C α * X) 1 m = 1 - C (B.eval α) * X := by
  have hr : (1 - C α * X).reflect 1 = X - C α := by simp
  rw [colemanDBounded, hr, Polynomial.map_sub, map_X, map_C,
    resultant_X_sub_C_left _ _ _ (natDegree_one_sub_C_X_mul_map_le hB),
    eval_sub, eval_one, eval_mul, eval_C, eval_map, eval₂_hom, mul_comm]

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

/-- Along `B = 1 - c P*`, where `P* = reflect n P` is the reversal of `P` in its rank `n`,
Coleman's transform of `P` is `(1 - T) ^ n`: if `P = ∏ (1 - αᵢ T)`, then `P* = ∏ (X - αᵢ)` and
`B(αᵢ) = 1` for every `i`. No hypothesis on `c` is needed. -/
theorem colemanDBounded_one_sub_C_mul_reflect_self (hP : P.natDegree ≤ n) (hP0 : P.coeff 0 = 1)
    (c : R) : colemanDBounded (1 - C c * P.reflect n) P n n = (1 - X) ^ n := by
  -- the kernel `1 - T B(X)` is `1 - T` plus a multiple of `P*` of degree zero in `X`
  have h : 1 - C X * (1 - C c * P.reflect n).map C =
      C (1 - X) + (P.reflect n).map C * C (C c * X) := by
    simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, C_sub, C_1,
      C_mul]
    ring
  rw [colemanDBounded, h, resultant_add_mul_right _ _ _ _ _ (by rw [natDegree_C, zero_add])
    (natDegree_map_reflect_le_of_natDegree_le C hP), resultant_C_right, coeff_map,
    coeff_reflect_self, hP0, C_1, one_pow, one_mul]

/-- Along `B = 1 - c Q*`, where `Q* = reflect d Q`, the value at `T = 1` of Coleman's transform of
`F` is the resultant of `c Q` and `F`. If `c Q = ∏ (T - rᵢ)` and `F = ∏ (1 - βⱼ T)` have degrees
`d` and `n`, then `1 - B = c Q* = ∏ (1 - rᵢ X)` and both sides are `∏ᵢ ∏ⱼ (1 - rᵢ βⱼ)`. -/
theorem eval_one_colemanDBounded_one_sub_C_mul_reflect (c : R) (F Q : R[X]) (n d : ℕ) :
    (colemanDBounded (1 - C c * Q.reflect d) F n d).eval 1 = resultant (C c * Q) F d n := by
  rw [eval_colemanDBounded, C_1, one_mul, sub_sub_cancel, resultant_C_mul_right,
    resultant_reflect, resultant_comm F Q, resultant_C_mul_left]
  simp [mul_comm n d, ← mul_assoc, ← mul_pow]

section RieszColeman

variable {Q F : R[X]} {c : R}

/-- If `c` inverts the leading coefficient of `Q`, then `1 - c Q*` vanishes at `0`, since the
constant coefficient of the reversal `Q*` is the leading coefficient of `Q`. -/
theorem coeff_zero_one_sub_C_mul_reverse (hc : c * Q.leadingCoeff = 1) :
    (1 - C c * Q.reverse).coeff 0 = 0 := by
  simp [coeff_zero_reverse, hc]

/-- The polynomial `1 - c Q*` has degree at most that of `Q`. -/
theorem natDegree_one_sub_C_mul_reverse_le (c : R) (Q : R[X]) :
    (1 - C c * Q.reverse).natDegree ≤ Q.natDegree :=
  (natDegree_sub_le _ _).trans (max_le (by simp)
    ((natDegree_C_mul_le _ _).trans (reverse_natDegree_le Q)))

/-- Let `c` invert the leading coefficient of `Q`. Along `B = 1 - c Q*`, the value at `T = 1` of
Coleman's transform of a polynomial `F` of degree at most `n` is a unit exactly when `Q` and `F`
are coprime. This is the polynomial step of Coleman's Appendix A4, in which a coprime factor `Q` of
a Fredholm determinant becomes a zero at `T = 1` along `1 - lc(Q)⁻¹ Q*`. -/
theorem isUnit_eval_one_colemanDBounded_one_sub_C_mul_reverse_iff
    (hc : c * Q.leadingCoeff = 1) (hF : F.natDegree ≤ n) :
    IsUnit ((colemanDBounded (1 - C c * Q.reverse) F n Q.natDegree).eval 1) ↔ IsCoprime Q F := by
  have hq : (C c * Q).Monic := monic_C_mul_of_mul_leadingCoeff_eq_one hc
  have hd : (C c * Q).natDegree = Q.natDegree :=
    natDegree_C_mul_eq_of_mul_eq_one (by rw [mul_comm]; exact hc)
  rw [reverse, eval_one_colemanDBounded_one_sub_C_mul_reflect, ← hd, hq.resultant_of_le hF,
    isUnit_resultant_iff_isCoprime hq,
    isCoprime_mul_unit_left_left (isUnit_C.2 (IsUnit.of_mul_eq_one _ hc))]

end RieszColeman

/-- An entry of the Sylvester matrix defining Coleman's transform `D_(n,m)(B, P)` with `B(0) = 0`,
in row `i` and column `x`, inside the band where it can be nonzero, is a monomial in `T`. In the
first `n` columns it is `1` on the diagonal and `-b_(i - x) T` below it, and in the last `m`
columns it is the coefficient `P_(x - i)`. -/
theorem sylvester_map_reflect_one_sub_apply (hB0 : B.coeff 0 = 0) {i x : Fin (n + m)}
    (h₁ : (x : ℕ) < n → (x : ℕ) ≤ i ∧ (i : ℕ) ≤ x + m)
    (h₂ : n ≤ (x : ℕ) → (x : ℕ) ≤ i + n ∧ (i : ℕ) ≤ x) :
    sylvester ((P.reflect n).map C) (1 - C X * B.map C) n m i x =
      C (if (x : ℕ) < i then -B.coeff (i - x) else if (x : ℕ) < n then 1 else P.coeff (x - i)) *
        X ^ (if (x : ℕ) < i then 1 else 0) := by
  rcases lt_or_ge (x : ℕ) n with hn | hn
  · rw [sylvester_apply_of_lt _ _ _ _ hn, ite_eq_left (h₁ hn)]
    simp only [coeff_sub, coeff_one, coeff_C_mul, coeff_map, ite_eq_left hn]
    by_cases hx : (x : ℕ) < i
    · rw [ite_eq_right (by omega), ite_eq_left hx, ite_eq_left hx, zero_sub, pow_one, map_neg,
        neg_mul, mul_comm]
    · have : (i : ℕ) - x = 0 := by omega
      simp [hx, this, hB0]
  · have hix : ¬(x : ℕ) < i := by have := h₂ hn; omega
    rw [sylvester_apply_of_le _ _ _ _ hn, ite_eq_left (h₂ hn)]
    simp only [coeff_map, coeff_reflect, ite_eq_right hix, ite_eq_right (not_lt.2 hn)]
    rw [revAt_le (by have := h₂ hn; omega), pow_zero, mul_one]
    congr 2
    have := h₂ hn
    omega

open Finset in
/-- The coefficients of the terms of the Leibniz expansion of the Sylvester matrix defining
Coleman's transform `D_(n,m)(B, P)` with `B(0) = 0`. The term of `σ` vanishes unless `σ` moves
each of the first `n` columns `x` to a row in `[x, x + m]` and each of the last `m` columns to a
row in `[x - n, x]`. It is then a monomial of degree the number of forward moves, whose entries
are `1` or `-b_(σ x - x) T` in the first `n` columns, according as `σ x = x` or not, and
`a_(x - σ x)` in the last `m` columns. -/
theorem coeff_prod_sylvester_colemanDBounded (hB0 : B.coeff 0 = 0)
    (σ : Equiv.Perm (Fin (n + m))) (k : ℕ) :
    (∏ x, sylvester ((P.reflect n).map C) (1 - C X * B.map C) n m (σ x) x).coeff k =
      if (∀ x : Fin (n + m), ((x : ℕ) < n → (x : ℕ) ≤ σ x ∧ (σ x : ℕ) ≤ x + m) ∧
          (n ≤ (x : ℕ) → (x : ℕ) ≤ σ x + n ∧ (σ x : ℕ) ≤ x)) ∧
          k = #{x : Fin (n + m) | (x : ℕ) < σ x} then
        ∏ x : Fin (n + m), if (x : ℕ) < σ x then -B.coeff (σ x - x)
          else if (x : ℕ) < n then 1 else P.coeff (x - σ x)
      else 0 := by
  set M := sylvester ((P.reflect n).map C) (1 - C X * B.map C) n m with hM_def
  by_cases hband : ∀ x : Fin (n + m), ((x : ℕ) < n → (x : ℕ) ≤ σ x ∧ (σ x : ℕ) ≤ x + m) ∧
      (n ≤ (x : ℕ) → (x : ℕ) ≤ σ x + n ∧ (σ x : ℕ) ≤ x)
  swap
  · -- some column is moved outside the band, where the Sylvester matrix vanishes
    obtain ⟨x, hx⟩ := not_forall.1 hband
    have hzero : M (σ x) x = 0 := by
      rcases lt_or_ge (x : ℕ) n with h | h
      · rw [hM_def, sylvester_apply_of_lt _ _ _ _ h]
        exact ite_eq_right_iff.2 fun hc ↦ absurd ⟨fun _ ↦ hc, fun h' ↦ absurd h' (not_le.2 h)⟩ hx
      · rw [hM_def, sylvester_apply_of_le _ _ _ _ h]
        exact ite_eq_right_iff.2 fun hc ↦ absurd ⟨fun h' ↦ absurd h' (not_lt.2 h), fun _ ↦ hc⟩ hx
    rw [prod_eq_zero (f := fun y ↦ M (σ y) y) (mem_univ x) hzero, coeff_zero]
    exact (ite_eq_right_iff.2 fun h ↦ absurd h.1 hband).symm
  set c : Fin (n + m) → R := fun x ↦
    if (x : ℕ) < σ x then -B.coeff (σ x - x) else if (x : ℕ) < n then 1 else P.coeff (x - σ x)
  set e : Fin (n + m) → ℕ := fun x ↦ if (x : ℕ) < σ x then 1 else 0
  have hM (x : Fin (n + m)) : M (σ x) x = C (c x) * X ^ e x :=
    sylvester_map_reflect_one_sub_apply hB0 (hband x).1 (hband x).2
  have hsum : ∑ x, e x = #{x : Fin (n + m) | (x : ℕ) < σ x} := by
    simp [e, sum_boole]
  simp_rw [hM]
  rw [prod_mul_distrib, ← map_prod, prod_pow_eq_pow_sum, coeff_C_mul_X_pow, hsum]
  exact if_congr (and_iff_right hband).symm rfl rfl

/-- **Locality of Coleman's transform.** When `B(0) = 0`, the `k`-th coefficient of
`D_(n,m)(B, P)` depends only on the coefficients of `P` of index at most `k m`. -/
theorem coeff_colemanDBounded_congr (hB0 : B.coeff 0 = 0) {P' : R[X]} {k : ℕ}
    (h : ∀ j ≤ k * m, P.coeff j = P'.coeff j) :
    (colemanDBounded B P n m).coeff k = (colemanDBounded B P' n m).coeff k := by
  rw [colemanDBounded_def, colemanDBounded_def, resultant, resultant, Matrix.det_apply,
    Matrix.det_apply, finsetSum_coeff, finsetSum_coeff]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_smul_apply,
    coeff_prod_sylvester_colemanDBounded hB0,
    coeff_prod_sylvester_colemanDBounded hB0]
  congr 1
  split_ifs with hk
  swap
  · rfl
  obtain ⟨hband, hk⟩ := hk
  -- Only the factors in the last `m` columns of a nonzero term involve `P`.
  refine Finset.prod_congr rfl fun x _ ↦ ?_
  split_ifs with h₁ h₂
  · rfl
  · rfl
  refine h _ ?_
  -- The total upward move of the columns equals the total downward move, made by the `k` columns
  -- moved down, each by at most `m`.
  calc (x : ℕ) - σ x ≤ ∑ y : Fin (n + m), ((y : ℕ) - σ y) :=
        Finset.single_le_sum (f := fun y : Fin (n + m) ↦ (y : ℕ) - σ y)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ x)
    _ = ∑ y : Fin (n + m), ((σ y : ℕ) - y) :=
        σ.sum_tsub_comp_eq_sum_comp_tsub fun y : Fin (n + m) ↦ (y : ℕ)
    _ ≤ ∑ y : Fin (n + m), (if (y : ℕ) < σ y then 1 else 0) * m :=
        Finset.sum_le_sum fun y _ ↦ by
          split_ifs with hy
          · have hyn : (y : ℕ) < n := by
              by_contra hyn
              have := (hband y).2 (not_lt.1 hyn)
              omega
            have := (hband y).1 hyn
            omega
          · omega
    _ = k * m := by rw [← Finset.sum_mul, hk, Finset.sum_boole, Nat.cast_id]

section Series

open PowerSeries (trunc natDegree_trunc_lt)

/-- Coleman's transform with polynomial functional input `B` and power series input `F`. Its
`k`-th coefficient is the `k`-th coefficient of `D_(N,m)(B, trunc (N + 1) F)` for `m = deg B` and
`N = k m`. When `B(0) = 0` the same coefficient is obtained for every rank `N ≥ k m`
(`Polynomial.coeff_colemanDSeries`), and for a polynomial `F` the series is the polynomial
transform (`Polynomial.colemanDSeries_coe`). If `B(0) ≠ 0` the finite transforms need not
stabilise and this series has no spectral meaning in general. -/
noncomputable def colemanDSeries (B : R[X]) (F : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun k ↦
    (colemanDBounded B (trunc (k * B.natDegree + 1) F) (k * B.natDegree) B.natDegree).coeff k

theorem colemanDSeries_def (B : R[X]) (F : PowerSeries R) :
    B.colemanDSeries F = PowerSeries.mk fun k ↦
      (colemanDBounded B (trunc (k * B.natDegree + 1) F) (k * B.natDegree)
        B.natDegree).coeff k := by
  rw [colemanDSeries]

/-- For any `B`, the `k`-th coefficient of Coleman's transform of `F` is that of the finite
transform of `trunc (N + 1) F` at the rank `N = k deg B`. -/
theorem coeff_colemanDSeries_eq_coeff_colemanDBounded (B : R[X]) (F : PowerSeries R) (k : ℕ) :
    PowerSeries.coeff k (B.colemanDSeries F) =
      (colemanDBounded B (trunc (k * B.natDegree + 1) F) (k * B.natDegree)
        B.natDegree).coeff k := by
  rw [colemanDSeries_def, PowerSeries.coeff_mk]

/-- When `B(0) = 0`, the `k`-th coefficient of Coleman's transform of `F` is that of the finite
transform of the truncation `trunc (N + 1) F` at any rank `N ≥ k deg B`. -/
theorem coeff_colemanDSeries (hB0 : B.coeff 0 = 0) {F : PowerSeries R} {k N : ℕ}
    (hN : k * B.natDegree ≤ N) :
    PowerSeries.coeff k (B.colemanDSeries F) =
      (colemanDBounded B (trunc (N + 1) F) N B.natDegree).coeff k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [coeff_colemanDSeries_eq_coeff_colemanDBounded,
    ← colemanDBounded_add_of_coeff_zero (Nat.lt_succ_iff.1 (natDegree_trunc_lt F _)) le_rfl hB0 j]
  refine coeff_colemanDBounded_congr hB0 fun i hi ↦ ?_
  simp only [PowerSeries.coeff_trunc]
  split_ifs <;> first | rfl | omega

/-- When `B(0) = 0` and `F(0) = 1`, the `k`-th coefficient of Coleman's transform of `F` is that
of `D_(N,m)(B, trunc (N + 1) F)` for every degree bound `m ≥ deg B` and rank `N ≥ k m`. -/
theorem coeff_colemanDSeries_of_natDegree_le (hB0 : B.coeff 0 = 0) {F : PowerSeries R}
    (hF0 : PowerSeries.constantCoeff F = 1) {k N : ℕ} (hB : B.natDegree ≤ m) (hN : k * m ≤ N) :
    PowerSeries.coeff k (B.colemanDSeries F) =
      (colemanDBounded B (trunc (N + 1) F) N m).coeff k := by
  rw [coeff_colemanDSeries hB0 ((Nat.mul_le_mul_left k hB).trans hN),
    colemanDBounded_of_natDegree_le hB (by simp [PowerSeries.coeff_trunc, hF0])]

/-- When `B(0) = 0`, Coleman's transform of a polynomial `P` of degree at most `n` is the finite
transform of rank `n`. -/
theorem colemanDSeries_coe_of_natDegree_le (hB0 : B.coeff 0 = 0) (hP : P.natDegree ≤ n) :
    B.colemanDSeries (P : PowerSeries R) = colemanDBounded B P n B.natDegree := by
  ext k
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (le_max_right (k * B.natDegree) n)
  rw [coeff_colemanDSeries hB0 (le_max_left _ n),
    PowerSeries.trunc_coe_eq_self (Nat.lt_succ_of_le (hP.trans (le_max_right _ n))), hj,
    colemanDBounded_add_of_coeff_zero hP le_rfl hB0, coeff_coe]

/-- When `B(0) = 0`, Coleman's transform of a polynomial `P` is the minimal-rank transform
`Polynomial.colemanD B P`. -/
@[simp]
theorem colemanDSeries_coe (hB0 : B.coeff 0 = 0) (P : R[X]) :
    B.colemanDSeries (P : PowerSeries R) = colemanD B P := by
  rw [colemanD_def, colemanDSeries_coe_of_natDegree_le hB0 le_rfl]

/-- Coleman's transform of a normalised power series is normalised. -/
@[simp]
theorem constantCoeff_colemanDSeries {F : PowerSeries R} (hF0 : PowerSeries.constantCoeff F = 1) :
    PowerSeries.constantCoeff (B.colemanDSeries F) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_colemanDSeries_eq_coeff_colemanDBounded, coeff_zero_colemanDBounded (by simp [hF0])]

/-- **Multiplicativity in `F`.** When `B(0) = 0`, Coleman's transform of a product of power series
is the product of their transforms. -/
theorem colemanDSeries_mul (hB0 : B.coeff 0 = 0) (F G : PowerSeries R) :
    B.colemanDSeries (F * G) = B.colemanDSeries F * B.colemanDSeries G := by
  ext k
  set N := k * B.natDegree
  have hF : (trunc (N + 1) F).natDegree ≤ N := Nat.lt_succ_iff.1 (natDegree_trunc_lt F N)
  have hG : (trunc (N + 1) G).natDegree ≤ N := Nat.lt_succ_iff.1 (natDegree_trunc_lt G N)
  -- Up to degree `k`, the transform of a series `H` is its finite transform of rank `N`.
  have htrunc (H : PowerSeries R) :
      trunc (k + 1) (B.colemanDSeries H) =
        trunc (k + 1) (colemanDBounded B (trunc (N + 1) H) N B.natDegree : PowerSeries R) := by
    ext i
    rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
    split_ifs with hi
    · rw [coeff_colemanDSeries hB0 (Nat.mul_le_mul_right _ (Nat.lt_succ_iff.1 hi)), coeff_coe]
    · rfl
  -- Up to degree `N`, `F * G` agrees with `trunc F * trunc G`, so by locality its transform has the
  -- same `k`-th coefficient as the finite transform of rank `N + N` of that product.
  have hprod : PowerSeries.coeff k (B.colemanDSeries (F * G)) =
      (colemanDBounded B (trunc (N + 1) F * trunc (N + 1) G) (N + N) B.natDegree).coeff k := by
    rw [coeff_colemanDSeries hB0 (Nat.le_add_right N N)]
    refine coeff_colemanDBounded_congr hB0 fun j hj ↦ ?_
    rw [PowerSeries.coeff_trunc, ite_eq_left (by omega),
      PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc _ _ (Nat.lt_succ_of_le hj), ← coe_mul,
      coeff_coe]
  -- The finite transform is multiplicative.
  have hmul : colemanDBounded B (trunc (N + 1) F * trunc (N + 1) G) (N + N) B.natDegree =
      colemanDBounded B (trunc (N + 1) F) N B.natDegree *
        colemanDBounded B (trunc (N + 1) G) N B.natDegree :=
    colemanDBounded_mul hF hG le_rfl
  rw [hprod, hmul, ← coeff_coe, coe_mul,
    PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc _ _ k.lt_succ_self,
    PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc (B.colemanDSeries F) _ k.lt_succ_self,
    htrunc, htrunc]

/-- With `B = T`, Coleman's transform returns `F`. -/
@[simp]
theorem colemanDSeries_X_left (F : PowerSeries R) : (X : R[X]).colemanDSeries F = F := by
  nontriviality R
  ext k
  rw [coeff_colemanDSeries coeff_X_zero (by rw [natDegree_X, mul_one]), natDegree_X,
    colemanDBounded_X_left (Nat.lt_succ_iff.1 (natDegree_trunc_lt F k)), PowerSeries.coeff_trunc,
    ite_eq_left k.lt_succ_self]

/-- With `B = 0`, Coleman's transform of any power series is one. -/
@[simp]
theorem colemanDSeries_zero_left (F : PowerSeries R) : (0 : R[X]).colemanDSeries F = 1 := by
  ext k
  rw [coeff_colemanDSeries_eq_coeff_colemanDBounded, natDegree_zero, colemanDBounded,
    Polynomial.map_zero, mul_zero, mul_zero, sub_zero, resultant_one_right, pow_zero, ← coeff_coe,
    coe_one]

/-- When `B(0) = 0`, Coleman's transform of `1` is one. -/
@[simp]
theorem colemanDSeries_one_right (hB0 : B.coeff 0 = 0) : B.colemanDSeries 1 = 1 := by
  rw [← Polynomial.coe_one, colemanDSeries_coe hB0, colemanD_def, natDegree_one,
    colemanDBounded_one_right le_rfl, pow_zero]

/-- Let `Q(0) = 1` and let `c` invert the leading coefficient of `Q`, so that `B = 1 - c Q*`
vanishes at `0`. Coleman's transform of `Q` along `B` is `(1 - T) ^ deg Q`: the polynomial `B`
sends every inverse root of `Q` to `1`. -/
theorem colemanDSeries_one_sub_C_mul_reverse_self {Q : R[X]} {c : R} (hQ0 : Q.coeff 0 = 1)
    (hc : c * Q.leadingCoeff = 1) :
    colemanDSeries (1 - C c * Q.reverse) Q = (1 - PowerSeries.X) ^ Q.natDegree := by
  rw [colemanDSeries_coe_of_natDegree_le (coeff_zero_one_sub_C_mul_reverse hc) le_rfl,
    ← colemanDBounded_of_natDegree_le (natDegree_one_sub_C_mul_reverse_le c Q) hQ0, reverse,
    colemanDBounded_one_sub_C_mul_reflect_self le_rfl hQ0]
  simp

open scoped PowerSeries.WithPiTopology in
/-- Each coefficient of Coleman's transform is a continuous function of `F` for the topology of
coefficientwise convergence: it is a polynomial in the coefficients of `F` of index at most
`k deg B`. -/
theorem continuous_coeff_colemanDSeries [TopologicalSpace R] [IsTopologicalSemiring R] (B : R[X])
    (k : ℕ) : Continuous fun F : PowerSeries R ↦ PowerSeries.coeff k (B.colemanDSeries F) := by
  set N := k * B.natDegree
  -- the finite transform of the generic polynomial of degree `N`
  set U : (MvPolynomial (Fin (N + 1)) R)[X] := ∑ j : Fin (N + 1), monomial j (MvPolynomial.X j)
  set Φ := (colemanDBounded (B.map MvPolynomial.C) U N B.natDegree).coeff k with hΦ_def
  have hC (c : Fin (N + 1) → R) : (MvPolynomial.eval c).comp MvPolynomial.C = RingHom.id R := by
    ext; simp
  have hΦ (F : PowerSeries R) :
      PowerSeries.coeff k (B.colemanDSeries F) =
        MvPolynomial.eval (fun j : Fin (N + 1) ↦ PowerSeries.coeff j F) Φ := by
    have hU : U.map (MvPolynomial.eval fun j : Fin (N + 1) ↦ PowerSeries.coeff j F) =
        trunc (N + 1) F := by
      simp [U, Polynomial.map_sum, PowerSeries.trunc_apply,
        Fin.sum_univ_eq_sum_range (fun j ↦ monomial j (PowerSeries.coeff j F))]
    rw [coeff_colemanDSeries_eq_coeff_colemanDBounded, hΦ_def, ← coeff_map, colemanDBounded_map,
      Polynomial.map_map, hC, Polynomial.map_id, hU]
  simp_rw [hΦ]
  exact (MvPolynomial.continuous_eval Φ).comp
    (continuous_pi fun j ↦ PowerSeries.WithPiTopology.continuous_coeff R j)

end Series

end Polynomial

namespace Matrix

open Polynomial

/-- **Finite matrix spectral mapping.** For an `n × n` matrix `A` and `B` of degree at most `m`,
Coleman's transform of rank `n` of `det (1 - T A)` is `det (1 - T B(A))`. The rank must be the
dimension: a zero eigenvalue of `A` contributes the factor `1 - B(0) T` on the right even though it
is invisible in `det (1 - T A)`. -/
theorem colemanDBounded_charpolyRev {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A : Matrix ι ι R) {B : R[X]} {m : ℕ} (hB : B.natDegree ≤ m) :
    colemanDBounded B A.charpolyRev (Fintype.card ι) m = (aeval A B).charpolyRev := by
  -- The matrix in `det (1 - T B(A))` is `1 - T B(X)` evaluated at `A`, read over `R[T]`.
  have hmat : aeval (A.map C) (1 - C X * B.map C) = 1 - (X : R[X]) • (aeval A B).map C := by
    simp [aeval_map, Algebra.smul_def]
  rw [colemanDBounded, charpolyRev_eq_reflect, reflect_reflect, ← charpoly_map,
    ← det_aeval_eq_resultant _ _ (natDegree_one_sub_C_X_mul_map_le hB), hmat, charpolyRev]

end Matrix

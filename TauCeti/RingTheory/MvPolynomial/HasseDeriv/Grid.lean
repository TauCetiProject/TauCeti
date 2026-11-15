/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import TauCeti.Algebra.MvPolynomial.HasseDeriv.Basic
public import TauCeti.Algebra.Polynomial.HasseDeriv
public import TauCeti.Data.Finsupp.Fin

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Interval
import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.MvPolynomial.Basic
import TauCeti.Algebra.MvPolynomial.Equiv

/-!
# Nonvanishing of multivariate Hasse jets on rectangular grids

Singling out the first variable `X₀` of `MvPolynomial (Fin (n + 1)) R` via
`MvPolynomial.finSuccEquiv` turns the Hasse derivative `∂^(k e₀)` into the univariate Hasse
derivative `Polynomial.hasseDeriv k`, and evaluating at `C a` commutes with Hasse differentiation
`∂^d` in the remaining `n` variables to produce
`(finSuccEquiv R n (hasseDeriv (Finsupp.cons k d) P)).eval (C a)` without increasing the partial
degrees in `X₁, …, Xₙ`.

Iterating this single-variable reduction across `Fin n` and lifting along
`MvPolynomial.exists_fin_rename` shows that over any integral domain, a nonzero polynomial
`P : MvPolynomial σ R` whose partial degrees satisfy `P.degreeOf j < #(S j) * (k j + 1)` has a
nonzero Hasse jet of multi-order `d ≤ k` at a point of the product grid `∏ⱼ S j`
(`MvPolynomial.exists_eval_hasseDeriv_ne_zero_of_degreeOf_lt`). In characteristic zero,
specializing `S j` to the integer interval `[-⌊B j⌋₊, ⌊B j⌋₊]` gives Evertse's rectangular
integer-grid jet nonvanishing lemma (`MvPolynomial.exists_int_eval_hasseDeriv_ne_zero`).

## Main results

* `MvPolynomial.coeff_finSuccEquiv_hasseDeriv_cons`,
  `MvPolynomial.finSuccEquiv_hasseDeriv_single_zero`: singling out `X₀` intertwines `hasseDeriv`
  with `Polynomial.hasseDeriv` in `X₀` and coefficientwise `hasseDeriv` in the remaining variables.
* `MvPolynomial.hasseDeriv_eval_C_finSuccEquiv_hasseDeriv_single_zero`,
  `MvPolynomial.eval_cons_hasseDeriv_cons`: evaluating `X₀` at `a` after `∂^(k e₀)` commutes with
  `hasseDeriv d` in the remaining variables.
* `MvPolynomial.degreeOf_eval_C_finSuccEquiv_hasseDeriv_single_zero_le`: applying `∂^(k e₀)` and
  evaluating `X₀` at `a` bounds the residual degree in `Xⱼ` by `P.degreeOf j.succ`.
* `MvPolynomial.exists_eval_C_finSuccEquiv_hasseDeriv_single_zero_ne_zero`,
  `MvPolynomial.exists_int_eval_C_finSuccEquiv_hasseDeriv_single_zero_ne_zero`: the single-variable
  finite-grid and integer-grid reduction steps in `X₀`.
* `MvPolynomial.exists_eval_hasseDeriv_ne_zero_of_degreeOf_lt`: finite-grid Hasse jet nonvanishing
  over an integral domain, for an arbitrary variable index type `σ`.
* `MvPolynomial.exists_int_eval_hasseDeriv_ne_zero`: rectangular integer-grid Hasse jet nonvanishing
  over a domain of characteristic zero (Evertse, Lemma 25).

## References

* J.-H. Evertse, *An improvement of the quantitative subspace theorem*, Compositio Math. 101
  (1996), §7, Lemma 25.
-/

public section

namespace MvPolynomial

open Finset

section FinSucc

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- Singling out `X₀` turns `hasseDeriv (Finsupp.cons k d)` into `Polynomial.hasseDeriv k` in `X₀`
followed by `hasseDeriv d` on each coefficient in the remaining variables. -/
theorem coeff_finSuccEquiv_hasseDeriv_cons (k : ℕ) (d : Fin n →₀ ℕ)
    (P : MvPolynomial (Fin (n + 1)) R) (i : ℕ) :
    (finSuccEquiv R n (hasseDeriv (Finsupp.cons k d) P)).coeff i =
      hasseDeriv d ((Polynomial.hasseDeriv k (finSuccEquiv R n P)).coeff i) := by
  ext m
  rw [finSuccEquiv_coeff_coeff, hasseDeriv_coeff, Polynomial.hasseDeriv_coeff,
    ← nsmul_eq_mul ((i + k).choose k), map_nsmul, coeff_smul, nsmul_eq_mul, hasseDeriv_coeff,
    finSuccEquiv_coeff_coeff]
  have hadd : Finsupp.cons i m + Finsupp.cons k d = Finsupp.cons (i + k) (m + d) :=
    Finsupp.cons_add_cons i k m d
  have hprod : (Finsupp.cons k d).prod (fun j c ↦ (Finsupp.cons i m j + c).choose c) =
      (i + k).choose k * d.prod (fun j c ↦ (m j + c).choose c) := by
    rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ]
    simp
  rw [hadd, hprod, Nat.cast_mul, mul_assoc]

/-- Singling out `X₀` turns the pure Hasse derivative `∂^(k e₀)` into the univariate Hasse
derivative `Polynomial.hasseDeriv k`. -/
@[simp]
theorem finSuccEquiv_hasseDeriv_single_zero (k : ℕ) (P : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv R n (hasseDeriv (Finsupp.single 0 k) P) =
      Polynomial.hasseDeriv k (finSuccEquiv R n P) := by
  ext i m
  have h := congrArg (fun g ↦ g.coeff m) (coeff_finSuccEquiv_hasseDeriv_cons k 0 P i)
  simpa [Finsupp.cons_zero_eq_single_zero] using h

/-- Evaluating `X₀ = a` after taking `∂^(k e₀)` and then differentiating by `∂^d` in the remaining
variables agrees with differentiating by `Finsupp.cons k d` and then evaluating `X₀ = a`. -/
theorem hasseDeriv_eval_C_finSuccEquiv_hasseDeriv_single_zero (a : R) (k : ℕ)
    (d : Fin n →₀ ℕ) (P : MvPolynomial (Fin (n + 1)) R) :
    hasseDeriv d ((finSuccEquiv R n (hasseDeriv (Finsupp.single 0 k) P)).eval (C a)) =
      (finSuccEquiv R n (hasseDeriv (Finsupp.cons k d) P)).eval (C a) := by
  set Q₁ := finSuccEquiv R n (hasseDeriv (Finsupp.single 0 k) P)
  set Q₂ := finSuccEquiv R n (hasseDeriv (Finsupp.cons k d) P)
  set N := max Q₁.natDegree Q₂.natDegree + 1
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (le_max_left _ _)),
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (le_max_right _ _)), map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hcoeff : Q₂.coeff i = hasseDeriv d (Q₁.coeff i) := by
    simp [Q₁, Q₂, coeff_finSuccEquiv_hasseDeriv_cons]
  rw [hcoeff, ← map_pow, mul_comm (Q₁.coeff i), ← smul_eq_C_mul, LinearMap.map_smul,
    smul_eq_C_mul, mul_comm]

/-- The jet `∂^(Finsupp.cons k d) P` at `Fin.cons a x` equals the jet `∂^d` at `x` of the residual
polynomial obtained by applying `∂^(k e₀)` and setting `X₀ = a`. -/
theorem eval_cons_hasseDeriv_cons (a : R) (x : Fin n → R) (k : ℕ) (d : Fin n →₀ ℕ)
    (P : MvPolynomial (Fin (n + 1)) R) :
    eval (Fin.cons a x) (hasseDeriv (Finsupp.cons k d) P) =
      eval x (hasseDeriv d
        ((finSuccEquiv R n (hasseDeriv (Finsupp.single 0 k) P)).eval (C a))) := by
  rw [hasseDeriv_eval_C_finSuccEquiv_hasseDeriv_single_zero, eval_polynomial_eval_finSuccEquiv]
  congr 2
  funext i
  cases i using Fin.cases <;> simp

/-- Applying `∂^(k e₀)` and specializing `X₀ = a` bounds the residual degree in `Xⱼ` by
`P.degreeOf j.succ`. -/
theorem degreeOf_eval_C_finSuccEquiv_hasseDeriv_single_zero_le (a : R) (k : ℕ)
    (P : MvPolynomial (Fin (n + 1)) R) (j : Fin n) :
    ((finSuccEquiv R n (hasseDeriv (Finsupp.single 0 k) P)).eval (C a)).degreeOf j ≤
      P.degreeOf j.succ :=
  ((degreeOf_eval_C_finSuccEquiv_le a _ j).trans (degreeOf_hasseDeriv_le _ P j.succ)).trans
    (Nat.sub_le _ _)

end FinSucc

section FiniteGrid

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Single-variable finite-grid reduction step.** Over an integral domain, if `P ≠ 0` has degree
in `X₀` strictly less than `#S * (k + 1)`, some Hasse derivative `∂^(i e₀) P` with `i ≤ k` remains
nonzero as a polynomial in the remaining variables after setting `X₀ = a` for some `a ∈ S`. -/
theorem exists_eval_C_finSuccEquiv_hasseDeriv_single_zero_ne_zero {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) R} (hP : P ≠ 0) {S : Finset R} {k : ℕ}
    (hdeg : P.degreeOf 0 < #S * (k + 1)) :
    ∃ a ∈ S, ∃ i ≤ k,
      (finSuccEquiv R n (hasseDeriv (Finsupp.single 0 i) P)).eval (C a) ≠ 0 := by
  classical
  have hQ : finSuccEquiv R n P ≠ 0 := EmbeddingLike.map_ne_zero_iff.2 hP
  have hdegQ : (finSuccEquiv R n P).natDegree <
      #(S.image (C : R →+* MvPolynomial (Fin n) R)) * (k + 1) := by
    rw [Finset.card_image_of_injective _ (C_injective (Fin n) R), natDegree_finSuccEquiv]
    exact hdeg
  obtain ⟨x, hx, i, hi, hne⟩ :=
    Polynomial.exists_eval_hasseDeriv_ne_zero_of_natDegree_lt hQ hdegQ
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
  refine ⟨a, ha, i, hi, ?_⟩
  rwa [finSuccEquiv_hasseDeriv_single_zero]

private theorem exists_eval_hasseDeriv_ne_zero_of_degreeOf_lt_fin :
    ∀ {n : ℕ} {P : MvPolynomial (Fin n) R} (_ : P ≠ 0) {S : Fin n → Finset R} {k : Fin n → ℕ}
      (_ : ∀ j, P.degreeOf j < #(S j) * (k j + 1)),
      ∃ (a : Fin n → R) (d : Fin n →₀ ℕ),
        (∀ j, a j ∈ S j) ∧ (∀ j, d j ≤ k j) ∧ eval a (hasseDeriv d P) ≠ 0
  | 0, P, hP, _, _, _ => by
    refine ⟨Fin.elim0, 0, fun j ↦ j.elim0, fun j ↦ j.elim0, ?_⟩
    rw [eq_C_of_isEmpty P] at hP ⊢
    simpa using hP
  | n + 1, P, hP, S, k, hdeg => by
    obtain ⟨a₀, ha₀, k₀, hk₀, hQ⟩ :=
      exists_eval_C_finSuccEquiv_hasseDeriv_single_zero_ne_zero hP (hdeg 0)
    have hdegQ (j : Fin n) :
        ((finSuccEquiv R n (hasseDeriv (Finsupp.single 0 k₀) P)).eval (C a₀)).degreeOf j <
          #(S j.succ) * (k j.succ + 1) :=
      (degreeOf_eval_C_finSuccEquiv_hasseDeriv_single_zero_le a₀ k₀ P j).trans_lt (hdeg j.succ)
    obtain ⟨x, d, hx, hd, hne⟩ :=
      exists_eval_hasseDeriv_ne_zero_of_degreeOf_lt_fin hQ hdegQ
    refine ⟨Fin.cons a₀ x, Finsupp.cons k₀ d, fun j ↦ ?_, fun j ↦ ?_, ?_⟩
    · cases j using Fin.cases with
      | zero => exact ha₀
      | succ j => exact hx j
    · cases j using Fin.cases with
      | zero => exact hk₀
      | succ j => exact hd j
    · rwa [eval_cons_hasseDeriv_cons]

/-- **Multivariate Hasse-jet nonvanishing on a finite product grid.** Over an integral domain, if
`P ≠ 0` satisfies `P.degreeOf j < #(S j) * (k j + 1)` in every variable `j`, then some Hasse
derivative `∂^d P` with `d ≤ k` does not vanish at some point `a ∈ ∏ⱼ S j`. No finiteness
assumption on the variable index type `σ` is needed. -/
theorem exists_eval_hasseDeriv_ne_zero_of_degreeOf_lt {σ : Type*} {P : MvPolynomial σ R}
    (hP : P ≠ 0) {S : σ → Finset R} {k : σ → ℕ}
    (hdeg : ∀ j, P.degreeOf j < #(S j) * (k j + 1)) :
    ∃ (a : σ → R) (d : σ →₀ ℕ),
      (∀ j, a j ∈ S j) ∧ (∀ j, d j ≤ k j) ∧ eval a (hasseDeriv d P) ≠ 0 := by
  classical
  obtain ⟨n, f, hf, Q, rfl⟩ := exists_fin_rename P
  have hQ : Q ≠ 0 := fun h ↦ hP (by simp [h])
  have hdegQ (i : Fin n) : Q.degreeOf i < #(S (f i)) * (k (f i) + 1) := by
    rw [← degreeOf_rename_of_injective hf]
    exact hdeg (f i)
  obtain ⟨a₀, d₀, ha₀, hd₀, hne⟩ :=
    exists_eval_hasseDeriv_ne_zero_of_degreeOf_lt_fin hQ hdegQ
  have hneS (j : σ) : (S j).Nonempty :=
    Finset.card_pos.1 (pos_of_mul_pos_left ((Nat.zero_le _).trans_lt (hdeg j)) (Nat.zero_le _))
  let a : σ → R := Function.extend f a₀ fun j ↦ (hneS j).choose
  refine ⟨a, d₀.mapDomain f, fun j ↦ ?_, fun j ↦ ?_, ?_⟩
  · dsimp only [a]
    by_cases hj : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [hf.extend_apply]
      exact ha₀ i
    · rw [Function.extend_apply' _ _ _ hj]
      exact (hneS j).choose_spec
  · by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      rw [Finsupp.mapDomain_apply_of_injective hf]
      exact hd₀ i
    · simp [Finsupp.mapDomain_of_notMem_range, hj]
  · rw [hasseDeriv_rename hf, eval_rename, Function.extend_comp hf]
    exact hne

end FiniteGrid

section IntGrid

variable {R K : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [DivisionSemiring K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

/-- **Single-variable integer-grid reduction step** (Evertse, Lemma 25, inductive step). Over a
domain of characteristic zero, if `P ≠ 0`, `P.degreeOf 0 ≤ s`, and `0 < B`, there exist `z : ℤ`
with `z.natAbs ≤ B` and `k : ℕ` with `k ≤ s / B` such that specializing `X₀ = z` in `∂^(k e₀) P`
leaves a nonzero polynomial in the remaining variables. -/
theorem exists_int_eval_C_finSuccEquiv_hasseDeriv_single_zero_ne_zero {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) R} (hP : P ≠ 0) {s : ℕ} (hs : P.degreeOf 0 ≤ s)
    {B : K} (hB : 0 < B) :
    ∃ (z : ℤ) (k : ℕ), (z.natAbs : K) ≤ B ∧ (k : K) ≤ (s : K) / B ∧
      (finSuccEquiv R n (hasseDeriv (Finsupp.single 0 k) P)).eval (C (z : R)) ≠ 0 := by
  have hQ : finSuccEquiv R n P ≠ 0 := EmbeddingLike.map_ne_zero_iff.2 hP
  have hsQ : (finSuccEquiv R n P).natDegree ≤ s := (natDegree_finSuccEquiv P).le.trans hs
  obtain ⟨z, k, hz, hk, hne⟩ := Polynomial.exists_int_eval_hasseDeriv_ne_zero hQ hsQ hB
  refine ⟨z, k, hz, hk, ?_⟩
  simpa [finSuccEquiv_hasseDeriv_single_zero] using hne

/-- **Multivariate Hasse-jet nonvanishing on a rectangular integer grid** (Evertse, Lemma 25).
Over a domain of characteristic zero, let `P : MvPolynomial σ R` be nonzero with partial degrees
`P.degreeOf j ≤ s j`, and let `B j > 0` for every variable `j`. Then there exist `z : σ → ℤ` and
`d : σ →₀ ℕ` with `(z j).natAbs ≤ B j`, `d j ≤ s j / B j`, and `eval z (hasseDeriv d P) ≠ 0`.
This includes nonzero constants and empty variable index types. -/
theorem exists_int_eval_hasseDeriv_ne_zero {σ : Type*} {P : MvPolynomial σ R} (hP : P ≠ 0)
    {s : σ → ℕ} (hs : ∀ j, P.degreeOf j ≤ s j) {B : σ → K} (hB : ∀ j, 0 < B j) :
    ∃ (z : σ → ℤ) (d : σ →₀ ℕ),
      (∀ j, ((z j).natAbs : K) ≤ B j) ∧
      (∀ j, (d j : K) ≤ (s j : K) / B j) ∧
      eval (fun j ↦ (z j : R)) (hasseDeriv d P) ≠ 0 := by
  classical
  let a : σ → ℕ := fun j ↦ ⌊B j⌋₊
  let b : σ → ℕ := fun j ↦ ⌊(s j : K) / B j⌋₊
  let I : σ → Finset ℤ := fun j ↦ Finset.Icc (-(a j : ℤ)) (a j : ℤ)
  let S : σ → Finset R := fun j ↦ (I j).image Int.cast
  have hdeg (j : σ) : P.degreeOf j < #(S j) * (b j + 1) := by
    have hcard : #(S j) = 2 * a j + 1 := by
      rw [Finset.card_image_of_injective _ Int.cast_injective, Int.card_Icc]
      omega
    rw [hcard]
    exact (hs j).trans_lt (TauCeti.lt_two_mul_floor_add_one_mul_floor_div_add_one (hB j) (s j))
  obtain ⟨x, d, hx, hd, hne⟩ := exists_eval_hasseDeriv_ne_zero_of_degreeOf_lt hP hdeg
  have hz_ex (j : σ) : ∃ z ∈ I j, (z : R) = x j := Finset.mem_image.1 (hx j)
  let z : σ → ℤ := fun j ↦ (hz_ex j).choose
  have hz_mem (j : σ) : z j ∈ I j := (hz_ex j).choose_spec.1
  have hz_cast : (fun j ↦ (z j : R)) = x := funext fun j ↦ (hz_ex j).choose_spec.2
  refine ⟨z, d, fun j ↦ ?_, fun j ↦ ?_, hz_cast.symm ▸ hne⟩
  · have hzj := Finset.mem_Icc.1 (hz_mem j)
    have hza : (z j).natAbs ≤ a j := by omega
    exact (Nat.cast_le.2 hza).trans (Nat.floor_le (hB j).le)
  · exact (Nat.cast_le.2 (hd j)).trans (Nat.floor_le (div_nonneg (Nat.cast_nonneg (s j)) (hB j).le))

/-- In zero variables (`Fin 0`), a nonzero constant `C c` has nonvanishing order-zero Hasse jet
equal to `c`. -/
example {c : ℚ} (hc : c ≠ 0) :
    eval (fun _ : Fin 0 ↦ ((0 : ℤ) : ℚ)) (hasseDeriv 0 (C c : MvPolynomial (Fin 0) ℚ)) = c ∧
    eval (fun _ : Fin 0 ↦ ((0 : ℤ) : ℚ)) (hasseDeriv 0 (C c : MvPolynomial (Fin 0) ℚ)) ≠ 0 :=
  ⟨by simp, by simpa using hc⟩

/-- Mixed radii `B = ![1, 1 / 2]` and partial degrees `s = ![3, 2]` for
`P = (X 0 ^ 3 - X 0) * X 1 ^ 2` over `ℚ`: every order-zero evaluation on `{-1, 0, 1} × {0}`
vanishes, while at `z = ![0, 0]` and `d = single 0 1 + single 1 2` (satisfying `1 ≤ 3 / 1` and
`2 ≤ 2 / (1 / 2)`), `(∂^d P)(0, 0) = -1`. -/
example :
    (∀ z : Fin 2 → ℤ, (∀ j, ((z j).natAbs : ℚ) ≤ (![1, 1 / 2] : Fin 2 → ℚ) j) →
      eval (fun j ↦ (z j : ℚ)) ((X 0 ^ 3 - X 0) * X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) = 0) ∧
    eval (fun _ : Fin 2 ↦ (0 : ℚ))
      (hasseDeriv (Finsupp.single 0 1 + Finsupp.single 1 2)
        ((X 0 ^ 3 - X 0) * X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)) = -1 := by
  refine ⟨fun z hz ↦ ?_, ?_⟩
  · have hz1 : z 1 = 0 := by
      have h1 : ((z 1).natAbs : ℚ) ≤ 1 / 2 := by simpa using hz 1
      have h1' : ((z 1).natAbs : ℚ) < 1 := h1.trans_lt (by norm_num)
      have h2 : (z 1).natAbs < 1 := by exact_mod_cast h1'
      omega
    simp [hz1]
  · have hP : ((X 0 ^ 3 - X 0) * X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) =
        monomial (Finsupp.single 0 3 + Finsupp.single 1 2) 1 -
          monomial (Finsupp.single 0 1 + Finsupp.single 1 2) 1 := by
      rw [sub_mul, X_pow_eq_monomial, X_pow_eq_monomial, X,
        monomial_mul_monomial, monomial_mul_monomial, one_mul]
    have hsub1 : (Finsupp.single 0 3 + Finsupp.single 1 2 -
        (Finsupp.single 0 1 + Finsupp.single 1 2) : Fin 2 →₀ ℕ) = Finsupp.single 0 2 := by
      ext j
      fin_cases j <;> simp
    rw [hP, map_sub, hasseDeriv_monomial, hasseDeriv_monomial, hsub1, tsub_self]
    simp [Finsupp.prod_fintype _ _ (fun _ ↦ Nat.choose_zero_right _), Fin.prod_univ_two,
      constantCoeff_monomial]

end IntGrid

end MvPolynomial

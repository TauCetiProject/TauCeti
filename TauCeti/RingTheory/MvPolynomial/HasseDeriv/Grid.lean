/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.HasseDeriv.Grid
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.Taylor

/-!
# Nonvanishing of Hasse derivatives on rectangular integer grids

Over an integral domain `R` of characteristic zero, a nonzero polynomial cannot vanish to high
order at every point of a rectangular integer box. In one variable, if a nonzero polynomial
`p : R[X]` of degree at most `s` had `(D^i p)(z) = 0` for every integer `z` with `|z| ≤ B` and
every order `i ≤ s / B`, then each of the `2 ⌊B⌋₊ + 1` integers in `[-⌊B⌋₊, ⌊B⌋₊]` would be a root
of `p` of multiplicity at least `⌊s / B⌋₊ + 1`, and the sum of these root multiplicities would be
at least `(2 ⌊B⌋₊ + 1) (⌊s / B⌋₊ + 1) > s ≥ deg p`, contradicting the root-multiplicity bound
`∑ a ∈ S, p.rootMultiplicity a ≤ p.natDegree`.

Applying the one-variable result to `finSuccEquiv R n P` over the integral domain
`MvPolynomial (Fin n) R` eliminates one variable at a time without increasing the partial degrees
in the remaining variables. By induction on the number of variables, any nonzero multivariate
polynomial `P : MvPolynomial σ R` in finitely many variables with partial degrees
`P.degreeOf j ≤ s j` has an integer point `z : σ → ℤ` with `|z j| ≤ B j` and a multi-index
`i : σ →₀ ℕ` with `i j ≤ s j / B j` at which `(∂^i P)(z) ≠ 0` (Evertse 1996, §7, Lemma 25).

The core finite-grid results work in any characteristic: on a product of finite sets `S j`,
partial degrees strictly below `(S j).card * (M j + 1)` guarantee a nonzero jet of coordinate
orders at most `M j`. The integer-grid statements follow by counting integer points and orders.

## Main results

* `TauCeti.exists_eval_mvPolynomial_hasseDeriv_ne_zero`: nonvanishing on finite grids.
* `TauCeti.exists_eval_mvPolynomial_hasseDeriv_intCast_ne_zero`: Evertse's Lemma 25 on
  nonvanishing of a Hasse derivative on a rectangular integer grid.

## References

* J.-H. Evertse, *An improvement of the quantitative Subspace Theorem*, Compos. Math. 101 (1996),
  225–311, §7, Lemma 25.
-/

public section

namespace TauCeti

open _root_.MvPolynomial

variable {R : Type*}

/-- Inductive form of `exists_eval_mvPolynomial_hasseDeriv_ne_zero` on `Fin n`. -/
private theorem exists_eval_mvPolynomial_hasseDeriv_ne_zero_fin {n : ℕ} [CommRing R] [IsDomain R]
    {P : MvPolynomial (Fin n) R} (hP : P ≠ 0) (S : Fin n → Finset R) (M : Fin n → ℕ)
    (hdeg : ∀ j, P.degreeOf j < (S j).card * (M j + 1)) :
    ∃ x : Fin n → R, (∀ j, x j ∈ S j) ∧ ∃ i : Fin n →₀ ℕ,
      (∀ j, i j ≤ M j) ∧ eval x (hasseDeriv i P) ≠ 0 := by
  induction n with
  | zero =>
    refine ⟨0, fun j ↦ j.elim0, 0, fun j ↦ j.elim0, ?_⟩
    rw [hasseDeriv_zero, LinearMap.id_apply]
    intro h0
    apply hP
    rw [eq_C_of_isEmpty P] at h0 ⊢
    simpa using congrArg (C : R → MvPolynomial (Fin 0) R) h0
  | succ n ih =>
    obtain ⟨a, ha, k, hk, hQ⟩ := exists_eval_polynomial_hasseDeriv_ne_zero
      ((EmbeddingLike.map_ne_zero_iff (f := finSuccEquiv R n)).2 hP)
      ((S 0).map ⟨C, C_injective _ _⟩) (M 0) (by
        simpa only [natDegree_finSuccEquiv, Finset.card_map] using hdeg 0)
    obtain ⟨a, haS, rfl⟩ := Finset.mem_map.1 ha
    simp only [Function.Embedding.coeFn_mk] at hQ
    obtain ⟨x, hx, i, hi, hne⟩ := ih hQ (S ∘ Fin.succ) (M ∘ Fin.succ)
      (fun j ↦ (degreeOf_eval_hasseDeriv_finSuccEquiv_le P a k j).trans_lt (hdeg j.succ))
    refine ⟨Fin.cons a x, ?_, i.cons k, ?_, ?_⟩
    · intro j
      cases j using Fin.cases with
      | zero => exact haS
      | succ j => exact hx j
    · intro j
      cases j using Fin.cases with
      | zero => exact hk
      | succ j => exact hi j
    · rwa [eval_hasseDeriv_eval_hasseDeriv_finSuccEquiv] at hne

/-- A nonzero polynomial on a product of finite sets has a nonvanishing Hasse derivative with
coordinate orders bounded by `M`, provided each grid size times `M j + 1` exceeds the corresponding
partial degree. The coefficient ring may be an integral domain of any characteristic. -/
theorem exists_eval_mvPolynomial_hasseDeriv_ne_zero {σ : Type*} [Finite σ] [CommRing R] [IsDomain R]
    {P : MvPolynomial σ R} (hP : P ≠ 0) (S : σ → Finset R) (M : σ → ℕ)
    (hdeg : ∀ j, P.degreeOf j < (S j).card * (M j + 1)) :
    ∃ x : σ → R, (∀ j, x j ∈ S j) ∧ ∃ i : σ →₀ ℕ,
      (∀ j, i j ≤ M j) ∧ eval x (hasseDeriv i P) ≠ 0 := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  have hPe : rename e P ≠ 0 := (EmbeddingLike.map_ne_zero_iff (f := renameEquiv R e)).2 hP
  have hdege (j : Fin n) :
      (rename e P).degreeOf j < (S (e.symm j)).card * (M (e.symm j) + 1) := by
    classical
    conv_lhs => rw [← e.apply_symm_apply j, degreeOf_rename_of_injective e.injective]
    exact hdeg (e.symm j)
  obtain ⟨x, hx, i, hi, hne⟩ :=
    exists_eval_mvPolynomial_hasseDeriv_ne_zero_fin hPe (S ∘ e.symm) (M ∘ e.symm) hdege
  refine ⟨x ∘ e, fun j ↦ ?_, i.equivMapDomain e.symm, fun j ↦ ?_, ?_⟩
  · simpa using hx (e j)
  · simpa using hi (e j)
  · have hi_eq : (i.equivMapDomain e.symm).mapDomain e = i := by
      ext j
      simp [Finsupp.mapDomain_equiv_apply]
    rw [← hi_eq, eval_hasseDeriv_rename e.injective] at hne
    exact hne

/-- **Nonvanishing of Hasse derivatives on a rectangular integer grid**
(Evertse 1996, §7, Lemma 25). Over an integral domain `R` of characteristic zero, for any nonzero
polynomial `P : MvPolynomial σ R` in finitely many variables, any partial-degree bounds
`P.degreeOf j ≤ s j`, and any positive real numbers `B j > 0`, there exist an integer grid point
`z : σ → ℤ` with `|z j| ≤ B j` and a multi-index `i : σ →₀ ℕ` with `i j ≤ s j / B j` such that
the Hasse derivative `∂^i P` does not vanish at `z`. -/
theorem exists_eval_mvPolynomial_hasseDeriv_intCast_ne_zero {σ : Type*} [Finite σ] [CommRing R]
    [IsDomain R] [CharZero R] {P : MvPolynomial σ R} (hP : P ≠ 0) (s : σ → ℕ)
    (hs : ∀ j, P.degreeOf j ≤ s j) (B : σ → ℝ) (hB : ∀ j, 0 < B j) :
    ∃ z : σ → ℤ, ∃ i : σ →₀ ℕ,
      (∀ j, ((z j).natAbs : ℝ) ≤ B j) ∧
      (∀ j, (i j : ℝ) ≤ (s j : ℝ) / B j) ∧
      eval (fun j ↦ (z j : R)) (hasseDeriv i P) ≠ 0 := by
  let I (j : σ) : Finset ℤ := Finset.Icc (-(⌊B j⌋₊ : ℤ)) (⌊B j⌋₊ : ℤ)
  obtain ⟨x, hx, i, hi, hne⟩ := exists_eval_mvPolynomial_hasseDeriv_ne_zero hP
    (fun j ↦ (I j).map ⟨Int.cast, Int.cast_injective⟩) (fun j ↦ ⌊(s j : ℝ) / B j⌋₊)
    (fun j ↦ by
      rw [card_intCast_Icc_floor]
      exact (hs j).trans_lt
        (lt_two_mul_floor_add_one_mul_floor_div_add_one (s j) (hB j)))
  choose z hz hzx using fun j ↦ Finset.mem_map.1 (hx j)
  refine ⟨z, i, ?_, ?_, ?_⟩
  · exact fun j ↦ natAbs_le_of_mem_Icc_floor (hB j).le (hz j)
  · intro j
    exact (Nat.cast_le.2 (hi j)).trans
      (Nat.floor_le (div_nonneg (Nat.cast_nonneg (s j)) (hB j).le))
  · simpa only [← funext hzx, Function.Embedding.coeFn_mk] using hne

/-- In `0` variables, a nonzero constant polynomial `C c : MvPolynomial (Fin 0) ℤ` is already
nonzero at `z = 0` in derivative order `i = 0`. -/
example {c : ℤ} (hc : c ≠ 0) :
    eval (fun j : Fin 0 ↦ ((0 : Fin 0 → ℤ) j : ℤ))
      (hasseDeriv 0 (C c : MvPolynomial (Fin 0) ℤ)) ≠ 0 := by
  simpa using hc

/-- For `P = (X₀³ - X₀) X₁²` over `ℤ`, the Hasse derivative of order `(1, 2)` is `-1 ≠ 0`
at `(0, 0)`. -/
example :
    eval (0 : Fin 2 → ℤ)
      (hasseDeriv (Finsupp.single 0 1 + Finsupp.single 1 2)
        ((X 0 ^ 3 - X 0) * X 1 ^ 2 : MvPolynomial (Fin 2) ℤ)) = -1 := by
  have h1 : (X 0 ^ 3 * X 1 ^ 2 : MvPolynomial (Fin 2) ℤ) =
      monomial (Finsupp.single 0 3 + Finsupp.single 1 2) 1 := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]
  have h2 : (X 0 * X 1 ^ 2 : MvPolynomial (Fin 2) ℤ) =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 2) 1 := by
    rw [X, X_pow_eq_monomial, monomial_mul_monomial, one_mul]
  have hne : Finsupp.single 0 3 + Finsupp.single 1 2 ≠
      (Finsupp.single 0 1 + Finsupp.single 1 2 : Fin 2 →₀ ℕ) := by
    intro h
    have := DFunLike.congr_fun h 0
    simp at this
  rw [← coeff_taylor, taylor_zero, sub_mul, h1, h2]
  simp [hne]

end TauCeti

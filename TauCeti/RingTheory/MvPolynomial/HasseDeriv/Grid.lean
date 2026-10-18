/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.Algebra.Polynomial.Taylor
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.Taylor
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

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

## Main results

* `Polynomial.sum_rootMultiplicity_le_natDegree`: over an integral domain, the sum of the root
  multiplicities of `p : R[X]` over any finite set of points is at most `p.natDegree`.
* `Polynomial.exists_eval_hasseDeriv_intCast_ne_zero`: for `p : R[X]` nonzero of degree `≤ s` and
  `B > 0`, there exist `z : ℤ` and `i : ℕ` with `|z| ≤ B`, `i ≤ s / B`, and
  `(hasseDeriv i p).eval (z : R) ≠ 0`.
* `MvPolynomial.exists_eval_hasseDeriv_finSuccEquiv_ne_zero`: single-variable specialization step
  producing a grid point `(z, k)` in the first variable whose specialized `k`-th Hasse derivative is
  nonzero in the remaining variables.
* `MvPolynomial.exists_eval_hasseDeriv_intCast_ne_zero`: Evertse's Lemma 25 on nonvanishing of a
  Hasse derivative on a rectangular integer grid.

## References

* J.-H. Evertse, *An improvement of the quantitative Subspace Theorem*, Compos. Math. 101 (1996),
  225–311, §7, Lemma 25.
-/

public section

namespace Polynomial

variable {R : Type*}

/-- Over an integral domain, the sum of the root multiplicities of a polynomial `p` over any
finite set of points is at most `p.natDegree`. -/
theorem sum_rootMultiplicity_le_natDegree [CommRing R] [IsDomain R] (p : R[X]) (s : Finset R) :
    ∑ a ∈ s, p.rootMultiplicity a ≤ p.natDegree := by
  classical
  calc ∑ a ∈ s, p.rootMultiplicity a
      = ∑ a ∈ s, p.roots.count a := Finset.sum_congr rfl fun a _ ↦ (count_roots p).symm
    _ ≤ ∑ a ∈ p.roots.toFinset, p.roots.count a :=
        Finset.sum_le_sum_of_ne_zero fun a _ ha ↦
          Multiset.mem_toFinset.2 (Multiset.count_ne_zero.1 ha)
    _ = p.roots.card := Multiset.toFinset_sum_count_eq p.roots
    _ ≤ p.natDegree := card_roots' p

/-- For any degree bound `s : ℕ` and positive parameter `B : ℝ`, the number of integer grid points
in `[-⌊B⌋₊, ⌊B⌋₊]` times the number of derivative orders in `[0, ⌊s / B⌋₊]` strictly exceeds
`s`. -/
private theorem lt_two_mul_floor_add_one_mul_floor_div_add_one (s : ℕ) {B : ℝ} (hB : 0 < B) :
    s < (2 * ⌊B⌋₊ + 1) * (⌊(s : ℝ) / B⌋₊ + 1) := by
  have h1 : B < 2 * (⌊B⌋₊ : ℝ) + 1 := by
    linarith [Nat.lt_floor_add_one B, Nat.cast_nonneg (α := ℝ) ⌊B⌋₊]
  have h2 : (s : ℝ) / B < (⌊(s : ℝ) / B⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h3 : (s : ℝ) < (2 * (⌊B⌋₊ : ℝ) + 1) * ((⌊(s : ℝ) / B⌋₊ : ℝ) + 1) := by
    calc (s : ℝ) = B * ((s : ℝ) / B) := (mul_div_cancel₀ _ hB.ne').symm
      _ < (2 * (⌊B⌋₊ : ℝ) + 1) * ((⌊(s : ℝ) / B⌋₊ : ℝ) + 1) :=
          mul_lt_mul'' h1 h2 hB.le (div_nonneg (Nat.cast_nonneg s) hB.le)
  exact_mod_cast h3

/-- Over an integral domain of characteristic zero, for any nonzero polynomial `p : R[X]` of degree
at most `s` and any `B > 0`, there exist an integer `z` with `|z| ≤ B` and an order `i` with
`i ≤ s / B` such that the `i`-th Hasse derivative of `p` does not vanish at `z`. -/
theorem exists_eval_hasseDeriv_intCast_ne_zero [CommRing R] [IsDomain R] [CharZero R]
    {p : R[X]} (hp : p ≠ 0) {s : ℕ} (hs : p.natDegree ≤ s) {B : ℝ} (hB : 0 < B) :
    ∃ z : ℤ, ∃ i : ℕ,
      (z.natAbs : ℝ) ≤ B ∧ (i : ℝ) ≤ (s : ℝ) / B ∧ (hasseDeriv i p).eval (z : R) ≠ 0 := by
  by_contra! h
  set M : ℕ := ⌊B⌋₊
  set N : ℕ := ⌊(s : ℝ) / B⌋₊
  let I : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  have hcard : I.card = 2 * M + 1 := by
    rw [Int.card_Icc]
    omega
  have hmult (z : ℤ) (hz : z ∈ I) : N + 1 ≤ p.rootMultiplicity (z : R) := by
    obtain ⟨hz1, hz2⟩ := Finset.mem_Icc.1 hz
    have hza : (z.natAbs : ℝ) ≤ B :=
      (Nat.cast_le.2 (by omega : z.natAbs ≤ M)).trans (Nat.floor_le hB.le)
    refine le_rootMultiplicity_of_eval_hasseDeriv_eq_zero hp fun i hi ↦ h z i hza ?_
    exact (Nat.cast_le.2 (Nat.le_of_lt_succ hi)).trans
      (Nat.floor_le (div_nonneg (Nat.cast_nonneg s) hB.le))
  have hsum : (2 * M + 1) * (N + 1) ≤ s := by
    calc (2 * M + 1) * (N + 1)
        = ∑ _z ∈ I, (N + 1) := by rw [Finset.sum_const, hcard, smul_eq_mul]
      _ ≤ ∑ z ∈ I, p.rootMultiplicity (z : R) := Finset.sum_le_sum hmult
      _ = ∑ r ∈ I.map ⟨Int.cast, Int.cast_injective⟩, p.rootMultiplicity r :=
          (Finset.sum_map I ⟨Int.cast, Int.cast_injective⟩ p.rootMultiplicity).symm
      _ ≤ p.natDegree := p.sum_rootMultiplicity_le_natDegree _
      _ ≤ s := hs
  exact (lt_two_mul_floor_add_one_mul_floor_div_add_one s hB).not_ge hsum

/-- For `p = X (X - 1) (X + 1) = X³ - X` over `ℤ` with `s = 3` and `B = 1`, `p` vanishes in order
`i = 0` at every integer `z ∈ {-1, 0, 1}`, while its first Hasse derivative `3 X² - 1` is nonzero
there. -/
example : (∀ z ∈ ({-1, 0, 1} : Finset ℤ),
      (hasseDeriv 0 (X ^ 3 - X : ℤ[X])).eval z = 0) ∧
    (hasseDeriv 1 (X ^ 3 - X : ℤ[X])).eval (0 : ℤ) ≠ 0 := by
  refine ⟨by simp [hasseDeriv_zero], ?_⟩
  simp

/-- For `p = X³` over `ℤ` with `s = 3` and `B = 1 / 2`, the only integer with `|z| ≤ 1 / 2` is
`z = 0`, where the Hasse derivatives of orders `0, 1, 2` vanish and the Hasse derivative of order
`3` is `1 ≠ 0`. -/
example : (∀ i < 3, (hasseDeriv i (X ^ 3 : ℤ[X])).eval (0 : ℤ) = 0) ∧
    (hasseDeriv 3 (X ^ 3 : ℤ[X])).eval (0 : ℤ) = 1 := by
  refine ⟨fun i hi ↦ ?_, by simp [← taylor_coeff]⟩
  rw [← taylor_coeff, taylor_zero', LinearMap.id_apply, coeff_X_pow, ite_eq_right (by omega)]

/-- In positive characteristic, `exists_eval_hasseDeriv_intCast_ne_zero` can fail: over `ZMod 2`,
the nonzero polynomial `X² - X` of degree `2` vanishes in order `0` at every integer cast, so
`s = 2` and `B = 3` (which forces `i ≤ ⌊2 / 3⌋ = 0`) admit no nonvanishing grid jet. -/
example : (X ^ 2 - X : (ZMod 2)[X]) ≠ 0 ∧
    ∀ z : ℤ, (hasseDeriv 0 (X ^ 2 - X : (ZMod 2)[X])).eval (z : ZMod 2) = 0 := by
  refine ⟨?_, fun z ↦ ?_⟩
  · intro h
    have := congrArg (fun p : (ZMod 2)[X] ↦ p.coeff 1) h
    simp at this
  · rw [hasseDeriv_zero, LinearMap.id_apply, eval_sub, eval_pow, eval_X]
    generalize (z : ZMod 2) = x
    fin_cases x <;> rfl

end Polynomial

namespace MvPolynomial

variable {R : Type*}

/-- Over an integral domain of characteristic zero, for any nonzero polynomial
`P : MvPolynomial (Fin (n + 1)) R` with `P.degreeOf 0 ≤ s` and any `B > 0`, there exist an integer
`z` with `|z| ≤ B` and an order `k` with `k ≤ s / B` such that specializing `X₀` to `z` in the
`k`-th univariate Hasse derivative of `finSuccEquiv R n P` gives a nonzero polynomial in the
remaining variables. -/
theorem exists_eval_hasseDeriv_finSuccEquiv_ne_zero {n : ℕ} [CommRing R] [IsDomain R]
    [CharZero R] {P : MvPolynomial (Fin (n + 1)) R} (hP : P ≠ 0) {s : ℕ}
    (hs : P.degreeOf 0 ≤ s) {B : ℝ} (hB : 0 < B) :
    ∃ z : ℤ, ∃ k : ℕ,
      (z.natAbs : ℝ) ≤ B ∧ (k : ℝ) ≤ (s : ℝ) / B ∧
      (Polynomial.hasseDeriv k (finSuccEquiv R n P)).eval (C (z : R)) ≠ 0 := by
  obtain ⟨z, k, hz, hk, hne⟩ := (finSuccEquiv R n P).exists_eval_hasseDeriv_intCast_ne_zero
    ((EmbeddingLike.map_ne_zero_iff (f := finSuccEquiv R n)).2 hP)
    ((natDegree_finSuccEquiv P).le.trans hs) hB
  exact ⟨z, k, hz, hk, by rwa [_root_.map_intCast]⟩

/-- Inductive form of `exists_eval_hasseDeriv_intCast_ne_zero` on `Fin n`. -/
private theorem exists_eval_hasseDeriv_intCast_ne_zero_fin {n : ℕ} [CommRing R] [IsDomain R]
    [CharZero R] {P : MvPolynomial (Fin n) R} (hP : P ≠ 0) (s : Fin n → ℕ)
    (hs : ∀ j, P.degreeOf j ≤ s j) (B : Fin n → ℝ) (hB : ∀ j, 0 < B j) :
    ∃ z : Fin n → ℤ, ∃ i : Fin n →₀ ℕ,
      (∀ j, ((z j).natAbs : ℝ) ≤ B j) ∧
      (∀ j, (i j : ℝ) ≤ (s j : ℝ) / B j) ∧
      eval (fun j ↦ (z j : R)) (hasseDeriv i P) ≠ 0 := by
  induction n with
  | zero =>
    refine ⟨0, 0, fun j ↦ j.elim0, fun j ↦ j.elim0, ?_⟩
    rw [hasseDeriv_zero, LinearMap.id_apply]
    intro h0
    exact hP ((eq_C_of_isEmpty P).trans (by
      rw [← constantCoeff_eq, ← eval_zero, Subsingleton.elim 0 (fun j ↦ _), h0, map_zero]))
  | succ n ih =>
    obtain ⟨z₀, k, hz₀, hk, hQ⟩ :=
      exists_eval_hasseDeriv_finSuccEquiv_ne_zero hP (hs 0) (hB 0)
    obtain ⟨z', i', hz', hi', hne⟩ := ih hQ (s ∘ Fin.succ)
      (fun j ↦ (degreeOf_eval_hasseDeriv_finSuccEquiv_le P (z₀ : R) k j).trans (hs j.succ))
      (B ∘ Fin.succ) (fun j ↦ hB j.succ)
    refine ⟨Fin.cons z₀ z', i'.cons k, ?_, ?_, ?_⟩
    · intro j
      cases j using Fin.cases with
      | zero => exact hz₀
      | succ j => exact hz' j
    · intro j
      cases j using Fin.cases with
      | zero => exact hk
      | succ j => exact hi' j
    · have hcons : (fun j : Fin (n + 1) ↦ (Fin.cons (α := fun _ ↦ ℤ) z₀ z' j : R)) =
          Fin.cons (z₀ : R) (fun j ↦ (z' j : R)) := by
        ext j
        cases j using Fin.cases <;> rfl
      rw [hcons, ← eval_hasseDeriv_eval_finSuccEquiv]
      exact hne

/-- **Nonvanishing of Hasse derivatives on a rectangular integer grid**
(Evertse 1996, §7, Lemma 25). Over an integral domain `R` of characteristic zero, for any nonzero
polynomial `P : MvPolynomial σ R` in finitely many variables, any partial-degree bounds
`P.degreeOf j ≤ s j`, and any positive real numbers `B j > 0`, there exist an integer grid point
`z : σ → ℤ` with `|z j| ≤ B j` and a multi-index `i : σ →₀ ℕ` with `i j ≤ s j / B j` such that
the Hasse derivative `∂^i P` does not vanish at `z`. -/
theorem exists_eval_hasseDeriv_intCast_ne_zero {σ : Type*} [Finite σ] [CommRing R] [IsDomain R]
    [CharZero R] {P : MvPolynomial σ R} (hP : P ≠ 0) (s : σ → ℕ)
    (hs : ∀ j, P.degreeOf j ≤ s j) (B : σ → ℝ) (hB : ∀ j, 0 < B j) :
    ∃ z : σ → ℤ, ∃ i : σ →₀ ℕ,
      (∀ j, ((z j).natAbs : ℝ) ≤ B j) ∧
      (∀ j, (i j : ℝ) ≤ (s j : ℝ) / B j) ∧
      eval (fun j ↦ (z j : R)) (hasseDeriv i P) ≠ 0 := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  have hPe : rename e P ≠ 0 := (EmbeddingLike.map_ne_zero_iff (f := renameEquiv R e)).2 hP
  have hse (j : Fin n) : (rename e P).degreeOf j ≤ s (e.symm j) := by
    classical
    conv_lhs => rw [← e.apply_symm_apply j, degreeOf_rename_of_injective e.injective]
    exact hs (e.symm j)
  obtain ⟨z, i, hz, hi, hne⟩ :=
    exists_eval_hasseDeriv_intCast_ne_zero_fin hPe (s ∘ e.symm) hse (B ∘ e.symm)
      (fun j ↦ hB (e.symm j))
  refine ⟨z ∘ e, i.equivMapDomain e.symm, fun j ↦ ?_, fun j ↦ ?_, ?_⟩
  · simpa using hz (e j)
  · simpa using hi (e j)
  · have hi_eq : (i.equivMapDomain e.symm).mapDomain e = i := by
      ext j
      simp [Finsupp.mapDomain_equiv_apply]
    rw [← hi_eq, eval_hasseDeriv_rename e.injective] at hne
    exact hne

/-- In `0` variables, a nonzero constant polynomial `C c : MvPolynomial (Fin 0) ℤ` is already
nonzero at `z = 0` in derivative order `i = 0`. -/
example {c : ℤ} (hc : c ≠ 0) :
    eval (fun j : Fin 0 ↦ ((0 : Fin 0 → ℤ) j : ℤ))
      (hasseDeriv 0 (C c : MvPolynomial (Fin 0) ℤ)) ≠ 0 := by
  simpa using hc

/-- For `P = (X₀³ - X₀) X₁²` over `ℤ` with `s = ![3, 2]` and `B = ![1, 1 / 2]`, `P` vanishes in
derivative order `0` at every integer point with `|z₀| ≤ 1` and `|z₁| ≤ 1 / 2`, while its Hasse
derivative of order `(1, 2)` is `-1 ≠ 0` at `(0, 0)`. -/
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

end MvPolynomial

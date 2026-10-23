/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Scaling the variables of a homogeneous polynomial

Evaluating a homogeneous polynomial of degree `n` after multiplying every variable by `a`
multiplies its value by `a ^ n`. This permits normalizing linear substitutions without
expanding the polynomial.

The results live in `MvPolynomial.IsHomogeneous`, so a homogeneity proof supports dot
notation such as `hp.eval₂_const_mul`, `hp.aeval_smul`, and `hp.eval_smul`. In the same way
`hp.coeff_single_eq_eval` reads the coefficient of `X_j ^ n` off the value at the `j`-th basis
vector, `hp.aeval_eq_sum_finsuppAntidiag` expands a value as a sum over the exponent vectors of
degree `n`, `hp.constantCoeff_eq_zero` records that the constant coefficient vanishes in
positive degree, `hp.natDegree_aeval_le` bounds by `n` the degree of a substitution of
polynomials of degree at most one, and `hp.homogeneousComponent_mul_right` records that
multiplying on the right by a homogeneous polynomial of degree `d` shifts homogeneous components
by `d`.

The file also records `MvPolynomial.isHomogeneous_coeff_prod_X_sub_C`: the coefficients of a
product of linear factors `X - C Ψ` with homogeneous `Ψ` of degree `m` are homogeneous, and
`TauCeti.sum_smul_X_pow_mem_homogeneousSubmodule`: the `n`-th power of a linear form is
homogeneous of degree `n`.
-/

public section

namespace MvPolynomial.IsHomogeneous

/-- Scaling all variables by `a` scales the value of a degree-`n` homogeneous polynomial
by `a ^ n`, after any change of coefficient ring.

This is not a global `simp` lemma: the degree `n` cannot be inferred from its left-hand side. -/
theorem eval₂_const_mul {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (f : R →+* S) (g : σ → S) (a : S) :
    _root_.MvPolynomial.eval₂ f (fun i ↦ a * g i) p =
      a ^ n * _root_.MvPolynomial.eval₂ f g p := by
  classical
  simp only [_root_.MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : ∑ i ∈ d.support, d i = n := (hp.degree_eq_sum_deg_support hd).symm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- Scaling the variables of a homogeneous polynomial by a scalar scales its algebra
evaluation by the corresponding power of that scalar. The scalar algebra may differ
from the coefficient algebra. -/
theorem aeval_smul {σ R S A : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring A] [Algebra R A] [Algebra S A]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) (g : σ → A) (a : S) :
    _root_.MvPolynomial.aeval (a • g) p = a ^ n • _root_.MvPolynomial.aeval g p := by
  rw [Pi.smul_def]
  simpa only [_root_.MvPolynomial.aeval_def, Algebra.smul_def, map_pow] using
    hp.eval₂_const_mul (algebraMap R A) g (algebraMap S A a)

/-- Scaling the variables of a homogeneous polynomial scales its evaluation by the
corresponding power of the scalar. -/
theorem eval_smul {σ R : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) (g : σ → R) (a : R) :
    _root_.MvPolynomial.eval (a • g) p = a ^ n • _root_.MvPolynomial.eval g p := by
  simpa only [_root_.MvPolynomial.eval, coe_eval₂Hom, Pi.smul_def, smul_eq_mul] using
    hp.eval₂_const_mul (RingHom.id R) g a

/-- The coefficient of `X_j ^ n` in a homogeneous polynomial of degree `n` is its value at the
`j`-th basis vector: every other monomial involves a variable other than `X_j`. -/
theorem coeff_single_eq_eval {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) (j : σ) :
    p.coeff (Finsupp.single j n) = _root_.MvPolynomial.eval (Pi.single j 1) p := by
  conv_rhs => rw [p.as_sum]
  rw [map_sum, Finset.sum_eq_single (Finsupp.single j n)]
  · simp [_root_.MvPolynomial.eval_monomial]
  · intro s hs hne
    obtain ⟨i, hij, hi⟩ : ∃ i, i ≠ j ∧ s i ≠ 0 := by
      by_contra! h
      have hs' : s = Finsupp.single j (s j) := Finsupp.ext fun i ↦ by
        by_cases hi : i = j
        · simp [hi]
        · simp [hi, h i hi]
      have hdeg := hp (_root_.MvPolynomial.mem_support_iff.mp hs)
      rw [hs'] at hdeg
      simp only [Finsupp.weight_apply, Finsupp.sum_single_index, Pi.one_apply, smul_eq_mul,
        mul_one] at hdeg
      exact hne (hs'.trans (by rw [hdeg]))
    rw [_root_.MvPolynomial.eval_monomial, Finsupp.prod,
      Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
        (by rw [Pi.single_eq_of_ne hij, zero_pow hi]), mul_zero]
  · intro h
    simp [_root_.MvPolynomial.notMem_support_iff.mp h]

/-- A homogeneous polynomial of positive degree has zero constant coefficient. -/
theorem constantCoeff_eq_zero {σ R : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) (hn : n ≠ 0) :
    _root_.MvPolynomial.constantCoeff p = 0 := by
  rw [_root_.MvPolynomial.constantCoeff_eq]
  exact hp.coeff_eq_zero (by simpa using hn.symm)

/-- Substituting polynomials of degree at most one for the variables of a homogeneous
polynomial of degree `n` gives a polynomial of degree at most `n`. For instance, the
dehomogenization `F(X, 1)` of a binary form `F` of degree `n` has degree at most `n`. -/
theorem natDegree_aeval_le {σ R : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) {v : σ → Polynomial R}
    (hv : ∀ i, (v i).natDegree ≤ 1) : (_root_.MvPolynomial.aeval v p).natDegree ≤ n := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs ↦ ?_
  rw [aeval_monomial, Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans <| (Polynomial.natDegree_prod_le _ _).trans ?_
  rw [← hp (mem_support_iff.mp hs), Finsupp.weight_apply, Finsupp.sum]
  refine Finset.sum_le_sum fun i _ ↦ (Polynomial.natDegree_pow_le).trans ?_
  simpa using Nat.mul_le_mul_left (s i) (hv i)

attribute [local instance] gradedAlgebra in
/-- Multiplying by a polynomial homogeneous of degree `d` shifts homogeneous components by `d`:
the degree-`n` component of `a * t` is `homogeneousComponent (n - d) a * t` when `d ≤ n`, and
vanishes otherwise. -/
theorem homogeneousComponent_mul_right {σ R : Type*} [CommSemiring R]
    {t : MvPolynomial σ R} {d : ℕ} (ht : t.IsHomogeneous d) (a : MvPolynomial σ R) (n : ℕ) :
    homogeneousComponent n (a * t) =
      if d ≤ n then homogeneousComponent (n - d) a * t else 0 := by
  have key (φ : MvPolynomial σ R) (i : ℕ) :
      (DirectSum.decompose (homogeneousSubmodule σ R) φ i : MvPolynomial σ R) =
        homogeneousComponent i φ :=
    decomposition.decompose'_apply φ i
  simpa only [key] using DirectSum.coe_decompose_mul_of_right_mem (homogeneousSubmodule σ R) n
    (a := a) ((mem_homogeneousSubmodule d t).mpr ht)

/-- The value of a homogeneous polynomial of degree `n` in finitely many variables is the sum, over
the exponent vectors `l` of total degree `n`, of its coefficient at `l` times the corresponding
monomial in the values: no monomial of any other degree occurs. -/
theorem aeval_eq_sum_finsuppAntidiag {σ R S : Type*} [Fintype σ] [DecidableEq σ]
    [CommSemiring R] [CommSemiring S] [Algebra R S] {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) (f : σ → S) :
    _root_.MvPolynomial.aeval f p = ∑ l ∈ Finset.univ.finsuppAntidiag n,
      algebraMap R S (p.coeff l) * ∏ i, f i ^ l i := by
  rw [_root_.MvPolynomial.aeval_def, _root_.MvPolynomial.eval₂_eq']
  refine Finset.sum_subset (fun l hl => Finset.mem_finsuppAntidiag.mpr
    ⟨?_, Finset.subset_univ _⟩) fun l _ hl => ?_
  · rw [← Finsupp.degree_eq_sum]
    exact (hp.degree_eq_sum_deg_support hl).symm
  · rw [notMem_support_iff.mp hl, map_zero, zero_mul]

end MvPolynomial.IsHomogeneous

namespace MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- The coefficient of `X ^ k` in a product of linear factors `X - C Ψ`, whose constant terms `Ψ`
are all homogeneous of degree `m`, is homogeneous of degree `m * (s.card - k)`. -/
theorem isHomogeneous_coeff_prod_X_sub_C {ι : Type*} (s : Finset ι)
    (Ψ : ι → MvPolynomial σ R) {m : ℕ} (hΨ : ∀ i ∈ s, (Ψ i).IsHomogeneous m) (k : ℕ) :
    ((∏ i ∈ s, (Polynomial.X - Polynomial.C (Ψ i))).coeff k).IsHomogeneous
      (m * (s.card - k)) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    rw [Finset.prod_empty, Polynomial.coeff_one]
    split_ifs
    · simpa using isHomogeneous_one σ R
    · exact isHomogeneous_zero σ R _
  | insert a s ha ih =>
    have hs (k : ℕ) := ih (fun i hi => hΨ i (Finset.mem_insert_of_mem hi)) k
    have ha' := hΨ a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, mul_comm]
    rcases k with _ | j
    · rw [Polynomial.mul_coeff_zero, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
        Polynomial.coeff_C_zero, zero_sub, Nat.sub_zero, mul_add_one]
      have h0 := hs 0
      rw [Nat.sub_zero] at h0
      exact h0.mul ha'.neg
    · rw [Polynomial.coeff_mul_X_sub_C, Nat.add_sub_add_right]
      refine (hs j).sub ?_
      by_cases hj : j + 1 ≤ s.card
      · have hdeg : s.card - j = s.card - (j + 1) + 1 := by omega
        rw [hdeg, mul_add_one]
        exact (hs (j + 1)).mul ha'
      · have hle : (∏ i ∈ s, (Polynomial.X - Polynomial.C (Ψ i))).natDegree ≤ s.card := by
          refine (Polynomial.natDegree_prod_le _ _).trans ?_
          simpa using Finset.sum_le_card_nsmul s _ 1 fun i _ =>
            Polynomial.natDegree_X_sub_C_le (Ψ i)
        have hlt : (∏ i ∈ s, (Polynomial.X - Polynomial.C (Ψ i))).natDegree < j + 1 := by
          omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, zero_mul]
        exact isHomogeneous_zero σ R _

end MvPolynomial

namespace TauCeti

open MvPolynomial

/-- The `n`-th power of a linear form is homogeneous of degree `n`. -/
theorem sum_smul_X_pow_mem_homogeneousSubmodule {σ R : Type*} [Fintype σ] [CommSemiring R]
    (x : σ → R) (n : ℕ) :
    (∑ i, x i • X i : MvPolynomial σ R) ^ n ∈ homogeneousSubmodule σ R n := by
  have h1 : (∑ i, x i • X i : MvPolynomial σ R) ∈ homogeneousSubmodule σ R 1 :=
    Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ ((mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X R i))
  simpa using ((mem_homogeneousSubmodule 1 _).mp h1).pow n

end TauCeti

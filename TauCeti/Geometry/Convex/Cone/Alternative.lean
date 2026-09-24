/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.DotProduct
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Theorems of the alternative for nonnegative vectors

This file proves the classical theorems of the alternative of Gordan, Stiemke and Tucker over an
arbitrary linearly ordered field.

For a finite family of vectors `a j` in a vector space over a linearly ordered field `K`,
*Gordan's theorem* says that either some linear functional is strictly positive on every `a j`,
or the family admits a nontrivial linear relation with nonnegative coefficients, and not both.
Applied to the images of the coordinate vectors in a quotient `(ι → K) ⧸ S`, it becomes
*Stiemke's theorem*: a subspace `S` contains no nonzero nonnegative vector exactly when some
strictly positive vector is orthogonal to all of `S`. Both are consequences of *Tucker's key
lemma*, which for each index `k` produces a nonnegative relation `x` and a functional `y` that is
nonnegative on the family, one of them strictly positive at `k`. Unlike Mathlib's
separation-based Farkas lemma `ProperCone.hyperplane_separation`, these results apply over `ℚ`.

The integer-lattice form of Stiemke's theorem is proved in
`TauCeti.Algebra.Group.AddSubgroup.PositiveWeights`. The equivalent finiteness condition for
nonnegative vectors in cosets is proved in `TauCeti.Algebra.Group.AddSubgroup.NonnegativeCoset`.

These results supply the field-level alternative needed for the integer-lattice admissibility
lemmas of Heegaard Floer theory.

## Main declarations

* `TauCeti.exists_nonneg_sum_smul_eq_zero_and_dual_nonneg`: Tucker's key lemma.
* `TauCeti.exists_forall_dual_pos_iff`: Gordan's theorem.
* `TauCeti.submodule_exists_pos_dotProduct_eq_zero_iff`: Stiemke's theorem for a subspace of
  `ι → K`.

## References

* A. W. Tucker, *Dual systems of homogeneous linear relations*, in *Linear Inequalities and
  Related Systems*, Annals of Mathematics Studies 38, 1956, Lemma 1.
* C. G. Broyden, *A simple algebraic proof of Farkas's lemma and related theorems*, Optimization
  Methods and Software 8 (1998).
* P. Ozsváth, Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. 159 (2004), [arXiv:math/0101206](https://arxiv.org/abs/math/0101206),
  Lemmas 4.12 and 4.13.
-/

public section

namespace TauCeti

variable {ι K V : Type*}

section Field

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup V] [Module K V]

/-- Tucker's key lemma for the vectors indexed by `insert k s`. -/
private theorem exists_nonneg_sum_smul_eq_zero_and_dual_nonneg_of_finset [DecidableEq ι] (k : ι)
    (s : Finset ι) (a : ι → V) :
    ∃ x : ι → K, ∃ y : Module.Dual K V, (∀ j ∈ insert k s, 0 ≤ x j ∧ 0 ≤ y (a j)) ∧
      ∑ j ∈ insert k s, x j • a j = 0 ∧ 0 < x k + y (a k) := by
  induction s using Finset.induction_on generalizing a with
  | empty =>
    by_cases ha : a k = 0
    · exact ⟨Pi.single k 1, 0, by simp, by simp [ha], by simp⟩
    · obtain ⟨y, hy⟩ := Module.Projective.exists_dual_eq_one K ha
      exact ⟨0, y, by simp [hy], by simp, by simp [hy]⟩
  | insert n s hn ih =>
    by_cases hnk : n = k
    · subst hnk
      simpa only [Finset.insert_idem] using ih a
    have hn' : n ∉ insert k s := by simp [hn, hnk]
    have hne : ∀ j ∈ insert k s, j ≠ n := fun j hj h => hn' (h ▸ hj)
    rw [Finset.insert_comm]
    obtain ⟨x, y, hxy, hsum, hpos⟩ := ih a
    by_cases hy : 0 ≤ y (a n)
    · -- `y` is already nonnegative on the new vector: extend `x` by zero.
      refine ⟨Function.update x n 0, y, ?_, ?_, ?_⟩
      · rintro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · simp [hy]
        · simpa [Function.update_of_ne (hne j hj)] using hxy j hj
      · rw [Finset.sum_insert hn', Function.update_self, zero_smul, zero_add, ← hsum]
        exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (hne j hj)]
      · rwa [Function.update_of_ne (Ne.symm hnk)]
    · -- Otherwise project the old vectors along `a n` onto `ker y` and apply the induction
      -- hypothesis to the projected family `b j = a j + c j • a n`, where `y (b j) = 0`.
      push Not at hy
      set d := y (a n)
      have hd : d ≠ 0 := hy.ne
      set c : ι → K := fun j => -y (a j) / d
      have hc : ∀ j ∈ insert k s, 0 ≤ c j := fun j hj =>
        div_nonneg_of_nonpos (neg_nonpos.2 (hxy j hj).2) hy.le
      obtain ⟨u, z, huz, hsum', hpos'⟩ := ih fun j => a j + c j • a n
      set w : Module.Dual K V := z + (-z (a n) / d) • y
      have hw : ∀ j, w (a j) = z (a j + c j • a n) := fun j => by
        simp only [w, c, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
          smul_eq_mul]
        field_simp
      refine ⟨Function.update u n (∑ j ∈ insert k s, c j * u j), w, ?_, ?_, ?_⟩
      · rintro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · refine ⟨?_, ?_⟩
          · rw [Function.update_self]
            exact Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (huz i hi).1
          · simp only [w, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
            rw [div_mul_cancel₀ _ hd, add_neg_cancel]
        · rw [Function.update_of_ne (hne j hj), hw]
          exact huz j hj
      · rw [Finset.sum_insert hn', Function.update_self, ← hsum', Finset.sum_smul]
        simp only [smul_add, smul_smul, Finset.sum_add_distrib]
        rw [add_comm]
        congr 1
        · exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (hne j hj)]
        · exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
      · rw [Function.update_of_ne (Ne.symm hnk), hw]
        exact hpos'

/-- **Tucker's key lemma.** For a finite family of vectors `a j` and an index `k`, there are a
nonnegative linear relation `x` among the `a j` and a linear functional `y` that is nonnegative on
every `a j`, such that `x k + y (a k) > 0`: either `a k` occurs in a nonnegative relation, or some
functional nonnegative on the family is strictly positive on `a k`. -/
theorem exists_nonneg_sum_smul_eq_zero_and_dual_nonneg [Fintype ι] (a : ι → V) (k : ι) :
    ∃ x : ι → K, ∃ y : Module.Dual K V, 0 ≤ x ∧ ∑ j, x j • a j = 0 ∧ (∀ j, 0 ≤ y (a j)) ∧
      0 < x k + y (a k) := by
  classical
  obtain ⟨x, y, hxy, hsum, hpos⟩ :=
    exists_nonneg_sum_smul_eq_zero_and_dual_nonneg_of_finset (K := K) k (Finset.univ.erase k) a
  rw [Finset.insert_erase (Finset.mem_univ k)] at hxy hsum
  exact ⟨x, y, fun j => (hxy j (Finset.mem_univ j)).1, hsum,
    fun j => (hxy j (Finset.mem_univ j)).2, hpos⟩

/-- **Gordan's theorem.** Some linear functional is strictly positive on every vector of a finite
family exactly when the only nonnegative linear relation among the vectors is the trivial one. -/
theorem exists_forall_dual_pos_iff [Fintype ι] (a : ι → V) :
    (∃ y : Module.Dual K V, ∀ j, 0 < y (a j)) ↔
      ∀ x : ι → K, 0 ≤ x → ∑ j, x j • a j = 0 → x = 0 := by
  constructor
  · rintro ⟨y, hy⟩ x hx hsum
    refine (dotProduct_eq_zero_iff_of_pos hy hx).1 ?_
    simpa [dotProduct, mul_comm] using congrArg y hsum
  · intro h
    choose x y hx hsum hy hpos using exists_nonneg_sum_smul_eq_zero_and_dual_nonneg (K := K) a
    refine ⟨∑ k, y k, fun j => ?_⟩
    rw [LinearMap.sum_apply]
    refine Finset.sum_pos' (fun k _ => hy k j) ⟨j, Finset.mem_univ j, ?_⟩
    simpa [h (x j) (hx j) (hsum j)] using hpos j

end Field

section Field

variable {ι K : Type*} [Fintype ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Stiemke's theorem.** A subspace `S` of `ι → K` contains no nonzero nonnegative vector
exactly when some vector with strictly positive coordinates is orthogonal to all of `S`. -/
theorem submodule_exists_pos_dotProduct_eq_zero_iff (S : Submodule K (ι → K)) :
    (∃ c : ι → K, (∀ i, 0 < c i) ∧ ∀ x ∈ S, c ⬝ᵥ x = 0) ↔ ∀ x ∈ S, 0 ≤ x → x = 0 := by
  classical
  constructor
  · rintro ⟨c, hc, hS⟩ x hx hx0
    exact (dotProduct_eq_zero_iff_of_pos hc hx0).1 (hS x hx)
  · intro h
    -- Apply Gordan's theorem to the images of the coordinate vectors in `(ι → K) ⧸ S`.
    have hmk : ∀ x : ι → K, ∑ j, x j • S.mkQ (Pi.single j 1) = S.mkQ x := fun x => by
      conv_rhs => rw [pi_eq_sum_univ' x]
      simp only [map_sum, map_smul]
    obtain ⟨y, hy⟩ := (exists_forall_dual_pos_iff fun j => S.mkQ (Pi.single j 1)).2
      fun x hx hsum => h x ((Submodule.Quotient.mk_eq_zero S).1 ((hmk x).symm.trans hsum)) hx
    refine ⟨fun j => y (S.mkQ (Pi.single j 1)), hy, fun x hx => ?_⟩
    have := congrArg y (hmk x)
    simp only [map_sum, map_smul, smul_eq_mul, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero S).2 hx, map_zero] at this
    simpa [dotProduct, mul_comm] using this

end Field
end TauCeti

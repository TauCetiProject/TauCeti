/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Lifting linear independence from `k` to `k[X]`

Let `M` be a `k[X]`-module. A family in `M` that is linearly independent over `k` need not be
linearly independent over `k[X]`. It is, provided `X` acts injectively on the `k[X]`-span of the
family and the `k`-span of the family meets `X` times its `k[X]`-span only in zero: a relation over
`k[X]` then has vanishing constant terms, so it can be divided by `X` indefinitely.

## Main results

* `LinearIndependent.polynomial`: a `k`-linearly independent family is `k[X]`-linearly independent
  if `X` is injective on its `k[X]`-span and its `k`-span meets `X` times that span only in zero.
-/

public section

open Polynomial

namespace LinearIndependent

variable {k M ι : Type*} [CommRing k] [AddCommGroup M] [Module k M] [Module k[X] M]
  [IsScalarTower k k[X] M] {b : ι → M}

/-- A family that is linearly independent over `k` is linearly independent over `k[X]`, provided
`X` acts injectively on its `k[X]`-span and its `k`-span meets `X` times its `k[X]`-span only in
zero. A relation over `k[X]` then has vanishing constant terms, so it can be divided by `X`
indefinitely. -/
theorem polynomial (hli : LinearIndependent k b)
    (hreg : ∀ x ∈ Submodule.span k[X] (Set.range b), (X : k[X]) • x = 0 → x = 0)
    (hdisj : ∀ z ∈ Submodule.span k (Set.range b), ∀ y ∈ Submodule.span k[X] (Set.range b),
      z = (X : k[X]) • y → z = 0) :
    LinearIndependent k[X] b := by
  classical
  rw [linearIndependent_iff']
  have hdvd (n : ℕ) : ∀ (t : Finset ι) (g : ι → k[X]),
      ∑ i ∈ t, g i • b i = 0 → ∀ i ∈ t, X ^ n ∣ g i := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro t g hg
      have hsplit : ∑ i ∈ t, g i • b i =
          (X : k[X]) • ∑ i ∈ t, (g i).divX • b i + ∑ i ∈ t, (g i).coeff 0 • b i := by
        rw [Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        conv_lhs => rw [← X_mul_divX_add (g i)]
        rw [add_smul, mul_smul, ← algebraMap_eq, algebraMap_smul]
      have hdiv_mem : ∑ i ∈ t, (g i).divX • b i ∈ Submodule.span k[X] (Set.range b) :=
        Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hc : ∑ i ∈ t, (g i).coeff 0 • b i = 0 := by
        refine hdisj _ (Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
          (Submodule.subset_span ⟨i, rfl⟩)) _ (Submodule.neg_mem _ hdiv_mem) ?_
        rw [smul_neg, eq_neg_iff_add_eq_zero, add_comm, ← hsplit, hg]
      have hc0 := linearIndependent_iff'.mp hli t _ hc
      have hdiv : ∑ i ∈ t, (g i).divX • b i = 0 := by
        refine hreg _ hdiv_mem ?_
        rw [hg, hc, add_zero] at hsplit
        exact hsplit.symm
      intro i hi
      obtain ⟨q, hq⟩ := ih t _ hdiv i hi
      refine ⟨q, ?_⟩
      rw [← X_mul_divX_add (g i), hc0 i hi, C_0, add_zero, hq, pow_succ', mul_assoc]
  intro t g hg i hi
  ext m
  exact X_pow_dvd_iff.mp (hdvd (m + 1) t g hg i hi) m m.lt_succ_self

end LinearIndependent

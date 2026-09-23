/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Sums over ordered pairs

A sum of `F : l × l → M` over all ordered pairs, for `l` a finite linear order, can be folded onto
the increasing pairs by adding each term to its transpose. When `F` vanishes on the diagonal the
diagonal contributes nothing and the fold is exact, which is
`TauCeti.sum_univ_prod_eq_sum_lt_add_swap`.

This is the shape a sum indexed by unordered pairs takes once the linear order is used to name each
pair by its increasing representative. It is what lets an antisymmetric summand, for which the two
terms of a transposed pair combine, be summed over pairs rather than over ordered pairs.

For a symmetric summand the increasing representative carries no information beyond the unordered
pair, so a product `∏_{i<j} f i j` over the increasing pairs is unchanged when the indices are
permuted, which is `TauCeti.prod_prod_Ioi_comp_perm`. This is the symmetric counterpart of
Mathlib's `Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod`, where an antisymmetric summand picks up the
sign of the permutation.

## Main results

* `TauCeti.sum_univ_prod_eq_sum_lt_add_swap`: a sum over all ordered pairs of a function vanishing
  on the diagonal, as a sum over the increasing pairs of the term plus its transpose.
* `TauCeti.prod_prod_Ioi_comp_perm`: a product of a symmetric function over the increasing pairs is
  invariant under permuting the indices.
-/

public section

namespace TauCeti

open Finset

/-- **A sum over all ordered pairs, folded onto the increasing ones.** A function vanishing on the
diagonal sums over `l × l` to the sum over the increasing pairs of its value together with its
value at the transposed pair. -/
theorem sum_univ_prod_eq_sum_lt_add_swap {l : Type*} [Fintype l] [LinearOrder l] {M : Type*}
    [AddCommMonoid M] (F : l × l → M) (hdiag : ∀ a, F (a, a) = 0) :
    ∑ ij : l × l, F ij =
      ∑ ij ∈ {ij : l × l | ij.1 < ij.2}, (F ij + F ij.swap) := by
  classical
  have hswap : ∑ ij ∈ {ij : l × l | ij.2 < ij.1}, F ij =
      ∑ ij ∈ {ij : l × l | ij.1 < ij.2}, F ij.swap :=
    Finset.sum_nbij' (i := Prod.swap) (j := Prod.swap) (by simp) (by simp) (by simp) (by simp)
      (by simp)
  have hnot : ∑ ij ∈ {ij : l × l | ij.2 < ij.1}, F ij =
      ∑ ij ∈ {ij : l × l | ¬ ij.1 < ij.2}, F ij := by
    refine Finset.sum_subset ?_ ?_
    · intro ij hij
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hij ⊢
      exact hij.le
    · rintro ⟨a, b⟩ hmem hnotmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hmem hnotmem
      exact hdiag a ▸ congrArg (fun c => F (a, c)) (le_antisymm hnotmem hmem).symm
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ij : l × l => ij.1 < ij.2) F,
    ← hnot, hswap, Finset.sum_add_distrib]

/-- **A product over the increasing pairs of a symmetric function is permutation invariant:**
for symmetric `f`, `∏_{i<j} f (σ i) (σ j) = ∏_{i<j} f i j` for every permutation `σ`. -/
@[to_additive /-- **A sum over the increasing pairs of a symmetric function is permutation
invariant:** for symmetric `f`, `∑_{i<j} f (σ i) (σ j) = ∑_{i<j} f i j` for every permutation
`σ`. -/]
theorem prod_prod_Ioi_comp_perm {ι M : Type*} [LinearOrder ι] [Fintype ι]
    [LocallyFiniteOrderTop ι] [CommMonoid M] (σ : Equiv.Perm ι) {f : ι → ι → M}
    (hf : ∀ i j, f i j = f j i) :
    ∏ i, ∏ j ∈ Ioi i, f (σ i) (σ j) = ∏ i, ∏ j ∈ Ioi i, f i j := by
  rw [prod_sigma', prod_sigma']
  refine prod_nbij' (fun x ↦ ⟨min (σ x.1) (σ x.2), max (σ x.1) (σ x.2)⟩)
    (fun y ↦ ⟨min (σ.symm y.1) (σ.symm y.2), max (σ.symm y.1) (σ.symm y.2)⟩) ?_ ?_ ?_ ?_ ?_
  all_goals
    rintro ⟨a, b⟩ h
    simp only [mem_sigma, mem_univ, mem_Ioi, true_and] at h ⊢
  · rcases lt_or_gt_of_ne (σ.injective.ne h.ne) with hab | hab
    · simpa [hab.le] using hab
    · simpa [hab.le] using hab
  · rcases lt_or_gt_of_ne (σ.symm.injective.ne h.ne) with hab | hab
    · simpa [hab.le] using hab
    · simpa [hab.le] using hab
  · rcases le_total (σ a) (σ b) with hab | hab <;> simp [hab, h.le]
  · rcases le_total (σ.symm a) (σ.symm b) with hab | hab <;> simp [hab, h.le]
  · rcases le_total (σ a) (σ b) with hab | hab
    · simp [hab]
    · simp [hab, hf]

end TauCeti

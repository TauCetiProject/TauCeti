/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Prod

/-!
# Sums over ordered pairs

A sum of `F : l × l → M` over all ordered pairs, for `l` a finite linear order, can be folded onto
the increasing pairs by adding each term to its transpose. When `F` vanishes on the diagonal the
diagonal contributes nothing and the fold is exact, which is
`TauCeti.sum_univ_prod_eq_sum_lt_add_swap`.

This is the shape a sum indexed by unordered pairs takes once the linear order is used to name each
pair by its increasing representative. It is what lets an antisymmetric summand, for which the two
terms of a transposed pair combine, be summed over pairs rather than over ordered pairs.

## Main results

* `TauCeti.sum_univ_prod_eq_sum_lt_add_swap`: a sum over all ordered pairs of a function vanishing
  on the diagonal, as a sum over the increasing pairs of the term plus its transpose.
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

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import TauCeti.Algebra.Order.Floor.Ring

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Fintype.Perm

/-!
# Finite grids for affine sums

The theorem `TauCeti.exists_finset_forall_affine_sum_le` rounds each input up on a fixed mesh
and bounds the resulting error in every affine sum. The cardinality bound depends on the
number of inputs, independently of the number of outputs. The proof uses the grid in
`TauCeti.exists_finset_forall_exists_le_lt_add` and Mathlib's `Finset.card_image₂_le`
and `Fintype.card_equiv`.

In the parametric Subspace Theorem the inputs are the base-`Q` logarithms of the successive
minima. For the wedge exponents at one infinite place, the summation indices are the inverse images
of the form indices under the chosen bijection. On the top block, replace the jump index
`k` by `k - 1` in that sum to account for the gain `μ (k - 1) / μ k`. The coefficient of
the sum is zero at the other places. The fixed term can include an upper bound for the logarithm of
a fixed multiplicative constant once the level is sufficiently large.

## References

* J.-H. Evertse, *An improvement of the quantitative Subspace theorem*,
  Compositio Math. 101 (1996), Lemma 18.
-/

public section

open Finset

namespace TauCeti

/-- A mesh of width `γ > 0` gives a finite family of upper bounds for affine sums of
`#ι` inputs in `[-B, B]`. The summation sets may depend on a bijection `σ` and on the
output index `j`. For each `j`, the excess is at most one mesh width per summand, scaled by
the nonnegative coefficient `a j`. The cardinality bound is `n! (2m + 1)^n`, where
`n = #ι` and `m = ⌈B / γ⌉₊`. See Evertse (1996), Lemma 18. -/
theorem exists_finset_forall_affine_sum_le {ι κ R : Type*} [Fintype ι]
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] {B γ : R}
    (hγ : 0 < γ) (c : κ → R) {a : κ → R} (ha : ∀ j, 0 ≤ a j)
    (s : (Fin (Fintype.card ι) ≃ ι) → κ → Finset (Fin (Fintype.card ι))) :
    ∃ T : Finset (κ → R), T.card ≤ (Fintype.card ι).factorial *
        (2 * ⌈B / γ⌉₊ + 1) ^ Fintype.card ι ∧
      ∀ σ (x : Fin (Fintype.card ι) → R), (∀ i, x i ∈ Set.Icc (-B) B) →
        ∃ e ∈ T, ∀ j, c j + a j * (∑ i ∈ s σ j, x i) ≤ e j ∧
          e j ≤ c j + a j * (∑ i ∈ s σ j, x i) + a j * ((s σ j).card * γ) := by
  classical
  let n := Fintype.card ι
  obtain ⟨G, hGcard, hG⟩ := exists_finset_forall_exists_le_lt_add (κ := Fin n) hγ B
  let system (σ : Fin n ≃ ι) (z : Fin n → R) (j : κ) :=
    c j + a j * (∑ i ∈ s σ j, z i)
  refine ⟨image₂ system univ G, ?_, ?_⟩
  · refine (card_image₂_le system univ G).trans ?_
    rw [card_univ, Fintype.card_equiv (Fintype.equivFin ι).symm, Fintype.card_fin]
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hGcard
    exact Nat.mul_le_mul_left _ hGcard
  · intro σ x hx
    obtain ⟨z, hzG, hz⟩ := hG x fun i ↦ abs_le.mpr (hx i)
    refine ⟨system σ z, mem_image₂_of_mem (mem_univ _) hzG, fun j ↦ ?_⟩
    have hnonneg := ha j
    have hsystem : system σ z j = c j + a j * (∑ i ∈ s σ j, z i) := rfl
    rw [hsystem]
    constructor
    · gcongr with i
      exact (hz i).1
    · have hsum : ∑ i ∈ s σ j, z i ≤
          (∑ i ∈ s σ j, x i) + (s σ j).card * γ := by
        simpa only [sum_add_distrib, sum_const, nsmul_eq_mul] using
          sum_le_sum (s := s σ j) (fun i _ ↦ (hz i).2.le)
      rw [add_assoc, ← mul_add]
      gcongr

end TauCeti

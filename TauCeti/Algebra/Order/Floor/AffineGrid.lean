/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite grids for affine sums

The theorem `TauCeti.exists_finset_forall_affine_sum_le` rounds each input up on a fixed mesh
and bounds the resulting error in every affine sum. The cardinality bound depends on the
number of inputs, independently of the number of outputs. The proof uses Mathlib's
`Int.ceil` API and `Fintype.card_equiv`.

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
  let m := ⌈B / γ⌉₊
  let I := Finset.Icc (-(m : ℤ)) (m : ℤ)
  let system (data : (Fin n ≃ ι) × (Fin n → I)) (j : κ) :=
    c j + a j * (∑ i ∈ s data.1 j, ((data.2 i : ℤ) : R) * γ)
  refine ⟨Finset.univ.image system, ?_, ?_⟩
  · have hgrid : Fintype.card (Fin n → I) = (2 * m + 1) ^ n := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Int.card_Icc]
      exact congrArg (· ^ n) (by lia)
    refine Finset.card_image_le.trans_eq ?_
    rw [card_univ, Fintype.card_prod, Fintype.card_equiv (Fintype.equivFin ι).symm,
      Fintype.card_fin, hgrid]
  · intro σ x hx
    have hB : B ≤ (m : R) * γ := (div_le_iff₀ hγ).mp (Nat.le_ceil _)
    let z (i : Fin n) : I := ⟨⌈x i / γ⌉, Finset.mem_Icc.mpr (by
      constructor
      · rw [Int.le_ceil_iff, Int.cast_neg, Int.cast_natCast]
        refine (sub_lt_self _ zero_lt_one).trans_le ((le_div_iff₀ hγ).2 ?_)
        simpa only [neg_mul] using (neg_le_neg hB).trans (hx i).1
      · simpa only [Int.ceil_le, Int.cast_natCast, div_le_iff₀ hγ] using (hx i).2.trans hB)⟩
    have hz (i : Fin n) : x i ≤ ((z i : ℤ) : R) * γ ∧ ((z i : ℤ) : R) * γ ≤ x i + γ := by
      have hlo := (div_le_iff₀ hγ).mp (Int.le_ceil (x i / γ))
      have hhi := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one (x i / γ)) hγ
      rw [add_mul, div_mul_cancel₀ _ hγ.ne', one_mul] at hhi
      exact ⟨hlo, hhi.le⟩
    refine ⟨system (σ, z), mem_image_of_mem _ (mem_univ _), fun j ↦ ?_⟩
    dsimp only [system, Prod.fst, Prod.snd]
    have hnonneg := ha j
    constructor
    · gcongr with i
      exact (hz i).1
    · have hsum : ∑ i ∈ s σ j, ((z i : ℤ) : R) * γ ≤
          (∑ i ∈ s σ j, x i) + (s σ j).card * γ := by
        simpa only [sum_add_distrib, sum_const, nsmul_eq_mul] using
          sum_le_sum (s := s σ j) (fun i _ ↦ (hz i).2)
      rw [add_assoc, ← mul_add]
      gcongr

end TauCeti

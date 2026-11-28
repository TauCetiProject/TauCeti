/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Dimension bounds from weighted coordinates

If every nonzero vector in a subspace has a nonzero coordinate of weight at least `d`,
projection onto those coordinates is injective. Summing over positive integer thresholds
charges a coordinate at most its weight. The subspaces need not be nested.
-/

public section

open Finset Module

namespace Submodule

/-- A subspace detected by a finite set of coordinates has dimension at most the number of
those coordinates. -/
theorem finrank_le_card_of_exists_ne_zero_apply {K ι : Type*} [DivisionRing K]
    (U : Submodule K (ι → K)) (s : Finset ι)
    (h : ∀ v ∈ U, v ≠ 0 → ∃ i ∈ s, v i ≠ 0) : finrank K U ≤ #s := by
  let f := (LinearMap.funLeft K K (Subtype.val : s → ι)).comp U.subtype
  have hf : Function.Injective f := (injective_iff_map_eq_zero f).2 fun v hv ↦ by
    apply Subtype.ext
    by_contra hne
    obtain ⟨i, hi, hvi⟩ := h v v.property hne
    exact hvi (congrFun hv ⟨i, hi⟩)
  simpa using LinearMap.finrank_le_finrank_of_injective hf

/-- If every nonzero vector at threshold `d` has a nonzero coordinate of weight at least `d`,
then the sum of the dimensions at thresholds `1, …, M` is at most the total weight. -/
theorem sum_finrank_le_sum_of_exists_le_weight {K ι : Type*} [DivisionRing K] [Fintype ι]
    {M : ℕ} (U : ℕ → Submodule K (ι → K)) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (h : ∀ d ∈ Icc 1 M, ∀ v ∈ U d, v ≠ 0 → ∃ i, (d : ℝ) ≤ w i ∧ v i ≠ 0) :
    ∑ d ∈ Icc 1 M, (finrank K (U d) : ℝ) ≤ ∑ i, w i := by
  classical
  calc
    _ ≤ ∑ d ∈ Icc 1 M, (#(univ.filter fun i ↦ (d : ℝ) ≤ w i) : ℝ) := by
      apply sum_le_sum
      intro d hd
      exact_mod_cast (U d).finrank_le_card_of_exists_ne_zero_apply _ (fun v hv hv₀ ↦ by
        obtain ⟨i, hi, hvi⟩ := h d hd v hv hv₀
        exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩, hvi⟩)
    _ = ∑ i, (#((Icc 1 M).filter fun d : ℕ ↦ (d : ℝ) ≤ w i) : ℝ) := by
      simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
      exact sum_comm
    _ ≤ ∑ i, w i := by
      apply sum_le_sum
      intro i _
      have hs : ((Icc 1 M).filter fun d : ℕ ↦ (d : ℝ) ≤ w i) ⊆ Icc 1 ⌊w i⌋₊ := by
        intro d hd
        obtain ⟨hd, hdi⟩ := mem_filter.mp hd
        exact mem_Icc.mpr ⟨(mem_Icc.mp hd).1, (Nat.le_floor_iff (hw i)).mpr hdi⟩
      have hc := card_le_card hs
      rw [Nat.card_Icc] at hc
      simp only [Nat.add_sub_cancel] at hc
      exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (hw i))

end Submodule

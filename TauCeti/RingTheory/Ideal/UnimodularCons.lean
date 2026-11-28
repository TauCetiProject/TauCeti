/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.RingTheory.Ideal.Span

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Unimodularity of a linear-combination vector with pairwise-unit differences

Given a commutative ring `A`, a unimodular vector `v : ι → A` (`Ideal.span (Set.range v) = ⊤`),
a unimodular pair `(u₀, u₁)` (`Ideal.span {u₀, u₁} = ⊤`), and scalars `c : ι → A` whose
pairwise differences `c i - c j` (`i ≠ j`) are units in `A`, the vector with entries
`u₀ * ∑ i, v i` and `(u₁ - c i * u₀) * v i` (`i : ι`) is again unimodular.

## Main results

* `Ideal.span_insert_mul_sum_eq_top`: the general statement for any finite index type `ι` and
  scalars `c : ι → A` with unit pairwise differences.
* `Ideal.span_range_cons_mul_eq_top`: the `Fin.cons` form for `v : Fin (d + 1) → A` and
  `u : Fin 2 → A`, used to construct the projective product morphism `ℙ^d × ℙ¹ → ℙ^(d + 1)`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Cohomology/PointClass/ProjectiveSpace.lean` (`span_range_cons_mul_eq_top`).
-/

public section

namespace Ideal

/-- If `v : ι → A` and `(u₀, u₁)` each generate the unit ideal of a commutative ring `A`, and
`c : ι → A` has pairwise-unit differences (`IsUnit (c i - c j)` for `i ≠ j`), then the elements
`u₀ * ∑ i, v i` and `(u₁ - c i * u₀) * v i` (`i : ι`) also generate the unit ideal. -/
theorem span_insert_mul_sum_eq_top {A ι : Type*} [CommRing A] [Fintype ι]
    {v c : ι → A} {u₀ u₁ : A}
    (hc : ∀ i j, i ≠ j → IsUnit (c i - c j))
    (hv : span (Set.range v) = ⊤) (hu : span ({u₀, u₁} : Set A) = ⊤) :
    span (insert (u₀ * ∑ i, v i) (Set.range fun i ↦ (u₁ - c i * u₀) * v i)) = ⊤ := by
  classical
  by_contra h_ne
  obtain ⟨m, hm, h_le⟩ := exists_le_maximal _ h_ne
  let _ : Field (A ⧸ m) := Quotient.field m
  let ψ : A →+* A ⧸ m := Quotient.mk m
  have h_first : ψ u₀ * ∑ i, ψ (v i) = 0 := by
    have hmem : u₀ * ∑ i, v i ∈ m := h_le (subset_span (Set.mem_insert _ _))
    simpa only [ψ, map_mul, map_sum] using (Quotient.eq_zero_iff_mem).mpr hmem
  have h_rest (i : ι) : (ψ u₁ - ψ (c i) * ψ u₀) * ψ (v i) = 0 := by
    have hmem : (u₁ - c i * u₀) * v i ∈ m :=
      h_le (subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
    simpa only [ψ, map_mul, map_sub] using (Quotient.eq_zero_iff_mem).mpr hmem
  obtain ⟨j, hj⟩ : ∃ j : ι, ψ (v j) ≠ 0 := by
    by_contra h_all
    push Not at h_all
    have hv_le : span (Set.range v) ≤ m := span_le.mpr <| by
      rintro _ ⟨i, rfl⟩
      exact (Quotient.eq_zero_iff_mem).mp (h_all i)
    exact hm.ne_top (eq_top_mono hv_le hv)
  have hu1 : ψ u₁ = ψ (c j) * ψ u₀ :=
    sub_eq_zero.mp ((mul_eq_zero.mp (h_rest j)).resolve_right hj)
  have hu0 : ψ u₀ ≠ 0 := by
    intro h0
    have hu_le : span ({u₀, u₁} : Set A) ≤ m := span_le.mpr <| by
      rintro x (rfl | rfl)
      · exact (Quotient.eq_zero_iff_mem).mp h0
      · exact (Quotient.eq_zero_iff_mem).mp (by rw [hu1, h0, mul_zero])
    exact hm.ne_top (eq_top_mono hu_le hu)
  have h_other (i : ι) (hij : i ≠ j) : ψ (v i) = 0 := by
    have hdiff : ψ (c j) - ψ (c i) ≠ 0 := by
      rw [← map_sub]
      exact ((hc j i hij.symm).map ψ).ne_zero
    have hmul : (ψ (c j) - ψ (c i)) * ψ u₀ * ψ (v i) = 0 := by
      simpa [hu1, sub_mul] using h_rest i
    exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hdiff hu0)
  rw [Fintype.sum_eq_single j h_other] at h_first
  exact mul_ne_zero hu0 hj h_first

/-- `Fin.cons` specialization of `Ideal.span_insert_mul_sum_eq_top`: if `v : Fin (d + 1) → A` and
`u : Fin 2 → A` are unimodular and `c : Fin (d + 1) → A` has pairwise-unit differences, then the
vector with entries `u 0 * ∑ i, v i` and `(u 1 - c i * u 0) * v i` is unimodular. -/
theorem span_range_cons_mul_eq_top {A : Type*} [CommRing A] {d : ℕ}
    {v c : Fin (d + 1) → A} {u : Fin 2 → A}
    (hc : ∀ i j, i ≠ j → IsUnit (c i - c j))
    (hv : span (Set.range v) = ⊤) (hu : span (Set.range u) = ⊤) :
    span (Set.range (Fin.cons (u 0 * ∑ i, v i)
      fun i ↦ (u 1 - c i * u 0) * v i : Fin (d + 2) → A)) = ⊤ := by
  rw [Fin.range_cons]
  have hu' : Set.range u = {u 0, u 1} := by
    ext x
    simp [Fin.exists_fin_two, eq_comm]
  rw [hu'] at hu
  exact span_insert_mul_sum_eq_top hc hv hu

end Ideal

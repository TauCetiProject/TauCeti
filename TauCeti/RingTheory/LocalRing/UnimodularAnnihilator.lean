/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span

/-!
# Unimodular vectors annihilated by a diagonal pencil

Let `A` be a local commutative ring and `c : ι → A` a family of scalars whose pairwise differences
`c i - c j` (`i ≠ j`) are units (for instance, natural numbers in a characteristic-zero algebra).
If `v : ι → A` is a unimodular vector (`Ideal.span (Set.range v) = ⊤`), `u₀, u₁ : A` generate the
unit ideal (`Ideal.span {u₀, u₁} = ⊤`), and `(u₁ - c i * u₀) * v i = 0` for every `i`, then some
coordinate `v j` is a unit, `u₀` is a unit with `u₁ = c j * u₀`, and `v i = 0` for all `i ≠ j`.

Passing to the residue field `A ⧸ m` at every maximal ideal `m` shows that, when `ι` is finite,
`u₀ * ∑ i, v i` is a unit over any commutative ring `A` (without assuming `A` is local).

## Main results

* `IsLocalRing.exists_isUnit_of_mul_eq_zero`: over a local ring, a unimodular vector annihilated by
  a diagonal linear pencil `(u₁ - c i * u₀)` with pairwise-unit differences concentrates at a
  single unit coordinate.
* `isUnit_mul_sum_of_mul_eq_zero`: over any commutative ring with finite `ι`, `u₀ * ∑ i, v i` is a
  unit.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Cohomology/PointClass/ProjectiveSpace.lean` (`exists_isUnit_coord_of_mul_eq_zero`,
`isUnit_mul_sum_of_mul_eq_zero`, `exists_eq_map_affinePoint_of_mul_eq_zero`), generalized from
characteristic-zero field algebras and `Fin (d + 1)` to arbitrary commutative rings and index types
with pairwise-unit scalar differences.
-/

public section

namespace IsLocalRing

/-- Let `A` be a local commutative ring and `c : ι → A` have pairwise-unit differences. If
`v : ι → A` is unimodular, `{u₀, u₁}` generates `⊤`, and `(u₁ - c i * u₀) * v i = 0` for all `i`,
then for some `j : ι`, `v j` and `u₀` are units, `c j * u₀ = u₁`, and `v i = 0` for all `i ≠ j`. -/
theorem exists_isUnit_of_mul_eq_zero {A ι : Type*} [CommRing A] [IsLocalRing A]
    {c v : ι → A} {u₀ u₁ : A}
    (hc : ∀ i j, i ≠ j → IsUnit (c i - c j))
    (hv : Ideal.span (Set.range v) = ⊤) (hu : Ideal.span ({u₀, u₁} : Set A) = ⊤)
    (h : ∀ i, (u₁ - c i * u₀) * v i = 0) :
    ∃ j : ι, IsUnit (v j) ∧ IsUnit u₀ ∧ c j * u₀ = u₁ ∧ ∀ i ≠ j, v i = 0 := by
  have hnot : ¬Set.range v ⊆ (maximalIdeal A : Set A) := fun hsub ↦
    (maximalIdeal.isMaximal A).ne_top (top_le_iff.1 (hv ▸ Ideal.span_le.2 hsub))
  obtain ⟨_, ⟨j, rfl⟩, hj_mem⟩ := Set.not_subset.1 hnot
  have hj : IsUnit (v j) := by simpa [mem_maximalIdeal] using hj_mem
  have hu1 : c j * u₀ = u₁ := (sub_eq_zero.1 (hj.mul_left_eq_zero.1 (h j))).symm
  have hle : Ideal.span ({u₀, u₁} : Set A) ≤ Ideal.span {u₀} := by
    rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact Ideal.subset_span rfl
    · exact hu1 ▸ Ideal.mul_mem_left _ (c j) (Ideal.subset_span rfl)
  have hu0 : IsUnit u₀ := Ideal.span_singleton_eq_top.1 (eq_top_mono hle hu)
  refine ⟨j, hj, hu0, hu1, fun i hij ↦ ?_⟩
  have h0 : (c j - c i) * u₀ * v i = 0 := by
    have := h i
    rw [← hu1, ← sub_mul] at this
    exact this
  exact ((hc j i hij.symm).mul hu0).mul_right_eq_zero.1 h0

end IsLocalRing

/-- Over any commutative ring `A` with finite `ι`, if `c : ι → A` has pairwise-unit differences,
`v : ι → A` is unimodular, `{u₀, u₁}` generates `⊤`, and `(u₁ - c i * u₀) * v i = 0` for all `i`,
then `u₀ * ∑ i, v i` is a unit. -/
theorem isUnit_mul_sum_of_mul_eq_zero {A ι : Type*} [CommRing A] [Fintype ι]
    {c v : ι → A} {u₀ u₁ : A}
    (hc : ∀ i j, i ≠ j → IsUnit (c i - c j))
    (hv : Ideal.span (Set.range v) = ⊤) (hu : Ideal.span ({u₀, u₁} : Set A) = ⊤)
    (h : ∀ i, (u₁ - c i * u₀) * v i = 0) :
    IsUnit (u₀ * ∑ i, v i) := by
  by_contra hnu
  obtain ⟨m, hm, hmem⟩ := Ideal.exists_le_maximal (Ideal.span {u₀ * ∑ i, v i})
    (Ideal.span_singleton_ne_top hnu)
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  let q := Ideal.Quotient.mk m
  have hq_span : ∀ s : Set A, Ideal.span s = ⊤ → Ideal.span (q '' s) = ⊤ := fun s hs ↦ by
    rw [← Ideal.map_span, hs, Ideal.map_top]
  obtain ⟨j, hj, hu0, -, hzero⟩ := IsLocalRing.exists_isUnit_of_mul_eq_zero (A := A ⧸ m)
    (c := q ∘ c) (v := q ∘ v) (u₀ := q u₀) (u₁ := q u₁)
    (fun i j hij ↦ by simpa [q] using (hc i j hij).map q)
    (by simpa [Set.range_comp] using hq_span (Set.range v) hv)
    (by simpa [Set.image_pair] using hq_span {u₀, u₁} hu)
    (fun i ↦ by simpa [q] using congrArg q (h i))
  have hsum : ∑ i, q (v i) = q (v j) := Fintype.sum_eq_single j fun i hij ↦ hzero i hij
  have hunit : IsUnit (q (u₀ * ∑ i, v i)) := by simpa [map_mul, map_sum, hsum] using hu0.mul hj
  exact hunit.ne_zero (Ideal.Quotient.eq_zero_iff_mem.2 (hmem (Ideal.subset_span rfl)))

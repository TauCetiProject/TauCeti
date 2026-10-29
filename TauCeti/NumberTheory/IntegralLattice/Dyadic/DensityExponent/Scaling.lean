/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Dyadic.DensityExponent.Basic

/-!
# Scaling dyadic Jordan profiles

Multiplying the form of a dyadic lattice by `2` moves every Jordan constituent from scale
`2 ^ i` to scale `2 ^ (i + 1)`. This file implements that shift on
`TauCeti.DyadicJordanProfile` and computes its effect on Cho's density exponents.

The parity types and the statistics `t`, `b`, and `c` are unchanged. The exponent `N_M` is
unchanged because it only uses differences of scales, while `N_Q` and `N = N_Q - N_M` acquire
the same correction. The correction is the sum of the triangular rank contribution of each
constituent and the products of the ranks of every pair of distinct constituents.

## References

* S. Cho, *Group schemes and local densities of quadratic lattices in residue characteristic 2*,
  Compositio Math. 151 (2015), Section 2.3 and Lemma 5.1.
-/

public section

namespace TauCeti.DyadicJordanProfile

private def succEmbedding : ℕ ↪ ℕ :=
  ⟨Nat.succ, Nat.succ_injective⟩

@[simp]
private theorem succEmbedding_apply (i : ℕ) : succEmbedding i = Nat.succ i := rfl

/-- Shift every constituent of a dyadic Jordan profile up by one scale. This is the profile
operation induced by multiplying the underlying bilinear form by `2`. -/
noncomputable def shift (P : DyadicJordanProfile) : DyadicJordanProfile where
  ranks := P.ranks.embDomain succEmbedding
  typeI := P.typeI.map succEmbedding
  typeI_subset_support := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    rw [Finsupp.support_embDomain, Finset.mem_map]
    exact ⟨j, P.typeI_subset_support hj, rfl⟩
  even_rank_of_notMem_typeI := by
    rintro (_ | i) hi
    · rw [Finsupp.embDomain_of_notMem_range]
      · exact Even.zero
      · simp [succEmbedding]
    · -- Expose the `embDomain` field so its computation theorem matches syntactically.
      change Even ((P.ranks.embDomain succEmbedding) (succEmbedding i))
      rw [Finsupp.embDomain_apply_self]
      exact P.even_rank_of_notMem_typeI i (by simpa [succEmbedding] using hi)

private theorem shift_ranks_eq (P : DyadicJordanProfile) :
    P.shift.ranks = P.ranks.embDomain succEmbedding := (rfl)

private theorem shift_typeI_eq (P : DyadicJordanProfile) :
    P.shift.typeI = P.typeI.map succEmbedding := (rfl)

/-- The scale-zero constituent of a shifted profile is empty. -/
@[simp]
theorem shift_ranks_zero (P : DyadicJordanProfile) : P.shift.ranks 0 = 0 := by
  rw [shift_ranks_eq]
  exact Finsupp.embDomain_of_notMem_range _ _ _ (by simp [succEmbedding])

/-- The constituent of scale `2 ^ (i + 1)` in a shifted profile is the old constituent of
scale `2 ^ i`. -/
@[simp]
theorem shift_ranks_succ (P : DyadicJordanProfile) (i : ℕ) :
    P.shift.ranks (Nat.succ i) = P.ranks i := by
  rw [shift_ranks_eq, ← succEmbedding_apply]
  exact Finsupp.embDomain_apply_self _ _ _

/-- The shifted profile has a type-I constituent at scale `2 ^ (i + 1)` exactly when the
original profile has one at scale `2 ^ i`. -/
@[simp]
theorem mem_shift_typeI_succ_iff (P : DyadicJordanProfile) (i : ℕ) :
    Nat.succ i ∈ P.shift.typeI ↔ i ∈ P.typeI := by
  rw [shift_typeI_eq, ← succEmbedding_apply]
  simp

/-- A shifted profile has no type-I constituent at scale zero. -/
@[simp]
theorem zero_notMem_shift_typeI (P : DyadicJordanProfile) : 0 ∉ P.shift.typeI := by
  rw [shift_typeI_eq]
  simp [succEmbedding]

private theorem shift_support_map (P : DyadicJordanProfile) :
    P.shift.ranks.support = P.ranks.support.map succEmbedding := by
  exact Finsupp.support_embDomain _ _

/-- The support of a shifted profile is the successor-image of the old support. -/
theorem shift_support (P : DyadicJordanProfile) :
    P.shift.ranks.support = P.ranks.support.image Nat.succ := by
  rw [shift_support_map]
  ext i
  simp [succEmbedding]

private theorem shift_support_filter_lt (P : DyadicJordanProfile) (i : ℕ) :
    (P.ranks.support.map succEmbedding).filter (fun j ↦ succEmbedding i < j) =
      (P.ranks.support.filter fun j ↦ i < j).map succEmbedding := by
  rw [Finset.filter_map]
  simp [Function.comp_def, succEmbedding]

/-- The type-I constituent count is unchanged by shifting every scale. -/
@[simp]
theorem typeICount_shift (P : DyadicJordanProfile) : P.shift.typeICount = P.typeICount := by
  rw [typeICount_def, typeICount_def]
  exact Finset.card_map _

/-- The number of adjacent type-I pairs is unchanged by shifting every scale. -/
@[simp]
theorem adjacentTypeICount_shift (P : DyadicJordanProfile) :
    P.shift.adjacentTypeICount = P.adjacentTypeICount := by
  rw [adjacentTypeICount_def, adjacentTypeICount_def]
  have hfilter :
      (P.shift.typeI.filter fun i ↦ i + 1 ∈ P.shift.typeI) =
        (P.typeI.filter fun i ↦ i + 1 ∈ P.typeI).map succEmbedding := by
    rw [shift_typeI_eq, Finset.filter_map]
    simp [succEmbedding]
  rw [hfilter, Finset.card_map]

/-- The total rank of the type-II constituents is unchanged by shifting every scale. -/
@[simp]
theorem typeIIRank_shift (P : DyadicJordanProfile) : P.shift.typeIIRank = P.typeIIRank := by
  rw [typeIIRank_def, typeIIRank_def, shift_support_map]
  have hfilter :
      (P.ranks.support.map succEmbedding).filter (fun i ↦ i ∉ P.shift.typeI) =
        (P.ranks.support.filter fun i ↦ i ∉ P.typeI).map succEmbedding := by
    rw [Finset.filter_map]
    simp [Function.comp_def, succEmbedding]
  rw [hfilter, Finset.sum_map]
  simp

/-- The correction acquired by `N_Q` and `N` when every dyadic scale is shifted by one.
It has one triangular contribution from each constituent and one product for each pair of
constituents at distinct scales. -/
def shiftCorrection (P : DyadicJordanProfile) : ℕ :=
  (∑ i ∈ P.ranks.support, P.ranks i * (P.ranks i + 1) / 2) +
    ∑ i ∈ P.ranks.support,
      ∑ j ∈ P.ranks.support.filter fun j ↦ i < j, P.ranks i * P.ranks j

/-- The scale-shift correction as a sum over constituent ranks. -/
theorem shiftCorrection_def (P : DyadicJordanProfile) :
    P.shiftCorrection =
      (∑ i ∈ P.ranks.support, P.ranks i * (P.ranks i + 1) / 2) +
        ∑ i ∈ P.ranks.support,
          ∑ j ∈ P.ranks.support.filter fun j ↦ i < j, P.ranks i * P.ranks j := (rfl)

/-- The empty profile has zero scale-shift correction. -/
@[simp]
theorem shiftCorrection_empty : empty.shiftCorrection = 0 := by
  rw [shiftCorrection_def]
  simp

/-- A unary type-I profile has scale-shift correction one. -/
@[simp]
theorem shiftCorrection_unaryTypeI (i : ℕ) : (unaryTypeI i).shiftCorrection = 1 := by
  rw [shiftCorrection_def, unaryTypeI_ranks]
  simp

/-- The distance-weighted cross term is unchanged by shifting every scale. -/
@[simp]
theorem distanceCrossExponent_shift (P : DyadicJordanProfile) :
    P.shift.distanceCrossExponent = P.distanceCrossExponent := by
  rw [distanceCrossExponent_def, distanceCrossExponent_def, shift_support_map]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i hi
  rw [shift_support_filter_lt, Finset.sum_map]
  simp [succEmbedding]

/-- Shifting every scale adds the unweighted pairwise rank products to the upper cross term. -/
theorem upperCrossExponent_shift (P : DyadicJordanProfile) :
    P.shift.upperCrossExponent = P.upperCrossExponent +
      ∑ i ∈ P.ranks.support,
        ∑ j ∈ P.ranks.support.filter fun j ↦ i < j, P.ranks i * P.ranks j := by
  rw [upperCrossExponent_def, upperCrossExponent_def, shift_support_map]
  rw [Finset.sum_map]
  simp_rw [shift_support_filter_lt]
  simp_rw [Finset.sum_map]
  simp only [succEmbedding_apply, shift_ranks_succ]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr
  · rfl
  · intro j hj
    rw [Nat.succ_mul, Nat.add_mul]

/-- Shifting every scale adds the triangular rank sum to the diagonal term. -/
theorem diagonalExponent_shift (P : DyadicJordanProfile) :
    P.shift.diagonalExponent = P.diagonalExponent +
      ∑ i ∈ P.ranks.support, P.ranks i * (P.ranks i + 1) / 2 := by
  rw [diagonalExponent_def, diagonalExponent_def, shift_support_map]
  rw [Finset.sum_map, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [succEmbedding_apply, shift_ranks_succ]
  exact Nat.succ_mul i (P.ranks i * (P.ranks i + 1) / 2)

/-- Cho's exponent `N_M` is invariant under multiplying all dyadic scales by `2`. -/
@[simp]
theorem nM_shift (P : DyadicJordanProfile) : P.shift.nM = P.nM := by
  rw [nM_def, nM_def, distanceCrossExponent_shift, adjacentTypeICount_shift]
  have htype : (∑ i ∈ P.shift.typeI, (2 * P.shift.ranks i - 1)) =
      ∑ i ∈ P.typeI, (2 * P.ranks i - 1) := by
    rw [shift_typeI_eq]
    rw [Finset.sum_map]
    simp
  rw [htype]

/-- Cho's exponent `N_Q` acquires `shiftCorrection` when all dyadic scales are multiplied
by `2`. -/
theorem nQ_shift (P : DyadicJordanProfile) :
    P.shift.nQ = P.nQ + P.shiftCorrection := by
  rw [nQ_def, nQ_def, typeIIRank_shift, adjacentTypeICount_shift, upperCrossExponent_shift,
    diagonalExponent_shift]
  simp only [shiftCorrection]
  have htype : (∑ i ∈ P.shift.typeI, 2 * P.shift.ranks i) =
      ∑ i ∈ P.typeI, 2 * P.ranks i := by
    rw [shift_typeI_eq]
    rw [Finset.sum_map]
    simp
  rw [htype]
  omega

/-- Cho's density exponent `N = N_Q - N_M` acquires `shiftCorrection` when all dyadic scales
are multiplied by `2`. -/
theorem densityExponent_shift (P : DyadicJordanProfile) :
    P.shift.densityExponent = P.densityExponent + P.shiftCorrection := by
  have h : P.nM + P.shift.densityExponent =
      P.nM + (P.densityExponent + P.shiftCorrection) := by
    calc
      P.nM + P.shift.densityExponent = P.shift.nM + P.shift.densityExponent := by
        rw [nM_shift]
      _ = P.shift.nQ := P.shift.nQ_eq_nM_add_densityExponent.symm
      _ = P.nQ + P.shiftCorrection := P.nQ_shift
      _ = (P.nM + P.densityExponent) + P.shiftCorrection := by
        rw [P.nQ_eq_nM_add_densityExponent]
      _ = P.nM + (P.densityExponent + P.shiftCorrection) := Nat.add_assoc _ _ _
  exact Nat.add_left_cancel h

end TauCeti.DyadicJordanProfile

end

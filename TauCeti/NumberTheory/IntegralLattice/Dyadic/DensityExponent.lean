/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic.NormNum

/-!
# Density exponents of dyadic Jordan data

The ranks and parity types of the nonzero constituents in a dyadic Jordan splitting determine
three natural numbers used in the local density formula. This file packages exactly that finite
data in `TauCeti.DyadicJordanProfile`, defines Cho's exponents `nM`, `nQ`, and
`densityExponent`, and proves the identity `nQ = nM + densityExponent`.

The profile records a finitely supported family of constituent ranks and the subset having type I.
Thus a nonzero constituent outside `typeI` has type II, while an empty constituent is never type I.
As for an actual splitting, every constituent outside `typeI` has even rank.
A constituent is bound when an adjacent constituent has type I, and free otherwise.
The definitions also expose the three statistics used in the closed formula: the number of type-I
constituents, the number of adjacent type-I pairs, and the sum of the ranks of type-II constituents.

## References

* S. Cho, *Group schemes and local densities of quadratic lattices in residue characteristic 2*,
  Compositio Math. 151 (2015), Definition 2.1, Section 2.3, and Lemma 5.1.
-/

public section

namespace TauCeti

/-- The finite rank and parity data of a dyadic Jordan splitting.

The value `ranks i` is the rank of the constituent of scale `2 ^ i`. The finset `typeI` consists
of the scales of the type-I constituents. The containment condition enforces the convention that
an empty constituent is not of type I; every nonempty constituent at a scale outside `typeI` is
of type II, and so has even rank. -/
@[ext]
structure DyadicJordanProfile where
  /-- The finitely supported ranks of the Jordan constituents. -/
  ranks : ℕ →₀ ℕ
  /-- The scales whose nonempty constituents have type I. -/
  typeI : Finset ℕ
  /-- A type-I constituent is nonempty. -/
  typeI_subset_support : typeI ⊆ ranks.support
  /-- A constituent that is not of type I has even rank. -/
  even_rank_of_notMem_typeI : ∀ i, i ∉ typeI → Even (ranks i)

namespace DyadicJordanProfile

/-- The constituent of scale `2 ^ i` is bound if a constituent of an adjacent scale `2 ^ (i - 1)`
or `2 ^ (i + 1)` has type I. -/
def IsBound (P : DyadicJordanProfile) (i : ℕ) : Prop :=
  i + 1 ∈ P.typeI ∨ ∃ j ∈ P.typeI, j + 1 = i

/-- The constituent of scale `2 ^ i` is free if it is not bound, that is, both adjacent
constituents have type II. -/
def IsFree (P : DyadicJordanProfile) (i : ℕ) : Prop :=
  ¬P.IsBound i

/-- The constituent of scale `1` is bound exactly when the one of scale `2` has type I. -/
@[simp]
theorem isBound_zero_iff (P : DyadicJordanProfile) : P.IsBound 0 ↔ 1 ∈ P.typeI := by
  simp [IsBound]

/-- The constituent of scale `2 ^ (i + 1)` is bound exactly when one of the constituents of
scales `2 ^ i` and `2 ^ (i + 2)` has type I. -/
@[simp]
theorem isBound_succ_iff (P : DyadicJordanProfile) (i : ℕ) :
    P.IsBound (i + 1) ↔ i + 2 ∈ P.typeI ∨ i ∈ P.typeI := by
  simp [IsBound]

/-- A constituent is free exactly when it is not bound. -/
@[simp]
theorem isFree_iff_not_isBound (P : DyadicJordanProfile) (i : ℕ) :
    P.IsFree i ↔ ¬P.IsBound i := by
  rw [IsFree]

instance (P : DyadicJordanProfile) : DecidablePred P.IsBound := fun i ↦
  decidable_of_iff (i + 1 ∈ P.typeI ∨ ∃ j ∈ P.typeI, j + 1 = i) (by rw [IsBound])

instance (P : DyadicJordanProfile) : DecidablePred P.IsFree := fun i ↦
  decidable_of_iff (¬P.IsBound i) (P.isFree_iff_not_isBound i).symm

/-- The number `t` of type-I constituents. -/
def typeICount (P : DyadicJordanProfile) : ℕ := P.typeI.card

/-- The number `b` of adjacent pairs of type-I constituents. -/
def adjacentTypeICount (P : DyadicJordanProfile) : ℕ :=
  (P.typeI.filter fun i ↦ i + 1 ∈ P.typeI).card

/-- The number `c`, the sum of the ranks of the nonempty type-II constituents. -/
def typeIIRank (P : DyadicJordanProfile) : ℕ :=
  ∑ i ∈ P.ranks.support.filter fun i ↦ i ∉ P.typeI, P.ranks i

/-- The sum `∑ i * n_i * (n_i + 1) / 2` of the diagonal contributions `d_i`. -/
def diagonalExponent (P : DyadicJordanProfile) : ℕ :=
  ∑ i ∈ P.ranks.support, i * (P.ranks i * (P.ranks i + 1) / 2)

/-- The cross term `∑_{i < j} (j - i) * n_i * n_j` occurring in `N_M`. -/
def distanceCrossExponent (P : DyadicJordanProfile) : ℕ :=
  ∑ i ∈ P.ranks.support,
    ∑ j ∈ P.ranks.support.filter fun j ↦ i < j, (j - i) * P.ranks i * P.ranks j

/-- The cross term `∑_{i < j} j * n_i * n_j` occurring in `N_Q`. -/
def upperCrossExponent (P : DyadicJordanProfile) : ℕ :=
  ∑ i ∈ P.ranks.support,
    ∑ j ∈ P.ranks.support.filter fun j ↦ i < j, j * P.ranks i * P.ranks j

/-- The cross term `∑_{i < j} i * n_i * n_j` occurring in Cho's formula for `N`. -/
def lowerCrossExponent (P : DyadicJordanProfile) : ℕ :=
  ∑ i ∈ P.ranks.support,
    ∑ j ∈ P.ranks.support.filter fun j ↦ i < j, i * P.ranks i * P.ranks j

/-- Cho's exponent `N_M` attached to dyadic Jordan data. -/
def nM (P : DyadicJordanProfile) : ℕ :=
  (∑ i ∈ P.typeI, (2 * P.ranks i - 1)) + P.distanceCrossExponent +
    2 * P.adjacentTypeICount

/-- Cho's exponent `N_Q` attached to dyadic Jordan data. -/
def nQ (P : DyadicJordanProfile) : ℕ :=
  (∑ i ∈ P.typeI, 2 * P.ranks i) + P.upperCrossExponent + P.diagonalExponent +
    P.adjacentTypeICount + P.typeIIRank

/-- The density exponent `N = N_Q - N_M` attached to dyadic Jordan data.

The subtraction is placed between `typeICount` and `adjacentTypeICount`; the latter never exceeds
the former. The theorem `densityExponent_eq` gives Cho's displayed order of terms, and
`nQ_sub_nM_eq_densityExponent` proves that this is exactly `N_Q - N_M`. -/
def densityExponent (P : DyadicJordanProfile) : ℕ :=
  P.typeICount - P.adjacentTypeICount + P.lowerCrossExponent + P.diagonalExponent +
    P.typeIIRank

/-- A scale declared to have type I has positive rank. -/
theorem rank_pos_of_mem_typeI (P : DyadicJordanProfile) {i : ℕ} (hi : i ∈ P.typeI) :
    0 < P.ranks i := by
  rw [Nat.pos_iff_ne_zero, ← Finsupp.mem_support_iff]
  exact P.typeI_subset_support hi

/-- The number of adjacent type-I pairs is at most the number of type-I constituents. -/
theorem adjacentTypeICount_le_typeICount (P : DyadicJordanProfile) :
    P.adjacentTypeICount ≤ P.typeICount := by
  exact Finset.card_filter_le _ _

/-- The type-I term in `N_Q` exceeds the corresponding term in `N_M` by `t`. -/
private theorem sum_two_mul_rank_typeI (P : DyadicJordanProfile) :
    (∑ i ∈ P.typeI, 2 * P.ranks i) =
      (∑ i ∈ P.typeI, (2 * P.ranks i - 1)) + P.typeICount := by
  calc
    (∑ i ∈ P.typeI, 2 * P.ranks i) =
        ∑ i ∈ P.typeI, ((2 * P.ranks i - 1) + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      have := P.rank_pos_of_mem_typeI hi
      omega
    _ = (∑ i ∈ P.typeI, (2 * P.ranks i - 1)) + ∑ _i ∈ P.typeI, 1 := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ i ∈ P.typeI, (2 * P.ranks i - 1)) + P.typeICount := by
      simp [typeICount]

/-- The `j`-weighted cross term splits into the distance term and the `i`-weighted term. -/
private theorem upperCrossExponent_eq_distance_add_lower (P : DyadicJordanProfile) :
    P.upperCrossExponent = P.distanceCrossExponent + P.lowerCrossExponent := by
  calc
    P.upperCrossExponent =
        ∑ i ∈ P.ranks.support,
          ((∑ j ∈ P.ranks.support.filter fun j ↦ i < j,
              (j - i) * P.ranks i * P.ranks j) +
            ∑ j ∈ P.ranks.support.filter fun j ↦ i < j,
              i * P.ranks i * P.ranks j) := by
      unfold upperCrossExponent
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ j ∈ P.ranks.support.filter fun j ↦ i < j,
            j * P.ranks i * P.ranks j) =
            ∑ j ∈ P.ranks.support.filter fun j ↦ i < j,
              ((j - i) * P.ranks i * P.ranks j + i * P.ranks i * P.ranks j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hij : i < j := (Finset.mem_filter.mp hj).2
          conv_lhs => rw [← Nat.sub_add_cancel hij.le]
          simp only [Nat.add_mul]
          rw [Nat.sub_add_cancel hij.le]
        _ = _ := Finset.sum_add_distrib
    _ = P.distanceCrossExponent + P.lowerCrossExponent := by
      rw [Finset.sum_add_distrib]
      rfl

/-- Cho's displayed expression `N = t + ∑_{i < j} i n_i n_j + ∑_i d_i - b + c`. -/
theorem densityExponent_eq (P : DyadicJordanProfile) :
    P.densityExponent = P.typeICount + P.lowerCrossExponent + P.diagonalExponent -
      P.adjacentTypeICount + P.typeIIRank := by
  have := P.adjacentTypeICount_le_typeICount
  simp only [densityExponent]
  omega

/-- **Cho's exponent identity.** The two deformation exponents differ by the density exponent:
`N_Q = N_M + N`. -/
theorem nQ_eq_nM_add_densityExponent (P : DyadicJordanProfile) :
    P.nQ = P.nM + P.densityExponent := by
  have htype := P.sum_two_mul_rank_typeI
  have hcross := P.upperCrossExponent_eq_distance_add_lower
  have hadj := P.adjacentTypeICount_le_typeICount
  simp only [nQ, nM, densityExponent] at *
  omega

/-- The density exponent is the natural-number difference `N_Q - N_M`. -/
theorem nQ_sub_nM_eq_densityExponent (P : DyadicJordanProfile) :
    P.nQ - P.nM = P.densityExponent := by
  rw [P.nQ_eq_nM_add_densityExponent, Nat.add_sub_cancel_left]

/-- The empty dyadic Jordan profile. -/
def empty : DyadicJordanProfile where
  ranks := 0
  typeI := ∅
  typeI_subset_support := by simp
  even_rank_of_notMem_typeI _ _ := by simp

/-- A single type-II unimodular constituent of even rank `n`. At `n = 0` this is the empty
profile. -/
noncomputable def unimodularTypeII (n : ℕ) (hn : Even n) : DyadicJordanProfile where
  ranks := Finsupp.single 0 n
  typeI := ∅
  typeI_subset_support := by simp
  even_rank_of_notMem_typeI i _ := by
    rcases eq_or_ne i 0 with rfl | hi
    · simpa using hn
    · simp [Finsupp.single_eq_of_ne hi]

/-- A unary type-I constituent at scale `2 ^ i`. -/
noncomputable def unaryTypeI (i : ℕ) : DyadicJordanProfile where
  ranks := Finsupp.single i 1
  typeI := {i}
  typeI_subset_support := by simp
  even_rank_of_notMem_typeI j hj := by
    simp [Finsupp.single_eq_of_ne (Finset.mem_singleton.not.mp hj)]

/-- Two unary type-I constituents at the adjacent scales `1` and `2`. -/
noncomputable def adjacentUnaryTypeI : DyadicJordanProfile where
  ranks := Finsupp.single 0 1 + Finsupp.single 1 1
  typeI := {0, 1}
  typeI_subset_support := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp
  even_rank_of_notMem_typeI j hj := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp [Finsupp.single_eq_of_ne hj.1, Finsupp.single_eq_of_ne hj.2]

/-- The empty profile has no nonzero ranks. -/
@[simp]
theorem empty_ranks : empty.ranks = 0 := (rfl)

/-- The empty profile has no type-I constituents. -/
@[simp]
theorem empty_typeI : empty.typeI = ∅ := (rfl)

/-- The unimodular type-II profile has one possibly nonzero rank at scale zero. -/
@[simp]
theorem unimodularTypeII_ranks (n : ℕ) (hn : Even n) :
    (unimodularTypeII n hn).ranks = Finsupp.single 0 n := (rfl)

/-- The unimodular type-II profile has no type-I constituents. -/
@[simp]
theorem unimodularTypeII_typeI (n : ℕ) (hn : Even n) : (unimodularTypeII n hn).typeI = ∅ :=
  (rfl)

/-- A unary type-I profile has rank one at its given scale. -/
@[simp]
theorem unaryTypeI_ranks (i : ℕ) : (unaryTypeI i).ranks = Finsupp.single i 1 := (rfl)

/-- A unary type-I profile has exactly its given scale of type I. -/
@[simp]
theorem unaryTypeI_typeI (i : ℕ) : (unaryTypeI i).typeI = {i} := (rfl)

/-- The adjacent unary profile has rank one at scales zero and one. -/
@[simp]
theorem adjacentUnaryTypeI_ranks :
    adjacentUnaryTypeI.ranks = Finsupp.single 0 1 + Finsupp.single 1 1 := (rfl)

/-- The adjacent unary profile has type I at scales zero and one. -/
@[simp]
theorem adjacentUnaryTypeI_typeI : adjacentUnaryTypeI.typeI = {0, 1} := (rfl)

/-- The empty profile has density exponent zero. -/
@[simp]
theorem densityExponent_empty : empty.densityExponent = 0 := by
  simp [empty, densityExponent, typeICount, adjacentTypeICount, lowerCrossExponent,
    diagonalExponent, typeIIRank]

/-- A unimodular type-II constituent of even rank `n` has density exponent `n`. -/
@[simp]
theorem densityExponent_unimodularTypeII (n : ℕ) (hn : Even n) :
    (unimodularTypeII n hn).densityExponent = n := by
  by_cases hn : n = 0
  · subst n
    simp [unimodularTypeII, densityExponent, typeICount, adjacentTypeICount,
      lowerCrossExponent, diagonalExponent, typeIIRank]
  · simp [unimodularTypeII, densityExponent, typeICount, adjacentTypeICount,
      lowerCrossExponent, diagonalExponent, typeIIRank, hn]

/-- A unary type-I constituent at scale `2 ^ i` has density exponent `i + 1`. -/
@[simp]
theorem densityExponent_unaryTypeI (i : ℕ) :
    (unaryTypeI i).densityExponent = i + 1 := by
  have hb : (unaryTypeI i).adjacentTypeICount = 0 := by
    simp [unaryTypeI, adjacentTypeICount, Finset.card_eq_zero]
  have ht : (unaryTypeI i).typeICount = 1 := by
    simp [unaryTypeI, typeICount]
  have hlower : (unaryTypeI i).lowerCrossExponent = 0 := by
    simp [unaryTypeI, lowerCrossExponent]
  have hdiag : (unaryTypeI i).diagonalExponent = i := by
    simp [unaryTypeI, diagonalExponent]
  have hc : (unaryTypeI i).typeIIRank = 0 := by
    simp [unaryTypeI, typeIIRank]
  rw [densityExponent, hb, ht, hlower, hdiag, hc]
  omega

/-- Two adjacent unary type-I constituents at scales `1` and `2` have density exponent `2`. -/
@[simp]
theorem densityExponent_adjacentUnaryTypeI : adjacentUnaryTypeI.densityExponent = 2 := by
  have hsupp : (Finsupp.single 0 1 + Finsupp.single 1 1 : ℕ →₀ ℕ).support = {0, 1} := by
    ext i
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply,
      Finset.mem_insert, Finset.mem_singleton]
    split_ifs <;> omega
  have ht : adjacentUnaryTypeI.typeICount = 2 := by
    norm_num [adjacentUnaryTypeI, typeICount]
  have hb : adjacentUnaryTypeI.adjacentTypeICount = 1 := by
    norm_num [adjacentUnaryTypeI, adjacentTypeICount]
    decide
  have hlower : adjacentUnaryTypeI.lowerCrossExponent = 0 := by
    norm_num [adjacentUnaryTypeI, lowerCrossExponent, hsupp]
  have hdiag : adjacentUnaryTypeI.diagonalExponent = 1 := by
    norm_num [adjacentUnaryTypeI, diagonalExponent, hsupp]
  have hc : adjacentUnaryTypeI.typeIIRank = 0 := by
    norm_num [adjacentUnaryTypeI, typeIIRank, hsupp]
  rw [densityExponent, ht, hb, hlower, hdiag, hc]

end DyadicJordanProfile

end TauCeti

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Dyadic.DensityExponent.Basic

/-!
# Dyadic Jordan profiles of orthogonal sums

A Jordan splitting of an orthogonal sum is obtained by adding the constituents of equal scale,
and such a sum of constituents is of type I when one of the two summands is. Accordingly the sum
`P + Q` of two dyadic Jordan profiles adds the ranks and takes the union of the type-I scales.

This file computes Cho's exponents of `P + Q` when the scales of `P` and `Q` do not interleave:
every scale of `P` is smaller than every scale of `Q`. Writing `n_i` for the ranks of `P`, `n'_j`
for those of `Q`, and `ε ∈ {0, 1}` for the number of type-I scales `i` of `P` such that `i + 1` is
a type-I scale of `Q`, the statistics `t` and `c` are additive, `b(P + Q) = b(P) + b(Q) + ε`, and

```text
N_M(P + Q) = N_M(P) + N_M(Q) + ∑_{i, j} (j - i) n_i n'_j + 2ε,
N_Q(P + Q) = N_Q(P) + N_Q(Q) + ∑_{i, j} j n_i n'_j + ε,
N(P + Q)   = N(P) + N(Q) + ∑_{i, j} i n_i n'_j - ε,
```

the sums running over the scales `i` of `P` and `j` of `Q`. The only interaction between the two
profiles is through the cross terms of the rank products and the possible adjacent type-I pair
straddling the two. For instance `⟨1⟩ ⊕ ⟨2⟩`, the sum of a type-I constituent at scale `1` and
one at scale `2`, has `ε = 1` and `N = 1 + 2 + 0 - 1 = 2`.

## Main definitions

* `TauCeti.DyadicJordanProfile.instAdd`: the sum of two profiles, the profile of an orthogonal
  sum.
* `TauCeti.DyadicJordanProfile.instAddCommMonoid`: profiles form a commutative monoid under this
  sum, with the empty profile `TauCeti.DyadicJordanProfile.instZero` as zero.

## Main results

* `TauCeti.DyadicJordanProfile.nM_add`, `TauCeti.DyadicJordanProfile.nQ_add`,
  `TauCeti.DyadicJordanProfile.densityExponent_add`: Cho's exponents of a sum of profiles whose
  scales do not interleave.
* `TauCeti.DyadicJordanProfile.unaryTypeI_zero_add_unaryTypeI_one`: the profile of
  `⟨1⟩ ⊕ ⟨2⟩` is the sum of the profiles of `⟨1⟩` and `⟨2⟩`.

## References

* S. Cho, *Group schemes and local densities of quadratic lattices in residue characteristic 2*,
  Compositio Math. 151 (2015), Section 2.3 and Lemma 5.1.
-/

public section

namespace TauCeti.DyadicJordanProfile

/-- The sum of two dyadic Jordan profiles: ranks add, and a scale is of type I when it is of
type I in one of the summands. This is the profile of an orthogonal sum. -/
noncomputable instance instAdd : Add DyadicJordanProfile where
  add P Q :=
    { ranks := P.ranks + Q.ranks
      typeI := P.typeI ∪ Q.typeI
      typeI_subset_support := by
        intro i hi
        rw [Finsupp.mem_support_iff, Finsupp.add_apply]
        rcases Finset.mem_union.mp hi with h | h
        · have := P.rank_pos_of_mem_typeI h
          omega
        · have := Q.rank_pos_of_mem_typeI h
          omega
      even_rank_of_notMem_typeI i hi := by
        rw [Finset.mem_union, not_or] at hi
        exact (P.even_rank_of_notMem_typeI i hi.1).add (Q.even_rank_of_notMem_typeI i hi.2) }

variable (P Q : DyadicJordanProfile)

/-- The ranks of a sum of profiles are the sums of the ranks. -/
@[simp]
theorem add_ranks : (P + Q).ranks = P.ranks + Q.ranks := (rfl)

/-- The type-I scales of a sum of profiles are those of either summand. -/
@[simp]
theorem add_typeI : (P + Q).typeI = P.typeI ∪ Q.typeI := (rfl)

/-- The zero profile is the empty profile, the profile of the zero lattice. -/
instance instZero : Zero DyadicJordanProfile := ⟨empty⟩

/-- The zero profile is the empty profile. -/
theorem zero_def : (0 : DyadicJordanProfile) = empty := (rfl)

/-- The zero profile has no constituents. -/
@[simp]
theorem zero_ranks : (0 : DyadicJordanProfile).ranks = 0 := empty_ranks

/-- The zero profile has no type-I scales. -/
@[simp]
theorem zero_typeI : (0 : DyadicJordanProfile).typeI = ∅ := empty_typeI

/-- Profiles form a commutative monoid under orthogonal sum, with the empty profile as zero. -/
noncomputable instance instAddCommMonoid : AddCommMonoid DyadicJordanProfile where
  add_assoc P Q R := by ext <;> simp [add_assoc, Finset.union_assoc]
  zero_add P := by ext <;> simp
  add_zero P := by ext <;> simp
  add_comm P Q := by ext <;> simp [add_comm, Finset.union_comm]
  nsmul := nsmulRec

/-- The profile of `⟨1⟩ ⊕ ⟨2⟩`, two adjacent type-I constituents at scales `1` and `2`, is the sum
of the profiles of its two unary summands. -/
theorem unaryTypeI_zero_add_unaryTypeI_one : unaryTypeI 0 + unaryTypeI 1 = adjacentUnaryTypeI := by
  ext i
  · simp
  · simp [Finset.mem_insert]

/-- The number of type-I constituents is additive when the type-I scales are disjoint. -/
theorem typeICount_add (h : Disjoint P.typeI Q.typeI) :
    (P + Q).typeICount = P.typeICount + Q.typeICount := by
  rw [typeICount_def, typeICount_def, typeICount_def, add_typeI, Finset.card_union_of_disjoint h]

variable {P Q}

section Disjoint

variable (h : Disjoint P.ranks.support Q.ranks.support)
include h

/-- Disjoint supports have disjoint type-I scales. -/
private theorem disjoint_typeI : Disjoint P.typeI Q.typeI :=
  Finset.disjoint_of_subset_left P.typeI_subset_support
    (Finset.disjoint_of_subset_right Q.typeI_subset_support h)

private theorem support_add : (P + Q).ranks.support = P.ranks.support ∪ Q.ranks.support :=
  Finsupp.support_add_eq h

private theorem add_ranks_of_mem_left {i : ℕ} (hi : i ∈ P.ranks.support) :
    (P + Q).ranks i = P.ranks i := by
  rw [add_ranks, Finsupp.add_apply, Finsupp.notMem_support_iff.mp
    (Finset.disjoint_left.mp h hi), add_zero]

private theorem add_ranks_of_mem_right {i : ℕ} (hi : i ∈ Q.ranks.support) :
    (P + Q).ranks i = Q.ranks i := by
  rw [add_ranks, Finsupp.add_apply, Finsupp.notMem_support_iff.mp
    (Finset.disjoint_right.mp h hi), zero_add]

private theorem mem_add_typeI_iff_of_mem_left {i : ℕ} (hi : i ∈ P.ranks.support) :
    i ∈ (P + Q).typeI ↔ i ∈ P.typeI := by
  rw [add_typeI, Finset.mem_union, or_iff_left fun hQ ↦
    Finset.disjoint_left.mp h hi (Q.typeI_subset_support hQ)]

private theorem mem_add_typeI_iff_of_mem_right {i : ℕ} (hi : i ∈ Q.ranks.support) :
    i ∈ (P + Q).typeI ↔ i ∈ Q.typeI := by
  rw [add_typeI, Finset.mem_union, or_iff_right fun hP ↦
    Finset.disjoint_right.mp h hi (P.typeI_subset_support hP)]

/-- A sum over the type-I scales of a sum of profiles with disjoint supports splits into the sums
for the two summands. -/
private theorem sum_add_typeI (f : ℕ → ℕ) :
    ∑ i ∈ (P + Q).typeI, f ((P + Q).ranks i) =
      ∑ i ∈ P.typeI, f (P.ranks i) + ∑ i ∈ Q.typeI, f (Q.ranks i) := by
  rw [add_typeI, Finset.sum_union (disjoint_typeI h)]
  congr 1 <;> refine Finset.sum_congr rfl fun i hi ↦ ?_
  · rw [add_ranks_of_mem_left h (P.typeI_subset_support hi)]
  · rw [add_ranks_of_mem_right h (Q.typeI_subset_support hi)]

/-- The diagonal exponent is additive over profiles with disjoint supports. -/
theorem diagonalExponent_add :
    (P + Q).diagonalExponent = P.diagonalExponent + Q.diagonalExponent := by
  simp only [diagonalExponent_def]
  rw [support_add h, Finset.sum_union h]
  congr 1 <;> refine Finset.sum_congr rfl fun i hi ↦ ?_
  · rw [add_ranks_of_mem_left h hi]
  · rw [add_ranks_of_mem_right h hi]

/-- The total rank `c` of the type-II constituents is additive over profiles with disjoint
supports. -/
theorem typeIIRank_add : (P + Q).typeIIRank = P.typeIIRank + Q.typeIIRank := by
  simp only [typeIIRank_def]
  rw [support_add h, Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter h)]
  congr 1
  · rw [Finset.filter_congr fun i hi ↦ by rw [mem_add_typeI_iff_of_mem_left h hi]]
    exact Finset.sum_congr rfl fun i hi ↦ add_ranks_of_mem_left h (Finset.mem_filter.mp hi).1
  · rw [Finset.filter_congr fun i hi ↦ by rw [mem_add_typeI_iff_of_mem_right h hi]]
    exact Finset.sum_congr rfl fun i hi ↦ add_ranks_of_mem_right h (Finset.mem_filter.mp hi).1

end Disjoint

section NonInterleaving

variable (hPQ : ∀ i ∈ P.ranks.support, ∀ j ∈ Q.ranks.support, i < j)
include hPQ

private theorem disjoint_support : Disjoint P.ranks.support Q.ranks.support :=
  Finset.disjoint_left.mpr fun i hi hi' ↦ lt_irrefl i (hPQ i hi i hi')

/-- A sum of weighted rank products over the ordered pairs of scales of `P + Q` splits into the
sums for `P` and for `Q` and a cross term over the pairs of a scale of `P` and one of `Q`. -/
private theorem sum_sum_add (w : ℕ → ℕ → ℕ) :
    ∑ i ∈ (P + Q).ranks.support, ∑ j ∈ (P + Q).ranks.support.filter fun j ↦ i < j,
        w i j * (P + Q).ranks i * (P + Q).ranks j =
      (∑ i ∈ P.ranks.support, ∑ j ∈ P.ranks.support.filter fun j ↦ i < j,
          w i j * P.ranks i * P.ranks j) +
        (∑ i ∈ Q.ranks.support, ∑ j ∈ Q.ranks.support.filter fun j ↦ i < j,
          w i j * Q.ranks i * Q.ranks j) +
        ∑ i ∈ P.ranks.support, ∑ j ∈ Q.ranks.support, w i j * P.ranks i * Q.ranks j := by
  have h := disjoint_support hPQ
  rw [support_add h, Finset.sum_union h]
  -- A scale of `P` pairs with the larger scales of `P` and with every scale of `Q`.
  have hP : ∀ i ∈ P.ranks.support,
      ∑ j ∈ (P.ranks.support ∪ Q.ranks.support).filter (fun j ↦ i < j),
          w i j * (P + Q).ranks i * (P + Q).ranks j =
        ∑ j ∈ P.ranks.support.filter (fun j ↦ i < j), w i j * P.ranks i * P.ranks j +
          ∑ j ∈ Q.ranks.support, w i j * P.ranks i * Q.ranks j := fun i hi ↦ by
    rw [Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter h),
      Finset.filter_true_of_mem fun j hj ↦ hPQ i hi j hj, add_ranks_of_mem_left h hi]
    congr 1 <;> refine Finset.sum_congr rfl fun j hj ↦ ?_
    · rw [add_ranks_of_mem_left h (Finset.mem_filter.mp hj).1]
    · rw [add_ranks_of_mem_right h hj]
  -- A scale of `Q` only pairs with the larger scales of `Q`.
  have hQ : ∀ i ∈ Q.ranks.support,
      ∑ j ∈ (P.ranks.support ∪ Q.ranks.support).filter (fun j ↦ i < j),
          w i j * (P + Q).ranks i * (P + Q).ranks j =
        ∑ j ∈ Q.ranks.support.filter (fun j ↦ i < j), w i j * Q.ranks i * Q.ranks j :=
      fun i hi ↦ by
    rw [Finset.filter_union, Finset.filter_false_of_mem fun j hj hij ↦
      (hPQ j hj i hi).not_gt hij, Finset.empty_union, add_ranks_of_mem_right h hi]
    exact Finset.sum_congr rfl fun j hj ↦ by
      rw [add_ranks_of_mem_right h (Finset.mem_filter.mp hj).1]
  rw [Finset.sum_congr rfl hP, Finset.sum_congr rfl hQ, Finset.sum_add_distrib]
  omega

/-- The distance cross term of `N_M` for profiles whose scales do not interleave. -/
theorem distanceCrossExponent_add :
    (P + Q).distanceCrossExponent = P.distanceCrossExponent + Q.distanceCrossExponent +
      ∑ i ∈ P.ranks.support, ∑ j ∈ Q.ranks.support, (j - i) * P.ranks i * Q.ranks j :=
  by simpa only [distanceCrossExponent_def] using sum_sum_add hPQ fun i j ↦ j - i

/-- The upper cross term of `N_Q` for profiles whose scales do not interleave. -/
theorem upperCrossExponent_add :
    (P + Q).upperCrossExponent = P.upperCrossExponent + Q.upperCrossExponent +
      ∑ i ∈ P.ranks.support, ∑ j ∈ Q.ranks.support, j * P.ranks i * Q.ranks j :=
  by simpa only [upperCrossExponent_def] using sum_sum_add hPQ fun _ j ↦ j

/-- The lower cross term of `N` for profiles whose scales do not interleave. -/
theorem lowerCrossExponent_add :
    (P + Q).lowerCrossExponent = P.lowerCrossExponent + Q.lowerCrossExponent +
      ∑ i ∈ P.ranks.support, ∑ j ∈ Q.ranks.support, i * P.ranks i * Q.ranks j :=
  by simpa only [lowerCrossExponent_def] using sum_sum_add hPQ fun i _ ↦ i

/-- The number `b` of adjacent type-I pairs for profiles whose scales do not interleave: the
pairs of each summand, and a type-I scale `i` of `P` with `i + 1` a type-I scale of `Q`. -/
theorem adjacentTypeICount_add :
    (P + Q).adjacentTypeICount = P.adjacentTypeICount + Q.adjacentTypeICount +
      (P.typeI.filter fun i ↦ i + 1 ∈ Q.typeI).card := by
  have hd := disjoint_typeI (disjoint_support hPQ)
  rw [adjacentTypeICount_def, add_typeI, Finset.filter_union, Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter hd)]
  simp only [Finset.mem_union]
  -- A scale of `Q` is never followed by a scale of `P`.
  rw [Finset.filter_congr (s := Q.typeI) fun i hi ↦ or_iff_right fun hP ↦
      (lt_asymm (hPQ _ (P.typeI_subset_support hP) i (Q.typeI_subset_support hi)))
        (Nat.lt_succ_self i),
    Finset.filter_or, Finset.card_union_of_disjoint
      (Finset.disjoint_filter.mpr fun i _ hP hQ ↦ Finset.disjoint_left.mp hd hP hQ)]
  rw [adjacentTypeICount_def, adjacentTypeICount_def]
  omega

/-- **Cho's exponent `N_M` of a sum of profiles whose scales do not interleave.** -/
theorem nM_add :
    (P + Q).nM = P.nM + Q.nM +
      (∑ i ∈ P.ranks.support, ∑ j ∈ Q.ranks.support, (j - i) * P.ranks i * Q.ranks j) +
      2 * (P.typeI.filter fun i ↦ i + 1 ∈ Q.typeI).card := by
  have h := disjoint_support hPQ
  have hs := sum_add_typeI h fun n ↦ 2 * n - 1
  rw [nM_def, hs, distanceCrossExponent_add hPQ, adjacentTypeICount_add hPQ, nM_def, nM_def]
  omega

/-- **Cho's exponent `N_Q` of a sum of profiles whose scales do not interleave.** -/
theorem nQ_add :
    (P + Q).nQ = P.nQ + Q.nQ +
      (∑ i ∈ P.ranks.support, ∑ j ∈ Q.ranks.support, j * P.ranks i * Q.ranks j) +
      (P.typeI.filter fun i ↦ i + 1 ∈ Q.typeI).card := by
  have h := disjoint_support hPQ
  have hs := sum_add_typeI h fun n ↦ 2 * n
  rw [nQ_def, hs, upperCrossExponent_add hPQ, diagonalExponent_add h,
    adjacentTypeICount_add hPQ, typeIIRank_add h, nQ_def, nQ_def]
  omega

/-- **The density exponent `N` of a sum of profiles whose scales do not interleave.** The
subtraction is that of natural numbers, but it does not truncate: an adjacent type-I pair
straddling the two summands starts at a type-I scale of `P` that starts no adjacent pair within
`P`, so it is accounted for in `N(P)`. -/
theorem densityExponent_add :
    (P + Q).densityExponent = P.densityExponent + Q.densityExponent +
      (∑ i ∈ P.ranks.support, ∑ j ∈ Q.ranks.support, i * P.ranks i * Q.ranks j) -
      (P.typeI.filter fun i ↦ i + 1 ∈ Q.typeI).card := by
  have h := disjoint_support hPQ
  have hb := (P + Q).adjacentTypeICount_le_typeICount
  have hbP := P.adjacentTypeICount_le_typeICount
  have hbQ := Q.adjacentTypeICount_le_typeICount
  rw [adjacentTypeICount_add hPQ, typeICount_add P Q (disjoint_typeI h)] at hb
  rw [densityExponent_def, typeICount_add P Q (disjoint_typeI h), adjacentTypeICount_add hPQ,
    lowerCrossExponent_add hPQ, diagonalExponent_add h, typeIIRank_add h, densityExponent_def,
    densityExponent_def]
  omega

end NonInterleaving

end TauCeti.DyadicJordanProfile

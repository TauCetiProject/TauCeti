/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.CAR.HighestWeight
import TauCeti.Algebra.Lie.GeneralLinear.CAR.Occupation
import TauCeti.RingTheory.Idempotents.Eigenvalue

/-!
# The coordinate spectrum of CAR diagonal eigenvectors

For the left regular action of `gl_n` on the Clifford algebra of its trace form, every eigenvalue
of a diagonal matrix unit on a nonzero vector is one of the half-integral expressions `m + 1/2`
for a natural number `m < n`. In particular, this restricts every coordinate of a highest weight.

The diagonal lift is a sum of commuting occupation projections together with its scalar diagonal
term. Removing the diagonal `1/2` from a diagonal eigenvector equation leaves `n - 1` commuting
idempotents, reducing the coordinate result to the general spectrum theorem for their sum.

More generally, summing diagonal equations over a subset `s` leaves the commuting occupation
projections crossing from `s` to its complement. Their eigenvalue is a natural number `m` bounded
by `|s| (n - |s|)`. Consequently, natural occupation counts for the coordinates have subset sum
`choose |s| 2 + m`. This gives all cut bounds at once, while the full subset has no crossing terms
and fixes the total sum.

## Main results

* `TauCeti.exists_eq_natCast_add_inv_two_of_lie_single_self_eq_smul`: every diagonal matrix-unit
  eigenvalue has the form `m + 1/2` with `m < n`.
* `TauCeti.IsGlHighestWeightVector.exists_weight_apply_eq_natCast_add_inv_two`: every coordinate of
  a CAR highest weight has the form `m + 1/2` with `m < n`.
* `TauCeti.exists_occupationCutCount_of_lie_single_self_eq_smul`: occupation counts on a subset
  have the form `choose |s| 2 + m`, with `m` bounded by the size of the cut.
* `TauCeti.exists_sum_eq_natCast_add_card_sq_div_two_of_lie_single_self_eq_smul`: without any
  characteristic assumption, the sum of the diagonal eigenvalues is a bounded natural cast plus
  `|s|² / 2`.
* `TauCeti.IsGlHighestWeightVector.sum_occupationCounts_le`: every subset of the occupation counts
  of a CAR highest-weight vector satisfies the cut bound.
* `TauCeti.IsGlHighestWeightVector.sum_occupationCounts_univ_eq_choose_two`: the total occupation
  count is `choose n 2`.

## References

* D. Panyushev, *The exterior algebra and "spin" of an orthogonal g-module*, Transformation Groups
  6 (2001), 371–396, Proposition 2.4 and Example 2.5(1).
* D. Shlyakhtenko, *Failure of Strong Convergence of Matrices with Fermionic Entries*,
  arXiv:2606.28648, §2.3.
-/

public section

open scoped BigOperators TauCeti

namespace TauCeti

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K n : Type*} [Field K] [Fintype n]

variable [h2 : Invertible (2 : K)]

section Diagonal

variable [decEq : DecidableEq n]

/-- Every eigenvalue of a diagonal matrix unit on a nonzero vector in the left regular CAR module
is a natural number less than the matrix size, shifted by `1/2`. -/
theorem exists_eq_natCast_add_inv_two_of_lie_single_self_eq_smul {μ : K}
    {v : CliffordAlgebra (traceQuadraticForm K n)} {i : n} (hv : v ≠ 0)
    (hdiag : ⁅Matrix.single i i (1 : K), v⁆ = μ • v) :
    ∃ m : ℕ, m < Fintype.card n ∧ μ = (m : K) + (2 : K)⁻¹ := by
  cases Subsingleton.elim decEq (Classical.decEq n)
  classical
  let s := Finset.univ.erase i
  have hsum : (∑ k ∈ s, carOccupationElement (K := K) i k) • v =
      (μ - (2 : K)⁻¹) • v := by
    rw [smul_eq_mul]
    rw [car_lie_def,
      @glCliffordHom_single_self_eq_sum_occupation K n inferInstance inferInstance h2 i] at hdiag
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_mul,
      carOccupationElement_self, smul_mul_assoc, one_mul] at hdiag
    rw [sub_smul]
    exact eq_sub_of_add_eq hdiag
  obtain ⟨m, hm, hμ⟩ := s.exists_eq_natCast_of_sum_smul_eq_smul
    (carOccupationElement (K := K) i)
    (fun k hk => isIdempotentElem_carOccupationElement (Finset.ne_of_mem_erase hk).symm)
    (fun _ _ _ _ _ => commute_carOccupationElement (K := K)) hv hsum
  refine ⟨m, ?_, eq_add_of_sub_eq hμ⟩
  have hcard : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨i⟩
  have hm' : m ≤ Fintype.card n - 1 := by
    simpa only [s, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] using hm
  omega

/-- If a nonzero vector is a simultaneous eigenvector for the diagonal matrix units indexed by
`s`, the sum of their eigenvalues is `m + |s|² / 2`, where `m` is a natural number bounded by the
number of ordered pairs crossing from `s` to its complement.

The natural number is the eigenvalue of the sum of the commuting cut occupation projections. No
characteristic, finite-dimensionality, or splitting hypothesis is needed. -/
theorem exists_sum_eq_natCast_add_card_sq_div_two_of_lie_single_self_eq_smul
    {μ : n → K} {v : CliffordAlgebra (traceQuadraticForm K n)} (s : Finset n) (hv : v ≠ 0)
    (hdiag : ∀ i ∈ s, ⁅Matrix.single i i (1 : K), v⁆ = μ i • v) :
    ∃ m : ℕ, m ≤ s.card * (Fintype.card n - s.card) ∧
      (∑ i ∈ s, μ i) = (m : K) + (s.card : K) ^ 2 / 2 := by
  cases Subsingleton.elim decEq (Classical.decEq n)
  classical
  let t := s.product (Finset.univ \ s)
  let p : n × n → CliffordAlgebra (traceQuadraticForm K n) :=
    fun ij => carOccupationElement (K := K) ij.1 ij.2
  have hsumdiag :
      (∑ i ∈ s, glCliffordHom (K := K) (n := n) (Matrix.single i i 1)) * v =
        (∑ i ∈ s, μ i) • v := by
    rw [Finset.sum_mul, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← car_lie_def]
    exact hdiag i hi
  have hboundary : (∑ ij ∈ t, p ij) • v =
      ((∑ i ∈ s, μ i) - (s.card : K) ^ 2 / 2) • v := by
    rw [smul_eq_mul]
    rw [sum_glCliffordHom_single_self_eq_cut_occupation, add_mul, smul_mul_assoc,
      one_mul] at hsumdiag
    rw [sub_smul]
    exact eq_sub_of_add_eq' hsumdiag
  obtain ⟨m, hm, hμ⟩ := t.exists_eq_natCast_of_sum_smul_eq_smul p
    (fun ij hij => by
      apply isIdempotentElem_carOccupationElement
      have hi := (Finset.mem_product.mp hij).1
      have hj := (Finset.mem_sdiff.mp (Finset.mem_product.mp hij).2).2
      intro hij'
      exact hj (hij' ▸ hi))
    (fun _ _ _ _ _ => commute_carOccupationElement (K := K)) hv hboundary
  refine ⟨m, ?_, eq_add_of_sub_eq hμ⟩
  dsimp [t] at hm
  rw [Finset.card_product, Finset.card_sdiff, Finset.inter_univ,
    Finset.card_univ] at hm
  exact hm

/-- Let a nonzero vector be a simultaneous eigenvector for the diagonal matrix units, with each
eigenvalue written as a natural occupation count plus `1/2`. On a subset `s`, the sum of the
counts is `choose |s| 2 + m`, where `m` is bounded by the number of ordered pairs crossing from
`s` to its complement.

The natural number `m` is the eigenvalue of the sum of the commuting cut occupation projections.
No finite-dimensionality or splitting hypothesis is needed. -/
theorem exists_occupationCutCount_of_lie_single_self_eq_smul [CharZero K]
    {μ : n → K} {a : n → ℕ} {v : CliffordAlgebra (traceQuadraticForm K n)}
    (s : Finset n) (hv : v ≠ 0)
    (hdiag : ∀ i ∈ s, ⁅Matrix.single i i (1 : K), v⁆ = μ i • v)
    (hμ : ∀ i ∈ s, μ i = (a i : K) + (2 : K)⁻¹) :
    ∃ m : ℕ, m ≤ s.card * (Fintype.card n - s.card) ∧
      (∑ i ∈ s, a i) = s.card.choose 2 + m := by
  obtain ⟨m, hm, hscalar⟩ :=
    exists_sum_eq_natCast_add_card_sq_div_two_of_lie_single_self_eq_smul s hv hdiag
  refine ⟨m, hm, Nat.cast_injective (R := K) ?_⟩
  rw [Nat.cast_add, Nat.cast_choose_two]
  have hleft : ((∑ i ∈ s, a i : ℕ) : K) + (s.card : K) / 2 =
      ∑ i ∈ s, μ i := by
    rw [Nat.cast_sum]
    calc
      (∑ i ∈ s, (a i : K)) + (s.card : K) / 2 =
          ∑ i ∈ s, ((a i : K) + (2 : K)⁻¹) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        simp [div_eq_mul_inv]
      _ = ∑ i ∈ s, μ i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hμ i hi).symm
  rw [← hleft] at hscalar
  field_simp at hscalar ⊢
  linear_combination hscalar

/-- Under the hypotheses of
`TauCeti.exists_occupationCutCount_of_lie_single_self_eq_smul`, the occupation-count sum on `s`
is bounded by `choose |s| 2 + |s| (n - |s|)`. -/
theorem sum_occupationCounts_le_of_lie_single_self_eq_smul [CharZero K]
    {μ : n → K} {a : n → ℕ} {v : CliffordAlgebra (traceQuadraticForm K n)}
    (s : Finset n) (hv : v ≠ 0)
    (hdiag : ∀ i ∈ s, ⁅Matrix.single i i (1 : K), v⁆ = μ i • v)
    (hμ : ∀ i ∈ s, μ i = (a i : K) + (2 : K)⁻¹) :
    (∑ i ∈ s, a i) ≤ s.card.choose 2 + s.card * (Fintype.card n - s.card) := by
  obtain ⟨m, hm, hsum⟩ :=
    exists_occupationCutCount_of_lie_single_self_eq_smul s hv hdiag hμ
  rw [hsum]
  omega

/-- For simultaneous half-shifted natural diagonal eigenvalues, the total occupation count is
`choose n 2`. This is the full-subset case of the cut calculation, where no projection crosses
the boundary. -/
theorem sum_occupationCounts_univ_eq_choose_two_of_lie_single_self_eq_smul [CharZero K]
    {μ : n → K} {a : n → ℕ} {v : CliffordAlgebra (traceQuadraticForm K n)} (hv : v ≠ 0)
    (hdiag : ∀ i : n, ⁅Matrix.single i i (1 : K), v⁆ = μ i • v)
    (hμ : ∀ i : n, μ i = (a i : K) + (2 : K)⁻¹) :
    (∑ i : n, a i) = (Fintype.card n).choose 2 := by
  obtain ⟨m, hm, hsum⟩ := exists_occupationCutCount_of_lie_single_self_eq_smul
    (Finset.univ : Finset n) hv (fun i _ => hdiag i) (fun i _ => hμ i)
  have hm0 : m = 0 := by simpa using hm
  simpa [hm0] using hsum

end Diagonal

namespace IsGlHighestWeightVector

variable [LinearOrder n]

/-- Every coordinate of a highest weight in the left regular CAR module is a natural number less
than the matrix size, shifted by `1/2`.

This statement supplies the coordinate restriction; it does not assert that every expression is
attained by a given vector. -/
theorem exists_weight_apply_eq_natCast_add_inv_two [DecidableEq n] {μ : n → K}
    {v : CliffordAlgebra (traceQuadraticForm K n)}
    (hv : IsGlHighestWeightVector μ v) (i : n) :
    ∃ m : ℕ, m < Fintype.card n ∧ μ i = (m : K) + (2 : K)⁻¹ := by
  exact exists_eq_natCast_add_inv_two_of_lie_single_self_eq_smul hv.ne_zero
    (hv.lie_single_self_eq_smul i)

/-- Package the coordinate spectrum into one natural-valued occupation-count tuple. -/
theorem exists_occupationCounts [DecidableEq n] {μ : n → K}
    {v : CliffordAlgebra (traceQuadraticForm K n)}
    (hv : IsGlHighestWeightVector μ v) :
    ∃ a : n → ℕ, ∀ i,
      a i < Fintype.card n ∧ μ i = (a i : K) + (2 : K)⁻¹ := by
  have hcoord (i : n) :
      ∃ m : ℕ, m < Fintype.card n ∧ μ i = (m : K) + (2 : K)⁻¹ := by
    exact exists_eq_natCast_add_inv_two_of_lie_single_self_eq_smul hv.ne_zero
      (hv.lie_single_self_eq_smul i)
  let a : n → ℕ := fun i => (hcoord i).choose
  exact ⟨a, fun i => (hcoord i).choose_spec⟩

/-- Every subset of a half-shifted natural occupation-count tuple for a CAR highest-weight vector
satisfies the cut bound. For an initial segment of `Fin N`, the right side is the corresponding
prefix sum of the reverse tuple. -/
theorem sum_occupationCounts_le [CharZero K] [DecidableEq n] {μ : n → K} {a : n → ℕ}
    {v : CliffordAlgebra (traceQuadraticForm K n)}
    (hv : IsGlHighestWeightVector μ v)
    (hμ : ∀ i, μ i = (a i : K) + (2 : K)⁻¹) (s : Finset n) :
    (∑ i ∈ s, a i) ≤ s.card.choose 2 + s.card * (Fintype.card n - s.card) := by
  exact sum_occupationCounts_le_of_lie_single_self_eq_smul s hv.ne_zero
    (fun i _ => hv.lie_single_self_eq_smul i) (fun i _ => hμ i)

/-- The total of a half-shifted natural occupation-count tuple for a CAR highest-weight vector is
`choose n 2`. -/
theorem sum_occupationCounts_univ_eq_choose_two [CharZero K] [DecidableEq n]
    {μ : n → K} {a : n → ℕ} {v : CliffordAlgebra (traceQuadraticForm K n)}
    (hv : IsGlHighestWeightVector μ v)
    (hμ : ∀ i, μ i = (a i : K) + (2 : K)⁻¹) :
    (∑ i : n, a i) = (Fintype.card n).choose 2 := by
  exact sum_occupationCounts_univ_eq_choose_two_of_lie_single_self_eq_smul hv.ne_zero
    hv.lie_single_self_eq_smul hμ

end IsGlHighestWeightVector

end

end TauCeti

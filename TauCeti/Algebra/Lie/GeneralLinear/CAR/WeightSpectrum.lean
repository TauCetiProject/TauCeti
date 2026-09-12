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
idempotents, reducing the result to the general spectrum theorem for their sum.

## Main results

* `TauCeti.exists_eq_natCast_add_inv_two_of_lie_single_self_eq_smul`: every diagonal matrix-unit
  eigenvalue has the form `m + 1/2` with `m < n`.
* `TauCeti.IsGlHighestWeightVector.exists_weight_apply_eq_natCast_add_inv_two`: every coordinate of
  a CAR highest weight has the form `m + 1/2` with `m < n`.

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

attribute [local instance] Classical.decEq

variable {K n : Type*} [Field K] [Fintype n]

variable [h2 : Invertible (2 : K)]

/-- Every eigenvalue of a diagonal matrix unit on a nonzero vector in the left regular CAR module
is a natural number less than the matrix size, shifted by `1/2`. -/
theorem exists_eq_natCast_add_inv_two_of_lie_single_self_eq_smul {μ : K}
    {v : CliffordAlgebra (traceQuadraticForm K n)} {i : n} (hv : v ≠ 0)
    (hdiag : ⁅Matrix.single i i (1 : K), v⁆ = μ • v) :
    ∃ m : ℕ, m < Fintype.card n ∧ μ = (m : K) + (2 : K)⁻¹ := by
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

namespace IsGlHighestWeightVector

variable [LinearOrder n]

/-- Every coordinate of a highest weight in the left regular CAR module is a natural number less
than the matrix size, shifted by `1/2`.

This statement supplies the coordinate restriction; it does not assert that every expression is
attained by a given vector. -/
theorem exists_weight_apply_eq_natCast_add_inv_two {μ : n → K}
    {v : CliffordAlgebra (traceQuadraticForm K n)}
    (hv : IsGlHighestWeightVector μ v) (i : n) :
    ∃ m : ℕ, m < Fintype.card n ∧ μ i = (m : K) + (2 : K)⁻¹ := by
  exact exists_eq_natCast_add_inv_two_of_lie_single_self_eq_smul hv.ne_zero
    (hv.lie_single_self_eq_smul i)

end IsGlHighestWeightVector

end

end TauCeti

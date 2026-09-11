/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.CAR.HighestWeight
public import TauCeti.Algebra.Lie.GeneralLinear.CAR.Occupation
public import TauCeti.RingTheory.Idempotents.Eigenvalue

/-!
# The coordinate spectrum of CAR highest weights

For the left regular action of `gl_n` on the Clifford algebra of its trace form, every coordinate
of a highest weight is one of the half-integral expressions `m + 1/2` for a natural number `m < n`.

The diagonal lift is a sum of commuting occupation projections together with its scalar diagonal
term. Orienting every off-diagonal pair positively gives `n - 1` commuting idempotents. Removing
the diagonal `1/2` from a highest-weight equation reduces the result to the general spectrum
theorem for a sum of commuting idempotents.

## Main results

* `TauCeti.IsGlHighestWeightVector.exists_carWeight_eq_natCast_add_inv_two`: every coordinate of a
  CAR highest weight has the form `m + 1/2` with `m < n`.

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

variable {K n : Type*} [Field K] [Fintype n] [LinearOrder n]

/-- The occupation projection attached to `k ≠ i`, oriented by the order on the index type. -/
private def orientedCarOccupationElement (i k : n) :
    CliffordAlgebra (traceQuadraticForm K n) :=
  if k < i then 1 - carOccupationElement (K := K) k i
  else carOccupationElement (K := K) i k

/-- The diagonal member of the oriented family is the scalar `1/2`. -/
private theorem orientedCarOccupationElement_self (i : n) :
    orientedCarOccupationElement (K := K) i i = (2 : K)⁻¹ • 1 := by
  simp [orientedCarOccupationElement]

/-- Every off-diagonal member of the oriented family is idempotent. -/
private theorem orientedCarOccupationElement_idempotent {i k : n} (hki : k ≠ i) :
    IsIdempotentElem (orientedCarOccupationElement (K := K) i k) := by
  rw [orientedCarOccupationElement]
  split_ifs with h
  · exact (isIdempotentElem_carOccupationElement (K := K) (ne_of_lt h)).one_sub
  · exact isIdempotentElem_carOccupationElement (K := K) hki.symm

/-- The oriented occupation elements with a fixed diagonal index commute. -/
private theorem commute_orientedCarOccupationElement (i k l : n) :
    Commute (orientedCarOccupationElement (K := K) i k)
      (orientedCarOccupationElement (K := K) i l) := by
  rw [orientedCarOccupationElement, orientedCarOccupationElement]
  split_ifs <;>
    first
    | exact commute_carOccupationElement (K := K)
    | exact (Commute.one_left _).sub_left commute_carOccupationElement
    | exact (Commute.one_right _).sub_right commute_carOccupationElement
    | exact ((Commute.one_left _).sub_left
        ((Commute.one_right _).sub_right commute_carOccupationElement))

namespace IsGlHighestWeightVector

variable [h2 : Invertible (2 : K)]

/-- Every coordinate of a highest weight in the left regular CAR module is a natural number less
than the matrix size, shifted by `1/2`.

This statement supplies the coordinate restriction; it does not assert that every expression is
attained by a given vector. -/
theorem exists_carWeight_eq_natCast_add_inv_two {μ : n → K}
    {v : CliffordAlgebra (traceQuadraticForm K n)}
    (hv : IsGlHighestWeightVector μ v) (i : n) :
    ∃ m : ℕ, m < Fintype.card n ∧ μ i = (m : K) + (2 : K)⁻¹ := by
  let s := Finset.univ.erase i
  have hsum : (∑ k ∈ s, orientedCarOccupationElement (K := K) i k) • v =
      (μ i - (2 : K)⁻¹) • v := by
    change (∑ k ∈ s, orientedCarOccupationElement (K := K) i k) * v =
      (μ i - (2 : K)⁻¹) • v
    have hdiag := hv.lie_single_self_eq_smul i
    rw [car_lie_def,
      @glCliffordHom_single_self_eq_sum_positive_occupation K n inferInstance inferInstance h2
        inferInstance i] at hdiag
    change (∑ k, orientedCarOccupationElement (K := K) i k) * v = μ i • v at hdiag
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_mul,
      orientedCarOccupationElement_self, smul_mul_assoc, one_mul] at hdiag
    rw [sub_smul]
    exact eq_sub_of_add_eq hdiag
  obtain ⟨m, hm, hμ⟩ := exists_eq_natCast_of_sum_smul_eq_smul s
    (orientedCarOccupationElement (K := K) i)
    (fun k hk => orientedCarOccupationElement_idempotent (Finset.ne_of_mem_erase hk))
    (fun k _ l _ _ => commute_orientedCarOccupationElement i k l) hv.ne_zero hsum
  refine ⟨m, ?_, eq_add_of_sub_eq hμ⟩
  have hcard : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨i⟩
  have hm' : m ≤ Fintype.card n - 1 := by
    simpa only [s, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] using hm
  omega

end IsGlHighestWeightVector

end

end TauCeti

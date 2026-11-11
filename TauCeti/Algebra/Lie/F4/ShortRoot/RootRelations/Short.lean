/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.RootSubgroup
import Mathlib.GroupTheory.Commutator.Basic
import TauCeti.LinearAlgebra.Matrix.Step

/-!
# The adjacent short-root Chevalley relation in the F₄ carrier

The two short simple roots, Bourbaki nodes three and four, span a subsystem of type A₂.
Their positive root points have commutator `n₂ x₃(ab) n₂⁻¹`, where `n₂` is the pinned
simple Weyl representative at zero-based node two. The quadratic divided-square terms of
these root points are retained over arbitrary commutative rings.

The calculation uses the integral weight tables of `F4ShortRoot.Basic` and the existing
Weyl-transported root parametrization, so it fixes the sign relative to that parametrization.
It does not identify the carrier with an independently constructed pinned group scheme.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
-/

public section

open scoped commutatorElement

namespace TauCeti.F4ShortRoot

universe v

private abbrev target (k : Fin 4 ⊕ Fin 4) : Fin 26 → Fin 26 :=
  Sum.elim raisingTarget loweringTarget k

private abbrev coeff (k : Fin 4 ⊕ Fin 4) : Fin 26 → ℤ :=
  Sum.elim raisingCoeff loweringCoeff k

private abbrev squareTarget (k : Fin 4 ⊕ Fin 4) : Fin 26 → Fin 26 :=
  Sum.elim raisingDividedSquareTarget loweringDividedSquareTarget k

private abbrev squareCoeff (k : Fin 4 ⊕ Fin 4) : Fin 26 → ℤ :=
  Sum.elim raisingDividedSquareCoeff loweringDividedSquareCoeff k

private theorem rootMatrix_isStep (k : Fin 4 ⊕ Fin 4) :
    (rootMatrix k).IsStep (target k) (coeff k) := by
  apply Matrix.isStep_of_apply
  cases k <;> simp only [rootMatrix_inl, rootMatrix_inr, raisingMatrix_apply,
    loweringMatrix_apply, target, coeff, Sum.elim_inl, Sum.elim_inr] <;> intros <;> rfl

private theorem rootDividedSquareMatrix_isStep (k : Fin 4 ⊕ Fin 4) :
    (rootDividedSquareMatrix k).IsStep (squareTarget k) (squareCoeff k) := by
  apply Matrix.isStep_of_apply
  cases k <;> simp only [rootDividedSquareMatrix_inl, rootDividedSquareMatrix_inr,
    raisingDividedSquareMatrix_apply, loweringDividedSquareMatrix_apply,
    squareTarget, squareCoeff, Sum.elim_inl, Sum.elim_inr] <;> intros <;> rfl

/-- Entries of a root word, read from right to left. Each multiplication selects only three
columns, avoiding sums over all twenty-six weights. -/
private def wordEntry {A : Type*} [CommRing A] :
    List ((Fin 4 ⊕ Fin 4) × A) → Fin 26 → Fin 26 → A
  | [], r, s => if r = s then 1 else 0
  | (k, t) :: l, r, s => wordEntry l r s +
      (if coeff k s = 0 then 0 else t * (coeff k s : A) * wordEntry l r (target k s)) +
      (if squareCoeff k s = 0 then 0 else
        t ^ 2 * (squareCoeff k s : A) * wordEntry l r (squareTarget k s))

private theorem wordEntry_eq {A : Type v} [CommRing A]
    (l : List ((Fin 4 ⊕ Fin 4) × A)) (r s : Fin 26) :
    wordEntry l r s =
      (((l.reverse.map fun kt ↦ rootSubgroupPoints kt.1 A (Multiplicative.ofAdd kt.2)).prod :
        Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) r s := by
  induction l generalizing s with
  | nil => simp [wordEntry, Matrix.one_apply]
  | cons kt l ih =>
    rcases kt with ⟨k, t⟩
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one,
      Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_rootSubgroupPoints_eq]
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.smul_apply,
      ((rootMatrix_isStep k).map (Int.cast : ℤ → A) (Int.cast_zero)).mul_right_apply,
      ((rootDividedSquareMatrix_isStep k).map (Int.cast : ℤ → A)
        (Int.cast_zero)).mul_right_apply]
    simp only [wordEntry, ih, smul_eq_mul, toAdd_ofAdd]
    split_ifs <;> simp_all [mul_assoc, mul_comm]

private def shortRelationAt {A : Type v} [CommRing A] (a b : A) (r s : Fin 26) : Prop :=
  wordEntry [(.inl 3, -b), (.inl 2, -a), (.inl 3, b), (.inl 2, a)] r s =
    wordEntry [(.inl 2, -1), (.inr 2, 1), (.inl 2, -1), (.inl 3, a * b),
      (.inl 2, 1), (.inr 2, -1), (.inl 2, 1)] r s

-- Checking all 676 entries in one declaration exceeds the default elaboration budget.
-- This local tactic shares the table reduction for the twenty-six separately checked rows.
local macro "short_relation_row" : tactic => `(tactic|
  (intro s; fin_cases s <;>
    norm_num [shortRelationAt, wordEntry, target, coeff, squareTarget, squareCoeff,
      raisingTarget, raisingCoeff, loweringTarget, loweringCoeff,
      raisingDividedSquareTarget, raisingDividedSquareCoeff,
      loweringDividedSquareTarget, loweringDividedSquareCoeff] <;>
    simp [pow_two, two_mul, mul_two, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm,
      add_assoc]))

variable {A : Type v} [CommRing A] (a b : A)

private theorem short_relation_row0 : ∀ s, shortRelationAt a b 0 s := by short_relation_row
private theorem short_relation_row1 : ∀ s, shortRelationAt a b 1 s := by short_relation_row
private theorem short_relation_row2 : ∀ s, shortRelationAt a b 2 s := by short_relation_row
private theorem short_relation_row3 : ∀ s, shortRelationAt a b 3 s := by short_relation_row
private theorem short_relation_row4 : ∀ s, shortRelationAt a b 4 s := by short_relation_row
private theorem short_relation_row5 : ∀ s, shortRelationAt a b 5 s := by short_relation_row
private theorem short_relation_row6 : ∀ s, shortRelationAt a b 6 s := by short_relation_row
private theorem short_relation_row7 : ∀ s, shortRelationAt a b 7 s := by short_relation_row
private theorem short_relation_row8 : ∀ s, shortRelationAt a b 8 s := by short_relation_row
private theorem short_relation_row9 : ∀ s, shortRelationAt a b 9 s := by short_relation_row
private theorem short_relation_row10 : ∀ s, shortRelationAt a b 10 s := by short_relation_row
private theorem short_relation_row11 : ∀ s, shortRelationAt a b 11 s := by short_relation_row
private theorem short_relation_row12 : ∀ s, shortRelationAt a b 12 s := by short_relation_row
private theorem short_relation_row13 : ∀ s, shortRelationAt a b 13 s := by short_relation_row
private theorem short_relation_row14 : ∀ s, shortRelationAt a b 14 s := by short_relation_row
private theorem short_relation_row15 : ∀ s, shortRelationAt a b 15 s := by short_relation_row
private theorem short_relation_row16 : ∀ s, shortRelationAt a b 16 s := by short_relation_row
private theorem short_relation_row17 : ∀ s, shortRelationAt a b 17 s := by short_relation_row
private theorem short_relation_row18 : ∀ s, shortRelationAt a b 18 s := by short_relation_row
private theorem short_relation_row19 : ∀ s, shortRelationAt a b 19 s := by short_relation_row
private theorem short_relation_row20 : ∀ s, shortRelationAt a b 20 s := by short_relation_row
private theorem short_relation_row21 : ∀ s, shortRelationAt a b 21 s := by short_relation_row
private theorem short_relation_row22 : ∀ s, shortRelationAt a b 22 s := by short_relation_row
private theorem short_relation_row23 : ∀ s, shortRelationAt a b 23 s := by short_relation_row
private theorem short_relation_row24 : ∀ s, shortRelationAt a b 24 s := by short_relation_row
private theorem short_relation_row25 : ∀ s, shortRelationAt a b 25 s := by short_relation_row

private theorem short_relation_certificate (r s : Fin 26) : shortRelationAt a b r s := by
  fin_cases r
  · exact short_relation_row0 a b s
  · exact short_relation_row1 a b s
  · exact short_relation_row2 a b s
  · exact short_relation_row3 a b s
  · exact short_relation_row4 a b s
  · exact short_relation_row5 a b s
  · exact short_relation_row6 a b s
  · exact short_relation_row7 a b s
  · exact short_relation_row8 a b s
  · exact short_relation_row9 a b s
  · exact short_relation_row10 a b s
  · exact short_relation_row11 a b s
  · exact short_relation_row12 a b s
  · exact short_relation_row13 a b s
  · exact short_relation_row14 a b s
  · exact short_relation_row15 a b s
  · exact short_relation_row16 a b s
  · exact short_relation_row17 a b s
  · exact short_relation_row18 a b s
  · exact short_relation_row19 a b s
  · exact short_relation_row20 a b s
  · exact short_relation_row21 a b s
  · exact short_relation_row22 a b s
  · exact short_relation_row23 a b s
  · exact short_relation_row24 a b s
  · exact short_relation_row25 a b s

/-- The commutator at the adjacent short simple roots is the sum-root point with parameter
`a * b`, normalized by the pinned Weyl representative at node two. -/
theorem commutatorElement_rootSubgroupPoints_inl_two_three
    (A : Type v) [CommRing A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 2) A (Multiplicative.ofAdd a),
      rootSubgroupPoints (.inl 3) A (Multiplicative.ofAdd b)⁆ =
      weylRootSubgroupPoints [2] 3 A (Multiplicative.ofAdd (a * b)) := by
  apply Subtype.ext
  apply Units.ext
  ext r s
  have h := short_relation_certificate a b r s
  rw [shortRelationAt] at h
  simpa only [wordEntry_eq, List.reverse_cons, List.reverse_nil, List.map_append,
    List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil,
    mul_one, weylRootSubgroupPoints_cons, weylRootSubgroupPoints_nil,
    simpleWeylPoint_def, commutatorElement_def, mul_inv_rev,
    ← map_inv, ← ofAdd_neg, neg_neg, mul_assoc, one_mul] using h

/-- Reversing the adjacent short simple roots negates the sum-root parameter. -/
theorem commutatorElement_rootSubgroupPoints_inl_three_two
    (A : Type v) [CommRing A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 3) A (Multiplicative.ofAdd b),
      rootSubgroupPoints (.inl 2) A (Multiplicative.ofAdd a)⁆ =
      weylRootSubgroupPoints [2] 3 A (Multiplicative.ofAdd (-(a * b))) := by
  rw [← commutatorElement_inv, commutatorElement_rootSubgroupPoints_inl_two_three,
    ofAdd_neg, map_inv]

end TauCeti.F4ShortRoot

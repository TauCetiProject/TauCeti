/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.TransitionCheck
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.BigOperators.Fin

/-!
# A checked two-cell cover in the symmetric group on three letters

The stabilizer of `0` in `S₃` has normal forms `1` and `(1 2)`. Eight correction triples
certify all signed transitions between its two double cosets, represented by `1` and `(0 1)`.
The inverse transitions reuse the same triples because the generators are involutions.
The accepted check gives finite index and the bound `1 + 2 = 3`, without using the ambient
order as an input. Replacing the corrections by identity triples makes the check fail.
-/

public section

open Equiv
open scoped Pointwise

namespace TauCeti.Examples.DoubleCosetTransition

/-- The point stabilizer whose cosets are being covered. -/
abbrev H : Subgroup (Perm (Fin 3)) :=
  MulAction.stabilizer (Perm (Fin 3)) (0 : Fin 3)

/-- The adjacent transpositions generating `S₃`. -/
def generators (i : Fin 2) : Perm (Fin 3) := swap i.castSucc i.succ

/-- The identity cell and the cell of `(0 1)`. -/
def representatives (i : Fin 2) : Perm (Fin 3) :=
  if i = 0 then 1 else generators 0

/-- The two-element normal form for the point stabilizer. -/
def normalForm (i : Fin 2) : H :=
  if i = 0 then 1 else ⟨swap 1 2, by decide⟩

/-- The correction indices `(l, j, r)` for each generator, subgroup normal form and source cell.
Both factors indexed by `l` and `r` are evaluated in the subgroup normal form. -/
def correctionIndices (s t i : Fin 2) : Fin 2 × Fin 2 × Fin 2 :=
  if s = 0 then
    if t = 0 then
      if i = 0 then (0, 1, 0) else (0, 0, 0)
    else
      if i = 0 then (0, 1, 1) else (1, 1, 1)
  else
    if t = 0 then
      if i = 0 then (0, 0, 1) else (1, 1, 0)
    else
      if i = 0 then (0, 0, 0) else (0, 1, 0)

/-- The correction triples interpreted in the point stabilizer; both signs use the same data. -/
def corrections (s : Fin 2) (_b : Bool) (t i : Fin 2) : H × Fin 2 × H :=
  let c := correctionIndices s t i
  (normalForm c.1, c.2.1, normalForm c.2.2)

/-- The literal correction table passes all sixteen signed transition checks in the actual
permutation group. -/
theorem check_corrections :
    H.checkDoubleCosetTransitions generators representatives normalForm 0 corrections =
    true := by
  decide +kernel

/-- The checked double-coset transitions certify finite index and the three-coset upper bound. -/
theorem finiteIndex_and_index_le_three : H.FiniteIndex ∧ H.index ≤ 3 := by
  have hgen : Subgroup.closure (Set.range generators) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top (Perm.mclosure_swap_castSucc_succ 2)
  have hnormal : Function.Surjective normalForm := by decide +kernel
  have hcheck : H.checkDoubleCosetTransitions generators representatives normalForm 0
      corrections = true := check_corrections
  refine ⟨H.finiteIndex_of_checkDoubleCosetTransitions generators representatives normalForm 0
    corrections hgen hnormal hcheck, ?_⟩
  have bound := H.index_le_sum_of_checkDoubleCosetTransitions generators representatives
    normalForm 0 corrections hgen hnormal hcheck
  have hzero : (ConjAct.toConjAct (representatives 0) • H).relIndex H = 1 := by
    simp [representatives]
  have hcard : Nat.card H = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hone : (ConjAct.toConjAct (representatives 1) • H).relIndex H ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _)).trans hcard.le
  exact bound.trans (by
    simpa only [Fin.sum_univ_two, hzero] using Nat.add_le_add_left hone 1)

/-- Incorrect correction triples are rejected, even with a correct root and subgroup normal
form. The checker does not trust target-cell labels. -/
theorem check_incorrect_corrections :
    H.checkDoubleCosetTransitions generators representatives normalForm 0
      (fun _ _ _ _ ↦ (1, 0, 1)) = false := by
  decide +kernel

end TauCeti.Examples.DoubleCosetTransition

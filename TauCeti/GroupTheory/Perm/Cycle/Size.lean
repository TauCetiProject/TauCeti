/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Sizes of permutation cycles

`Equiv.Perm.cycleSize` counts the coordinates in a class of the same-cycle quotient,
including singleton cycles at fixed points. For finite coordinate types these sizes are
positive and sum to the ambient cardinality. On a nontrivial cycle they agree with the
support cardinality of Mathlib's `Equiv.Perm.cycleOf`.
-/

public noncomputable section

namespace Equiv.Perm

variable {I : Type*} (σ : Equiv.Perm I)

/-- The number of coordinates in a permutation cycle, independent of decidability instances. -/
def cycleSize (c : Quotient (SameCycle.setoid σ)) : ℕ :=
  Nat.card {i : I // Quotient.mk (SameCycle.setoid σ) i = c}

/-- A cycle size is the cardinality of the corresponding quotient fibre. -/
theorem cycleSize_def (c : Quotient (SameCycle.setoid σ)) :
    cycleSize σ c = Nat.card {i : I // Quotient.mk (SameCycle.setoid σ) i = c} := (rfl)

/-- The size of the cycle containing `i` counts the coordinates in the same cycle as `i`. -/
theorem cycleSize_mk (i : I) :
    cycleSize σ (Quotient.mk _ i) = Nat.card {j : I // σ.SameCycle j i} := by
  simp only [cycleSize, Quotient.eq, SameCycle.setoid]

/-- A fixed point belongs to a singleton cycle. -/
@[simp]
theorem cycleSize_mk_of_apply_eq_self {i : I} (hi : σ i = i) :
    cycleSize σ (Quotient.mk _ i) = 1 := by
  rw [cycleSize_mk]
  have h : (fun j ↦ σ.SameCycle j i) = (fun j ↦ j = i) := by
    funext j
    exact propext ⟨fun h ↦ h.eq_of_right hi, fun h ↦ h ▸ SameCycle.rfl⟩
  simp [h]

variable [Finite I]

/-- Every permutation cycle contains at least one coordinate. -/
theorem cycleSize_pos (c : Quotient (SameCycle.setoid σ)) : 0 < cycleSize σ c := by
  have : Nonempty {i : I // Quotient.mk (SameCycle.setoid σ) i = c} :=
    ⟨⟨c.out, Quotient.out_eq c⟩⟩
  exact Nat.card_pos

/-- The cycle sizes partition the ambient coordinate cardinality. -/
theorem finsum_cycleSize :
    ∑ᶠ c : Quotient (SameCycle.setoid σ), cycleSize σ c = Nat.card I := by
  classical
  let := Fintype.ofFinite I
  simpa only [Nat.card_sigma, ← cycleSize_def, finsum_eq_sum_of_fintype] using
    Nat.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk (SameCycle.setoid σ)))

omit [Finite I] in
/-- On a nontrivial cycle, the quotient cycle size is the support size of `cycleOf`. -/
theorem cycleSize_mk_eq_card_support_cycleOf [Fintype I] [DecidableEq I]
    {i : I} (hi : σ i ≠ i) :
    cycleSize σ (Quotient.mk _ i) = (σ.cycleOf i).support.card := by
  rw [cycleSize_mk]
  have h : (fun j ↦ σ.SameCycle j i) = (fun j ↦ j ∈ (σ.cycleOf i).support) := by
    funext j
    exact propext ((sameCycle_comm).trans (mem_support_cycleOf_iff' hi).symm)
  rw [h]
  exact Nat.card_eq_finsetCard _

end Equiv.Perm

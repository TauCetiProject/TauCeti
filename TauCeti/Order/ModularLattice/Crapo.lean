/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.ModularLattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.WellFoundedSet

/-!
# Crapo's complementation theorem

Let `μ` be a function on a finite modular lattice `L` with values in a commutative monoid, whose
sum over the elements below `X` vanishes for every `X ≠ ⊥`; this is the defining recursion of the
Möbius function `U ↦ μ(⊥, U)`. If `μ ⊤ ≠ 0`, then `L` is complemented. For the Möbius function
this is one half of Crapo's complementation theorem: if `μ(⊥, ⊤) ≠ 0`, the modular lattice is
complemented.

## Main results

* `TauCeti.complementedLattice_of_sum_le_eq_zero`: the statement above.

## References

* H. H. Crapo, *The Möbius function of a lattice*, J. Combinatorial Theory 1 (1966), 126–131.
* Adapted from `src/Lib/LocalGL/Green/CuspidalFunctions.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.Hall.crapo_complementation`, here for values in any commutative monoid.
-/

public section

namespace TauCeti

variable {L M : Type*} [Lattice L] [BoundedOrder L] [IsModularLattice L] [Fintype L]
  [DecidableLE L] [AddCommMonoid M]

/-- If the sum of `μ` over the elements below `X` vanishes for every `X ≠ ⊥`, then `μ U = 0` for
every `U` that is not below `Y`, whenever `Y` is the supremum of an element `W` and of an element
`C` maximal among those disjoint from `W`. -/
private theorem eq_zero_of_not_le_sup {μ : L → M}
    (h_sum : ∀ X ≠ ⊥, ∑ U with U ≤ X, μ U = 0) {W C : L} (hC : Maximal (Disjoint W) C)
    (U : L) (hU : ¬U ≤ W ⊔ C) : μ U = 0 := by
  classical
  induction U using WellFoundedLT.induction with | ind U ih => ?_
  -- If `U ⊓ (W ⊔ C) = ⊥` then `W` is disjoint from `C ⊔ U` by modularity, so `U ≤ C` by
  -- maximality of `C`.
  have h_meet : U ⊓ (W ⊔ C) ≠ ⊥ := by
    intro h_bot
    have h_disj : Disjoint W (C ⊔ U) :=
      hC.prop.disjoint_sup_right_of_disjoint_sup_left (disjoint_iff.2 (by rwa [inf_comm]))
    exact hU (le_sup_right.trans ((hC.le_of_ge h_disj le_sup_left).trans le_sup_right))
  -- The sums of `μ` below `U` and below `U ⊓ (W ⊔ C)` vanish; by `ih` their difference is `μ U`.
  have h_sub : ({A | A ≤ U ⊓ (W ⊔ C)} : Finset L) ⊆ ({A | A ≤ U} : Finset L) :=
    fun A hA ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hA).2.trans inf_le_left⟩
  have h_diff := Finset.sum_sdiff (f := μ) h_sub
  rw [h_sum _ h_meet, add_zero, h_sum _ (ne_bot_of_le_ne_bot h_meet inf_le_left),
    Finset.sum_eq_single_of_mem U (by simp [hU])] at h_diff
  · exact h_diff
  · intro A hA hAU
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, le_inf_iff,
      not_and] at hA
    exact ih A (lt_of_le_of_ne hA.1 hAU) fun h ↦ hA.2 hA.1 h

/-- **Crapo's complementation theorem**, the vanishing half. Let `μ` be a function on a finite
modular lattice whose sum over the elements below `X` vanishes for every `X ≠ ⊥`. If `μ ⊤ ≠ 0`,
the lattice is complemented. -/
theorem complementedLattice_of_sum_le_eq_zero {μ : L → M}
    (h_sum : ∀ X ≠ ⊥, ∑ U with U ≤ X, μ U = 0) (h_top : μ ⊤ ≠ 0) : ComplementedLattice L := by
  refine ⟨fun W ↦ ?_⟩
  -- Take `C` maximal among the elements disjoint from `W`; then `W ⊔ C = ⊤`.
  obtain ⟨C, hC⟩ : ∃ C : L, Maximal (Disjoint W) C :=
    exists_maximal_of_wellFoundedGT (Disjoint W) ⟨⊥, disjoint_bot_right⟩
  refine ⟨C, hC.prop, codisjoint_iff_le_sup.2 ?_⟩
  by_contra h_top'
  exact h_top (eq_zero_of_not_le_sup h_sum hC ⊤ h_top')

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FiniteAbelian.TorsionFree
public import TauCeti.GroupTheory.FreeGroup.TwoGenerator
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree

/-!
# Two-generated subgroups of residually free groups

Two elements `a` and `b` of a residually free group generate the trivial group, `ℤ`, `ℤ²`, or a
free group of rank two. If they commute, they generate a free abelian group of rank at most two,
since residually free groups are torsion-free. If they do not, some homomorphism `φ` to a free
group keeps their commutator nontrivial; then `φ a` and `φ b` do not commute, so they freely
generate a free group of rank two, and therefore so do `a` and `b`. In particular a nonabelian
residually free group contains a free group of rank two, and full residual freeness is not needed
for this.

## Main results

* `TauCeti.LimitGroup.IsResiduallyFree.injective_lift_iff_not_commute`: in a residually free group,
  `a` and `b` freely generate a free group of rank two if and only if they do not commute.
* `TauCeti.LimitGroup.IsResiduallyFree.closure_pair_mulEquiv_int_or_freeGroup`: two elements of a
  residually free group generate a subgroup isomorphic to `ℤᵏ` with `k ≤ 2`, or to the free group
  of rank two.

## References

* C. Champetier, V. Guirardel, *Limit groups as limits of free groups*, Israel J. Math. 146
  (2005), Proposition 3.1.
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti.LimitGroup

variable {G : Type*} [Group G]

/-- In a residually free group, two noncommuting elements freely generate a free group of rank
two. -/
theorem IsResiduallyFree.injective_lift_of_not_commute (h : IsResiduallyFree G) {a b : G}
    (hab : ¬Commute a b) : Function.Injective (FreeGroup.lift ![a, b]) := by
  -- A homomorphism to a free group keeping `⁅a, b⁆` nontrivial keeps `a` and `b` noncommuting.
  obtain ⟨ι, φ, hφ⟩ :=
    isResiduallyFree_def.mp h ⁅a, b⁆ (by rwa [Ne, commutatorElement_eq_one_iff_commute])
  have hφab : ¬Commute (φ a) (φ b) := by
    rwa [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
  have hcomp : φ.comp (FreeGroup.lift ![a, b]) = FreeGroup.lift ![φ a, φ b] := by
    ext i
    fin_cases i <;> simp
  have hinj := IsFreeGroup.injective_lift_of_not_commute hφab
  rw [← hcomp, MonoidHom.coe_comp] at hinj
  exact hinj.of_comp

/-- In a residually free group, `a` and `b` freely generate a free group of rank two if and only if
they do not commute. -/
theorem IsResiduallyFree.injective_lift_iff_not_commute (h : IsResiduallyFree G) {a b : G} :
    Function.Injective (FreeGroup.lift ![a, b]) ↔ ¬Commute a b :=
  ⟨FreeGroup.not_commute_of_injective_lift, h.injective_lift_of_not_commute⟩

/-- **Two-generated subgroups of residually free groups.** Two elements of a residually free group
generate a subgroup isomorphic to `ℤᵏ` for some `k ≤ 2`, that is the trivial group, `ℤ` or `ℤ²`,
when they commute, and to the free group of rank two when they do not. -/
theorem IsResiduallyFree.closure_pair_mulEquiv_int_or_freeGroup (h : IsResiduallyFree G)
    (a b : G) :
    (Commute a b ∧ ∃ k ≤ 2, Nonempty (closure {a, b} ≃* Multiplicative (Fin k → ℤ))) ∨
      (¬Commute a b ∧ Nonempty (closure {a, b} ≃* FreeGroup (Fin 2))) := by
  classical
  by_cases hab : Commute a b
  · have := h.isMulTorsionFree
    have hs : (({a, b} : Finset G) : Set G).Pairwise Commute := by
      rw [Finset.coe_pair]
      exact Set.pairwise_pair.mpr fun _ => ⟨hab, hab.symm⟩
    obtain ⟨k, hk, he⟩ := exists_mulEquiv_closure_of_pairwise_commute hs
    rw [Finset.coe_pair] at he
    exact .inl ⟨hab, k, hk.trans Finset.card_le_two, he⟩
  · have hrange : (FreeGroup.lift ![a, b]).range = closure {a, b} := by
      rw [FreeGroup.range_lift_eq_closure, Matrix.range_cons_cons_empty]
    exact .inr ⟨hab, ⟨((MonoidHom.ofInjective (h.injective_lift_of_not_commute hab)).trans
      (MulEquiv.subgroupCongr hrange)).symm⟩⟩

end TauCeti.LimitGroup

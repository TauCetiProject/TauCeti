/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.AlmostConjugate
import TauCeti.GroupTheory.GroupAction.Orbit.CycleType
import TauCeti.GroupTheory.Perm.PermCongr

/-!
# Almost-conjugate regular representations

Let `G` be a finite group of order `m`, with its left-regular action on itself. An element of
order `d` acts on `G` with `m / d` cycles, all of length `d`
(`MulAction.fullCycleType_toPerm_eq_replicate`). Reading the regular representation inside the
symmetric group of an `m`-element set `α` through a numbering `e : G ≃ α`, the cycle type of the
image of `g` therefore depends only on `orderOf g`. Since two permutations are conjugate exactly
when they have the same cycle type, two groups of order `m` with the same number of elements of
each order have almost-conjugate regular images in `Equiv.Perm α`. If one of the groups is
commutative and the other is not, the images are not conjugate, because conjugate subgroups are
isomorphic (`Equiv.not_exists_map_conj_map_range_toPermHom_eq`, in
`TauCeti.GroupTheory.Perm.PermCongr`).

The concrete Gassmann pair in `S₁₆` built from these results is in
`TauCeti.GroupTheory.AlmostConjugate.GassmannPair`.

## Main statements

* `Equiv.natCard_cycleType_eq_and_mem_map_range_toPermHom`: the number of permutations of a
  given cycle type in a regular image, as a count of group elements by their order.
* `Equiv.almostConjugate_map_range_toPermHom`: groups with the same number of elements of each
  order have almost-conjugate regular images.

## References

* F. Gassmann, *Bemerkungen zur vorstehenden Arbeit von Hurwitz*, Math. Z. **25** (1926), 665–675.
* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory **9** (1977), 342–360.
-/

public section

open MulAction

namespace Equiv

variable {G Γ α : Type*} [Group G] [Group Γ]

/-- **Cycle types in a regular representation.** The regular representation of `G`, read in
`Equiv.Perm α` through `e : G ≃ α`, contains as many permutations of cycle type `m` as `G` has
elements `g` for which `Nat.card α / orderOf g` copies of `orderOf g`, with the parts equal to `1`
(the fixed points) discarded, form the multiset `m`. -/
theorem natCard_cycleType_eq_and_mem_map_range_toPermHom [Fintype α] [DecidableEq α]
    (e : G ≃ α) (m : Multiset ℕ) :
    Nat.card {σ : Equiv.Perm α //
        σ.cycleType = m ∧ σ ∈ (toPermHom G G).range.map e.permCongrHom.toMonoidHom} =
      Nat.card {g : G //
        (Multiset.replicate (Nat.card α / orderOf g) (orderOf g)).filter (2 ≤ ·) = m} := by
  classical
  have : Fintype G := Fintype.ofEquiv α e.symm
  set φ : G →* Equiv.Perm α := e.permCongrHom.toMonoidHom.comp (toPermHom G G) with hφ
  have hcyc (g : G) : (φ g).cycleType =
      (Multiset.replicate (Nat.card α / orderOf g) (orderOf g)).filter (2 ≤ ·) := by
    rw [← Perm.filter_fullCycleType_eq_cycleType]
    simp only [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, permCongrHom_coe,
      toPermHom_apply]
    -- Transport keeps the full cycle type, which for the regular action is read off `orderOf g`.
    rw [Perm.fullCycleType_permCongr, fullCycleType_toPerm_eq_replicate, Nat.card_congr e]
  rw [MonoidHom.map_range, ← hφ]
  refine (Nat.card_congr ?_).symm
  exact ((Equiv.ofInjective φ e.permCongrHom_comp_toPermHom_injective).subtypeEquiv fun g ↦ by
      rw [Equiv.ofInjective_apply, hcyc]).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ φ.range) (·.cycleType = m)).trans <|
      Equiv.subtypeEquivRight fun _ ↦ and_comm

/-- **Regular representations of groups with the same order statistics are almost conjugate.** If
two groups have the same number of elements of each order, their regular representations, read in
the symmetric group of a finite set through numberings `e` and `f`, are almost conjugate. -/
theorem almostConjugate_map_range_toPermHom [Finite α] (e : G ≃ α) (f : Γ ≃ α)
    (h : ∀ n : ℕ, Nat.card {g : G // orderOf g = n} = Nat.card {γ : Γ // orderOf γ = n}) :
    ((toPermHom G G).range.map e.permCongrHom.toMonoidHom).AlmostConjugate
      ((toPermHom Γ Γ).range.map f.permCongrHom.toMonoidHom) := by
  classical
  have := Fintype.ofFinite α
  have : Finite G := .of_equiv α e.symm
  have : Finite Γ := .of_equiv α f.symm
  -- A bijection `G ≃ Γ` preserving orders matches the cycle-type counts of the two images.
  let ψ : G ≃ Γ := Equiv.ofFiberEquiv fun n ↦ (Finite.card_eq.mp (h n)).some
  have hψ (g : G) : orderOf (ψ g) = orderOf g := Equiv.ofFiberEquiv_map _ g
  rw [Subgroup.almostConjugate_iff_forall_natCard_cycleType_eq]
  intro m
  rw [natCard_cycleType_eq_and_mem_map_range_toPermHom,
    natCard_cycleType_eq_and_mem_map_range_toPermHom]
  exact Nat.card_congr (ψ.subtypeEquiv fun g ↦ by rw [hψ])

end Equiv

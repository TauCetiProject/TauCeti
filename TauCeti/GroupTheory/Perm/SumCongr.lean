/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import TauCeti.GroupTheory.Perm.OrbitCount
import Mathlib.Tactic.Abel

/-!
# The cycles of a permutation acting separately on the two halves of a sum

`Equiv.Perm.sumCongr σ τ` permutes `α ⊕ β` by `σ` on the left summand and by `τ` on the right
one. Every cycle stays inside one of the two halves, so all the cycle data simply concatenates.

## Main results

* `Equiv.Perm.cycleType_sumCongr`, `Equiv.Perm.card_support_sumCongr`,
  `Equiv.Perm.parts_partition_sumCongr`: the cycle type, the number of moved points and the parts
  of the full, fixed-point-aware partition are additive.
* `Equiv.Perm.orbitCount_sumCongr`: so is the number of orbits, fixed points included.
* `Equiv.Perm.finSumPerm`: the same construction read on `Fin (m + n)` through
  `finSumFinEquiv`, with `Equiv.Perm.finSumPermHom` packaging it as a monoid homomorphism from
  `Equiv.Perm (Fin m) × Equiv.Perm (Fin n)`, and with the two cycle-counting results transported.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

variable {α β : Type*}

/-! ### Splitting a sum permutation into its two halves -/

/-- A permutation of the left summand, extended by the identity, is the extension of its domain
along `Equiv.sumIsLeft`. -/
theorem _root_.Equiv.Perm.sumCongr_one_eq_extendDomain (σ : Perm α) :
    Perm.sumCongr σ (1 : Perm β) =
      σ.extendDomain (Equiv.sumIsLeft (α := α) (β := β)).symm := by
  refine Equiv.ext fun x => ?_
  match x with
  | Sum.inl a =>
    simpa using
      (σ.extendDomain_apply_image (Equiv.sumIsLeft (α := α) (β := β)).symm a).symm
  | Sum.inr b =>
    rw [Perm.extendDomain_apply_not_subtype _ _ (by simp)]
    rfl

/-- A permutation of the right summand, extended by the identity, is the extension of its domain
along `Equiv.sumIsRight`. -/
theorem _root_.Equiv.Perm.one_sumCongr_eq_extendDomain (τ : Perm β) :
    Perm.sumCongr (1 : Perm α) τ =
      τ.extendDomain (Equiv.sumIsRight (α := α) (β := β)).symm := by
  refine Equiv.ext fun x => ?_
  match x with
  | Sum.inl a =>
    rw [Perm.extendDomain_apply_not_subtype _ _ (by simp)]
    rfl
  | Sum.inr b =>
    simpa using
      (τ.extendDomain_apply_image (Equiv.sumIsRight (α := α) (β := β)).symm b).symm

/-- The two halves of a sum permutation are disjoint: each of them fixes everything the other
can move. -/
theorem _root_.Equiv.Perm.disjoint_sumCongr_one_one_sumCongr (σ : Perm α) (τ : Perm β) :
    Perm.Disjoint (Perm.sumCongr σ (1 : Perm β)) (Perm.sumCongr (1 : Perm α) τ) := by
  rw [Perm.disjoint_iff_eq_or_eq]
  rintro (a | b)
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ### Additivity of the cycle data -/

section Finite

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The cycles of `Equiv.Perm.sumCongr σ τ` are those of `σ` together with those of `τ`. -/
@[simp]
theorem _root_.Equiv.Perm.cycleType_sumCongr (σ : Perm α) (τ : Perm β) :
    (Perm.sumCongr σ τ).cycleType = σ.cycleType + τ.cycleType := by
  have h := Perm.sumCongr_mul σ (1 : Perm β) (1 : Perm α) τ
  simp only [mul_one, one_mul] at h
  rw [← h, (Perm.disjoint_sumCongr_one_one_sumCongr σ τ).cycleType_mul,
    Perm.sumCongr_one_eq_extendDomain, Perm.one_sumCongr_eq_extendDomain,
    cycleType_extendDomain, cycleType_extendDomain]

/-- The points moved by `Equiv.Perm.sumCongr σ τ` are those moved by `σ` together with those
moved by `τ`. -/
@[simp]
theorem _root_.Equiv.Perm.card_support_sumCongr (σ : Perm α) (τ : Perm β) :
    (Perm.sumCongr σ τ).support.card = σ.support.card + τ.support.card := by
  rw [← sum_cycleType, ← sum_cycleType, ← sum_cycleType, cycleType_sumCongr, Multiset.sum_add]

/-- The full, fixed-point-aware cycle partition of a sum permutation is the concatenation of the
two partitions it is assembled from. Unlike `Equiv.Perm.cycleType_sumCongr` this keeps track of
the fixed points, and it is the form the Euler characteristic of a disjoint sum of permutation
triples is computed from. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_sumCongr (σ : Perm α) (τ : Perm β) :
    (Perm.sumCongr σ τ).partition.parts = σ.partition.parts + τ.partition.parts := by
  have hα : σ.support.card ≤ Fintype.card α := by simpa using σ.support.card_le_univ
  have hβ : τ.support.card ≤ Fintype.card β := by simpa using τ.support.card_le_univ
  have hsub : Fintype.card α + Fintype.card β - (σ.support.card + τ.support.card) =
      (Fintype.card α - σ.support.card) + (Fintype.card β - τ.support.card) := by omega
  rw [parts_partition, parts_partition, parts_partition, cycleType_sumCongr,
    card_support_sumCongr, Fintype.card_sum, hsub, Multiset.replicate_add]
  abel

end Finite

/-- The orbits of `Equiv.Perm.sumCongr σ τ`, fixed points included, are those of `σ` together
with those of `τ`. -/
@[simp]
theorem _root_.Equiv.Perm.orbitCount_sumCongr [Finite α] [Finite β] (σ : Perm α) (τ : Perm β) :
    orbitCount (Perm.sumCongr σ τ) = orbitCount σ + orbitCount τ := by
  classical
  cases nonempty_fintype α
  cases nonempty_fintype β
  rw [orbitCount_eq_card_parts_partition, orbitCount_eq_card_parts_partition,
    orbitCount_eq_card_parts_partition, parts_partition_sumCongr, Multiset.card_add]

/-! ### The sum of a permutation of `Fin m` and a permutation of `Fin n` -/

variable {m n : ℕ}

end TauCeti

namespace Equiv.Perm

open TauCeti

/-- Permuting the first `m` labels and the last `n` labels separately, as a monoid homomorphism.
Its range is the subgroup of `Equiv.Perm (Fin (m + n))` preserving the two blocks. -/
def finSumPermHom (m n : ℕ) : Perm (Fin m) × Perm (Fin n) →* Perm (Fin (m + n)) :=
  finSumFinEquiv.permCongrHom.toMonoidHom.comp (sumCongrHom (Fin m) (Fin n))

/-- The permutation of `Fin (m + n)` that acts as `σ` on the first `m` labels and as `τ` on the
last `n`, the two blocks being separated by `finSumFinEquiv`. -/
def finSumPerm (σ : Perm (Fin m)) (τ : Perm (Fin n)) : Perm (Fin (m + n)) :=
  finSumPermHom m n (σ, τ)

@[simp]
theorem finSumPermHom_apply (p : Perm (Fin m) × Perm (Fin n)) :
    finSumPermHom m n p = finSumPerm p.1 p.2 := by
  rfl

theorem finSumPerm_apply (σ : Perm (Fin m)) (τ : Perm (Fin n)) (x : Fin (m + n)) :
    finSumPerm σ τ x = finSumFinEquiv (Sum.map σ τ (finSumFinEquiv.symm x)) := by
  rfl

@[simp]
theorem finSumPerm_apply_castAdd (σ : Perm (Fin m)) (τ : Perm (Fin n)) (i : Fin m) :
    finSumPerm σ τ (Fin.castAdd n i) = Fin.castAdd n (σ i) := by
  rw [← finSumFinEquiv_apply_left, finSumPerm_apply,
    Equiv.symm_apply_apply, Sum.map_inl, finSumFinEquiv_apply_left]

@[simp]
theorem finSumPerm_apply_natAdd (σ : Perm (Fin m)) (τ : Perm (Fin n)) (j : Fin n) :
    finSumPerm σ τ (Fin.natAdd m j) = Fin.natAdd m (τ j) := by
  rw [← finSumFinEquiv_apply_right, finSumPerm_apply,
    Equiv.symm_apply_apply, Sum.map_inr, finSumFinEquiv_apply_right]

@[simp]
theorem finSumPerm_one : finSumPerm (1 : Perm (Fin m)) (1 : Perm (Fin n)) = 1 := by
  change finSumPermHom m n (1, 1) = 1
  exact map_one (finSumPermHom m n)

@[simp]
theorem finSumPerm_inv (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    (finSumPerm σ τ)⁻¹ = finSumPerm σ⁻¹ τ⁻¹ := by
  change (finSumPermHom m n (σ, τ))⁻¹ = finSumPermHom m n (σ⁻¹, τ⁻¹)
  exact (map_inv (finSumPermHom m n) (σ, τ)).symm

theorem finSumPerm_mul (σ σ' : Perm (Fin m)) (τ τ' : Perm (Fin n)) :
    finSumPerm σ τ * finSumPerm σ' τ' = finSumPerm (σ * σ') (τ * τ') := by
  change finSumPermHom m n (σ, τ) * finSumPermHom m n (σ', τ') =
    finSumPermHom m n (σ * σ', τ * τ')
  exact (map_mul (finSumPermHom m n) (σ, τ) (σ', τ')).symm

/-- The full cycle partition of `Equiv.Perm.finSumPerm σ τ` is the concatenation of those of `σ`
and of `τ`. -/
@[simp]
theorem parts_partition_finSumPerm (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    (finSumPerm σ τ).partition.parts = σ.partition.parts + τ.partition.parts := by
  change (finSumFinEquiv.permCongr (Perm.sumCongr σ τ)).partition.parts = _
  rw [parts_partition_permCongr, parts_partition_sumCongr]

/-- The number of orbits of `Equiv.Perm.finSumPerm σ τ`, fixed points included, is the sum of the
numbers of orbits of `σ` and of `τ`. -/
@[simp]
theorem orbitCount_finSumPerm (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    orbitCount (finSumPerm σ τ) = orbitCount σ + orbitCount τ := by
  change orbitCount (finSumFinEquiv.permCongr (Perm.sumCongr σ τ)) = _
  rw [orbitCount_permCongr, orbitCount_sumCongr]

end Equiv.Perm

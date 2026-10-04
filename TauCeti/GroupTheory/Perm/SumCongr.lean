/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic
public import TauCeti.GroupTheory.Perm.SwapFactors
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
* `Equiv.Perm.orbitCount_sumCongr_one_mul_swap_mul_swap_mul_swap_mul_swap`: splicing four
  adjoined fixed points into the orbits of a permutation leaves its number of orbits.
* `Equiv.Perm.sumCongr_zpow`: powers are taken summandwise.
* `Equiv.Perm.sameCycle_sumCongr_inl`, `Equiv.Perm.sameCycle_sumCongr_inr`: two points of one
  summand share a cycle exactly when they share a cycle of the permutation of that summand.
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

/-- The powers of a sum permutation are taken separately on the two summands. -/
@[simp]
theorem _root_.Equiv.Perm.sumCongr_zpow (σ : Perm α) (τ : Perm β) (k : ℤ) :
    Perm.sumCongr σ τ ^ k = Perm.sumCongr (σ ^ k) (τ ^ k) := by
  simpa using (map_zpow (Perm.sumCongrHom α β) (σ, τ) k).symm

/-- Two points of the left summand lie in one cycle of `Equiv.Perm.sumCongr σ τ` exactly when they
lie in one cycle of `σ`. -/
@[simp]
theorem _root_.Equiv.Perm.sameCycle_sumCongr_inl {σ : Perm α} {τ : Perm β} {a b : α} :
    (Perm.sumCongr σ τ).SameCycle (.inl a) (.inl b) ↔ σ.SameCycle a b :=
  exists_congr fun k => by
    rw [Perm.sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inl, Sum.inl.injEq]

/-- Two points of the right summand lie in one cycle of `Equiv.Perm.sumCongr σ τ` exactly when
they lie in one cycle of `τ`. -/
@[simp]
theorem _root_.Equiv.Perm.sameCycle_sumCongr_inr {σ : Perm α} {τ : Perm β} {a b : β} :
    (Perm.sumCongr σ τ).SameCycle (.inr a) (.inr b) ↔ τ.SameCycle a b :=
  exists_congr fun k => by
    rw [Perm.sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inr, Sum.inr.injEq]

/-- Points in different summands cannot lie in the same cycle of a sum permutation. -/
@[simp] theorem not_sameCycle_sumCongr_inl_inr
    (σ : Perm α) (τ : Perm β) (a : α) (b : β) :
    ¬ (Perm.sumCongr σ τ).SameCycle (.inl a) (.inr b) := by
  rintro ⟨k, hk⟩
  simp only [Perm.sumCongr_zpow, Perm.sumCongr_apply, Sum.map_inl,
    Sum.inl_ne_inr] at hk

/-! ### Additivity of the cycle data -/

section Finite

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The cycles of `Equiv.Perm.sumCongr σ τ` are those of `σ` together with those of `τ`. -/
@[simp]
theorem _root_.Equiv.Perm.cycleType_sumCongr (σ : Perm α) (τ : Perm β) :
    (Perm.sumCongr σ τ).cycleType = σ.cycleType + τ.cycleType := by
  have h : Perm.sumCongr σ τ = Perm.sumCongr σ (1 : Perm β) * Perm.sumCongr (1 : Perm α) τ := by
    rw [Perm.sumCongr_mul, mul_one, one_mul]
  rw [h, (Perm.disjoint_sumCongr_one_one_sumCongr σ τ).cycleType_mul,
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

/-- Attach two distinct cycles of the right summand to cycles of the left summand.
Each attachment removes one orbit, even if the two left endpoints lie in the same cycle. -/
theorem orbitCount_sumCongr_mul_swap_mul_swap_add_two
    [DecidableEq α] [DecidableEq β] [Finite α] [Finite β]
    (σ : Perm α) (τ : Perm β) (a c : α) {b d : β} (hbd : ¬ τ.SameCycle b d) :
    orbitCount (Perm.sumCongr σ τ * swap (Sum.inl a : α ⊕ β) (.inr b) *
      swap (.inl c) (.inr d)) + 2 = orbitCount σ + orbitCount τ := by
  have h₁ := orbitCount_mul_swap_add_one_of_not_sameCycle
    (not_sameCycle_sumCongr_inl_inr σ τ a b)
  have h₂ : ¬ (Perm.sumCongr σ τ * swap (Sum.inl a : α ⊕ β) (.inr b)).SameCycle
      (.inl c) (.inr d) := by
    rw [Equiv.mul_swap_eq_swap_mul]
    intro h
    rcases h.sameCycle_or_of_swap_mul with h | ⟨-, h⟩
    · exact not_sameCycle_sumCongr_inl_inr σ τ c d h
    · rcases h with h | h
      · exact not_sameCycle_sumCongr_inl_inr σ τ (σ a) d h.symm
      · apply hbd
        simpa only [Perm.sumCongr_apply, Sum.map_inr, Perm.sameCycle_sumCongr_inr,
          sameCycle_apply_left] using h.symm
  have h₃ := orbitCount_mul_swap_add_one_of_not_sameCycle h₂
  rw [Perm.orbitCount_sumCongr] at h₁
  omega

/-- **Splicing four adjoined fixed points.** Adjoin four fixed points to `σ` and splice each of
them into an orbit, `i₀` after `x₀`, then `i₁` after `x₁`, `i₂` after `x₂` and `i₃` after `x₃`:
each splice removes one orbit, so as many orbits as `σ` has are left. -/
theorem _root_.Equiv.Perm.orbitCount_sumCongr_one_mul_swap_mul_swap_mul_swap_mul_swap
    [DecidableEq α] [Finite α] (σ : Perm α) (x₀ x₁ x₂ x₃ : α) {i₀ i₁ i₂ i₃ : Fin 4}
    (h₀₁ : i₀ ≠ i₁) (h₀₂ : i₀ ≠ i₂) (h₀₃ : i₀ ≠ i₃) (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) :
    orbitCount (Perm.sumCongr σ 1 * swap (.inl x₀) (.inr i₀) * swap (.inl x₁) (.inr i₁) *
      swap (.inl x₂) (.inr i₂) * swap (.inl x₃) (.inr i₃)) = orbitCount σ := by
  have k₀ := orbitCount_mul_swap_add_one (τ := Perm.sumCongr σ (1 : Perm (Fin 4)))
    (p := .inr i₀) (a := .inl x₀) (by simp) (by simp)
  have k₁ := orbitCount_mul_swap_add_one
    (τ := Perm.sumCongr σ (1 : Perm (Fin 4)) * swap (.inl x₀) (.inr i₀))
    (p := .inr i₁) (a := .inl x₁) (by simp [swap_apply_of_ne_of_ne, Ne.symm h₀₁]) (by simp)
  have k₂ := orbitCount_mul_swap_add_one
    (τ := Perm.sumCongr σ (1 : Perm (Fin 4)) * swap (.inl x₀) (.inr i₀) *
      swap (.inl x₁) (.inr i₁))
    (p := .inr i₂) (a := .inl x₂)
    (by simp [swap_apply_of_ne_of_ne, Ne.symm h₀₂, Ne.symm h₁₂]) (by simp)
  have k₃ := orbitCount_mul_swap_add_one
    (τ := Perm.sumCongr σ (1 : Perm (Fin 4)) * swap (.inl x₀) (.inr i₀) *
      swap (.inl x₁) (.inr i₁) * swap (.inl x₂) (.inr i₂))
    (p := .inr i₃) (a := .inl x₃)
    (by simp [swap_apply_of_ne_of_ne, Ne.symm h₀₃, Ne.symm h₁₃, Ne.symm h₂₃]) (by simp)
  have k : orbitCount (Perm.sumCongr σ (1 : Perm (Fin 4))) = orbitCount σ + 4 := by
    rw [Perm.orbitCount_sumCongr, orbitCount_one, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

/-! ### The sum of a permutation of `Fin m` and a permutation of `Fin n` -/

variable {m n : ℕ}

/-- The permutation of `Fin (m + n)` that acts as `σ` on the first `m` labels and as `τ` on the
last `n`, the two blocks being separated by `finSumFinEquiv`. -/
def _root_.Equiv.Perm.finSumPerm (σ : Perm (Fin m)) (τ : Perm (Fin n)) : Perm (Fin (m + n)) :=
  finSumFinEquiv.permCongr (Perm.sumCongr σ τ)

/-- Permuting the first `m` labels and the last `n` labels separately, as a monoid homomorphism.
Its range is the subgroup of `Equiv.Perm (Fin (m + n))` preserving the two blocks. -/
def _root_.Equiv.Perm.finSumPermHom (m n : ℕ) :
    Perm (Fin m) × Perm (Fin n) →* Perm (Fin (m + n)) :=
  finSumFinEquiv.permCongrHom.toMonoidHom.comp (Perm.sumCongrHom (Fin m) (Fin n))

@[simp]
theorem _root_.Equiv.Perm.finSumPermHom_apply (p : Perm (Fin m) × Perm (Fin n)) :
    finSumPermHom m n p = finSumPerm p.1 p.2 := (rfl)

theorem _root_.Equiv.Perm.finSumPerm_apply (σ : Perm (Fin m)) (τ : Perm (Fin n))
    (x : Fin (m + n)) :
    finSumPerm σ τ x = finSumFinEquiv (Sum.map σ τ (finSumFinEquiv.symm x)) := (rfl)

@[simp]
theorem _root_.Equiv.Perm.finSumPerm_apply_castAdd (σ : Perm (Fin m)) (τ : Perm (Fin n))
    (i : Fin m) :
    finSumPerm σ τ (Fin.castAdd n i) = Fin.castAdd n (σ i) := by
  rw [← finSumFinEquiv_apply_left, finSumPerm_apply, Equiv.symm_apply_apply, Sum.map_inl,
    finSumFinEquiv_apply_left]

@[simp]
theorem _root_.Equiv.Perm.finSumPerm_apply_natAdd (σ : Perm (Fin m)) (τ : Perm (Fin n))
    (j : Fin n) :
    finSumPerm σ τ (Fin.natAdd m j) = Fin.natAdd m (τ j) := by
  rw [← finSumFinEquiv_apply_right, finSumPerm_apply, Equiv.symm_apply_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]

@[simp]
theorem _root_.Equiv.Perm.finSumPerm_one :
    finSumPerm (1 : Perm (Fin m)) (1 : Perm (Fin n)) = 1 :=
  map_one (finSumPermHom m n)

@[simp]
theorem _root_.Equiv.Perm.finSumPerm_inv (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    (finSumPerm σ τ)⁻¹ = finSumPerm σ⁻¹ τ⁻¹ :=
  (map_inv (finSumPermHom m n) (σ, τ)).symm

@[simp]
theorem _root_.Equiv.Perm.finSumPerm_mul (σ σ' : Perm (Fin m)) (τ τ' : Perm (Fin n)) :
    finSumPerm σ τ * finSumPerm σ' τ' = finSumPerm (σ * σ') (τ * τ') :=
  (map_mul (finSumPermHom m n) (σ, τ) (σ', τ')).symm

/-- The full cycle partition of `Equiv.Perm.finSumPerm σ τ` is the concatenation of those of `σ`
and of `τ`. -/
@[simp]
theorem _root_.Equiv.Perm.parts_partition_finSumPerm (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    (finSumPerm σ τ).partition.parts = σ.partition.parts + τ.partition.parts := by
  rw [finSumPerm, parts_partition_permCongr, parts_partition_sumCongr]

/-- The number of orbits of `Equiv.Perm.finSumPerm σ τ`, fixed points included, is the sum of the
numbers of orbits of `σ` and of `τ`. -/
@[simp]
theorem _root_.Equiv.Perm.orbitCount_finSumPerm (σ : Perm (Fin m)) (τ : Perm (Fin n)) :
    orbitCount (finSumPerm σ τ) = orbitCount σ + orbitCount τ := by
  rw [finSumPerm, orbitCount_permCongr, orbitCount_sumCongr]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Permutations of the complement of a point

`Equiv.permStabilizerEquiv` identifies permutations of a labelled complement with the point
stabilizer. For `i : Fin (n + 1)`, `Fin.permStabilizerEquiv i` uses the increasing labelling
`i.succAbove` to identify the stabilizer with permutations of `Fin n`.
This gives an explicit coordinate convention for restricting representations of a symmetric
group to a point stabilizer. The construction uses Mathlib's `Equiv.Perm.subtypeEquivSubtypePerm`
to extend permutations of the complement.
-/

public section

namespace Equiv

/-- Permutations of a labelled complement of `a` form its point stabilizer. -/
def permStabilizerEquiv {α β : Type*} [DecidableEq α] {a : α}
    (e : β ≃ {x : α // x ≠ a}) : Perm β ≃* MulAction.stabilizer (Perm α) a where
  toEquiv := (e.permCongr.trans (Perm.subtypeEquivSubtypePerm (· ≠ a))).trans
    (Equiv.subtypeEquivRight fun σ => by
      simp [MulAction.mem_stabilizer_iff, Perm.smul_def])
  map_mul' σ τ := Subtype.ext (by
    -- The equivalence combinators forget the multiplicative structure; recover the two
    -- bundled homomorphisms on the underlying permutations to use `map_mul`.
    change Perm.ofSubtype (e.permCongrHom (σ * τ)) =
      Perm.ofSubtype (e.permCongrHom σ) * Perm.ofSubtype (e.permCongrHom τ)
    simp only [map_mul])

/-- The underlying permutation is extension by the identity at the omitted point. -/
theorem coe_permStabilizerEquiv {α β : Type*} [DecidableEq α] {a : α}
    (e : β ≃ {x : α // x ≠ a}) (σ : Perm β) :
    (e.permStabilizerEquiv σ : Perm α) = σ.extendDomain e := by
  -- Project the composite equivalence to its permutation in order to compare the two extensions.
  change Perm.ofSubtype (e.permCongr σ) = σ.extendDomain e
  simp [Perm.ofSubtype, Perm.extendDomain, ← Perm.one_def]

/-- The extended permutation fixes the omitted point. -/
@[simp]
theorem permStabilizerEquiv_apply_self {α β : Type*} [DecidableEq α] {a : α}
    (e : β ≃ {x : α // x ≠ a}) (σ : Perm β) :
    (e.permStabilizerEquiv σ : Perm α) a = a := by
  rw [coe_permStabilizerEquiv, Perm.extendDomain_apply_not_subtype σ e (by simp)]

/-- On the complement, the stabilizer equivalence acts by the given labelling. -/
@[simp]
theorem permStabilizerEquiv_apply_image {α β : Type*} [DecidableEq α] {a : α}
    (e : β ≃ {x : α // x ≠ a}) (σ : Perm β) (b : β) :
    (e.permStabilizerEquiv σ : Perm α) (e b) = e (σ b) := by
  rw [coe_permStabilizerEquiv, Perm.extendDomain_apply_image]

end Equiv

namespace Fin

/-- Permutations of the complement of `i`, labelled by `i.succAbove`, form its stabilizer. -/
def permStabilizerEquiv {n : ℕ} (i : Fin (n + 1)) :
    Equiv.Perm (Fin n) ≃* MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) i :=
  (finSuccAboveEquiv i).permStabilizerEquiv

/-- The underlying permutation extends the permutation of the complement by fixing `i`. -/
theorem coe_permStabilizerEquiv {n : ℕ} (i : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    (i.permStabilizerEquiv σ : Equiv.Perm (Fin (n + 1))) = σ.extendDomain (finSuccAboveEquiv i) :=
  (finSuccAboveEquiv i).coe_permStabilizerEquiv σ

/-- The stabilizer equivalence fixes `i`. -/
@[simp]
theorem permStabilizerEquiv_apply_self {n : ℕ} (i : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    (i.permStabilizerEquiv σ : Equiv.Perm (Fin (n + 1))) i = i :=
  (finSuccAboveEquiv i).permStabilizerEquiv_apply_self σ

/-- On the complement, the stabilizer equivalence uses the increasing labelling. -/
@[simp]
theorem permStabilizerEquiv_apply_succAbove {n : ℕ} (i : Fin (n + 1))
    (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    (i.permStabilizerEquiv σ : Equiv.Perm (Fin (n + 1))) (i.succAbove j) =
      i.succAbove (σ j) := by
  simpa only [permStabilizerEquiv, finSuccAboveEquiv_apply] using
    (finSuccAboveEquiv i).permStabilizerEquiv_apply_image σ j

/-- Recovering a permutation of the complement commutes with the increasing labelling. -/
@[simp]
theorem succAbove_permStabilizerEquiv_symm_apply {n : ℕ} (i : Fin (n + 1))
    (σ : MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) i) (j : Fin n) :
    i.succAbove (i.permStabilizerEquiv.symm σ j) = σ.val (i.succAbove j) := by
  rw [← permStabilizerEquiv_apply_succAbove, MulEquiv.apply_symm_apply]

/-- Extending a permutation of the complement adds one fixed point, namely `i`. -/
theorem card_fixedPoints_permStabilizerEquiv {n : ℕ} (i : Fin (n + 1)) (σ : Equiv.Perm (Fin n)) :
    Nat.card {j : Fin (n + 1) // (i.permStabilizerEquiv σ : Equiv.Perm (Fin (n + 1))) j = j} =
      Nat.card {j : Fin n // σ j = j} + 1 := by
  classical
  have hle := σ.sum_cycleType_le
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  -- The cycle-type count is stated for `Function.fixedPoints` rather than the explicit subtype.
  change Fintype.card (Function.fixedPoints (i.permStabilizerEquiv σ : Equiv.Perm (Fin (n + 1)))) =
    Fintype.card (Function.fixedPoints σ) + 1
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.card_fixedPoints, coe_permStabilizerEquiv,
    Equiv.Perm.cycleType_extendDomain]
  simp only [Fintype.card_fin] at hle ⊢
  omega

end Fin

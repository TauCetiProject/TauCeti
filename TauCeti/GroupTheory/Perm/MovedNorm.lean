/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.InformationTheory.Hamming
public import TauCeti.Analysis.Normed.Group.ConjInvariant

/-!
# The moved-point norm on finite permutation groups

`Equiv.Perm.movedNorm` packages the cardinality of a permutation's support as a `GroupNorm`.
It is invariant under conjugation, and its associated distance is the Hamming distance between
permutations. Counting rather than normalizing by the degree makes the norm meaningful even
on an empty type; normalization cancels in same-degree coboundary expansion ratios.

The construction uses Mathlib's support inequalities and conjugation formula. Nonidentity
permutations move at least two points, with equality precisely for transpositions. These facts
also supply the norm estimate for the parity retraction.
-/

public section

namespace Equiv.Perm

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- The group norm counting the points moved by a permutation. -/
def movedNorm : GroupNorm (Perm α) where
  toFun σ := σ.support.card
  map_one' := by simp
  mul_le' σ τ := by
    exact_mod_cast (Finset.card_le_card (support_mul_le σ τ)).trans
      (Finset.card_union_le σ.support τ.support)
  inv' σ := by simp
  eq_one_of_map_eq_zero' σ h := by
    exact card_support_eq_zero.mp (by exact_mod_cast h)

variable {α}

/-- Evaluating the moved-point norm gives the support cardinality, as a real number. -/
@[simp]
theorem movedNorm_apply (σ : Perm α) : movedNorm α σ = (σ.support.card : ℝ) :=
  (rfl)

/-- The moved-point norm is invariant under conjugation. -/
theorem movedNorm_conj (σ τ : Perm α) :
    movedNorm α (σ * τ * σ⁻¹) = movedNorm α τ := by
  simp

/-- The moved-point norm is a conjugation-invariant group norm. -/
theorem isConjInvariant_movedNorm : (movedNorm α).toGroupSeminorm.IsConjInvariant :=
  (GroupSeminorm.isConjInvariant_iff _).2 fun τ σ ↦ movedNorm_conj σ τ

/-- The Hamming distance of two permutations is the moved-point norm of their quotient. -/
theorem hammingDist_eq_movedNorm (σ τ : Perm α) :
    (hammingDist (⇑σ) (⇑τ) : ℝ) = movedNorm α (σ⁻¹ * τ) := by
  simp only [hammingDist, movedNorm_apply, support, mul_apply, ne_eq, inv_eq_iff_eq]
  simp only [ne_comm]

/-- A nonidentity permutation has moved-point norm at least two. -/
theorem two_le_movedNorm_of_ne_one {σ : Perm α} (hσ : σ ≠ 1) :
    2 ≤ movedNorm α σ := by
  rw [movedNorm_apply]
  exact_mod_cast two_le_card_support_of_ne_one hσ

/-- A permutation has moved-point norm two exactly when it is a transposition. -/
theorem movedNorm_eq_two_iff {σ : Perm α} : movedNorm α σ = 2 ↔ σ.IsSwap := by
  rw [movedNorm_apply]
  exact_mod_cast (card_support_eq_two (f := σ))

/-- Transpositions move exactly two points. -/
theorem IsSwap.movedNorm {σ : Perm α} (hσ : σ.IsSwap) : movedNorm α σ = 2 :=
  movedNorm_eq_two_iff.mpr hσ

/-- An odd permutation has moved-point norm at least two. -/
theorem two_le_movedNorm_of_sign_eq_neg_one {σ : Perm α} (hσ : sign σ = -1) :
    2 ≤ movedNorm α σ := by
  apply two_le_movedNorm_of_ne_one
  rintro rfl
  exact (by decide : (1 : ℤˣ) ≠ -1) (by simpa using hσ)

end Equiv.Perm

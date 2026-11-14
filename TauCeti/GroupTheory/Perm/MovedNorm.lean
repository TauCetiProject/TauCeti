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
permutations move at least two points, with equality precisely for transpositions, while
nonidentity even permutations move at least three points. Consequently, distinct permutations of
the same sign lie at Hamming distance at least three, and on a domain of at most three points they
disagree everywhere.
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

/-- A nonidentity even permutation moves at least three points. -/
theorem three_le_card_support_of_sign_eq_one {σ : Perm α} (hsign : sign σ = 1) (hσ : σ ≠ 1) :
    3 ≤ σ.support.card := by
  have h2 : 2 ≤ σ.support.card := two_le_card_support_of_ne_one hσ
  have hne2 : σ.support.card ≠ 2 := by
    intro h
    have hswap : σ.IsSwap := card_support_eq_two.mp h
    exact (by decide : (1 : ℤˣ) ≠ -1) (hsign.symm.trans hswap.sign_eq)
  omega

/-- A nonidentity even permutation has moved-point norm at least three. -/
theorem three_le_movedNorm_of_sign_eq_one {σ : Perm α} (hsign : sign σ = 1) (hσ : σ ≠ 1) :
    3 ≤ movedNorm α σ := by
  rw [movedNorm_apply]
  exact_mod_cast three_le_card_support_of_sign_eq_one hsign hσ

/-- Distinct permutations of the same sign are at Hamming distance at least three. -/
theorem three_le_hammingDist_of_sign_eq {σ τ : Perm α} (hsign : sign σ = sign τ) (hne : σ ≠ τ) :
    3 ≤ hammingDist (⇑σ) (⇑τ) := by
  have hsign' : sign (σ⁻¹ * τ) = 1 := by simp [hsign]
  have hne' : σ⁻¹ * τ ≠ 1 := inv_mul_eq_one.not.mpr hne
  have h3 : (3 : ℝ) ≤ movedNorm α (σ⁻¹ * τ) := three_le_movedNorm_of_sign_eq_one hsign' hne'
  rw [← hammingDist_eq_movedNorm] at h3
  exact_mod_cast h3

/-- On a type of at most three elements, distinct permutations of the same sign disagree
everywhere. -/
theorem apply_ne_apply_of_sign_eq_of_card_le_three (hcard : Fintype.card α ≤ 3) {σ τ : Perm α}
    (hsign : sign σ = sign τ) (hne : σ ≠ τ) (x : α) : σ x ≠ τ x := by
  intro hx
  have hle : hammingDist (⇑σ) (⇑τ) ≤ (Finset.univ.erase x).card := by
    rw [hammingDist]
    refine Finset.card_le_card fun y hy ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact Finset.mem_erase.mpr ⟨fun hyx ↦ hy (hyx ▸ hx), Finset.mem_univ y⟩
  rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ] at hle
  have h3 := three_le_hammingDist_of_sign_eq hsign hne
  omega

/-- On a type of at most three elements, distinct transpositions disagree everywhere. -/
theorem IsSwap.apply_ne_apply_of_ne {σ τ : Perm α} (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (hcard : Fintype.card α ≤ 3) (hne : σ ≠ τ) (x : α) : σ x ≠ τ x :=
  apply_ne_apply_of_sign_eq_of_card_le_three hcard (hσ.sign_eq.trans hτ.sign_eq.symm) hne x

end Equiv.Perm

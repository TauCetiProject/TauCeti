/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.AlternatingForm

/-!
# The integral matrices of the numbered root generators

Each numbered root generator of the full-weight type-`C` carrier squares to zero in the standard
representation, so its divided-power exponential is `1 + u X` for `X` the integral matrix
`TauCeti.SpStd.rootIntMatrix` of the generator. This file writes that matrix out in the enumerated
coordinate basis and reads the root-subgroup points off it.

In the enumerated basis the matrix is the single unit `E_{i,m+i}` at the final node and the
difference `E_{i,i+1} - E_{m+i+1,m+i}` of two units at a nonfinal one. Those are the matrices of
the symplectic group's long-root transvection at the terminal coordinate and of its difference
short-root element at an adjacent pair, which is what
`TauCeti/Algebra/Lie/Symplectic/StandardCarrier/Generation.lean` uses to identify the two point
groups.

## Main results

* `TauCeti.SpStd.rootIntMatrix_inl_last` and its three siblings: the integral matrix of each
  numbered root generator, written out.
* `TauCeti.SpStd.coe_rootSubgroupPoints_eq_one_add_smul`: a root-subgroup point is `1 + u X`.
-/

public section

open Matrix

namespace TauCeti.SpStd

universe v

variable (n : ℕ)

/-- The integral matrix of the final raising generator is a single matrix unit. -/
@[simp]
theorem rootIntMatrix_inl_last :
    rootIntMatrix n (.inl (Fin.last n)) =
      Matrix.single (finSumFinEquiv (Sum.inl (Fin.last n)))
        (finSumFinEquiv (Sum.inr (Fin.last n))) 1 := by
  ext r s
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective r
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective s
  apply Int.cast_injective (α := ℚ)
  rw [intCast_rootIntMatrix, val_rootGenerator_inl, positiveRootMatrix_last]
  cases a <;> cases b <;>
    simp [Matrix.single_apply, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

/-- The integral matrix of the final lowering generator is a single matrix unit. -/
@[simp]
theorem rootIntMatrix_inr_last :
    rootIntMatrix n (.inr (Fin.last n)) =
      Matrix.single (finSumFinEquiv (Sum.inr (Fin.last n)))
        (finSumFinEquiv (Sum.inl (Fin.last n))) 1 := by
  ext r s
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective r
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective s
  apply Int.cast_injective (α := ℚ)
  rw [intCast_rootIntMatrix, val_rootGenerator_inr, negativeRootMatrix_last]
  cases a <;> cases b <;>
    simp [Matrix.single_apply, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

/-- The integral matrix of a nonfinal raising generator is a difference of two matrix units. -/
@[simp]
theorem rootIntMatrix_inl_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    rootIntMatrix n (.inl i) =
      Matrix.single (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl (next n i hi))) 1 -
        Matrix.single (finSumFinEquiv (Sum.inr (next n i hi))) (finSumFinEquiv (Sum.inr i)) 1 := by
  ext r s
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective r
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective s
  apply Int.cast_injective (α := ℚ)
  rw [intCast_rootIntMatrix, val_rootGenerator_inl, positiveRootMatrix_of_ne_last n i hi]
  cases a <;> cases b <;>
    simp [Matrix.single_apply, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

/-- The integral matrix of a nonfinal lowering generator is a difference of two matrix units. -/
@[simp]
theorem rootIntMatrix_inr_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    rootIntMatrix n (.inr i) =
      Matrix.single (finSumFinEquiv (Sum.inl (next n i hi))) (finSumFinEquiv (Sum.inl i)) 1 -
        Matrix.single (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr (next n i hi))) 1 := by
  ext r s
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective r
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective s
  apply Int.cast_injective (α := ℚ)
  rw [intCast_rootIntMatrix, val_rootGenerator_inr, negativeRootMatrix_of_ne_last n i hi]
  cases a <;> cases b <;>
    simp [Matrix.single_apply, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

/-- The matrix of a carrier root subgroup point is `1 + u X` for the integral matrix `X` of the
corresponding root generator. -/
-- Not `@[simp]`: `coe_rootSubgroupPoints` is already a simp lemma and rewrites this
-- left-hand side first, so a simp normal form stated against `rootSubgroupPoints` is
-- unreachable. Consumers rewrite with it by name.
theorem coe_rootSubgroupPoints_eq_one_add_smul (k : Fin (n + 1) ⊕ Fin (n + 1))
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    ((rootSubgroupPoints n k A u :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) :
        Matrix (Fin ((n + 1) + (n + 1))) (Fin ((n + 1) + (n + 1))) A) =
      1 + Multiplicative.toAdd u • (rootIntMatrix n k).map (Int.cast : ℤ → A) := by
  rw [coe_rootSubgroupPoints]
  simpa only [MulEquiv.apply_symm_apply] using
    (TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_eq_one_add_smul
      (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) k
      (isNilpotent_rep_rootGenerator n k) (latticeBasis n) (rootIntMatrix n k)
      (nilpotencyClass_rep_rootGenerator n k).le
      (rep_rootGenerator_latticeBasis_eq_sum n k)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u))

end TauCeti.SpStd

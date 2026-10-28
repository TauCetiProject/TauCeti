/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.CoordinateRotation
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# The center of the special orthogonal matrix group

In dimension at least three, over a commutative ring where two is a non-zero-divisor, the matrices
commuting with the special orthogonal group are exactly the scalar matrices. Consequently its
center consists of the scalar matrices `c • 1` with `c² = 1` and `c^n = 1`. In odd dimension
the center is trivial. The ring may have nilpotents, so these statements also detect the
scheme-theoretic center when applied to algebra-valued points.

The argument uses the signed coordinate rotations and their half-turns from
`TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.CoordinateRotation`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.3 and Chapter 21.
-/

public section

namespace Matrix

open TauCeti.Matrix.SpecialOrthogonalGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

attribute [local instance] starRingOfComm

/-- A matrix commuting with every special orthogonal matrix in dimension at least three is
scalar, over any commutative ring where two is a non-zero-divisor. -/
theorem mem_range_scalar_of_commute_specialOrthogonalGroup (h2 : IsRegular (2 : R))
    (M : Matrix n n R) (hn : 3 ≤ Fintype.card n)
    (hM : ∀ g : specialOrthogonalGroup n R, Commute (g : Matrix n n R) M) :
    M ∈ Set.range (scalar n) := by
  classical
  have hoff (i j : n) (hij : i ≠ j) : M i j = 0 := by
    have hcard : ({i, j} : Finset n).card < (Finset.univ : Finset n).card := by
      simp only [Finset.card_pair hij, Finset.card_univ]
      omega
    obtain ⟨l, _, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hli : l ≠ i := by simp_all
    have hlj : l ≠ j := by simp_all
    let g := coordinateHalfTurn (R := R) i l hli.symm
    have hfix : (g : Matrix n n R) *ᵥ Pi.single j 1 = Pi.single j 1 := by
      ext a
      simp only [g, coordinateHalfTurn_mulVec, Pi.single_apply]
      by_cases haj : a = j
      · subst a
        simp [Ne.symm hij, Ne.symm hlj]
      · simp [haj]
    have h := congrArg (fun N : Matrix n n R ↦ (N *ᵥ Pi.single j 1) i) (hM g).eq
    rw [← mulVec_mulVec, ← mulVec_mulVec, hfix] at h
    simp only [g, coordinateHalfTurn_mulVec, mulVec_single_one, col_apply,
      true_or, ↓reduceIte] at h
    have hzero : (2 : R) * M i j = 0 := by linear_combination -h
    exact h2.left (hzero.trans (mul_zero _).symm)
  have hdiag (i j : n) : M i i = M j j := by
    by_cases hij : i = j
    · rw [hij]
    · let g := coordinateRotation (R := R) i j hij
      have h := congrArg (fun N : Matrix n n R ↦ (N *ᵥ Pi.single i 1) j) (hM g).eq
      rw [← mulVec_mulVec, ← mulVec_mulVec] at h
      simp only [mulVec_single_one, g, coordinateRotation_col_left] at h
      simp only [coordinateRotation_mulVec, col_apply, Ne.symm hij, ↓reduceIte] at h
      exact h
  obtain ⟨i⟩ : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  refine ⟨M i i, ?_⟩
  ext a b
  by_cases hab : a = b
  · subst b
    simpa [scalar_apply] using hdiag i a
  · simp [scalar_apply, hab, hoff a b hab]

namespace SpecialOrthogonalGroup

/-- A special orthogonal matrix that is scalar belongs to the center. -/
theorem mem_center_of_coe_eq_scalar (g : specialOrthogonalGroup n R) (c : R)
    (hc : (g : Matrix n n R) = scalar n c) :
    g ∈ Subgroup.center (specialOrthogonalGroup n R) := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  simpa only [Submonoid.coe_mul, hc] using
    (scalar_commute c (Commute.all c) (h : Matrix n n R)).symm.eq

/-- In dimension at least three, the center consists precisely of the scalar orthogonal
matrices of determinant one. This includes coefficients with nilpotents. -/
@[simp] theorem mem_center_iff (h2 : IsRegular (2 : R)) (g : specialOrthogonalGroup n R)
    (hn : 3 ≤ Fintype.card n) :
    g ∈ Subgroup.center (specialOrthogonalGroup n R) ↔
      ∃ c : R, (g : Matrix n n R) = scalar n c ∧ c ^ 2 = 1 ∧ c ^ Fintype.card n = 1 := by
  constructor
  · intro hg
    obtain ⟨c, hc⟩ := mem_range_scalar_of_commute_specialOrthogonalGroup h2 (g : Matrix n n R) hn
      (fun h ↦ congrArg Subtype.val ((Subgroup.mem_center_iff.mp hg) h))
    refine ⟨c, hc.symm, ?_, ?_⟩
    · let _ : Nonempty n := Fintype.card_pos_iff.mp (by omega)
      exact TauCeti.sq_eq_one_of_smul_one_mem_orthogonalGroup (n := n) (by
        simpa only [← hc, scalar_apply, Matrix.smul_one_eq_diagonal] using
          (mem_specialOrthogonalGroup_iff.mp g.2).1)
    · have hdet := (mem_specialOrthogonalGroup_iff.mp g.2).2
      simpa [← hc, scalar_apply, det_diagonal] using hdet
  · rintro ⟨c, hc, _, _⟩
    exact mem_center_of_coe_eq_scalar g c hc

/-- Odd-dimensional special orthogonal groups have trivial center when their dimension is at
least three and two is a non-zero-divisor in the coefficient ring. -/
theorem eq_one_of_mem_center_of_odd (h2 : IsRegular (2 : R))
    (g : specialOrthogonalGroup n R) (hn : 3 ≤ Fintype.card n)
    (hodd : Odd (Fintype.card n)) (hg : g ∈ Subgroup.center (specialOrthogonalGroup n R)) :
    g = 1 := by
  obtain ⟨c, hc, hc2, hcn⟩ := (mem_center_iff h2 g hn).mp hg
  obtain ⟨m, hm⟩ := hodd
  have hc1 : c = 1 := by
    simpa [hm, pow_add, pow_mul, hc2] using hcn
  apply Subtype.ext
  simp [hc, hc1, scalar_apply]

end SpecialOrthogonalGroup
end Matrix

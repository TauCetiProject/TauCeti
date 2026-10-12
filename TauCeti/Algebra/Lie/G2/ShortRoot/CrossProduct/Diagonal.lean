/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Generators

/-!
# Diagonal automorphisms of the type-G₂ cross product

When multiplication by two is injective, an invertible diagonal matrix preserves the
seven-dimensional cross product exactly when its diagonal entries are the characters
of the short-root weight diagram. Thus tensor invariance identifies diagonal elements
with the rank-two weight torus, rather than the full diagonal torus of `GL₇`.
This is the diagonal part of the centralizer calculation for the short-root carrier.

The cross-product normalization is that of
`TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Basic`; the weight coordinates follow
Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
-/

public section

open Matrix

namespace TauCeti.G2ShortRoot

variable {R : Type*} [CommRing R]

private theorem diagonal_cross_entry {d : Fin 7 → Rˣ}
    (h : PreservesG2Cross (diagonal fun i => (d i : R))) (k i j : Fin 7) :
    (d i : R) * (crossOperator k i j : ℤ) =
      (d k : R) * (crossOperator k i j : ℤ) * (d j : R) := by
  have he := congrFun (congrFun ((preservesG2Cross_def _).mp h k) i) j
  simpa [diagonal_mul, mul_diagonal, Matrix.sum_apply, diagonal_apply,
    Matrix.smul_apply, smul_eq_mul] using he

/-- An invertible diagonal matrix preserves the type-`G₂` cross product exactly when
its entries come from the rank-two weight torus, provided two is regular. -/
theorem preservesG2Cross_diagonal_iff (h2 : IsRegular (2 : R)) (d : Fin 7 → Rˣ) :
    PreservesG2Cross (diagonal fun i => (d i : R)) ↔
      ∃ s : Fin 2 → Rˣ, ∀ i, d i = torusCharacter s (weight i) := by
  constructor
  · intro h
    have h3 : d 3 = 1 := by
      apply Units.ext
      have he := diagonal_cross_entry h 3 0 0
      norm_num [crossOperator_def] at he
      have he' : (2 : R) = (d 3 : R) * 2 :=
        (d 0).mul_left_inj.mp (by simpa [mul_comm, mul_left_comm, mul_assoc] using he)
      exact h2.right (by simpa using he'.symm)
    have h24 : d 2 * d 4 = 1 := by
      apply Units.ext
      have he := diagonal_cross_entry h 2 3 4
      simpa [crossOperator_def, h3] using he.symm
    have h15 : d 1 * d 5 = 1 := by
      apply Units.ext
      have he := diagonal_cross_entry h 1 3 5
      simpa [crossOperator_def, h3] using he.symm
    have h06 : d 0 * d 6 = 1 := by
      apply Units.ext
      have he := diagonal_cross_entry h 0 3 6
      simpa [crossOperator_def, h3] using he.symm
    have h012 : d 0 = d 1 * d 2 := by
      apply Units.ext
      have he := diagonal_cross_entry h 1 0 2
      norm_num [crossOperator_def] at he
      exact h2.right (by simpa [mul_comm, mul_left_comm, mul_assoc] using he)
    have h4 := eq_inv_of_mul_eq_one_right h24
    have h5 := eq_inv_of_mul_eq_one_right h15
    have h6 := eq_inv_of_mul_eq_one_right h06
    refine ⟨![d 0, d 0 * d 1], fun i => ?_⟩
    fin_cases i <;> simp [torusCharacter_def, Fin.prod_univ_two, weight_apply, h3, h4, h5, h6]
    all_goals simp [h012, pow_two, mul_comm, mul_left_comm, mul_assoc]
  · rintro ⟨s, hs⟩
    simp_rw [hs]
    exact preservesG2Cross_diagonal_torusCharacter s

end TauCeti.G2ShortRoot

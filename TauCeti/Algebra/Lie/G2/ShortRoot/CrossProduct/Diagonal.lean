/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Generators

/-!
# Diagonal automorphisms and derivations of the type-G₂ cross product

When multiplication by two is injective, an invertible diagonal matrix preserves the
seven-dimensional cross product exactly when its diagonal entries are the characters
of the short-root weight diagram. Thus tensor invariance identifies diagonal elements
with the rank-two weight torus, rather than the full diagonal torus of `GL₇`.
This is the diagonal part of the centralizer calculation for the short-root carrier.
The infinitesimal counterpart, `diagonal_derivation_iff`, identifies the diagonal derivations
with the linear span of the two weight coordinates, for the corresponding zero-weight tangent
space calculation.

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

/-- A diagonal endomorphism is a derivation of the type-`G₂` cross product exactly when
its diagonal is an infinitesimal weight-torus character, provided two is regular.
The condition is written entrywise, so it applies over arbitrary commutative rings. -/
theorem diagonal_derivation_iff (h2 : IsRegular (2 : R)) (d : Fin 7 → R) :
    (∀ k i j, d i * (crossOperator k i j : R) =
      d k * (crossOperator k i j : R) + (crossOperator k i j : R) * d j) ↔
      ∃ c : Fin 2 → R, ∀ a, d a = ∑ i, (weight a i : R) * c i := by
  constructor
  · intro h
    have h3 : d 3 = 0 := by
      have he := h 3 0 0
      norm_num [crossOperator_def] at he
      apply h2.right
      linear_combination -he
    have h24 : d 4 = -d 2 := by
      have he := h 2 3 4
      simpa [crossOperator_def, h3, eq_neg_iff_add_eq_zero, add_comm] using he.symm
    have h15 : d 5 = -d 1 := by
      have he := h 1 3 5
      simp [crossOperator_def, h3] at he
      linear_combination he
    have h06 : d 6 = -d 0 := by
      have he := h 0 3 6
      simp [crossOperator_def, h3] at he
      linear_combination he
    have h012 : d 2 = d 0 - d 1 := by
      have he := h 1 0 2
      norm_num [crossOperator_def] at he
      have hc : (d 0 - d 1 - d 2) * 2 = 0 * (2 : R) := by
        linear_combination he
      have hz := h2.right hc
      linear_combination -hz
    refine ⟨![d 0, d 0 + d 1], fun a ↦ ?_⟩
    fin_cases a <;> simp [Fin.sum_univ_two, weight_apply, h3, h24, h15, h06, h012] <;> ring
  · rintro ⟨c, hc⟩ k i j
    by_cases h : crossOperator k i j = 0
    · simp [h]
    · simp_rw [hc, weight_eq_add_of_crossOperator_ne_zero k i j h,
        Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
      ring

end TauCeti.G2ShortRoot

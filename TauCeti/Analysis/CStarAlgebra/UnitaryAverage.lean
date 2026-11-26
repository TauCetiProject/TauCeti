/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Topology.Algebra.Star.Unitary
public import TauCeti.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Unitary conjugation averages in C⋆-algebras

For a finite family of unitaries `u : Fin N → unitary A` in a unital complex ⋆-algebra `A`,
`TauCeti.unitaryConjAverage u : A →ₗ[ℂ] A` is the averaging operator
`z ↦ (N : ℂ)⁻¹ • ∑ j : Fin N, (u j : A) * z * star (u j : A)`.

When `0 < N`, `unitaryConjAverage u` is unital (`TauCeti.unitaryConjAverage_one`), contractive in
any unital C⋆-ring (`TauCeti.norm_unitaryConjAverage_apply_le`), preserves tracial functionals
(`TauCeti.map_unitaryConjAverage_eq`), and is positive (`TauCeti.unitaryConjAverage_nonneg`), hence
bundles as a positive linear map `TauCeti.unitaryConjAveragePositive`.
-/

public section

namespace TauCeti

noncomputable section

section Ring

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-- Averaging operator `z ↦ (N : ℂ)⁻¹ • ∑ j, u j * z * star (u j)` for a finite family of
unitaries. -/
def unitaryConjAverage {N : ℕ} (u : Fin N → unitary A) : A →ₗ[ℂ] A where
  toFun z := (N : ℂ)⁻¹ • ∑ j : Fin N, (u j : A) * z * star (u j : A)
  map_add' x y := by
    simp only [mul_add, add_mul, Finset.sum_add_distrib, smul_add]
  map_smul' c x := by
    simp only [mul_smul_comm, smul_mul_assoc, ← Finset.smul_sum, RingHom.id_apply]
    rw [smul_comm]

/-- Unfolding lemma for `unitaryConjAverage`. -/
theorem unitaryConjAverage_apply {N : ℕ} (u : Fin N → unitary A) (z : A) :
    unitaryConjAverage u z = (N : ℂ)⁻¹ • ∑ j : Fin N, (u j : A) * z * star (u j : A) :=
  (rfl)

/-- Unitary conjugation averaging is unital for `0 < N`. -/
@[simp]
theorem unitaryConjAverage_one {N : ℕ} (hN : 0 < N) (u : Fin N → unitary A) :
    unitaryConjAverage u 1 = 1 := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hterm (j : Fin N) : (u j : A) * 1 * star (u j : A) = 1 := by
    rw [mul_one, Unitary.mul_star_self_of_mem (u j).property]
  simp only [unitaryConjAverage_apply, hterm, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]

/-- Every tracial linear functional is invariant under unitary conjugation averaging for
`0 < N`. -/
theorem map_unitaryConjAverage_eq {N : ℕ} (hN : 0 < N) (u : Fin N → unitary A)
    {M : Type*} [AddCommMonoid M] [Module ℂ M] (φ : A →ₗ[ℂ] M)
    (htrace : ∀ a b, φ (a * b) = φ (b * a)) (z : A) :
    φ (unitaryConjAverage u z) = φ z := by
  have hconj (j : Fin N) : φ ((u j : A) * z * star (u j : A)) = φ z := by
    rw [htrace, ← mul_assoc, Unitary.star_mul_self_of_mem (u j).property, one_mul]
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  simp only [unitaryConjAverage_apply, map_smul, map_sum, hconj, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hN0, one_smul]

end Ring

section Normed

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [NormedAlgebra ℂ A]

/-- Unitary conjugation averaging is contractive in a unital C⋆-ring. -/
theorem norm_unitaryConjAverage_apply_le {N : ℕ} (hN : 0 < N) (u : Fin N → unitary A) (z : A) :
    ‖unitaryConjAverage u z‖ ≤ ‖z‖ := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  rw [unitaryConjAverage_apply, norm_smul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ j : Fin N, (u j : A) * z * star (u j : A)‖
      ≤ (N : ℝ)⁻¹ * ∑ j : Fin N, ‖(u j : A) * z * star (u j : A)‖ := by
        gcongr
        exact norm_sum_le _ _
    _ = (N : ℝ)⁻¹ * (N • ‖z‖) := by
        simp [CStarRing.norm_unitary_conj]
    _ = ‖z‖ := by
        rw [nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN0.ne', one_mul]

end Normed

section Order

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Unitary conjugation averaging preserves positivity in a unital C⋆-algebra. -/
theorem unitaryConjAverage_nonneg {N : ℕ} (u : Fin N → unitary A) {z : A} (hz : 0 ≤ z) :
    0 ≤ unitaryConjAverage u z := by
  rw [unitaryConjAverage_apply]
  have hconj (j : Fin N) : 0 ≤ (u j : A) * z * star (u j : A) := by
    simpa [mul_assoc] using star_left_conjugate_nonneg hz (star (u j : A))
  have hsum : 0 ≤ ∑ j : Fin N, (u j : A) * z * star (u j : A) :=
    Finset.sum_nonneg fun j _ ↦ hconj j
  have hsmul : (N : ℂ)⁻¹ • ∑ j : Fin N, (u j : A) * z * star (u j : A) =
      (N : ℝ)⁻¹ • ∑ j : Fin N, (u j : A) * z * star (u j : A) := by
    rw [← algebraMap_smul ℂ (N : ℝ)⁻¹]
    simp
  rw [hsmul]
  exact smul_nonneg (by positivity) hsum

/-- Unitary conjugation averaging as a positive linear map `A →ₚ[ℂ] A`. -/
def unitaryConjAveragePositive {N : ℕ} (u : Fin N → unitary A) : A →ₚ[ℂ] A where
  toLinearMap := unitaryConjAverage u
  monotone' a b h := by
    rw [← sub_nonneg]
    change 0 ≤ unitaryConjAverage u b - unitaryConjAverage u a
    rw [← map_sub]
    exact unitaryConjAverage_nonneg u (sub_nonneg.2 h)

/-- Evaluating `unitaryConjAveragePositive u` yields `unitaryConjAverage u`. -/
@[simp]
theorem unitaryConjAveragePositive_apply {N : ℕ} (u : Fin N → unitary A) (z : A) :
    unitaryConjAveragePositive u z = unitaryConjAverage u z :=
  (rfl)

end Order

end

end TauCeti

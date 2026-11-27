/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical.Archimedean
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds

/-!
# Bounds for completed Dirichlet L-functions on right-hand strips

The gamma factor absorbs the linear growth of a nonprincipal Dirichlet L-function on a
closed vertical strip in the open right half-plane. On compact subsets of that half-plane,
the gamma factor is also bounded away from zero, uniformly in the character.
-/

public section

open Complex Set

namespace TauCeti.DirichletCharacter

/-- The gamma factor of a Dirichlet character absorbs linear growth on a closed strip to the
right of zero, with a constant independent of the modulus and parity. -/
theorem exists_norm_gammaFactor_mul_one_add_norm_le {a b : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ}, z.re ∈ Icc a b →
      ‖χ.gammaFactor z‖ * (1 + ‖z‖) ≤ C := by
  obtain ⟨C, hC, hΓ⟩ :=
    TauCeti.Complex.exists_norm_Gammaℝ_mul_one_add_norm_le_of_re_mem_Icc (b := b + 1) ha
  refine ⟨2 * C, by positivity, fun {_} χ {z} hz ↦ ?_⟩
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    exact (hΓ z ⟨hz.1, by linarith [hz.2]⟩).trans (by linarith)
  · rw [ho.gammaFactor_def]
    have hshift : (z + 1).re ∈ Icc a (b + 1) := by
      simp only [add_re, one_re, mem_Icc]
      exact ⟨by linarith [hz.1], add_le_add_left hz.2 1⟩
    have hnorm := norm_sub_le (z + 1) (1 : ℂ)
    rw [add_sub_cancel_right, norm_one] at hnorm
    calc
      _ ≤ ‖Gammaℝ (z + 1)‖ * (2 * (1 + ‖z + 1‖)) := by
        gcongr
        linarith [norm_nonneg (z + 1)]
      _ = 2 * (‖Gammaℝ (z + 1)‖ * (1 + ‖z + 1‖)) := by ring
      _ ≤ _ := by gcongr; exact hΓ _ hshift

/-- The completed L-function of a nonprincipal character is bounded on every closed vertical
strip strictly to the right of zero. -/
theorem exists_norm_completedLFunction_le_of_re_mem_Icc {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {a b : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∀ z : ℂ, z.re ∈ Icc a b → ‖χ.completedLFunction z‖ ≤ C := by
  obtain ⟨C, hC, hΓ⟩ := exists_norm_gammaFactor_mul_one_add_norm_le (b := b) ha
  have hN : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨C * N / a, by positivity, fun z hz ↦ ?_⟩
  have hz0 := ha.trans_le hz.1
  rw [χ.completedLFunction_eq_gammaFactor_mul_LFunction hz0, norm_mul]
  calc
    _ ≤ ‖χ.gammaFactor z‖ * (N * ‖z‖ / z.re) :=
      mul_le_mul_of_nonneg_left (χ.norm_LFunction_le_level_mul_norm_div_re hχ hz0) (norm_nonneg _)
    _ = (‖χ.gammaFactor z‖ * ‖z‖) * N / z.re := by ring
    _ ≤ _ := by
      refine div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right ?_ hN.le) ha hz.1
      exact (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)).trans (hΓ χ hz)

/-- A compact subset of the open right half-plane has a positive lower bound for the
norm of the archimedean factor, uniform over all Dirichlet characters. -/
theorem exists_pos_le_norm_gammaFactor_on_isCompact {K : Set ℂ} (hK : IsCompact K)
    (hpos : ∀ z ∈ K, 0 < z.re) :
    ∃ c > 0, ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ}, z ∈ K → c ≤ ‖χ.gammaFactor z‖ := by
  -- The same compact set of arguments works for the even and odd gamma factors.
  let S := insert (1 : ℂ) (K ∪ (fun z : ℂ ↦ z + 1) '' K)
  have hS : IsCompact S := (hK.union (hK.image (by fun_prop))).insert _
  have hSpos : ∀ w ∈ S, 0 < w.re := by
    rintro w (rfl | hw | ⟨v, hv, rfl⟩)
    · norm_num
    · exact hpos w hw
    · simpa using add_pos (hpos v hv) zero_lt_one
  have hc : ContinuousOn (fun w ↦ ‖Gammaℝ w‖) S := fun w hw ↦
    (continuousAt_Gammaℝ (Gammaℝ_ne_zero_of_re_pos (hSpos w hw))).norm.continuousWithinAt
  obtain ⟨w, hw, hmin⟩ := hS.exists_isMinOn ⟨1, mem_insert _ _⟩ hc
  refine ⟨‖Gammaℝ w‖, norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (hSpos w hw)), ?_⟩
  intro N χ z hz
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    exact hmin (mem_insert_of_mem _ (Or.inl hz))
  · rw [ho.gammaFactor_def]
    exact hmin (mem_insert_of_mem _ (Or.inr (mem_image_of_mem _ hz)))

end TauCeti.DirichletCharacter

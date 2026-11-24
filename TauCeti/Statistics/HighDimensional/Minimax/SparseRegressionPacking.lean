/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Statistics.HighDimensional.Toolkit.SparsePacking
import Mathlib.Tactic.Positivity

/-!
# Sparse regression packings

Two-sided norm bounds on a linear design over sparse vectors transfer a sparse packing
to its image. The resulting family has controlled squared norms and a uniform squared
separation, as needed to apply Fano's method in a Gaussian location experiment.

This is the packing step in Giraud, *Introduction to High-Dimensional Statistics*,
2nd ed., §3.4.1, using the sparse hypercube packing of Lemma 3.7.
-/

public section

open Finset

namespace LinearMap

variable {ι E : Type*} [Fintype ι] [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- A design with lower norm bound on 2D-sparse vectors and upper norm bound on
D-sparse vectors sends a scaled binary packing to a family of distinct regression means. -/
theorem exists_sparse_image_packing (X : EuclideanSpace ℝ ι →ₗ[ℝ] E)
    {D : ℕ} (hD : D ≤ Fintype.card ι) {a lower upper : ℝ} (ha : a ≠ 0) (hlower : 0 < lower)
    (hmin : ∀ b, hammingNorm (WithLp.ofLp b) ≤ 2 * D → lower * ‖b‖ ≤ ‖X b‖)
    (hmax : ∀ b, hammingNorm (WithLp.ofLp b) = D → ‖X b‖ ≤ upper * ‖b‖) :
    ∃ P : Finset E, P.Nonempty ∧
      (∀ f ∈ P, (∃ b, hammingNorm (WithLp.ofLp b) = D ∧ X b = f) ∧
        ‖f‖ ^ 2 ≤ upper ^ 2 * a ^ 2 * D) ∧
      (P : Set E).Pairwise (fun f g ↦ lower ^ 2 * a ^ 2 * D < ‖f - g‖ ^ 2) ∧
      (D : ℝ) / 2 * Real.log (Fintype.card ι / (4 * D)) ≤ Real.log P.card := by
  classical
  obtain ⟨C, hne, hmem, hsep, hlog⟩ := TauCeti.exists_sparse_euclidean_packing hD ha
  have hsepX : (C : Set (EuclideanSpace ℝ ι)).Pairwise
      (fun b b' ↦ lower ^ 2 * a ^ 2 * D < ‖X b - X b'‖ ^ 2) := by
    intro b hb b' hb' hbb'
    have hwt : hammingNorm (WithLp.ofLp (b - b')) ≤ 2 * D := by
      rw [WithLp.ofLp_sub, two_mul]
      exact (TauCeti.hammingNorm_sub_le _ _).trans_eq (by rw [(hmem b hb).1, (hmem b' hb').1])
    have hle := hmin (b - b') hwt
    rw [map_sub] at hle
    calc
      _ = lower ^ 2 * (a ^ 2 * D) := by rw [mul_assoc]
      _ < lower ^ 2 * ‖b - b'‖ ^ 2 := mul_lt_mul_of_pos_left (hsep hb hb' hbb') (by positivity)
      _ = (lower * ‖b - b'‖) ^ 2 := (mul_pow _ _ _).symm
      _ ≤ _ := (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hle
  have hinj : Set.InjOn X C := by
    intro b hb b' hb' heq
    by_contra hne'
    simpa [heq, not_lt.mpr (by positivity : 0 ≤ lower ^ 2 * a ^ 2 * D)] using hsepX hb hb' hne'
  refine ⟨C.image X, hne.image _, ?_, ?_, by simpa only [card_image_of_injOn hinj] using hlog⟩
  · intro f hf
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hf
    obtain ⟨hwt, hnorm⟩ := hmem b hb
    have hle := hmax b hwt
    refine ⟨⟨b, hwt, rfl⟩, ?_⟩
    calc
      ‖X b‖ ^ 2 ≤ (upper * ‖b‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hle)).2 hle
      _ = _ := by rw [mul_pow, hnorm, ← mul_assoc]
  · intro f hf g hg hfg
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hf
    obtain ⟨b', hb', rfl⟩ := mem_image.mp hg
    exact hsepX hb hb' (ne_of_apply_ne X hfg)

end LinearMap

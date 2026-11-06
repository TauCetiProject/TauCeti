/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Smooth
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth cutoffs on parabolic cylinders

These cutoffs localize a closed time slab to a spatial ball of radius `ρ` and a
time interval of radius `ρ²`. They are one on the smaller cylinder of spatial radius
`ρ / 2` and temporal radius `ρ² / 4`. One order-two parabolic Hölder norm bound works
for every spatial and temporal center and every slab. Centering the time interval at
the initial endpoint preserves the initial trace on the smaller spatial ball.

The construction uses Mathlib's `ContDiffBump` on ordinary product space, with the
time coordinate rescaled by `ρ`.
-/

public section
noncomputable section

open Set Metric TauCeti ParabolicSpaceTime
open scoped NNReal ContDiff

namespace TauCeti.ParabolicC2HolderSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {α : ℝ≥0}

/-- Smooth cutoffs on parabolic cylinders, with a common norm bound independent of
both centers and of the closed time slab. The cutoff is the restriction of a smooth
function on ordinary space-time. -/
theorem exists_cutoff (hα : α ≤ 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : E) (s a b : ℝ) (hab : a < b),
      ∃ χ : ParabolicC2HolderSpace α E ℝ hab,
        ‖χ‖ ≤ C ∧
        (∀ p, χ p ∈ Icc 0 1) ∧
        (∀ p : slab (E := E) a b, dist (p : ParabolicSpaceTime E).space z ≤ ρ / 2 →
          |(p : ParabolicSpaceTime E).time - s| ≤ ρ ^ 2 / 4 → χ p = 1) ∧
        (∀ p : slab (E := E) a b, ρ ≤ dist (p : ParabolicSpaceTime E).space z ∨
          ρ ^ 2 ≤ |(p : ParabolicSpaceTime E).time - s| → χ p = 0) ∧
        ∃ ψ : E × ℝ → ℝ, ContDiff ℝ ∞ ψ ∧
          ∀ p, χ p = ψ ((p : ParabolicSpaceTime E).space,
            (p : ParabolicSpaceTime E).time) := by
  -- The product norm gives a spatial ball and an independently rescaled time interval.
  let β : ContDiffBump (0 : E × ℝ) := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  let e : E × ℝ ≃ₜ E × ℝ := (Homeomorph.refl E).prodCongr
    (Homeomorph.smulOfNeZero ρ⁻¹ (inv_ne_zero hρ.ne'))
  let f : E × ℝ → ℝ := fun p ↦ β (p.1, p.2 / ρ)
  have hf : ContDiff ℝ ∞ f := β.contDiff.comp (contDiff_fst.prodMk (contDiff_snd.div_const ρ))
  have hs : HasCompactSupport f := by
    simpa [f, e, Function.comp_def, div_eq_inv_mul, Prod.map_def] using
      β.hasCompactSupport.comp_homeomorph e
  obtain ⟨C, hC, hχ⟩ := exists_norm_le_comp_coords hα (hf.of_le (by simp)) hs
  refine ⟨C, hC, fun z s a b hab ↦ ?_⟩
  obtain ⟨χ, hχ, hnχ⟩ := hχ (z, s) a b hab
  refine ⟨χ, hnχ, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [hχ]
    exact ⟨β.nonneg, β.le_one⟩
  · intro p hx ht
    rw [hχ]
    apply β.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
    simp only [β]
    constructor
    · simpa [dist_eq_norm] using hx
    · simp only [Real.norm_eq_abs, abs_div, abs_of_pos hρ]
      exact (div_le_iff₀ hρ).2 (by nlinarith)
  · intro p hp
    rw [hχ]
    apply β.zero_of_le_dist
    rw [dist_zero_right, Prod.norm_def]
    simp only [β]
    rcases hp with hx | ht
    · have hx' : ρ ≤ ‖(p : ParabolicSpaceTime E).space - z‖ := by
        simpa [dist_eq_norm] using hx
      exact hx'.trans (le_max_left _ _)
    · apply le_trans _ (le_max_right _ _)
      simp only [Real.norm_eq_abs, abs_div, abs_of_pos hρ]
      exact (le_div_iff₀ hρ).2 (by nlinarith)
  · refine ⟨fun p ↦ f (p.1 - z, p.2 - s), ?_, fun p ↦ hχ p⟩
    exact hf.comp ((contDiff_fst.sub contDiff_const).prodMk
      (contDiff_snd.sub contDiff_const))

end TauCeti.ParabolicC2HolderSpace

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.GaussianTheta.Basic
import Mathlib.Topology.Order.Compact
import TauCeti.NumberTheory.LSeries.GaussianTheta.MellinFactor

/-!
# Positive lower bounds for the Gaussian Mellin factor on compact boxes

The Mellin transform `TauCeti.gaussianMellin j` of the even or odd Gaussian weight is holomorphic
and nonvanishing on the open half-plane `-(j : ℝ) < Re s`. By compactness, its absolute value is
bounded away from zero by a positive constant on any closed rectangle `a ≤ Re s ≤ b`, `|Im s| ≤ H`
inside that half-plane. In particular, this holds on the critical-strip box `1/2 ≤ Re s ≤ 1`,
`|Im s| ≤ H`, which converts a three-lines upper bound on `‖gaussianMellin j s‖²` at a zero of a
primitive Dirichlet L-function into a lower bound for the theta tail integral.

## Main results

* `TauCeti.exists_pos_le_norm_gaussianMellin_on_box`: positive lower bound for
  `‖gaussianMellin j s‖` on any closed rectangle `a ≤ Re s ≤ b`, `|Im s| ≤ H` with `-(j : ℝ) < a`.
* `TauCeti.exists_pos_le_norm_sq_gaussianMellin_on_box`: the corresponding positive lower bound for
  `‖gaussianMellin j s‖ ^ 2`.
* `TauCeti.exists_pos_le_norm_gaussianMellin_criticalStrip`: specialization to `1/2 ≤ Re s ≤ 1`,
  `|Im s| ≤ H`.

## Provenance

Adapted from `New.exists_pos_le_norm_gaussianMellin` in `grh/src/Lib/Analytic/DirichletTheta.lean`
of `grh-lean` (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC) at
commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Complex Set

namespace TauCeti

/-- On any closed rectangle `a ≤ Re s ≤ b`, `|Im s| ≤ H` inside the convergence half-plane
`-(j : ℝ) < Re s`, the norm of `gaussianMellin j` is bounded below by a positive constant. -/
theorem exists_pos_le_norm_gaussianMellin_on_box (j : Fin 2) {a b : ℝ} (ha : -(j.val : ℝ) < a)
    (H : ℝ) :
    ∃ c > 0, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → |s.im| ≤ H → c ≤ ‖gaussianMellin j s‖ := by
  by_cases hne : a ≤ b ∧ 0 ≤ H
  · let K : Set ℂ := equivRealProdCLM ⁻¹' (Icc a b ×ˢ Icc (-H) H)
    have hK_compact : IsCompact K :=
      equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.prod isCompact_Icc)
    have hK_nonempty : K.Nonempty := ⟨(a : ℂ), by
      simp [K, equivRealProdCLM_apply, hne.left, hne.right]⟩
    have hK_sub : K ⊆ {z : ℂ | -(j.val : ℝ) < z.re} := fun z hz ↦
      ha.trans_le (by simpa [K, equivRealProdCLM_apply] using hz.left.left)
    have hcont : ContinuousOn (fun z ↦ ‖gaussianMellin j z‖) K :=
      ((analyticOnNhd_gaussianMellin j).continuousOn.mono hK_sub).norm
    obtain ⟨s₀, hs₀K, hs₀min⟩ := hK_compact.exists_isMinOn hK_nonempty hcont
    refine ⟨‖gaussianMellin j s₀‖, norm_pos_iff.mpr (gaussianMellin_ne_zero (hK_sub hs₀K)),
      fun s hsa hsb hsH ↦ hs₀min ?_⟩
    simp only [K, mem_preimage, equivRealProdCLM_apply, mem_prod, mem_Icc]
    exact ⟨⟨hsa, hsb⟩, abs_le.mp hsH⟩
  · refine ⟨1, one_pos, fun s hsa hsb hsH ↦ ?_⟩
    exact absurd ⟨hsa.trans hsb, (abs_nonneg s.im).trans hsH⟩ hne

/-- On any closed rectangle `a ≤ Re s ≤ b`, `|Im s| ≤ H` with `-(j : ℝ) < a`, the squared norm
`‖gaussianMellin j s‖ ^ 2` is bounded below by a positive constant. -/
theorem exists_pos_le_norm_sq_gaussianMellin_on_box (j : Fin 2) {a b : ℝ} (ha : -(j.val : ℝ) < a)
    (H : ℝ) :
    ∃ c > 0, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → |s.im| ≤ H → c ≤ ‖gaussianMellin j s‖ ^ 2 := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_le_norm_gaussianMellin_on_box j ha H
  exact ⟨c ^ 2, sq_pos_of_pos hc, fun s hsa hsb hsH ↦
    pow_le_pow_left₀ hc.le (hbound s hsa hsb hsH) 2⟩

/-- On the critical-strip box `1/2 ≤ Re s ≤ 1`, `|Im s| ≤ H`, the Gaussian Mellin factor is
bounded away from zero by a positive constant depending only on `j` and `H`. -/
theorem exists_pos_le_norm_gaussianMellin_criticalStrip (j : Fin 2) (H : ℝ) :
    ∃ c > 0, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ H → c ≤ ‖gaussianMellin j s‖ :=
  exists_pos_le_norm_gaussianMellin_on_box j
    (by linarith [Nat.cast_nonneg (α := ℝ) j.val] : -(j.val : ℝ) < 1 / 2) H

end TauCeti

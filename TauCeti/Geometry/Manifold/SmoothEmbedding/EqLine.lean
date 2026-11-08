/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Immersed lines which are an affine line outside a compact set

An injective `C^n` immersion `f : ℝ → V`, `1 ≤ n`, into a finite-dimensional real normed space,
which agrees with an affine line `s ↦ p + s • e` outside a compact set, is a smooth embedding
(`TauCeti.isSmoothEmbedding_of_eq_line`): such a map is proper, so
`Manifold.IsImmersion.isSmoothEmbedding_of_isProperMap` applies.
-/

public section

namespace TauCeti

open Function Set _root_.Manifold
open scoped _root_.Manifold ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- An injective `C^n` immersion of the line, `1 ≤ n`, which is an affine line outside a compact
set, is a smooth embedding: it is proper, so
`Manifold.IsImmersion.isSmoothEmbedding_of_isProperMap` applies. -/
theorem isSmoothEmbedding_of_eq_line {n : ℕ∞ω} (hn : 1 ≤ n) {f : ℝ → V}
    (hf : ContDiff ℝ n f) (hinj : Injective f) {f' : ℝ → V} (hder : ∀ s, HasDerivAt f (f' s) s)
    (hf' : ∀ s, f' s ≠ 0) {p e : V} (he : e ≠ 0) {R : ℝ}
    (hline : ∀ s, R ≤ |s| → f s = p + s • e) :
    IsSmoothEmbedding 𝓘(ℝ) 𝓘(ℝ, V) n f := by
  refine (isImmersion_iff_forall_isImmersionAt.2 fun s => ?_).isSmoothEmbedding_of_isProperMap
    hinj ?_
  · refine (hf.contDiffOn.isImmersionAt_iff_injective_fderiv isOpen_univ (mem_univ s) hn).2 ?_
    rw [(hder s).hasFDerivAt.fderiv]
    intro a b hab
    exact smul_left_injective ℝ (hf' s) (by simpa using hab)
  · rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hf.continuous, fun K hK => ?_⟩
    obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
    refine Metric.isCompact_of_isClosed_isBounded (hK.isClosed.preimage hf.continuous) ?_
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max R ((C + ‖p‖) / ‖e‖), fun s hs => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    by_contra! hlt
    have hfs : ‖p + s • e‖ ≤ C := hline s ((le_max_left _ _).trans hlt.le) ▸ hC _ hs
    have hse : ‖s • e‖ ≤ ‖p + s • e‖ + ‖p‖ := by
      simpa using norm_sub_le (p + s • e) p
    rw [norm_smul, Real.norm_eq_abs] at hse
    have := (div_lt_iff₀ (norm_pos_iff.2 he)).1 ((le_max_right _ _).trans_lt hlt)
    linarith

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convolution.Basic
public import TauCeti.Analysis.Convex.Topology

/-!
# Strict positivity of convolutions

For continuous nonnegative real functions, a finite convolution integral is positive precisely
when its argument is the sum of points where the two factors are positive. If the topological
supports are convex, this is precisely the interior of their sum. On the real line, the
convexity assumptions say that the topological supports are intervals; the densities may still
vanish at interior points.

These results allow strict positivity of a density to follow from a convolution factorization
and interval supports, without having to prove strict positivity of the factors first.
The geometric step uses that the nonzero sets of continuous functions are open and dense in
their topological supports.

Finiteness of the integral is retained explicitly. For an integrable factor and a bounded
continuous factor, the existing
`MeasureTheory.convolutionExists_of_integrable_of_ae_norm_le` establishes finiteness everywhere,
and `BddAbove.continuous_convolution_right_of_integrable` establishes continuity.

The positivity argument uses Mathlib's `integral_pos_of_integrable_nonneg_nonzero`; the
support geometry uses `IsOpen.add_closure` and `IsOpen.closure_add`.
-/

public section

open Set Function ContinuousLinearMap
open scoped Convolution Pointwise

namespace MeasureTheory

section AddGroup

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] {μ : Measure G} [μ.IsOpenPosMeasure] {f g : G → ℝ} {x : G}

/-- A finite convolution of continuous nonnegative real functions is strictly positive exactly
on the sum of their nonzero sets. No invariance assumption on the measure is needed. -/
theorem convolution_pos_iff_mem_add_support (hf : Continuous f) (hg : Continuous g)
    (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) (hfg : ConvolutionExistsAt f g x (mul ℝ ℝ) μ) :
    0 < (f ⋆[mul ℝ ℝ, μ] g) x ↔ x ∈ support f + support g := by
  constructor
  · intro hx
    exact support_convolution_subset (mul ℝ ℝ) hx.ne'
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [convolution_def]
    exact integral_pos_of_integrable_nonneg_nonzero
      (x := a)
      (hf.mul (hg.comp (continuous_const.sub continuous_id))) hfg.integrable
      (fun y ↦ mul_nonneg (hf0 y) (hg0 _))
      (by simpa only [mul_apply', add_sub_cancel_left] using mul_ne_zero ha hb)

end AddGroup

section Convex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [MeasurableSpace E]
    {μ : Measure E} [μ.IsOpenPosMeasure] {f g : E → ℝ} {x : E}

/-- For continuous nonnegative functions with convex topological supports, a finite convolution
integral is strictly positive exactly in the interior of the sum of those supports.

For functions on `ℝ`, this applies to all interval supports, including unbounded intervals.
It does not assume that either factor is positive throughout its support interior. -/
theorem convolution_pos_iff_mem_interior_add_tsupport (hf : Continuous f) (hg : Continuous g)
    (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) (hfs : Convex ℝ (tsupport f))
    (hgs : Convex ℝ (tsupport g)) (hfg : ConvolutionExistsAt f g x (mul ℝ ℝ) μ) :
    0 < (f ⋆[mul ℝ ℝ, μ] g) x ↔ x ∈ interior (tsupport f + tsupport g) := by
  rw [convolution_pos_iff_mem_add_support hf hg hf0 hg0 hfg]
  constructor
  · intro hx
    exact interior_maximal (add_subset_add (subset_tsupport f) (subset_tsupport g))
      hg.isOpen_support.add_left hx
  · intro hx
    have hsne : (interior (tsupport f)).Nonempty := by
      obtain ⟨a, ha, b, hb, _⟩ := interior_subset hx
      obtain ⟨y, hy⟩ := closure_nonempty_iff.mp (nonempty_of_mem ha)
      exact ⟨y, interior_maximal (subset_tsupport f) hf.isOpen_support hy⟩
    have htne : (interior (tsupport g)).Nonempty := by
      obtain ⟨a, ha, b, hb, _⟩ := interior_subset hx
      obtain ⟨y, hy⟩ := closure_nonempty_iff.mp (nonempty_of_mem hb)
      exact ⟨y, interior_maximal (subset_tsupport g) hg.isOpen_support hy⟩
    rw [hfs.interior_add hgs hsne htne] at hx
    have hsub : interior (tsupport f) + interior (tsupport g) ⊆ support f + support g := by
      calc
        interior (tsupport f) + interior (tsupport g) ⊆
            tsupport f + interior (tsupport g) := add_subset_add interior_subset Subset.rfl
        _ = support f + interior (tsupport g) := isOpen_interior.closure_add (support f)
        _ ⊆ support f + tsupport g := add_subset_add Subset.rfl interior_subset
        _ = support f + support g := hf.isOpen_support.add_closure (support g)
    exact hsub hx

end Convex

end MeasureTheory

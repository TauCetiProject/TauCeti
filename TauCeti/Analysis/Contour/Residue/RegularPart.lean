/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Basic
import Mathlib.Analysis.Calculus.DSlope

/-!
# The regular part at an at-most-simple pole

Subtracting the simple residue term leaves a germ with an analytic representative. This is the
local decomposition needed to compare Taylor coefficients with those of a simple pole.
-/

public section

open Filter Topology
open TauCeti.Contour

/-- At an at-most-simple pole, the punctured germ is the sum of the simple residue term and an
analytic germ. In the removable case the residue term vanishes. -/
theorem MeromorphicAt.exists_analyticAt_eventuallyEq_inv_smul_residue_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {ρ : ℂ} (hf : MeromorphicAt f ρ)
    (horder : (-1 : WithTop ℤ) ≤ meromorphicOrderAt f ρ) :
    ∃ h : ℂ → E, AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, f s = (s - ρ)⁻¹ • residue f ρ + h s := by
  obtain ⟨g, hg, hfg⟩ := exists_analyticAt_eventuallyEq_zpow_smul hf horder
  have hres : residue f ρ = g ρ := by
    simpa using residue_eq_of_eventuallyEq_zpow_smul (n := -1) (by decide) hg hfg
  refine ⟨dslope g ρ, hg.dslope _, ?_⟩
  filter_upwards [hfg, self_mem_nhdsWithin] with s hs hsρ
  rw [hs, hres, dslope_of_ne _ (Set.mem_compl_singleton_iff.1 hsρ), slope_def_module]
  simp [smul_sub]

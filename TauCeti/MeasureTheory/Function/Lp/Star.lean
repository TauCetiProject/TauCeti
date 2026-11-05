/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The star operation on `Lp`

Mathlib equips `Lp R p μ` with the pointwise involution `star` when `R` is a normed star group.
This file records that this involution is additive, isometric and, over a star module,
conjugate-linear. Thus `Lp R p μ` is a star additive monoid and a star module for every exponent
`p`, and a normed star group for `1 ≤ p`. Over `ℂ` the involution is pointwise complex
conjugation of classes of functions; these laws are part of the C⋆-algebra structure of `L∞`.
-/

public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α R 𝕜 : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

instance instStarAddMonoid : StarAddMonoid (Lp R p μ) where
  star_add f g := by
    ext
    filter_upwards [coeFn_star (f + g), coeFn_add f g, coeFn_star f, coeFn_star g,
      coeFn_add (star f) (star g)] with x h₁ h₂ h₃ h₄ h₅
    simp only [h₁, h₂, h₃, h₄, h₅, Pi.star_apply, Pi.add_apply, star_add]

instance instNormedStarGroup [Fact (1 ≤ p)] : NormedStarGroup (Lp R p μ) where
  norm_star_le f := by rw [norm_def, norm_def, eLpNorm_congr_ae (coeFn_star f), eLpNorm_star]

instance instStarModule [NormedRing 𝕜] [Star 𝕜] [Module 𝕜 R] [IsBoundedSMul 𝕜 R]
    [StarModule 𝕜 R] : StarModule 𝕜 (Lp R p μ) where
  star_smul c f := by
    ext
    filter_upwards [coeFn_star (c • f), coeFn_smul c f, coeFn_smul (star c) (star f),
      coeFn_star f] with x h₁ h₂ h₃ h₄
    simp only [h₁, h₂, h₃, h₄, Pi.star_apply, Pi.smul_apply, star_smul]

end MeasureTheory.Lp

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Standardized Brownian increments

This file defines `TauCeti.normalizedBrownianIncrements`, the increments on a finite time grid
divided by the square roots of their interval lengths. It proves measurability when the
observations are measurable and, for a strictly increasing grid and a pre-Brownian process,
the product standard Gaussian law. No path regularity or filtration is required. Empty grids
and positive initial dates are allowed; the vector does not include the initial observation.

For Hermite expansions of increment-dependent claims, import
`TauCeti/Probability/Distributions/Gaussian/Hermite/Pi/Pullback.lean` as well. Apply its
`ProbabilityTheory.HasLaw.gaussianVectorL2Isometry` and
`ProbabilityTheory.HasLaw.hasSum_gaussianVectorHermite` to
`ProbabilityTheory.IsPreBrownianReal.hasLaw_normalizedBrownianIncrements`, supplying
measurability of the increment vector separately. That general API uses the existing product
Gaussian Hermite basis `TauCeti.gaussianHermitePiBasis`; the present file supplies only the
increment vector and its law, not the pullback construction or a martingale representation.
The finite-dimensional Gaussian expansion underlying Brownian martingale representation is
described in Karatzas and Shreve, *Brownian Motion and Stochastic Calculus*, second edition, §3.4.
-/

public section

open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped NNReal ENNReal

namespace TauCeti

variable {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
  {n : ℕ} {t : Fin (n + 1) → ℝ≥0}

/-- The vector of Brownian increments standardized by their interval lengths. -/
noncomputable def normalizedBrownianIncrements (B : ℝ≥0 → Ω → ℝ) (t : Fin (n + 1) → ℝ≥0)
    (ω : Ω) (i : Fin n) : ℝ :=
  (B (t i.succ) ω - B (t i.castSucc) ω) /
    Real.sqrt ((t i.succ : ℝ) - t i.castSucc)

/-- Evaluation of a standardized increment. -/
@[simp]
theorem normalizedBrownianIncrements_apply (ω : Ω) (i : Fin n) :
    normalizedBrownianIncrements B t ω i =
      (B (t i.succ) ω - B (t i.castSucc) ω) /
        Real.sqrt ((t i.succ : ℝ) - t i.castSucc) := (rfl)

/-- Standardized increments are measurable when the process observations are measurable. -/
@[fun_prop]
theorem measurable_normalizedBrownianIncrements [MeasurableSpace Ω]
    (hB : ∀ s, Measurable (B s)) : Measurable (normalizedBrownianIncrements B t) := by
  exact Measurable.of_eval fun i => ((hB _).sub (hB _)).div_const _

end TauCeti

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
  {n : ℕ} {t : Fin (n + 1) → ℝ≥0}

/-- Standardized increments on a strictly increasing grid have independent standard Gaussian
coordinates. No path regularity or filtration assumption is needed. -/
theorem hasLaw_normalizedBrownianIncrements (hB : IsPreBrownianReal B P) (ht : StrictMono t) :
    HasLaw (normalizedBrownianIncrements B t)
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) P := by
  have hind := (hB.hasIndepIncrements n t ht.monotone).comp
    (fun i x => x / Real.sqrt ((t i.succ : ℝ) - t i.castSucc)) (by fun_prop)
  apply hind.hasLaw_pi
  intro i
  have hlt : (t i.castSucc : ℝ) < t i.succ := ht Fin.castSucc_lt_succ
  have hvar : nndist (t i.succ : ℝ) (t i.castSucc : ℝ) /
      NNReal.mk (Real.sqrt ((t i.succ : ℝ) - t i.castSucc) ^ 2) (sq_nonneg _) =
        (1 : ℝ≥0) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one, coe_nndist, Real.dist_eq,
      abs_of_pos (sub_pos.mpr hlt), Real.sq_sqrt (sub_nonneg.mpr hlt.le),
      div_self (sub_ne_zero.mpr hlt.ne')]
  -- Gaussian scaling currently uses the underlying subtype constructor for its variance.
  -- `convert!` reconciles that constructor with `NNReal.mk` without changing the law.
  convert! gaussianReal_div_const (hB.hasLaw_sub (t i.succ) (t i.castSucc))
    (Real.sqrt ((t i.succ : ℝ) - t i.castSucc)) using 1
  exact congrArg₂ gaussianReal (zero_div _).symm hvar.symm

end ProbabilityTheory.IsPreBrownianReal

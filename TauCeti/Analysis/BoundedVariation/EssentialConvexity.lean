/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.BoundedVariation.Perimeter
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.Convex.Measure
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.EssentialConvexity
import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Isoperimetric

/-!
# Isoperimetric rigidity for essentially convex sets

A positive finite-volume set that agrees almost everywhere with a convex set attains
isoperimetric equality exactly when it agrees almost everywhere with an open ball of
positive radius. No boundedness, closedness or regularity of the supplied representative
is required, and finite perimeter follows from essential convexity and finite volume.

The compact-convex equality theorem is transported using
`MeasureTheory.Measure.exists_isCompact_convex_ae_eq` and a.e. invariance of perimeter.
The nullity of spheres converts its closed-ball conclusion into open-ball a.e. equality.
The interval-section version applies essential convexity: in each unit direction almost
every line section must agree a.e. with an interval. The exceptional transverse null set
may depend on the direction. This separates the geometric rigidity argument from the
problem of obtaining interval sections from equality in a perimeter comparison.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge
  University Press, 2012, Chapters 13 and 14.
-/

public section

open MeasureTheory Metric Module Set
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {s : Set E}

/-- **Isoperimetric rigidity for essentially convex sets.** In positive dimension, a set
of positive finite volume that agrees a.e. with a convex set attains the sharp perimeter
bound exactly when it agrees a.e. with an open ball of positive radius. In particular,
null modifications of convex sets need not themselves be balls. -/
theorem perimeter_pow_eq_iff_exists_ae_eq_ball_of_ae_eq_convex
    (hn : finrank ℝ E ≠ 0) (hpos : 0 < volume s) (hfin : volume s ≠ ∞)
    (hc : ∃ C : Set E, Convex ℝ C ∧ s =ᵐ[volume] C) :
    perimeter volume ⊤ s ^ finrank ℝ E =
        (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
          volume s ^ (finrank ℝ E - 1) ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =ᵐ[volume] ball c r := by
  constructor
  · intro heq
    obtain ⟨K, hK, hKc, hKi, hsK⟩ := volume.exists_isCompact_convex_ae_eq hpos hfin hc
    let B : ConvexBody E := ⟨K, hKc, hK, hKi.mono interior_subset⟩
    have hB : (B : Set E) = K := ConvexBody.coe_mk _ _ _ _
    have hvol : volume (B : Set E) = volume s := by
      rw [hB]
      exact (measure_congr hsK).symm
    have hper : perimeter volume ⊤ (B : Set E) = perimeter volume ⊤ s := by
      rw [hB]
      exact (perimeter_congr_ae (ae_restrict_of_ae hsK)).symm
    obtain ⟨c, r, hr, hBr⟩ := (B.perimeter_pow_eq_iff_exists_eq_closedBall hn
      (hvol ▸ hpos.ne')).mp (by simpa only [hvol, hper] using heq)
    refine ⟨c, r, hr, hsK.trans ?_⟩
    rw [← hB, hBr]
    exact volume.addHaar_closedBall_ae_eq_ball_of_ne_zero c r hr.ne'
  · rintro ⟨c, r, hr, hsr⟩
    rw [perimeter_congr_ae (ae_restrict_of_ae hsr), measure_congr hsr]
    exact perimeter_ball_pow hn hr

end TauCeti

namespace MeasureTheory.NullMeasurableSet

/-- **Isoperimetric rigidity from interval sections.** For a positive finite-volume
Lebesgue-measurable set, suppose that in every unit direction almost every line section
agrees a.e. with an interval. Then equality in the sharp perimeter inequality is equivalent
to agreement a.e. with an open ball of positive radius. -/
theorem perimeter_pow_eq_iff_exists_ae_eq_ball_of_ae_lineSection_ordConnected
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {s : Set E}
    (hs : NullMeasurableSet s volume) (hn : finrank ℝ E ≠ 0)
    (hpos : 0 < volume s) (hfin : volume s ≠ ∞)
    (hsections : ∀ e : E, ‖e‖ = 1 → ∀ᵐ y : (ℝ ∙ e)ᗮ ∂volume,
      ∃ I : Set ℝ, I.OrdConnected ∧ {t : ℝ | (y : E) + t • e ∈ s} =ᵐ[volume] I) :
    TauCeti.perimeter volume ⊤ s ^ finrank ℝ E =
        (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) *
          volume s ^ (finrank ℝ E - 1) ↔
      ∃ c : E, ∃ r : ℝ, 0 < r ∧ s =ᵐ[volume] ball c r :=
  TauCeti.perimeter_pow_eq_iff_exists_ae_eq_ball_of_ae_eq_convex hn hpos hfin
    (TauCeti.exists_convex_ae_eq_of_ae_lineSection_ordConnected hs hsections)

end MeasureTheory.NullMeasurableSet

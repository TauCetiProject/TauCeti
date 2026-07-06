/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Schwarz
public import TauCeti.Analysis.Complex.Conformal.UnitDiscAutomorphism

/-!
# Schwarz--Pick for the pseudo-hyperbolic expression

This file proves the Schwarz--Pick contraction estimate for holomorphic self-maps of the
complex unit disc, stated using Tau Ceti's pseudo-hyperbolic expression
`pseudoHyperbolicExpr z w = ‖(z - w) / (1 - conj w * z)‖`.

The proof uses the standard reduction to Mathlib's Schwarz lemma: conjugate the source by the
disc Moebius factor sending `w` to `0`, conjugate the target by the factor sending `f w` to
`0`, and apply `Complex.norm_le_norm_of_mapsTo_ball` to the resulting holomorphic disc
self-map fixing `0`.

This advances the conformal-mapping roadmap's L2 Schwarz--Pick target.  It reuses Mathlib's
Schwarz lemma and Tau Ceti's unit-disc Moebius API.  As with the rest of the L0--L3
conformal-mapping material, it is coordinated with the upstream Mathlib RMT effort
leanprover-community/mathlib4#33505 and should be refactored to upstream API if that work
lands a human-curated Schwarz--Pick theorem.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

/-- The scalar unit-disc Moebius formula maps the open unit disc to itself. -/
lemma unitDiscMoebiusFormula_mapsTo_ball_of_norm_lt_one {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo
      (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro z hz
  rw [mem_ball_zero_iff, ← pseudoHyperbolicExpr_def]
  exact
    pseudoHyperbolicExpr_lt_one_of_norm_lt_one
      (by simpa only [mem_ball_zero_iff] using hz) ha

/-- The scalar formula of a unit-disc Moebius factor maps the open unit disc to itself. -/
lemma unitDiscMoebiusFormula_mapsTo_ball (a : Complex.UnitDisc) :
    MapsTo
      (fun z : ℂ => (z - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * z))
      (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
  unitDiscMoebiusFormula_mapsTo_ball_of_norm_lt_one a.norm_lt_one

/--
The Schwarz--Pick contraction estimate for the pseudo-hyperbolic expression on the open unit
disc.
-/
theorem schwarzPick_pseudoHyperbolicExpr {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicExpr (f z) (f w) ≤ pseudoHyperbolicExpr z w := by
  let source : ℂ → ℂ :=
    fun ξ => (ξ - (-(w : ℂ))) / (1 - (starRingEnd ℂ) (-(w : ℂ)) * ξ)
  let target : ℂ → ℂ :=
    fun η => (η - f w) / (1 - (starRingEnd ℂ) (f w) * η)
  let g : ℂ → ℂ := target ∘ f ∘ source
  have hw_norm : ‖w‖ < 1 := by
    simpa [mem_ball_zero_iff] using hw
  have hfw : f w ∈ ball (0 : ℂ) 1 := hmaps hw
  have hfw_norm : ‖f w‖ < 1 := by
    simpa [mem_ball_zero_iff] using hfw
  have hsource_maps : MapsTo source (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    simpa [source] using unitDiscMoebiusFormula_mapsTo_ball_of_norm_lt_one
      (a := -(w : ℂ)) (by simpa using hw_norm)
  have htarget_maps : MapsTo target (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    simpa [target] using unitDiscMoebiusFormula_mapsTo_ball_of_norm_lt_one
      (a := f w) hfw_norm
  have hg_maps_ball : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro ξ hξ
    exact htarget_maps (hmaps (hsource_maps hξ))
  have hg_maps_closed : MapsTo g (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    intro ξ hξ
    exact ball_subset_closedBall (hg_maps_ball hξ)
  have hsource_diff : DifferentiableOn ℂ source (ball (0 : ℂ) 1) := by
    simpa [source] using differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one
      (a := -(w : ℂ)) (by simpa using hw_norm)
  have htarget_diff : DifferentiableOn ℂ target (ball (0 : ℂ) 1) := by
    simpa [target] using differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one
      (a := f w) hfw_norm
  have hg_diff : DifferentiableOn ℂ g (ball (0 : ℂ) 1) :=
    htarget_diff.comp (hf.comp hsource_diff hsource_maps) (hmaps.comp hsource_maps)
  have hg_zero : g 0 = 0 := by
    have hsource_zero : source 0 = w := by
      simp [source]
    simp [g, target, hsource_zero]
  have hz_norm : ‖z‖ < 1 := by
    simpa [mem_ball_zero_iff] using hz
  let ξ : ℂ := (z - w) / (1 - (starRingEnd ℂ) w * z)
  have hξ_mem : ξ ∈ ball (0 : ℂ) 1 := by
    simpa [ξ] using unitDiscMoebiusFormula_mapsTo_ball_of_norm_lt_one
      (a := w) hw_norm hz
  have hsource_ξ : source ξ = z := by
    have hden : 1 - (starRingEnd ℂ) w * z ≠ 0 :=
      one_sub_conj_mul_ne_zero_of_norm_lt_one hz_norm hw_norm
    have hnorm : 1 - (starRingEnd ℂ) w * w ≠ 0 :=
      one_sub_conj_mul_ne_zero_of_norm_lt_one hw_norm hw_norm
    have hden₂ :
        1 + (starRingEnd ℂ) w * ((z - w) / (1 - (starRingEnd ℂ) w * z)) =
          (1 - (starRingEnd ℂ) w * w) / (1 - (starRingEnd ℂ) w * z) := by
      field_simp [hden]
      ring
    have hden_comm : 1 - z * (starRingEnd ℂ) w ≠ 0 := by
      simpa [mul_comm] using hden
    have hnorm_comm : 1 - w * (starRingEnd ℂ) w ≠ 0 := by
      simpa [mul_comm] using hnorm
    dsimp [source, ξ]
    simp only [map_neg, neg_mul, sub_neg_eq_add]
    rw [hden₂]
    field_simp [hden_comm, hnorm_comm]
    ring_nf
  have hg_ξ : g ξ = target (f z) := by
    simp [g, hsource_ξ]
  have hξ_norm : ‖ξ‖ < 1 := by
    simpa [mem_ball_zero_iff] using hξ_mem
  calc
    pseudoHyperbolicExpr (f z) (f w) = ‖g ξ‖ := by
      rw [hg_ξ, pseudoHyperbolicExpr_def]
    _ ≤ ‖ξ‖ := by
      exact Complex.norm_le_norm_of_mapsTo_ball hg_diff hg_maps_closed hg_zero hξ_norm
    _ = pseudoHyperbolicExpr z w := by
      rw [pseudoHyperbolicExpr_def]

/-- The raw norm-quotient form of Schwarz--Pick. -/
theorem schwarzPick_norm_div_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    ‖(f z - f w) / (1 - (starRingEnd ℂ) (f w) * f z)‖
      ≤ ‖(z - w) / (1 - (starRingEnd ℂ) w * z)‖ :=
  by
    simpa [pseudoHyperbolicExpr_def] using schwarzPick_pseudoHyperbolicExpr hf hmaps hz hw

/-- Bundled unit-disc form of the Schwarz--Pick contraction estimate. -/
theorem schwarzPick_pseudoHyperbolicExpr_unitDisc {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (z w : Complex.UnitDisc) :
    pseudoHyperbolicExpr (f z) (f w) ≤ pseudoHyperbolicExpr (z : ℂ) (w : ℂ) :=
  schwarzPick_pseudoHyperbolicExpr hf hmaps z.property w.property

end TauCeti

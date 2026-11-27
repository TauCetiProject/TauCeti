/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import TauCeti.RingTheory.Subring.ResidueClass

/-!
# Haar volume of residue classes over a subring

For a subring `R` of a locally compact ring `A` and a unit `g`, the product Haar measure
of the class `R.residueClass g x₀ = x₀ + g R^ι` is `Δ(g)^|ι| μ(R)^|ι|`, where `Δ` is
Mathlib's distributive Haar character. In particular, when `μ(R) = 1`, its volume is
`Δ(g)^|ι|`.
-/

public section

open MeasureTheory
open scoped Pointwise ENNReal

namespace Subring

variable {A ι : Type*} [Ring A] (R : Subring A)

section Measure

variable [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [MeasurableSpace A] [BorelSpace A] [Fintype ι]
  (μ : Measure A) [SigmaFinite μ] [μ.IsAddHaarMeasure] [μ.Regular]

/-- The volume of a class for the product Haar measure, without normalizing `μ R`. -/
theorem measure_residueClass (g : Aˣ) (x₀ : ι → A) :
    Measure.pi (fun _ : ι ↦ μ) (R.residueClass g x₀) =
      (distribHaarChar A g : ℝ≥0∞) ^ Fintype.card ι * μ R ^ Fintype.card ι := by
  rw [R.residueClass_eq_pi, Measure.pi_pi]
  have hcoord (i : ι) : μ ((fun y : A ↦ x₀ i + g * y) '' (R : Set A)) =
      (distribHaarChar A g : ℝ≥0∞) * μ R := by
    rw [← Set.image_image]
    rw [Set.image_add_left, measure_preimage_add]
    exact (distribHaarChar_mul μ g (R : Set A)).symm
  simp_rw [hcoord]
  simp [mul_pow]

/-- For a Haar measure giving the subring volume one, a class has volume `Δ(g)^|ι|`. -/
theorem measure_residueClass_of_measure_eq_one (hμ : μ R = 1) (g : Aˣ) (x₀ : ι → A) :
    Measure.pi (fun _ : ι ↦ μ) (R.residueClass g x₀) =
      (distribHaarChar A g : ℝ≥0∞) ^ Fintype.card ι := by
  simp [R.measure_residueClass μ, hμ]

end Measure

end Subring

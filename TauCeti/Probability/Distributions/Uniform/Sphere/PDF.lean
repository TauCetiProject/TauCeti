/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Sphere.Basic

/-!
# Surface densities of uniform sphere laws

The uniform law on the unit sphere in real dimension `d` has constant density
`Γ(d / 2) / (2 * π ^ (d / 2))` relative to the polar-coordinate surface measure
`volume.toSphere`. This is a density on the sphere subtype, not relative to ambient volume.
The measure identity, Radon–Nikodym derivative, and native sphere-valued `HasLaw` density
interfaces below use this reference measure explicitly.

The statements include dimension one, where the sphere has two points, and dimension zero,
where the sphere is empty and its uniform law and surface measure are both zero. No probability
claim is made in dimension zero.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, section 1.5.
-/

public section

open MeasureTheory ProbabilityTheory Metric Set

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The uniform sphere law has constant density equal to the reciprocal surface area, relative
to the polar-coordinate surface measure on the sphere subtype. -/
theorem uniformSphereMeasure_eq_withDensity :
    uniformSphereMeasure E = (volume : Measure E).toSphere.withDensity
      (fun _ ↦ ENNReal.ofReal (Real.Gamma ((Module.finrank ℝ E : ℝ) / 2) /
        (2 * Real.pi ^ ((Module.finrank ℝ E : ℝ) / 2)))) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Subsingleton.elim _ _
  · have hd : 0 < (Module.finrank ℝ E : ℝ) / 2 :=
      div_pos (Nat.cast_pos.mpr (Module.finrank_pos (R := ℝ) (M := E))) zero_lt_two
    have harea : 0 < 2 * Real.pi ^ ((Module.finrank ℝ E : ℝ) / 2) /
        Real.Gamma ((Module.finrank ℝ E : ℝ) / 2) :=
      div_pos (mul_pos zero_lt_two (Real.rpow_pos_of_pos Real.pi_pos _))
        (Real.Gamma_pos_of_pos hd)
    rw [uniformSphereMeasure_def, withDensity_const, toSphere_volume_apply_univ,
      ← ENNReal.ofReal_inv_of_pos harea, inv_div]

/-- The Radon–Nikodym derivative of the uniform sphere law against surface measure is the
constant reciprocal surface area. -/
theorem rnDeriv_uniformSphereMeasure :
    (uniformSphereMeasure E).rnDeriv (volume : Measure E).toSphere =ᵐ[(volume : Measure E).toSphere]
      fun _ ↦ ENNReal.ofReal (Real.Gamma ((Module.finrank ℝ E : ℝ) / 2) /
        (2 * Real.pi ^ ((Module.finrank ℝ E : ℝ) / 2))) := by
  rw [uniformSphereMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity _ measurable_const

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → sphere (0 : E) 1}

/-- A uniform sphere-valued random variable has a density relative to polar-coordinate surface
measure, including for the two-point sphere in dimension one. -/
theorem hasPDF_uniformSphereMeasure (hX : HasLaw X (uniformSphereMeasure E) P) :
    HasPDF X P (volume : Measure E).toSphere := by
  rw [uniformSphereMeasure_eq_withDensity] at hX
  exact hasPDF_of_hasLaw_withDensity measurable_const.aemeasurable hX

/-- The canonical density of a uniform sphere-valued random variable is the constant reciprocal
surface area, almost everywhere with respect to surface measure. -/
theorem pdf_uniformSphereMeasure (hX : HasLaw X (uniformSphereMeasure E) P) :
    pdf X P (volume : Measure E).toSphere =ᵐ[(volume : Measure E).toSphere]
      fun _ ↦ ENNReal.ofReal (Real.Gamma ((Module.finrank ℝ E : ℝ) / 2) /
        (2 * Real.pi ^ ((Module.finrank ℝ E : ℝ) / 2))) := by
  rw [uniformSphereMeasure_eq_withDensity] at hX
  exact pdf_eq_of_hasLaw_withDensity measurable_const.aemeasurable hX

end ProbabilityTheory.HasLaw

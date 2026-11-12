/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Kernel
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Cone

/-!
# The Mellin transform of a lattice theta integral over a unit cone

For a lattice theta series, `hasMellin_mellinKernel_sub` identifies the Mellin transform of the
existing covolume-rescaled kernel, minus its constant term, with the weighted theta integral over
the cone. Absolute integrability of that cone integral is an explicit hypothesis: this change of
variables does not perform the separate arithmetic unfolding of unit orbits. In particular it
does not identify a radial lattice-point sum with a partial zeta function.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.5).
-/

public section
noncomputable section

open MeasureTheory Set NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **The radial Mellin substitution in Hecke's integral.** If the norm-weighted theta series
minus its constant term is absolutely integrable over the cone, then the Mellin transform of
its kernel is that cone integral times `(2^r₂ / w) V_L^s`. The power of the covolume comes from
the substitution `u = V_L² t`, not from a Jacobian factor in `dt / t`. -/
theorem hasMellin_mellinKernel_sub {D : Set (realSpace K)} (hDm : MeasurableSet D)
    (hD : Bornology.IsBounded D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] (s : ℂ)
    (h : IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * (latticeTheta L y - 1))
      (unitCone D) (archHaar K)) :
    HasMellin (fun u ↦ mellinKernel D L u -
        (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
          (surfaceHaar K).real (Subtype.val ⁻¹' D)) (s / 2)
      ((2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (ZLattice.covolume L ^ 2 : ℂ) ^ (s / 2) *
          ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) * (latticeTheta L y - 1)
            ∂archHaar K) := by
  let F : ℝ → ℂ := fun t ↦ ∫ x in Subtype.val ⁻¹' D,
    (latticeTheta L (surfaceScale (x : realSpace K) t) - 1) ∂surfaceHaar K
  let c : ℂ := (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ)
  have hV : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  have hF : HasMellin F (s / 2)
      (∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) * (latticeTheta L y - 1) ∂archHaar K) :=
    hasMellin_integral_surfaceScale hDm (s / 2) h
  have hscaled := hF.comp_mul_right (a := (ZLattice.covolume L ^ 2)⁻¹) (by positivity)
  have havg (u : ℝ) (hu : 0 < u) : mellinKernel D L u -
      c * (surfaceHaar K).real (Subtype.val ⁻¹' D) =
        c • F (u * (ZLattice.covolume L ^ 2)⁻¹) := by
    rw [mellinKernel_sub_eq_integral_sub_one hDm hD L hu]
    simp only [F, c, smul_eq_mul, div_eq_mul_inv]
  have hc := (hasMellin_congr (fun u hu ↦ (havg u hu).symm)).mp
    (hasMellin_const_smul hscaled.1 c)
  rw [hscaled.2, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (sq_nonneg _),
    Complex.cpow_neg, inv_inv] at hc
  simpa only [c, smul_eq_mul, Complex.ofReal_pow, mul_assoc] using hc

end TauCeti.LFunctions

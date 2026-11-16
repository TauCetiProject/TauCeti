/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Kernel
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Pair
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Cone

/-!
# The Mellin transform of a lattice theta integral over a unit cone

For a lattice theta series, `hasMellin_mellinKernel_sub` identifies the Mellin transform of the
existing covolume-rescaled kernel, minus its constant term, with the weighted theta integral over
the cone. For a unit fundamental domain `D`, `mellinKernelFEPair_Λ_eq_integral_unitCone` equates
`(mellinKernelFEPair hD L).Λ s` on `Re s > 1/2` with that cone integral. Absolute integrability of
that cone integral is an explicit hypothesis: this change of variables does not perform the
separate arithmetic unfolding of unit orbits. In particular it does not identify a radial
lattice-point sum with a partial zeta function.

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

open scoped Classical in
/-- For a unit fundamental domain `D`, on `Re s > 1 / 2` the completed function
`(mellinKernelFEPair hD L).Λ s` equals `(2^r₂ / w) (V_L²)^s` times the norm-weighted cone integral
of `θ_L - 1`, provided that cone integral is absolutely integrable. -/
theorem mellinKernelFEPair_Λ_eq_integral_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] {s : ℂ} (hs : 1 / 2 < s.re)
    (h : IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ s * (latticeTheta L y - 1))
      (unitCone D) (archHaar K)) :
    (mellinKernelFEPair hD L).Λ s =
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (ZLattice.covolume L ^ 2 : ℂ) ^ s *
          ∫ y in unitCone D, (archNorm y : ℂ) ^ s * (latticeTheta L y - 1) ∂archHaar K := by
  have hm1 := hasMellin_mellinKernel_sub_mellinConstant hD L hs
  have hm2 := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded L (2 * s)
    (by simpa [mul_div_cancel_left₀ _ (two_ne_zero' ℂ)] using h)
  rw [mul_div_cancel_left₀ _ (two_ne_zero' ℂ)] at hm2
  rw [mellinConstant_eq_mul_surfaceHaar_real hD] at hm1
  push_cast at hm1
  exact hm1.2.symm.trans hm2.2

end TauCeti.LFunctions

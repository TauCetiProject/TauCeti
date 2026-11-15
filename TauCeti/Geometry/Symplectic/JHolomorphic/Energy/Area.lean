/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Integral
public import TauCeti.Geometry.Symplectic.Wirtinger

/-!
# Metric area between energy and symplectic area

For a compatible pair `(ω, J)` with associated metric `g = ω(·, J ·)`, the metric area density of
a real-linear map `F` out of the standard complex line is the wedge norm
`|F ∂s ∧ F ∂t|_g` (`TauCeti.SymplecticForm.wedgeNorm`). It sits between the two densities of
`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Basic`:

`ω(F ∂s, F ∂t) ≤ |F ∂s ∧ F ∂t|_g ≤ (g(F ∂s, F ∂s) + g(F ∂t, F ∂t)) / 2`.

The first inequality is the Wirtinger inequality. It is an equality `0 = 0` when `F ∂s` and `F ∂t`
are linearly dependent (`F` has rank at most one); when `F` has rank two it is an equality exactly
when the image plane is a `J`-complex line with its complex orientation. The second is an equality
exactly when `F` is conformal for `g`. Both are equalities exactly when `F` is complex linear.

Integrating over a measure on the source gives the chain `E(u) ≥ Area_g(u) ≥ ∫ u^*ω` for the
energy `TauCeti.SymplecticForm.stdComplexLineEnergy` and the metric area
`TauCeti.SymplecticForm.stdComplexLineArea` of a field of differentials, with equality throughout
for an almost everywhere complex-linear differential, in particular for a constant-structure
`J`-holomorphic map. As there, the differential is kept explicit and all integrals are lower
Lebesgue integrals of positive parts.

## Main declarations

* `TauCeti.SymplecticForm.two_mul_wedgeNorm_le_stdComplexLineEnergyDensity`: the pointwise
  inequality `2 |F ∂s ∧ F ∂t|_g ≤ energyDensity F`, with equality case
  `TauCeti.SymplecticForm.two_mul_wedgeNorm_eq_stdComplexLineEnergyDensity_iff` for conformal `F`.
* `TauCeti.SymplecticForm.stdComplexLineArea`: the metric area of a field of differentials.
* `TauCeti.SymplecticForm.lintegral_symplecticForm_le_stdComplexLineArea`: `∫ u^*ω ≤ Area_g(u)`.
* `TauCeti.SymplecticForm.stdComplexLineArea_le_stdComplexLineEnergy`: `Area_g(u) ≤ E(u)`.
* `TauCeti.SymplecticForm.stdComplexLineArea_eq_stdComplexLineEnergy` and
  `TauCeti.SymplecticForm.fderiv_stdComplexLineArea_eq_stdComplexLineEnergy`: equality for
  complex-linear differentials and for constant-structure `J`-holomorphic maps.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Lemma 2.2.1.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

namespace SymplecticForm

section Pointwise

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}

/-- **Area is at most energy, pointwise.** For a compatible pair, twice the metric area density
`|F ∂s ∧ F ∂t|_g` of a real-linear map out of the standard complex line is at most its energy
density. -/
theorem two_mul_wedgeNorm_le_stdComplexLineEnergyDensity (hcompat : ω.Compatible J)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    2 * ω.wedgeNorm J (F stdComplexLineReal) (F stdComplexLineImag) ≤
      ω.stdComplexLineEnergyDensity J F := by
  rw [stdComplexLineEnergyDensity_def]
  exact hcompat.two_mul_wedgeNorm_le _ _

/-- Twice the metric area density equals the energy density exactly when the map is conformal
for the associated metric: `F ∂s` and `F ∂t` have the same length and are orthogonal. -/
theorem two_mul_wedgeNorm_eq_stdComplexLineEnergyDensity_iff (hcompat : ω.Compatible J)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    2 * ω.wedgeNorm J (F stdComplexLineReal) (F stdComplexLineImag) =
        ω.stdComplexLineEnergyDensity J F ↔
      ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) =
          ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag) ∧
        ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineImag) = 0 := by
  rw [stdComplexLineEnergyDensity_def]
  exact hcompat.two_mul_wedgeNorm_eq_iff _ _

end Pointwise

variable {X V : Type*} [MeasurableSpace X]
variable [AddCommGroup V] [Module ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {μ ν : Measure X} {du dv : X → (ℝ × ℝ) →ₗ[ℝ] V}

/-- The metric area of a field of real-linear maps out of the standard complex line: the lower
Lebesgue integral of the wedge norm `|du ∂s ∧ du ∂t|_g` for the associated form
`g = ω(·, J ·)`. The source measure `μ` is arbitrary. For a compatible pair, Lebesgue measure on a
planar domain `X`, and the differential `du` of a `C¹` immersion `u`, the area formula identifies
this with the area of the image surface counted with multiplicity, measured in `g`. -/
noncomputable def stdComplexLineArea
    (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (du : X → ((ℝ × ℝ) →ₗ[ℝ] V)) (μ : Measure X) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (ω.wedgeNorm J (du x stdComplexLineReal) (du x stdComplexLineImag)) ∂μ

/-- The metric area of a differential field is the lower integral of its wedge norm. -/
lemma stdComplexLineArea_def
    (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (du : X → ((ℝ × ℝ) →ₗ[ℝ] V)) (μ : Measure X) :
    ω.stdComplexLineArea J du μ =
      ∫⁻ x, ENNReal.ofReal
        (ω.wedgeNorm J (du x stdComplexLineReal) (du x stdComplexLineImag)) ∂μ :=
  (rfl)

/-- The zero differential field has zero metric area. -/
@[simp]
lemma stdComplexLineArea_zero (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (μ : Measure X) :
    ω.stdComplexLineArea J (0 : X → ((ℝ × ℝ) →ₗ[ℝ] V)) μ = 0 := by
  simp [stdComplexLineArea_def]

/-- Metric area for the zero source measure is zero. -/
@[simp]
lemma stdComplexLineArea_zero_measure (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (du : X → ((ℝ × ℝ) →ₗ[ℝ] V)) :
    ω.stdComplexLineArea J du (0 : Measure X) = 0 := by
  simp [stdComplexLineArea_def]

/-- Metric area depends only on the differential field almost everywhere. -/
lemma stdComplexLineArea_congr_ae (h : du =ᵐ[μ] dv) :
    ω.stdComplexLineArea J du μ = ω.stdComplexLineArea J dv μ := by
  rw [stdComplexLineArea_def, stdComplexLineArea_def]
  exact lintegral_congr_ae <| h.mono fun x hx => by
    simp [hx]

/-- Enlarging the source measure cannot decrease metric area. -/
lemma stdComplexLineArea_mono_measure (hμν : μ ≤ ν) :
    ω.stdComplexLineArea J du μ ≤ ω.stdComplexLineArea J du ν := by
  rw [stdComplexLineArea_def, stdComplexLineArea_def]
  exact lintegral_mono' hμν le_rfl

/-- **Integrated Wirtinger inequality, area form.** For a compatible pair, the integral of the
positive symplectic area density is at most the metric area. -/
theorem lintegral_symplecticForm_le_stdComplexLineArea (hcompat : ω.Compatible J) :
    (∫⁻ x, ENNReal.ofReal
      (ω (du x stdComplexLineReal) (du x stdComplexLineImag)) ∂μ) ≤
        ω.stdComplexLineArea J du μ := by
  rw [stdComplexLineArea_def]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hcompat.apply_le_wedgeNorm _ _)

/-- **Area is at most energy.** For a compatible pair, the metric area of a differential field is
at most its energy. -/
theorem stdComplexLineArea_le_stdComplexLineEnergy (hcompat : ω.Compatible J) :
    ω.stdComplexLineArea J du μ ≤ ω.stdComplexLineEnergy J du μ := by
  rw [stdComplexLineArea_def, stdComplexLineEnergy_def]
  refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
  linarith [two_mul_wedgeNorm_le_stdComplexLineEnergyDensity hcompat (du x)]

/-- For a compatible pair, a differential field that is complex linear almost everywhere has
metric area equal to its energy, and hence, by
`TauCeti.SymplecticForm.stdComplexLineEnergy_eq_lintegral_symplecticForm`, to the integral of its
symplectic area density. -/
theorem stdComplexLineArea_eq_stdComplexLineEnergy (hcompat : ω.Compatible J)
    (hdu : ∀ᵐ x ∂μ, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (du x)) :
    ω.stdComplexLineArea J du μ = ω.stdComplexLineEnergy J du μ := by
  refine (stdComplexLineArea_le_stdComplexLineEnergy hcompat).antisymm ?_
  rw [stdComplexLineEnergy_eq_lintegral_symplecticForm hdu]
  exact lintegral_symplecticForm_le_stdComplexLineArea hcompat

section Map

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {J : AlmostComplexStructure W} {ω : SymplecticForm W}
variable {f : ℝ × ℝ → W} {μ : Measure (ℝ × ℝ)}

/-- For a compatible pair, a map that is constant-structure `J`-holomorphic almost everywhere has
metric area equal to its energy. -/
theorem fderiv_stdComplexLineArea_eq_stdComplexLineEnergy (hcompat : ω.Compatible J)
    (hf : ∀ᵐ x ∂μ, IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) :
    ω.stdComplexLineArea J (fun x ↦ (fderiv ℝ f x).toLinearMap) μ =
      ω.stdComplexLineEnergy J (fun x ↦ (fderiv ℝ f x).toLinearMap) μ :=
  stdComplexLineArea_eq_stdComplexLineEnergy hcompat <|
    hf.mono fun _ hx => hx.fderiv_isComplexLinear

end Map

end SymplecticForm

end TauCeti

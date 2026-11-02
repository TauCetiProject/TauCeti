/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The energy identity for a compactly supported map from the plane

A compactly supported `C²` map `u` from the standard complex line into a symplectic vector space
has vanishing symplectic area, `∫ ω(∂s u, ∂t u) = 0`: the area density is a null Lagrangian,
being the pullback of a constant — hence closed — two-form. Integrating the pointwise Wirtinger
identity
`e(du) - 2 ω(∂s u, ∂t u) = g(∂s u + J (∂t u), ∂s u + J (∂t u))`
over the plane therefore turns it into the **energy identity**

`∫ e(du) = ∫ g(D u, D u)`, where `D u = ∂s u + J (∂t u)` is the Cauchy--Riemann defect,

an equality of integrals that needs only `J`-invariance of `ω`. Invariance alone does not make
the associated form `g = ω(·, J ·)` positive, so neither side is a norm in that generality; when
`ω` in addition tames `J` the identity reads `‖du‖₂ = ‖D u‖₂`, a homogeneous `L²` estimate for
the Cauchy--Riemann operator on compactly supported maps, controlling the derivative alone and
saying nothing about `‖u‖₂`. With this normalization of `D` the constant is `1`; the constant for
the normalization `D u = (∂s u + J (∂t u)) / 2` is `2`. The identity is what makes the energy of
a holomorphic curve computable from its area.

For a holomorphic `u` the energy density is twice the area density, so the vanishing area makes
the energy integral vanish, and under tameness the energy density is positive wherever the
differential is not. A compactly supported `C²` solution of the Cauchy--Riemann equation on the
whole plane, with tame target, is therefore zero: there are no compactly supported nonconstant
holomorphic planes. Tameness alone suffices for this, without invariance, because the argument
runs through the vanishing area rather than through the energy identity.

The vanishing-area statement uses any additive Haar measure on `ℝ × ℝ`; `volume` is the
intended instance. The shared energy identity only needs a measure finite on compact sets,
a compactly supported `C¹` map, and a vanishing area integral. This also applies to restrictions
of volume, as used for the strip identity.

## Main results

* `TauCeti.SymplecticForm.integral_symplecticForm_fderiv_eq_zero`: the symplectic area of a
  compactly supported map from the plane is zero.
* `SymplecticForm.integral_stdComplexLineEnergyDensity_eq_of_integral_symplecticForm_eq_zero`:
  the energy identity for a compactly supported `C¹` map with vanishing area integral, against
  any measure finite on compact sets.
* `TauCeti.SymplecticForm.integral_stdComplexLineEnergyDensity_eq_integral_associatedBilinForm`:
  the energy identity, the integrated energy density of the differential against the integrated
  associated-metric square of the Cauchy--Riemann defect.
* `TauCeti.IsConstStructureJHolomorphic.eq_zero_of_hasCompactSupport`: a compactly supported
  holomorphic plane is zero.
* `TauCeti.SymplecticForm.continuous_stdComplexLineEnergyDensity_toLinearMap` and
  `TauCeti.SymplecticForm.integrable_stdComplexLineEnergyDensity_fderiv`: continuity of the energy
  density in the differential, and integrability of the energy density of a compactly supported
  map.

The convention and the argument follow McDuff--Salamon, *J-holomorphic Curves and Symplectic
Topology*, Section 2.2 (the energy identity `E(u) = ∫ u^*ω + ‖D_J u‖²`).
-/

public section

namespace TauCeti

open MeasureTheory

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}
variable {u : ℝ × ℝ → V} {μ : Measure (ℝ × ℝ)}

/-- The standard energy density is a continuous function of the differential it is evaluated on. -/
theorem continuous_stdComplexLineEnergyDensity_toLinearMap (ω : SymplecticForm V)
    (J : AlmostComplexStructure V) :
    Continuous fun L : (ℝ × ℝ) →L[ℝ] V ↦ ω.stdComplexLineEnergyDensity J L.toLinearMap := by
  have hdiag : ∀ p : ℝ × ℝ, Continuous fun L : (ℝ × ℝ) →L[ℝ] V ↦
      ω.associatedBilinForm J (L p) (L p) := fun p ↦ by
    have hL : Continuous fun L : (ℝ × ℝ) →L[ℝ] V ↦ L p := continuous_id.clm_apply continuous_const
    exact (ω.associatedBilinForm J).toContinuousBilinearMap.continuous₂.comp₂ hL hL
  refine ((hdiag stdComplexLineReal).add (hdiag stdComplexLineImag)).congr fun L ↦ ?_
  simp [stdComplexLineEnergyDensity_def]

/-- The standard energy density of the differential of a compactly supported `C¹` map from the
plane is integrable against any measure that is finite on compact sets. -/
theorem integrable_stdComplexLineEnergyDensity_fderiv [IsFiniteMeasureOnCompacts μ]
    (ω : SymplecticForm V) (J : AlmostComplexStructure V) (hu : ContDiff ℝ 1 u)
    (hsupp : HasCompactSupport u) :
    Integrable (fun z ↦ ω.stdComplexLineEnergyDensity J (fderiv ℝ u z).toLinearMap) μ :=
  Continuous.integrable_of_hasCompactSupport
    ((ω.continuous_stdComplexLineEnergyDensity_toLinearMap J).comp
      (hu.continuous_fderiv (by norm_num)))
    (HasCompactSupport.comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] V ↦
      ω.stdComplexLineEnergyDensity J L.toLinearMap) (hsupp.fderiv (𝕜 := ℝ)) (by simp))

/-- The energy identity for a compactly supported `C¹` map whose symplectic area integral
vanishes. Only invariance of the symplectic form and finiteness of the measure on compact sets
are needed; the measure can in particular be restricted to a domain with boundary. -/
theorem integral_stdComplexLineEnergyDensity_eq_of_integral_symplecticForm_eq_zero
    [IsFiniteMeasureOnCompacts μ] (hinv : ω.Invariant J) (hu : ContDiff ℝ 1 u)
    (hsupp : HasCompactSupport u)
    (hzero : ∫ z, ω (fderiv ℝ u z stdComplexLineReal)
      (fderiv ℝ u z stdComplexLineImag) ∂μ = 0) :
    ∫ z, ω.stdComplexLineEnergyDensity J (fderiv ℝ u z).toLinearMap ∂μ =
      ∫ z, ω.associatedBilinForm J
        (fderiv ℝ u z stdComplexLineReal + J (fderiv ℝ u z stdComplexLineImag))
        (fderiv ℝ u z stdComplexLineReal + J (fderiv ℝ u z stdComplexLineImag)) ∂μ := by
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have harea : Integrable (fun z ↦
      ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) μ :=
    Continuous.integrable_of_hasCompactSupport
      (ω.toBilinForm.toContinuousBilinearMap.continuous₂.comp₂
        (hdu.clm_apply continuous_const) (hdu.clm_apply continuous_const))
      ((hsupp.fderiv (𝕜 := ℝ)).comp_left
        (g := fun L : (ℝ × ℝ) →L[ℝ] V ↦ ω (L stdComplexLineReal) (L stdComplexLineImag))
        (by simp))
  have heq : (∫ z, (ω.stdComplexLineEnergyDensity J (fderiv ℝ u z).toLinearMap -
      2 * ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) ∂μ) =
      ∫ z, ω.associatedBilinForm J
        (fderiv ℝ u z stdComplexLineReal + J (fderiv ℝ u z stdComplexLineImag))
        (fderiv ℝ u z stdComplexLineReal + J (fderiv ℝ u z stdComplexLineImag)) ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦
      stdComplexLineEnergyDensity_sub_two_mul_symplecticForm hinv (fderiv ℝ u z).toLinearMap
  rw [integral_sub (integrable_stdComplexLineEnergyDensity_fderiv ω J hu hsupp)
    (harea.const_mul 2), integral_const_mul, hzero] at heq
  simpa using heq

variable [μ.IsAddHaarMeasure]

/-- **The symplectic area of a compactly supported map from the plane vanishes.** For a compactly
supported `C²` map `u`, the area density `ω(∂s u, ∂t u)` integrates to zero over the whole plane.
Nothing relates `ω` to an almost complex structure here: only that `ω` is alternating is used. -/
@[simp]
theorem integral_symplecticForm_fderiv_eq_zero (ω : SymplecticForm V) (hu : ContDiff ℝ 2 u)
    (hsupp : HasCompactSupport u) :
    ∫ z, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) ∂μ = 0 :=
  integral_bilinForm_fderiv_apply_eq_zero_of_isAlt ω.isAlt hu hsupp _ _

/-- **The energy identity for a compactly supported map.** The integrated standard energy density
of a compactly supported `C²` map from the plane equals the integrated associated-metric square
`g(D u, D u)` of its Cauchy--Riemann defect `D u = ∂s u + J (∂t u)`. This is an equality of
integrals: only `J`-invariance of `ω` is used, not tameness, and without tameness the associated
form `g = ω(·, J ·)` need not be positive, so neither side is a norm. Under tameness it reads
`‖du‖₂ = ‖D u‖₂`, the homogeneous `L²` estimate for the Cauchy--Riemann operator on compactly
supported maps, with constant `1` for this normalization of `D`. -/
theorem integral_stdComplexLineEnergyDensity_eq_integral_associatedBilinForm
    (hinv : ω.Invariant J) (hu : ContDiff ℝ 2 u) (hsupp : HasCompactSupport u) :
    ∫ z, ω.stdComplexLineEnergyDensity J (fderiv ℝ u z).toLinearMap ∂μ =
      ∫ z, ω.associatedBilinForm J
          (fderiv ℝ u z stdComplexLineReal + J (fderiv ℝ u z stdComplexLineImag))
          (fderiv ℝ u z stdComplexLineReal + J (fderiv ℝ u z stdComplexLineImag)) ∂μ :=
  integral_stdComplexLineEnergyDensity_eq_of_integral_symplecticForm_eq_zero
    hinv (hu.of_le (by norm_num)) hsupp (integral_symplecticForm_fderiv_eq_zero ω hu hsupp)

end SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {ω : SymplecticForm V} {J : AlmostComplexStructure V} {u : ℝ × ℝ → V}

/-- A compactly supported `C²` solution of the Cauchy--Riemann equation on the whole plane, with
values in a vector space carrying a symplectic form taming the target structure, is zero: there
are no compactly supported nonconstant holomorphic planes. Tameness is the only hypothesis
relating `ω` to `J`: for a holomorphic map the energy density is twice the area density, which
integrates to zero, and under tameness a vanishing energy density forces a vanishing
differential. -/
theorem IsConstStructureJHolomorphic.eq_zero_of_hasCompactSupport
    (hhol : IsConstStructureJHolomorphic (AlmostComplexStructure.product ℝ) J u)
    (htame : ω.Tames J) (hu : ContDiff ℝ 2 u) (hsupp : HasCompactSupport u) : u = 0 := by
  -- the plane's Lebesgue measure is the product of two copies of Lebesgue measure on the line,
  -- so it is an additive Haar measure
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  -- holomorphicity turns the energy density into twice the area density, which integrates to zero
  have hpt : ∀ z : ℝ × ℝ, ω.stdComplexLineEnergyDensity J (fderiv ℝ u z).toLinearMap =
      2 * ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) := fun z ↦
    hhol.isConstStructureJHolomorphicAt z
      |>.fderiv_stdComplexLineEnergyDensity_eq_two_mul_symplecticForm
  have hzero : ∫ z, ω.stdComplexLineEnergyDensity J (fderiv ℝ u z).toLinearMap ∂volume = 0 := by
    simp only [hpt]
    rw [integral_const_mul, SymplecticForm.integral_symplecticForm_fderiv_eq_zero ω hu hsupp,
      mul_zero]
  -- nonnegativity and continuity upgrade the vanishing integral to a vanishing differential
  have hcont : Continuous fun z ↦ ω.stdComplexLineEnergyDensity J (fderiv ℝ u z).toLinearMap :=
    (ω.continuous_stdComplexLineEnergyDensity_toLinearMap J).comp
      (hu.continuous_fderiv (by norm_num))
  have heq : (fun z ↦ ω.stdComplexLineEnergyDensity J (fderiv ℝ u z).toLinearMap) = 0 :=
    (hcont.ae_eq_iff_eq volume continuous_const).mp
      ((integral_eq_zero_iff_of_nonneg
        (fun z ↦ ω.stdComplexLineEnergyDensity_nonneg htame _)
        (SymplecticForm.integrable_stdComplexLineEnergyDensity_fderiv
          (μ := (volume : Measure (ℝ × ℝ))) ω J (hu.of_le (by norm_num)) hsupp)).mp hzero)
  have hfderiv : ∀ z, fderiv ℝ u z = 0 := fun z ↦
    (ω.stdComplexLineEnergyDensity_toLinearMap_eq_zero_iff htame _).mp (congrFun heq z)
  -- a constant map with compact support on a noncompact space is zero
  have hconst : ∀ z, u z = u 0 := fun z ↦
    is_const_of_fderiv_eq_zero (hu.differentiable (by norm_num)) hfderiv z 0
  have hu0 : u 0 = 0 := by
    by_contra h
    have hsub : (Set.univ : Set (ℝ × ℝ)) ⊆ tsupport u := fun z _ ↦
      subset_closure (by simpa [Function.mem_support, hconst z] using h)
    have hcompact : IsCompact (tsupport u) := hsupp
    exact noncompact_univ (ℝ × ℝ) (Set.eq_univ_of_univ_subset hsub ▸ hcompact)
  exact funext fun z ↦ by simp [hconst z, hu0]

end TauCeti

end

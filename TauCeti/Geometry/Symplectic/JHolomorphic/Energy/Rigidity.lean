/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Integral
public import TauCeti.Geometry.Symplectic.JHolomorphic.Varying
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import TauCeti.Geometry.Symplectic.TameMetric
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Zero-energy rigidity for maps into tame symplectic spaces

A continuously differentiable map from a connected open subset of the standard complex line
with zero energy is constant, provided that the target symplectic form tames its almost complex
structure. The argument uses the pointwise positivity of energy, then continuity of the
differential to upgrade almost-everywhere vanishing to vanishing everywhere. The source measure
may be any measure positive on nonempty open sets.

This is the elementary rigidity input in the compactness theory of holomorphic disks and strips:
nonconstant components must have positive energy. The energy convention is that of
`TauCeti.SymplecticForm.stdComplexLineEnergy`.

For a varying tame target structure, vanishing symplectic area likewise forces a holomorphic
map from a connected open subset of `ℂ` to be constant. No regularity of the structure is
needed. Continuity of the area density is explicit for arbitrary normed targets.

The mathematical argument is standard; see McDuff--Salamon, *J-holomorphic Curves and Symplectic
Topology*, Section 4.1.
-/

public section

namespace TauCeti

open MeasureTheory Set

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}
variable {U : Set (ℝ × ℝ)} {f : ℝ × ℝ → V} {μ : Measure (ℝ × ℝ)}

/-- On a connected open domain, zero energy is equivalent to constancy for a `C¹` map
into a tame almost complex target. The real energy density must be a.e. measurable, as in
`stdComplexLineEnergy_eq_zero_iff`; holomorphicity is not required. -/
theorem stdComplexLineEnergy_eq_zero_iff_exists_eqOn_const [μ.IsOpenPosMeasure]
    (hU : IsOpen U) (hconn : IsPreconnected U) (hf : ContDiffOn ℝ 1 f U)
    (htame : ω.Tames J)
    (hmeas : AEMeasurable
      (fun x ↦ ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap) (μ.restrict U)) :
    ω.stdComplexLineEnergy J (fun x ↦ (fderiv ℝ f x).toLinearMap)
      (μ.restrict U) = 0 ↔ ∃ c : V, ∀ x ∈ U, f x = c := by
  constructor
  · intro henergy
    have hae := (ω.stdComplexLineEnergy_eq_zero_iff htame hmeas).mp henergy
    have hderiv_ae : (fderiv ℝ f) =ᵐ[μ.restrict U] 0 := by
      filter_upwards [hae] with x hx
      apply ContinuousLinearMap.ext
      intro v
      have hv := congrArg (fun L : (ℝ × ℝ) →ₗ[ℝ] V ↦ L v) hx
      simpa using hv
    have hderiv : EqOn (fderiv ℝ f) 0 U :=
      μ.eqOn_open_of_ae_eq hderiv_ae hU
        (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)) continuousOn_const
    exact hU.exists_is_const_of_fderiv_eq_zero hconn hf.differentiableOn_one hderiv
  · rintro ⟨c, hc⟩
    have hzero : ∀ x ∈ U, fderiv ℝ f x = 0 := by
      intro x hx
      have hevent : f =ᶠ[nhds x] fun _ ↦ c := by
        filter_upwards [hU.mem_nhds hx] with y hy using hc y hy
      rw [hevent.fderiv_eq]
      simp
    apply ω.stdComplexLineEnergy_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    simp [hzero x hx]

/-- A nonconstant `C¹` map on a connected open domain has strictly positive energy when its
target form tames the almost complex structure. -/
theorem stdComplexLineEnergy_pos_of_ne [μ.IsOpenPosMeasure]
    (hU : IsOpen U) (hconn : IsPreconnected U) (hf : ContDiffOn ℝ 1 f U)
    (htame : ω.Tames J)
    (hmeas : AEMeasurable
      (fun x ↦ ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap) (μ.restrict U))
    {x y : ℝ × ℝ} (hx : x ∈ U) (hy : y ∈ U) (hxy : f x ≠ f y) :
    0 < ω.stdComplexLineEnergy J (fun z ↦ (fderiv ℝ f z).toLinearMap)
      (μ.restrict U) := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  obtain ⟨c, hc⟩ :=
    (ω.stdComplexLineEnergy_eq_zero_iff_exists_eqOn_const hU hconn hf htame hmeas).mp hzero
  exact hxy ((hc x hx).trans (hc y hy).symm)

/-- A holomorphic map on a connected open subset of `ℂ` with zero symplectic area is
constant. The target structure may vary, and needs only to be tamed at the image points.
The measure must be positive on nonempty open sets, and integrability of the area density
is explicit so a divergent integral cannot count as zero. Continuity of the area density
is assumed explicitly, allowing arbitrary real normed targets. -/
theorem exists_eqOn_const_of_integral_eq_zero_of_continuousOn
    {ν : Measure ℂ} [ν.IsOpenPosMeasure]
    {U : Set ℂ} {u : ℂ → V} {J : V → AlmostComplexStructure V}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hhol : ∀ z ∈ U,
      IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.ofComplexModule ℂ) J u z)
    (htame : ∀ z ∈ U, ω.Tames (J (u z)))
    (hcont : ContinuousOn (fun z ↦ ω (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I)) U)
    (hint : IntegrableOn (fun z ↦ ω (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I)) U ν)
    (hzero : ∫ z in U, ω (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I) ∂ν = 0) :
    ∃ c : V, EqOn u (fun _ ↦ c) U := by
  have hCR (z : ℂ) (hz : z ∈ U) :
      fderiv ℝ u z Complex.I = J (u z) (fderiv ℝ u z 1) := by
    simpa [AlmostComplexStructure.ofComplexModule_apply] using
      (hhol z hz).fderiv_apply_commute (v := 1)
  -- Positivity of the area density turns zero total area into a.e. vanishing.
  have hnonneg : ∀ z ∈ U, 0 ≤ ω (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I) := by
    intro z hz
    rw [hCR z hz]
    exact (htame z hz).symplecticForm_apply_apply_self_nonneg (fderiv ℝ u z 1)
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (ae_restrict_of_forall_mem hU.measurableSet hnonneg) hint).mp hzero
  -- Continuity upgrades vanishing to every point of the open domain.
  have harea := ν.eqOn_open_of_ae_eq hae hU hcont continuousOn_const
  have hderiv : EqOn (fderiv ℝ u) 0 U := by
    intro z hz
    have hone : fderiv ℝ u z 1 = 0 := by
      by_contra h
      have hpos := htame z hz _ h
      have harea' : ω (fderiv ℝ u z 1) (fderiv ℝ u z Complex.I) = 0 := harea hz
      rw [← hCR z hz, harea'] at hpos
      exact lt_irrefl 0 hpos
    have hI : fderiv ℝ u z Complex.I = 0 := by simp [hCR z hz, hone]
    apply ContinuousLinearMap.ext
    intro w
    simp only [Pi.zero_apply, zero_apply]
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      simp [Complex.real_smul, Complex.re_add_im]
    rw [hw]
    simp only [map_add, map_smul, hone, hI, smul_zero, add_zero]
  exact hU.exists_is_const_of_fderiv_eq_zero hconn
    (fun z hz ↦ (hhol z hz).differentiableAt.differentiableWithinAt) hderiv

end SymplecticForm

end TauCeti

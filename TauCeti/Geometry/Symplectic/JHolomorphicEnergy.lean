/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.JHolomorphicLine
public import TauCeti.Geometry.Symplectic.Prod

/-!
# Pointwise energy density for maps from the standard complex line

This file adds the first pointwise energy-density bookkeeping for the analytic Heegaard Floer
roadmap. For a compatible pair `(ω, J)`, the associated metric is
`g(v, w) = ω(v, J w)`. If a real-linear map `F : ℝ × ℝ → V` is complex-linear, then the
standard energy density
`g(F ∂s, F ∂s) + g(F ∂t, F ∂t)` is twice the symplectic area density
`ω(F ∂s, F ∂t)`.

Under a taming symplectic form the density is moreover nondegenerate: it is nonnegative for every
real-linear map, vanishes exactly for the zero map, and is positive otherwise. The
Frechet-derivative versions specialize this to pointwise and within-set `J`-holomorphic maps.

The statements here are still pointwise linear algebra and Frechet-derivative calculus. They are
the local identities that the later holomorphic-curve energy theory will integrate over strips
or disks.

## Main declarations

* `TauCeti.SymplecticForm.stdComplexLineEnergyDensity`: the metric energy density of a
  real-linear map from the standard complex line.
* `TauCeti.IsComplexLinearMap.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm`:
  for a complex-linear map, energy density is twice symplectic area density.
* `TauCeti.IsJHolomorphicAt.fderiv_stdComplexLineEnergyDensity_eq_two_mul_symplecticForm`:
  the corresponding Frechet-derivative statement for a pointwise `J`-holomorphic map.
* `TauCeti.SymplecticForm.stdComplexLineEnergyDensity_pos` and
  `TauCeti.SymplecticForm.stdComplexLineEnergyDensity_eq_zero_iff`: nondegeneracy of the density
  under tameness, with `TauCeti.IsJHolomorphicAt.fderiv_stdComplexLineEnergyDensity_eq_zero_iff`
  and `TauCeti.IsJHolomorphicWithinAt.fderivWithin_stdComplexLineEnergyDensity_eq_zero_iff` the
  Frechet-derivative versions.
* `TauCeti.SymplecticForm.prod_stdComplexLineEnergyDensity`: product-target energy density is
  the sum of the factor energy densities.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: for a compatible pair, `g(·, ·) = ω(·, J ·)` and `du(∂t) = J du(∂s)`.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {J : AlmostComplexStructure V}
variable {ω : SymplecticForm V}

/-- The pointwise metric energy density of a real-linear map from the standard complex line.

For a compatible pair `(ω, J)`, this is
`g(F ∂s, F ∂s) + g(F ∂t, F ∂t)`, where `g(v,w) = ω(v, J w)`. -/
irreducible_def stdComplexLineEnergyDensity (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) : ℝ :=
  ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) +
    ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag)

attribute [simp] stdComplexLineEnergyDensity_def

/-- The standard pointwise energy density of any real-linear map is nonnegative under tameness. -/
lemma stdComplexLineEnergyDensity_nonneg (hω : ω.Tames J)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    0 ≤ ω.stdComplexLineEnergyDensity J F := by
  rw [stdComplexLineEnergyDensity_def]
  refine add_nonneg ?_ ?_
  · rw [associatedBilinForm_apply]
    by_cases h : F stdComplexLineReal = 0
    · simp [h]
    · exact (hω (F stdComplexLineReal) h).le
  · rw [associatedBilinForm_apply]
    by_cases h : F stdComplexLineImag = 0
    · simp [h]
    · exact (hω (F stdComplexLineImag) h).le

/-- Under tameness, the standard pointwise energy density of a nonzero real-linear map from the
standard complex line is positive. -/
lemma stdComplexLineEnergyDensity_pos (hω : ω.Tames J) {F : (ℝ × ℝ) →ₗ[ℝ] V}
    (hFne : F ≠ 0) :
    0 < ω.stdComplexLineEnergyDensity J F := by
  rw [stdComplexLineEnergyDensity_def]
  by_cases hreal : F stdComplexLineReal = 0
  · have himag : F stdComplexLineImag ≠ 0 := by
      intro himag
      apply hFne
      apply LinearMap.ext
      intro z
      rw [LinearMap.apply_stdComplexLine F z, hreal, himag]
      simp
    exact add_pos_of_nonneg_of_pos
      (by simp [hreal])
      (by simpa [associatedBilinForm_apply] using hω (F stdComplexLineImag) himag)
  · exact add_pos_of_pos_of_nonneg
      (by simpa [associatedBilinForm_apply] using hω (F stdComplexLineReal) hreal)
      (by
        rw [associatedBilinForm_apply]
        by_cases himag : F stdComplexLineImag = 0
        · simp [himag]
        · exact (hω (F stdComplexLineImag) himag).le)

/-- Under tameness, standard pointwise energy density vanishes exactly for the zero real-linear
map from the standard complex line. -/
@[simp]
lemma stdComplexLineEnergyDensity_eq_zero_iff (hω : ω.Tames J)
    {F : (ℝ × ℝ) →ₗ[ℝ] V} :
    ω.stdComplexLineEnergyDensity J F = 0 ↔ F = 0 := by
  constructor
  · intro henergy
    rw [stdComplexLineEnergyDensity_def] at henergy
    have hreal_nonneg :
        0 ≤ ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) := by
      rw [associatedBilinForm_apply]
      by_cases hreal : F stdComplexLineReal = 0
      · simp [hreal]
      · exact (hω (F stdComplexLineReal) hreal).le
    have himag_nonneg :
        0 ≤ ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag) := by
      rw [associatedBilinForm_apply]
      by_cases himag : F stdComplexLineImag = 0
      · simp [himag]
      · exact (hω (F stdComplexLineImag) himag).le
    have hreal_zero :
        ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) = 0 := by
      linarith
    have himag_zero :
        ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag) = 0 := by
      linarith
    have hreal : F stdComplexLineReal = 0 :=
      (associatedBilinForm_self_eq_zero ((ω.tames_iff_associated_pos J).mp hω)).mp hreal_zero
    have himag : F stdComplexLineImag = 0 :=
      (associatedBilinForm_self_eq_zero ((ω.tames_iff_associated_pos J).mp hω)).mp himag_zero
    apply LinearMap.ext
    intro z
    rw [LinearMap.apply_stdComplexLine F z, hreal, himag]
    simp
  · intro hzero
    simp [hzero]

/-- Under tameness, the standard pointwise energy density is positive exactly for nonzero
real-linear maps from the standard complex line. -/
lemma stdComplexLineEnergyDensity_pos_iff (hω : ω.Tames J) {F : (ℝ × ℝ) →ₗ[ℝ] V} :
    0 < ω.stdComplexLineEnergyDensity J F ↔ F ≠ 0 := by
  constructor
  · intro hpos hzero
    exact hpos.ne' ((ω.stdComplexLineEnergyDensity_eq_zero_iff (J := J) hω).mpr hzero)
  · exact ω.stdComplexLineEnergyDensity_pos hω

section Prod

variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W}
variable {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W}

/-- The standard-line energy density of a real-linear map into a direct-sum target is the sum of
the two factor energy densities of its coordinate projections. -/
@[simp]
lemma prod_stdComplexLineEnergyDensity (F : (ℝ × ℝ) →ₗ[ℝ] V × W) :
    (ω₁.prod ω₂).stdComplexLineEnergyDensity (J₁.prod J₂) F =
      ω₁.stdComplexLineEnergyDensity J₁ ((LinearMap.fst ℝ V W).comp F) +
        ω₂.stdComplexLineEnergyDensity J₂ ((LinearMap.snd ℝ V W).comp F) := by
  simp only [stdComplexLineEnergyDensity_def, prod_associatedBilinForm_apply,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply]
  ring_nf

end Prod

end SymplecticForm

namespace IsComplexLinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {F : (ℝ × ℝ) →ₗ[ℝ] V}

/-- For a complex-linear map out of the standard complex line, the associated-bilinear-form
diagonal of the imaginary-coordinate image equals that of the real-coordinate image. -/
lemma associatedBilinForm_apply_stdComplexLineImag_self_eq
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag) =
      ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) := by
  simpa [AlmostComplexStructure.product_apply_stdComplexLineReal, stdComplexLineImag] using
    hF.associatedBilinForm_apply_apply_self_eq stdComplexLineReal

/-- For a complex-linear map out of the standard complex line, the real-coordinate
associated-bilinear-form diagonal is the symplectic area density of the ordered coordinate
pair. -/
lemma associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) =
      ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  simpa [AlmostComplexStructure.product_apply_stdComplexLineReal, stdComplexLineImag] using
    hF.associatedBilinForm_apply_self_eq_symplecticForm stdComplexLineReal

/-- For a complex-linear map out of the standard complex line, the standard pointwise energy
density is twice the symplectic area density. -/
lemma stdComplexLineEnergyDensity_eq_two_mul_symplecticForm
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    ω.stdComplexLineEnergyDensity J F =
      2 * ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  rw [SymplecticForm.stdComplexLineEnergyDensity_def,
    hF.associatedBilinForm_apply_stdComplexLineImag_self_eq,
    hF.associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm]
  ring

end IsComplexLinearMap

namespace IsJHolomorphicAt

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {f : ℝ × ℝ → V} {x : ℝ × ℝ}

/-- For a pointwise `J`-holomorphic map from the standard complex line, the
associated-bilinear-form diagonal of the `∂t` derivative equals that of the `∂s` derivative. -/
lemma associatedBilinForm_fderiv_stdComplexLineImag_self_eq
    (hf : IsJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) :
    ω.associatedBilinForm J (fderiv ℝ f x stdComplexLineImag)
        (fderiv ℝ f x stdComplexLineImag) =
      ω.associatedBilinForm J (fderiv ℝ f x stdComplexLineReal)
        (fderiv ℝ f x stdComplexLineReal) :=
  hf.fderiv_isComplexLinear.associatedBilinForm_apply_stdComplexLineImag_self_eq

/-- For a pointwise `J`-holomorphic map from the standard complex line, the `∂s`
associated-bilinear-form diagonal is the symplectic area density `ω(∂s u, ∂t u)`. -/
lemma associatedBilinForm_fderiv_stdComplexLineReal_self_eq_symplecticForm
    (hf : IsJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) :
    ω.associatedBilinForm J (fderiv ℝ f x stdComplexLineReal)
        (fderiv ℝ f x stdComplexLineReal) =
      ω (fderiv ℝ f x stdComplexLineReal) (fderiv ℝ f x stdComplexLineImag) :=
  hf.fderiv_isComplexLinear.associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm

/-- For a pointwise `J`-holomorphic map from the standard complex line, the derivative's
standard energy density is twice its symplectic area density. -/
lemma fderiv_stdComplexLineEnergyDensity_eq_two_mul_symplecticForm
    (hf : IsJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) :
    ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap =
      2 * ω (fderiv ℝ f x stdComplexLineReal) (fderiv ℝ f x stdComplexLineImag) :=
  hf.fderiv_isComplexLinear.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm

/-- The derivative's standard pointwise energy density is nonnegative under tameness. -/
lemma fderiv_stdComplexLineEnergyDensity_nonneg (hω : ω.Tames J) :
    0 ≤ ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap :=
  ω.stdComplexLineEnergyDensity_nonneg hω (fderiv ℝ f x).toLinearMap

/-- Under tameness, the derivative standard energy density of a map from the standard complex line
vanishes exactly when its Frechet derivative is zero. -/
@[simp]
lemma fderiv_stdComplexLineEnergyDensity_eq_zero_iff (hω : ω.Tames J) :
    ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap = 0 ↔ fderiv ℝ f x = 0 := by
  constructor
  · intro henergy
    have hlin :
        (fderiv ℝ f x).toLinearMap = 0 :=
      (ω.stdComplexLineEnergyDensity_eq_zero_iff hω).mp henergy
    exact ContinuousLinearMap.ext fun z => LinearMap.congr_fun hlin z
  · intro hzero
    exact (ω.stdComplexLineEnergyDensity_eq_zero_iff hω).mpr (by simp [hzero])

/-- Under tameness, the derivative standard energy density of a map from the standard complex
line is positive exactly when its Frechet derivative is nonzero. -/
lemma fderiv_stdComplexLineEnergyDensity_pos_iff (hω : ω.Tames J) :
    0 < ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap ↔ fderiv ℝ f x ≠ 0 := by
  constructor
  · intro hpos hzero
    exact hpos.ne' ((fderiv_stdComplexLineEnergyDensity_eq_zero_iff
      (ω := ω) (J := J) (f := f) (x := x) hω).mpr hzero)
  · intro hne
    exact (ω.stdComplexLineEnergyDensity_pos_iff hω).mpr fun hlin =>
      hne (ContinuousLinearMap.ext fun z => LinearMap.congr_fun hlin z)

/-- Under tameness, a map with nonzero Frechet derivative has positive standard derivative energy
density. -/
lemma fderiv_stdComplexLineEnergyDensity_pos (hω : ω.Tames J)
    (hfderiv : fderiv ℝ f x ≠ 0) :
    0 < ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap :=
  (fderiv_stdComplexLineEnergyDensity_pos_iff (ω := ω) (J := J) (f := f) (x := x) hω).mpr
    hfderiv

end IsJHolomorphicAt

namespace IsJHolomorphicWithinAt

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {f : ℝ × ℝ → V} {s : Set (ℝ × ℝ)} {x : ℝ × ℝ}

/-- For a within-set `J`-holomorphic map from the standard complex line, the
associated-bilinear-form diagonal of the `∂t` derivative equals that of the `∂s` derivative,
provided derivatives within the set are unique. -/
lemma associatedBilinForm_fderivWithin_stdComplexLineImag_self_eq
    (hf : IsJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J f s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    ω.associatedBilinForm J (fderivWithin ℝ f s x stdComplexLineImag)
        (fderivWithin ℝ f s x stdComplexLineImag) =
      ω.associatedBilinForm J (fderivWithin ℝ f s x stdComplexLineReal)
        (fderivWithin ℝ f s x stdComplexLineReal) :=
  (hf.fderivWithin_isComplexLinear hs).associatedBilinForm_apply_stdComplexLineImag_self_eq

/-- For a within-set `J`-holomorphic map from the standard complex line, the `∂s`
associated-bilinear-form diagonal is the symplectic area density `ω(∂s u, ∂t u)`,
provided derivatives within the set are unique. -/
lemma associatedBilinForm_fderivWithin_stdComplexLineReal_self_eq_symplecticForm
    (hf : IsJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J f s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    ω.associatedBilinForm J (fderivWithin ℝ f s x stdComplexLineReal)
        (fderivWithin ℝ f s x stdComplexLineReal) =
      ω (fderivWithin ℝ f s x stdComplexLineReal)
        (fderivWithin ℝ f s x stdComplexLineImag) :=
  by
    have hlin := hf.fderivWithin_isComplexLinear hs
    exact hlin.associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm

/-- For a within-set `J`-holomorphic map from the standard complex line, the derivative's
standard energy density is twice its symplectic area density, provided derivatives within the
set are unique. -/
lemma fderivWithin_stdComplexLineEnergyDensity_eq_two_mul_symplecticForm
    (hf : IsJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J f s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap =
      2 * ω (fderivWithin ℝ f s x stdComplexLineReal)
        (fderivWithin ℝ f s x stdComplexLineImag) :=
  (hf.fderivWithin_isComplexLinear hs).stdComplexLineEnergyDensity_eq_two_mul_symplecticForm

/-- The within-set derivative's standard pointwise energy density is nonnegative under tameness. -/
lemma fderivWithin_stdComplexLineEnergyDensity_nonneg (hω : ω.Tames J) :
    0 ≤ ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap :=
  ω.stdComplexLineEnergyDensity_nonneg hω (fderivWithin ℝ f s x).toLinearMap

/-- Under tameness, the within-set derivative standard energy density of a map from the standard
complex line vanishes exactly when its Frechet derivative within the set is zero. -/
@[simp]
lemma fderivWithin_stdComplexLineEnergyDensity_eq_zero_iff (hω : ω.Tames J) :
    ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap = 0 ↔
      fderivWithin ℝ f s x = 0 := by
  constructor
  · intro henergy
    have hlin :
        (fderivWithin ℝ f s x).toLinearMap = 0 :=
      (ω.stdComplexLineEnergyDensity_eq_zero_iff hω).mp henergy
    exact ContinuousLinearMap.ext fun z => LinearMap.congr_fun hlin z
  · intro hzero
    exact (ω.stdComplexLineEnergyDensity_eq_zero_iff hω).mpr (by simp [hzero])

/-- Under tameness, the within-set derivative standard energy density is positive exactly when
the Frechet derivative within the set is nonzero. -/
lemma fderivWithin_stdComplexLineEnergyDensity_pos_iff (hω : ω.Tames J) :
    0 < ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap ↔
      fderivWithin ℝ f s x ≠ 0 := by
  constructor
  · intro hpos hzero
    exact hpos.ne'
      ((fderivWithin_stdComplexLineEnergyDensity_eq_zero_iff
        (ω := ω) (J := J) (f := f) (s := s) (x := x) hω).mpr hzero)
  · intro hne
    exact (ω.stdComplexLineEnergyDensity_pos_iff hω).mpr fun hlin =>
      hne (ContinuousLinearMap.ext fun z => LinearMap.congr_fun hlin z)

/-- Under tameness, a map with nonzero Frechet derivative within a set has positive standard
derivative energy density. -/
lemma fderivWithin_stdComplexLineEnergyDensity_pos (hω : ω.Tames J)
    (hfderiv : fderivWithin ℝ f s x ≠ 0) :
    0 < ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap :=
  (fderivWithin_stdComplexLineEnergyDensity_pos_iff
    (ω := ω) (J := J) (f := f) (s := s) (x := x) hω).mpr hfderiv

end IsJHolomorphicWithinAt

end TauCeti

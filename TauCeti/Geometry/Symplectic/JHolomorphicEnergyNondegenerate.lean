/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphicEnergy

/-!
# Nondegeneracy of the standard complex-line energy density

This file adds the pointwise nondegeneracy API for the standard complex-line energy density
used by the analytic Heegaard Floer roadmap. For a map out of the standard complex line, a
complex-linear derivative is determined by its real-coordinate value. Under a taming symplectic
form, the standard energy density is therefore positive exactly when that derivative is nonzero,
and vanishes exactly for the zero derivative.

The statements are still local linear algebra and Frechet-derivative calculus. They are the
pointwise facts later integrated in the holomorphic-curve energy theory of
`TauCetiRoadmap/HeegaardFloer/README.md`, Lane F2.1.

## Main declarations

* `TauCeti.IsComplexLinearMap.stdComplexLineEnergyDensity_pos`: positivity of the standard
  energy density for a nonzero complex-linear map out of the standard complex line.
* `TauCeti.IsComplexLinearMap.stdComplexLineEnergyDensity_eq_zero_iff`: the corresponding
  zero-characterization.
* `TauCeti.IsJHolomorphicAt.fderiv_stdComplexLineEnergyDensity_eq_zero_iff` and
  `TauCeti.IsJHolomorphicWithinAt.fderivWithin_stdComplexLineEnergyDensity_eq_zero_iff`:
  derivative versions for `J`-holomorphic maps.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: the standard complex line is `ℝ × ℝ` with complex structure
`(s, t) ↦ (-t, s)`, and `du(∂t) = J du(∂s)` for a `J`-holomorphic map.
-/

public section

namespace TauCeti

namespace IsComplexLinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {F : (ℝ × ℝ) →ₗ[ℝ] V}

/-- A complex-linear map from the standard complex line is zero exactly when its real-coordinate
value is zero. -/
@[simp]
lemma eq_zero_iff_apply_stdComplexLineReal
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    F = 0 ↔ F stdComplexLineReal = 0 := by
  constructor
  · intro h
    simp [h]
  · intro hreal
    apply LinearMap.ext
    intro z
    rw [hF.apply_stdComplexLine z, hreal]
    simp

/-- The real-coordinate value of a nonzero complex-linear map from the standard complex line is
nonzero. -/
lemma apply_stdComplexLineReal_ne_zero
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (hFne : F ≠ 0) :
    F stdComplexLineReal ≠ 0 := by
  exact fun hreal => hFne ((hF.eq_zero_iff_apply_stdComplexLineReal).mpr hreal)

/-- Under tameness, the standard pointwise energy density of a nonzero complex-linear map from
the standard complex line is positive. -/
lemma stdComplexLineEnergyDensity_pos
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (hω : ω.Tames J)
    (hFne : F ≠ 0) :
    0 < ω.stdComplexLineEnergyDensity J F := by
  rw [hF.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm]
  exact mul_pos two_pos
    (hF.symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_pos hω
      (hF.apply_stdComplexLineReal_ne_zero hFne))

/-- For a complex-linear map from the standard complex line, standard pointwise energy density
vanishes under tameness exactly for the zero map. -/
@[simp]
lemma stdComplexLineEnergyDensity_eq_zero_iff
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (hω : ω.Tames J) :
    ω.stdComplexLineEnergyDensity J F = 0 ↔ F = 0 := by
  constructor
  · intro henergy
    by_contra hFne
    exact (hF.stdComplexLineEnergyDensity_pos hω hFne).ne' henergy
  · intro hzero
    rw [hF.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm]
    simp [hzero]

/-- Under tameness, the standard pointwise energy density is positive exactly for nonzero
complex-linear maps from the standard complex line. -/
lemma stdComplexLineEnergyDensity_pos_iff
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (hω : ω.Tames J) :
    0 < ω.stdComplexLineEnergyDensity J F ↔ F ≠ 0 := by
  constructor
  · intro hpos hzero
    exact hpos.ne' ((hF.stdComplexLineEnergyDensity_eq_zero_iff hω).mpr hzero)
  · exact hF.stdComplexLineEnergyDensity_pos hω

end IsComplexLinearMap

namespace IsJHolomorphicAt

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {f : ℝ × ℝ → V} {x : ℝ × ℝ}

/-- Under tameness, the derivative standard energy density of a pointwise `J`-holomorphic map
vanishes exactly when its Frechet derivative is zero. -/
@[simp]
lemma fderiv_stdComplexLineEnergyDensity_eq_zero_iff
    (hf : IsJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) (hω : ω.Tames J) :
    ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap = 0 ↔ fderiv ℝ f x = 0 := by
  constructor
  · intro henergy
    have hlin :
        (fderiv ℝ f x).toLinearMap = 0 :=
      (hf.fderiv_isComplexLinear.stdComplexLineEnergyDensity_eq_zero_iff hω).mp henergy
    exact ContinuousLinearMap.ext fun z => LinearMap.congr_fun hlin z
  · intro hzero
    exact (hf.fderiv_isComplexLinear.stdComplexLineEnergyDensity_eq_zero_iff hω).mpr
      (by simp [hzero])

/-- Under tameness, the derivative standard energy density of a pointwise `J`-holomorphic map is
positive exactly when its Frechet derivative is nonzero. -/
lemma fderiv_stdComplexLineEnergyDensity_pos_iff
    (hf : IsJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) (hω : ω.Tames J) :
    0 < ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap ↔ fderiv ℝ f x ≠ 0 := by
  constructor
  · intro hpos hzero
    exact hpos.ne' ((hf.fderiv_stdComplexLineEnergyDensity_eq_zero_iff hω).mpr hzero)
  · intro hne
    refine lt_of_le_of_ne
      (fderiv_stdComplexLineEnergyDensity_nonneg (ω := ω) (f := f) (x := x) hω) ?_
    exact fun hzero =>
      hne ((hf.fderiv_stdComplexLineEnergyDensity_eq_zero_iff hω).mp hzero.symm)

/-- Under tameness, a pointwise `J`-holomorphic map with nonzero Frechet derivative has positive
standard derivative energy density. -/
lemma fderiv_stdComplexLineEnergyDensity_pos
    (hf : IsJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) (hω : ω.Tames J)
    (hfderiv : fderiv ℝ f x ≠ 0) :
    0 < ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap :=
  (hf.fderiv_stdComplexLineEnergyDensity_pos_iff hω).mpr hfderiv

end IsJHolomorphicAt

namespace IsJHolomorphicWithinAt

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {f : ℝ × ℝ → V} {s : Set (ℝ × ℝ)} {x : ℝ × ℝ}

/-- Under tameness, the within-set derivative standard energy density of a `J`-holomorphic map
vanishes exactly when its Frechet derivative within the set is zero, provided derivatives within
the set are unique. -/
@[simp]
lemma fderivWithin_stdComplexLineEnergyDensity_eq_zero_iff
    (hf : IsJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J f s x)
    (hunique : UniqueDiffWithinAt ℝ s x) (hω : ω.Tames J) :
    ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap = 0 ↔
      fderivWithin ℝ f s x = 0 := by
  constructor
  · intro henergy
    have hlin :
        (fderivWithin ℝ f s x).toLinearMap = 0 :=
      ((hf.fderivWithin_isComplexLinear hunique).stdComplexLineEnergyDensity_eq_zero_iff hω).mp
        henergy
    exact ContinuousLinearMap.ext fun z => LinearMap.congr_fun hlin z
  · intro hzero
    exact ((hf.fderivWithin_isComplexLinear hunique).stdComplexLineEnergyDensity_eq_zero_iff hω).mpr
      (by simp [hzero])

/-- Under tameness, the within-set derivative standard energy density is positive exactly when
the Frechet derivative within the set is nonzero, provided derivatives within the set are
unique. -/
lemma fderivWithin_stdComplexLineEnergyDensity_pos_iff
    (hf : IsJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J f s x)
    (hunique : UniqueDiffWithinAt ℝ s x) (hω : ω.Tames J) :
    0 < ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap ↔
      fderivWithin ℝ f s x ≠ 0 := by
  constructor
  · intro hpos hzero
    exact hpos.ne'
      ((hf.fderivWithin_stdComplexLineEnergyDensity_eq_zero_iff hunique hω).mpr hzero)
  · intro hne
    refine lt_of_le_of_ne
      (fderivWithin_stdComplexLineEnergyDensity_nonneg (ω := ω) (f := f) (s := s) (x := x) hω)
      ?_
    exact fun hzero =>
      hne ((hf.fderivWithin_stdComplexLineEnergyDensity_eq_zero_iff hunique hω).mp hzero.symm)

/-- Under tameness, a within-set `J`-holomorphic map with nonzero Frechet derivative within the
set has positive standard derivative energy density, provided derivatives within the set are
unique. -/
lemma fderivWithin_stdComplexLineEnergyDensity_pos
    (hf : IsJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J f s x)
    (hunique : UniqueDiffWithinAt ℝ s x) (hω : ω.Tames J)
    (hfderiv : fderivWithin ℝ f s x ≠ 0) :
    0 < ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap :=
  (hf.fderivWithin_stdComplexLineEnergyDensity_pos_iff hunique hω).mpr hfderiv

end IsJHolomorphicWithinAt

end TauCeti

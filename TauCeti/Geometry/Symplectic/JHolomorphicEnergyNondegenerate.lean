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

* `TauCeti.SymplecticForm.stdComplexLineEnergyDensity_pos`: positivity of the standard energy
  density for a nonzero real-linear map out of the standard complex line.
* `TauCeti.SymplecticForm.stdComplexLineEnergyDensity_eq_zero_iff`: the corresponding
  zero-characterization.
* `TauCeti.IsJHolomorphicAt.fderiv_stdComplexLineEnergyDensity_eq_zero_iff` and
  `TauCeti.IsJHolomorphicWithinAt.fderivWithin_stdComplexLineEnergyDensity_eq_zero_iff`:
  derivative versions for Frechet derivatives.

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

/-- Under tameness, the standard pointwise energy density of a nonzero complex-linear map from
the standard complex line is positive. -/
lemma stdComplexLineEnergyDensity_pos
    (_hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (hω : ω.Tames J)
    (hFne : F ≠ 0) :
    0 < ω.stdComplexLineEnergyDensity J F :=
  ω.stdComplexLineEnergyDensity_pos hω hFne

/-- For a complex-linear map from the standard complex line, standard pointwise energy density
vanishes under tameness exactly for the zero map. -/
@[simp]
lemma stdComplexLineEnergyDensity_eq_zero_iff
    (_hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (hω : ω.Tames J) :
    ω.stdComplexLineEnergyDensity J F = 0 ↔ F = 0 :=
  ω.stdComplexLineEnergyDensity_eq_zero_iff hω

/-- Under tameness, the standard pointwise energy density is positive exactly for nonzero
complex-linear maps from the standard complex line. -/
lemma stdComplexLineEnergyDensity_pos_iff
    (_hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (hω : ω.Tames J) :
    0 < ω.stdComplexLineEnergyDensity J F ↔ F ≠ 0 :=
  ω.stdComplexLineEnergyDensity_pos_iff hω

end IsComplexLinearMap

namespace IsJHolomorphicAt

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {f : ℝ × ℝ → V} {x : ℝ × ℝ}

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

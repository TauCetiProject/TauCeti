/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphicLine

/-!
# Source rotations of the standard complex line

This file records the first reparametrization facts for real-linear maps from the standard
complex line. Precomposing `F : ℝ × ℝ →ₗ[ℝ] V` by the standard source almost complex structure
is the quarter-turn `(∂s, ∂t) ↦ (∂t, -∂s)`, recorded here as coordinate formulas together with
its effect on the oriented symplectic area density `ω(F ∂s, F ∂t)`. Preservation and reflection
of the Cauchy--Riemann condition, and the area-density invariance, hold for an arbitrary source
almost complex structure and are stated generally in `AlmostComplex.lean`; this file only
specialises the area-density fact to the standard-line coordinates.

These are pointwise linear-algebra statements, not a global reparametrization theorem for
curves. They are the local bookkeeping needed before the analytic Heegaard Floer roadmap's disk
and strip energy theory, where domain rotations and coordinate changes should not change the
local holomorphicity or area-density convention.

## Main declarations

* `TauCeti.LinearMap.comp_stdComplexLineProduct_apply_stdComplexLineReal` and
  `TauCeti.LinearMap.comp_stdComplexLineProduct_apply_stdComplexLineImag`: coordinate formulas for
  the source quarter-turn.
* `TauCeti.SymplecticForm.symplecticForm_comp_stdComplexLineProduct`: the ordered area density is
  unchanged by this source quarter-turn.

The sign convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: the standard source complex structure sends `∂s` to `∂t`.
-/

public section

namespace TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

namespace LinearMap

/-- Precomposing a standard-line linear map by the source complex structure sends the real
coordinate vector to the old imaginary coordinate vector. -/
@[simp]
lemma comp_stdComplexLineProduct_apply_stdComplexLineReal (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    (F.comp (AlmostComplexStructure.product ℝ).toLinearMap) stdComplexLineReal =
      F stdComplexLineImag := by
  simpa [LinearMap.comp_apply] using
    congrArg F AlmostComplexStructure.product_apply_stdComplexLineReal

/-- Precomposing a standard-line linear map by the source complex structure sends the imaginary
coordinate vector to the negative of the old real coordinate vector. -/
@[simp]
lemma comp_stdComplexLineProduct_apply_stdComplexLineImag (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    (F.comp (AlmostComplexStructure.product ℝ).toLinearMap) stdComplexLineImag =
      -F stdComplexLineReal := by
  calc
    (F.comp (AlmostComplexStructure.product ℝ).toLinearMap) stdComplexLineImag =
        F (AlmostComplexStructure.product ℝ stdComplexLineImag) := rfl
    _ = F (-stdComplexLineReal) := by rw [AlmostComplexStructure.product_apply_stdComplexLineImag]
    _ = -F stdComplexLineReal := by rw [map_neg]

end LinearMap

namespace SymplecticForm

variable {ω : SymplecticForm V}

/-- The ordered area density is unchanged after precomposing by the standard source complex
structure. This specialises `symplecticForm_comp_almostComplexStructure` to the standard-line
coordinates. -/
lemma symplecticForm_comp_stdComplexLineProduct (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    ω ((F.comp (AlmostComplexStructure.product ℝ).toLinearMap) stdComplexLineReal)
        ((F.comp (AlmostComplexStructure.product ℝ).toLinearMap) stdComplexLineImag) =
      ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  have h := ω.symplecticForm_comp_almostComplexStructure (AlmostComplexStructure.product ℝ) F
    stdComplexLineReal
  rwa [AlmostComplexStructure.product_apply_stdComplexLineReal] at h

end SymplecticForm

end TauCeti

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
is the quarter-turn `(∂s, ∂t) ↦ (∂t, -∂s)`. It preserves the Cauchy--Riemann condition for
complex-linear maps and the oriented symplectic area density `ω(F ∂s, F ∂t)`.

These are pointwise linear-algebra statements, not a global reparametrization theorem for
curves. They are the local bookkeeping needed before the analytic Heegaard Floer roadmap's disk
and strip energy theory, where domain rotations and coordinate changes should not change the
local holomorphicity or area-density convention.

## Main declarations

* `TauCeti.LinearMap.comp_stdComplexLineProduct_apply_stdComplexLineReal` and
  `TauCeti.LinearMap.comp_stdComplexLineProduct_apply_stdComplexLineImag`: coordinate formulas for
  the source quarter-turn.
* `TauCeti.isComplexLinearMap_comp_stdComplexLineProduct_iff`: precomposition by the source
  quarter-turn preserves and reflects complex-linearity.
* `TauCeti.SymplecticForm.symplecticForm_comp_stdComplexLineProduct`: the ordered area density is
  unchanged by this source quarter-turn.
* The corresponding complex-linearity lemma for the half-turn `-id`.

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

/-- Precomposing a standard-line linear map by the half-turn `-id` negates the real coordinate
value. -/
@[simp]
lemma comp_neg_apply_stdComplexLineReal (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    (F.comp (-LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) stdComplexLineReal =
      -F stdComplexLineReal := by
  calc
    (F.comp (-LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) stdComplexLineReal =
        F (-stdComplexLineReal) := rfl
    _ = -F stdComplexLineReal := by rw [map_neg]

/-- Precomposing a standard-line linear map by the half-turn `-id` negates the imaginary
coordinate value. -/
@[simp]
lemma comp_neg_apply_stdComplexLineImag (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    (F.comp (-LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) stdComplexLineImag =
      -F stdComplexLineImag := by
  calc
    (F.comp (-LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) stdComplexLineImag =
        F (-stdComplexLineImag) := rfl
    _ = -F stdComplexLineImag := by rw [map_neg]

end LinearMap

section ComplexLinear

variable {J : AlmostComplexStructure V}
variable {F : (ℝ × ℝ) →ₗ[ℝ] V}

/-- The standard source quarter-turn is complex-linear as a map from the standard complex line
to itself. -/
@[simp]
lemma isComplexLinearMap_stdComplexLineProduct :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ).toLinearMap := by
  rw [isComplexLinearMap_iff_apply]
  intro z
  simp

/-- Precomposing a complex-linear map from the standard complex line by the source quarter-turn
again gives a complex-linear map. -/
lemma IsComplexLinearMap.comp_stdComplexLineProduct
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (F.comp (AlmostComplexStructure.product ℝ).toLinearMap) :=
  hF.comp isComplexLinearMap_stdComplexLineProduct

/-- If precomposition by the source quarter-turn is complex-linear, then the original map was
complex-linear. -/
lemma IsComplexLinearMap.of_comp_stdComplexLineProduct
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (F.comp (AlmostComplexStructure.product ℝ).toLinearMap)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F := by
  rw [isComplexLinearMap_stdComplexLine_iff]
  have hcoord := (isComplexLinearMap_stdComplexLine_iff
    (F.comp (AlmostComplexStructure.product ℝ).toLinearMap)).mp hF
  simpa using (congrArg (fun v => -J v) hcoord).symm

/-- Precomposition by the source quarter-turn preserves and reflects complex-linearity of maps
from the standard complex line. -/
@[simp]
lemma isComplexLinearMap_comp_stdComplexLineProduct_iff :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (F.comp (AlmostComplexStructure.product ℝ).toLinearMap) ↔
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F :=
  ⟨fun hF => hF.of_comp_stdComplexLineProduct, fun hF => hF.comp_stdComplexLineProduct⟩

/-- Precomposing a complex-linear map from the standard complex line by the half-turn `-id`
again gives a complex-linear map. -/
lemma IsComplexLinearMap.comp_neg
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (F.comp (-LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) := by
  rw [isComplexLinearMap_stdComplexLine_iff] at hF ⊢
  simp [hF]

/-- Precomposition by the half-turn `-id` preserves and reflects complex-linearity of maps from
the standard complex line. -/
@[simp]
lemma isComplexLinearMap_comp_neg_iff :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (F.comp (-LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ)) ↔
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F := by
  constructor
  · intro hF
    have hrot := hF.comp_neg
    simpa using hrot
  · exact fun hF => hF.comp_neg

end ComplexLinear

namespace SymplecticForm

variable {ω : SymplecticForm V}

/-- Precomposition by the standard source complex structure preserves the ordered symplectic area
density `ω(F ∂s, F ∂t)`. -/
@[simp]
lemma symplecticForm_comp_stdComplexLineProduct (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    ω ((F.comp (AlmostComplexStructure.product ℝ).toLinearMap) stdComplexLineReal)
        ((F.comp (AlmostComplexStructure.product ℝ).toLinearMap) stdComplexLineImag) =
      ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  simp only [LinearMap.comp_stdComplexLineProduct_apply_stdComplexLineReal,
    LinearMap.comp_stdComplexLineProduct_apply_stdComplexLineImag]
  rw [map_neg]
  exact ω.neg_eq (F stdComplexLineImag) (F stdComplexLineReal)

end SymplecticForm

end TauCeti

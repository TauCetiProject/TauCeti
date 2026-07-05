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
* `TauCeti.isComplexLinearMap_comp_toLinearMap_iff`: precomposition by the source almost
  complex structure preserves and reflects complex-linearity.
* `TauCeti.SymplecticForm.symplecticForm_comp_stdComplexLineProduct`: the ordered area density is
  unchanged by this source quarter-turn.
* The corresponding complex-linearity lemma for the half-turn `-id`.

The sign convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: the standard source complex structure sends `∂s` to `∂t`.
-/

public section

namespace TauCeti

variable {U V : Type*} [AddCommGroup V] [Module ℝ V]

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

section ComplexLinear

variable [AddCommGroup U] [Module ℝ U]
variable {J₀ : AlmostComplexStructure U} {J : AlmostComplexStructure V}
variable {F₀ : U →ₗ[ℝ] V}
variable {F : (ℝ × ℝ) →ₗ[ℝ] V}

/-- An almost complex structure is complex-linear as a map from its module to itself. -/
@[simp]
lemma isComplexLinearMap_toLinearMap :
    IsComplexLinearMap J₀ J₀ J₀.toLinearMap := by
  rw [isComplexLinearMap_iff_apply]
  intro v
  rfl

/-- Precomposing a complex-linear map by the source almost complex structure again gives a
complex-linear map. -/
lemma IsComplexLinearMap.comp_toLinearMap
    (hF : IsComplexLinearMap J₀ J F₀) :
    IsComplexLinearMap J₀ J (F₀.comp J₀.toLinearMap) :=
  hF.comp isComplexLinearMap_toLinearMap

/-- If precomposition by the source almost complex structure is complex-linear, then the original
map was complex-linear. -/
lemma IsComplexLinearMap.of_comp_toLinearMap
    (hF : IsComplexLinearMap J₀ J (F₀.comp J₀.toLinearMap)) :
    IsComplexLinearMap J₀ J F₀ := by
  rw [isComplexLinearMap_iff_apply] at hF ⊢
  intro v
  have hJ := congrArg J (hF v)
  simpa using hJ.symm

/-- Precomposition by the source almost complex structure preserves and reflects
complex-linearity. -/
@[simp]
lemma isComplexLinearMap_comp_toLinearMap_iff :
    IsComplexLinearMap J₀ J (F₀.comp J₀.toLinearMap) ↔ IsComplexLinearMap J₀ J F₀ :=
  ⟨fun hF => hF.of_comp_toLinearMap, fun hF => hF.comp_toLinearMap⟩

/-- Precomposing a complex-linear map by the half-turn `-id` again gives a complex-linear map. -/
lemma IsComplexLinearMap.comp_neg
    (hF : IsComplexLinearMap J₀ J F₀) :
    IsComplexLinearMap J₀ J (F₀.comp (-LinearMap.id : U →ₗ[ℝ] U)) := by
  rw [isComplexLinearMap_iff_apply] at hF ⊢
  intro v
  simp [hF v]

/-- Negating a map preserves and reflects complex-linearity. -/
@[simp]
lemma isComplexLinearMap_neg_iff :
    IsComplexLinearMap J₀ J (-F₀) ↔ IsComplexLinearMap J₀ J F₀ :=
  ⟨fun hF => by simpa using hF.neg, fun hF => hF.neg⟩

/-- Precomposition by the half-turn `-id` preserves and reflects complex-linearity. -/
@[simp]
lemma isComplexLinearMap_comp_neg_iff :
    IsComplexLinearMap J₀ J (F₀.comp (-LinearMap.id : U →ₗ[ℝ] U)) ↔
        IsComplexLinearMap J₀ J F₀ := by
  have hcomp : F₀.comp (-LinearMap.id : U →ₗ[ℝ] U) = -F₀ := by
    ext v
    simp
  rw [hcomp]
  exact isComplexLinearMap_neg_iff

end ComplexLinear

namespace SymplecticForm

variable {ω : SymplecticForm V}

/-- The ordered area density is unchanged after precomposing by the standard source complex
structure. -/
lemma symplecticForm_comp_stdComplexLineProduct (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    ω ((F.comp (AlmostComplexStructure.product ℝ).toLinearMap) stdComplexLineReal)
        ((F.comp (AlmostComplexStructure.product ℝ).toLinearMap) stdComplexLineImag) =
      ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  rw [LinearMap.comp_stdComplexLineProduct_apply_stdComplexLineReal,
    LinearMap.comp_stdComplexLineProduct_apply_stdComplexLineImag]
  simpa using ω.neg_eq (F stdComplexLineImag) (F stdComplexLineReal)

end SymplecticForm

end TauCeti

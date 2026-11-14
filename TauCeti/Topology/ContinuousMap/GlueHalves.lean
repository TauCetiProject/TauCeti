/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.ProjIcc

/-!
# Gluing two maps along the halves of a parameter

Given a continuous parameter `s : C(Z, I)` and two maps `a, a' : C(Z, X)` that agree where
`s = 1/2`, `ContinuousMap.glueHalves s a a'` is `a` on `s ≤ 1/2` and `a'` on `1/2 ≤ s`.

## Main definitions

* `ContinuousMap.glueHalves`: the glued map, with the evaluation lemmas
  `ContinuousMap.glueHalves_of_le` and `ContinuousMap.glueHalves_of_not_le`.
* `ContinuousMap.pathLeftHalf`, `ContinuousMap.pathRightHalf`, and `ContinuousMap.concatPath`:
  first-half and second-half rescalings of `unitInterval` and concatenation of two paths
  `f, g : C(I, X)` satisfying `f 1 = g 0`.
-/

public section

open Set unitInterval

namespace ContinuousMap

/-- Glue two maps along the two halves `s ≤ 1/2` and `1/2 ≤ s` of the parameter `s`, assuming
that they agree where `s = 1/2`. -/
noncomputable def glueHalves {Z X : Type*} [TopologicalSpace Z] [TopologicalSpace X] (s : C(Z, I))
    (a a' : C(Z, X)) (h : ∀ z, (s z : ℝ) = 2⁻¹ → a z = a' z) : C(Z, X) :=
  ⟨fun z ↦ if (s z : ℝ) ≤ 2⁻¹ then a z else a' z,
    Continuous.if_le a.continuous a'.continuous (continuous_subtype_val.comp s.continuous)
      continuous_const h⟩

section GlueHalves

variable {Z X : Type*} [TopologicalSpace Z] [TopologicalSpace X] (s : C(Z, I))
  (a a' : C(Z, X)) (h : ∀ z, (s z : ℝ) = 2⁻¹ → a z = a' z) {z : Z}

@[simp]
theorem glueHalves_of_le (hz : (s z : ℝ) ≤ 2⁻¹) : glueHalves s a a' h z = a z :=
  by simp only [glueHalves, ContinuousMap.coe_mk, hz, ↓reduceIte]

@[simp]
theorem glueHalves_of_not_le (hz : ¬ (s z : ℝ) ≤ 2⁻¹) : glueHalves s a a' h z = a' z :=
  by simp only [glueHalves, ContinuousMap.coe_mk, hz, ↓reduceIte]

end GlueHalves

section ConcatPath

/-- First-half rescaling `t ↦ projIcc 0 1 _ (2 * t)` on `unitInterval`. -/
noncomputable def pathLeftHalf : C(I, I) where
  toFun t := projIcc 0 1 zero_le_one (2 * (t : ℝ))
  continuous_toFun := continuous_projIcc.comp (continuous_const.mul continuous_subtype_val)

/-- Second-half rescaling `t ↦ projIcc 0 1 _ (2 * t - 1)` on `unitInterval`. -/
noncomputable def pathRightHalf : C(I, I) where
  toFun t := projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)
  continuous_toFun :=
    continuous_projIcc.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const)

@[simp]
theorem pathLeftHalf_zero : pathLeftHalf 0 = 0 := by
  ext
  simp [pathLeftHalf]

@[simp]
theorem pathLeftHalf_half {t : I} (ht : (t : ℝ) = 2⁻¹) : pathLeftHalf t = 1 := by
  ext
  simp [pathLeftHalf, ht]

@[simp]
theorem pathRightHalf_half {t : I} (ht : (t : ℝ) = 2⁻¹) : pathRightHalf t = 0 := by
  ext
  simp [pathRightHalf, ht]

@[simp]
theorem pathRightHalf_one : pathRightHalf 1 = 1 := by
  ext
  simp [pathRightHalf]
  norm_num

/-- Concatenate two paths `f, g : C(unitInterval, X)` satisfying `f 1 = g 0`. -/
noncomputable def concatPath {X : Type*} [TopologicalSpace X] (f g : C(I, X)) (h : f 1 = g 0) :
    C(I, X) :=
  glueHalves (ContinuousMap.id I) (f.comp pathLeftHalf) (g.comp pathRightHalf) fun t ht => by
    have ht' : (t : ℝ) = 2⁻¹ := ht
    simp [ht', h]

theorem concatPath_of_le {X : Type*} [TopologicalSpace X] (f g : C(I, X)) (h : f 1 = g 0)
    {t : I} (ht : (t : ℝ) ≤ 2⁻¹) :
    concatPath f g h t = f (pathLeftHalf t) :=
  glueHalves_of_le (ContinuousMap.id I) _ _ _ ht

theorem concatPath_of_not_le {X : Type*} [TopologicalSpace X] (f g : C(I, X)) (h : f 1 = g 0)
    {t : I} (ht : ¬(t : ℝ) ≤ 2⁻¹) :
    concatPath f g h t = g (pathRightHalf t) :=
  glueHalves_of_not_le (ContinuousMap.id I) _ _ _ ht

@[simp]
theorem concatPath_zero {X : Type*} [TopologicalSpace X] (f g : C(I, X)) (h : f 1 = g 0) :
    concatPath f g h 0 = f 0 := by
  have hle : ((0 : I) : ℝ) ≤ 2⁻¹ := by norm_num
  rw [concatPath_of_le f g h hle, pathLeftHalf_zero]

@[simp]
theorem concatPath_one {X : Type*} [TopologicalSpace X] (f g : C(I, X)) (h : f 1 = g 0) :
    concatPath f g h 1 = g 1 := by
  have hnle : ¬((1 : I) : ℝ) ≤ 2⁻¹ := by norm_num
  rw [concatPath_of_not_le f g h hnle, pathRightHalf_one]

end ConcatPath

end ContinuousMap

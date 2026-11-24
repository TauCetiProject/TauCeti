/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.HyperplaneReflection

/-!
# Coordinate hyperplanes of Euclidean space

The coordinate vector `eᵢ = EuclideanSpace.single i 1` is a unit normal of the coordinate
hyperplane `{y | y i = 0}`. This file records the coordinate form of the half-spaces bounded by it
and of the reflection `TauCeti.hyperplaneReflection eᵢ 0` in it, `y ↦ y - 2 yᵢ eᵢ`.

## Main declarations

* `EuclideanSpace.real_inner_single_one_right`: `⟪y, eᵢ⟫ = y i`.
* `EuclideanSpace.isOpen_setOf_pos_apply`, `EuclideanSpace.isOpen_setOf_apply_neg`: the open
  coordinate half-spaces are open.
* `TauCeti.hyperplaneReflection_single_one_apply`: the reflection in `{y | y i = 0}` is
  `y ↦ y - 2 yᵢ eᵢ`, and `TauCeti.reflection_single_one_apply` the same formula for its linear part.
* `TauCeti.hyperplaneReflection_single_one_apply_self`: the reflection negates the `i`-th
  coordinate.
* `TauCeti.coe_orthogonalProjectionOnto_single_one_apply`: the orthogonal projection onto
  `{y | y i = 0}` is `y ↦ y - yᵢ eᵢ`.
-/

public section

open scoped RealInnerProductSpace

namespace EuclideanSpace

/-- The open coordinate half-space `{y | 0 < y i}` is open. -/
theorem isOpen_setOf_pos_apply {ι : Type*} (i : ι) : IsOpen {y : EuclideanSpace ℝ ι | 0 < y i} :=
  isOpen_lt continuous_const (by fun_prop)

/-- The open coordinate half-space `{y | y i < 0}` is open. -/
theorem isOpen_setOf_apply_neg {ι : Type*} (i : ι) : IsOpen {y : EuclideanSpace ℝ ι | y i < 0} :=
  isOpen_lt (by fun_prop) continuous_const

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pairing with the coordinate vector `eᵢ` reads off the `i`-th coordinate. -/
theorem real_inner_single_one_right (y : EuclideanSpace ℝ ι) (i : ι) :
    ⟪y, single i (1 : ℝ)⟫ = y i := by
  simp [inner_single_right]

end EuclideanSpace

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The reflection in the coordinate hyperplane `{y | y i = 0}` is `y ↦ y - 2 yᵢ eᵢ`. -/
theorem hyperplaneReflection_single_one_apply (i : ι) (y : EuclideanSpace ℝ ι) :
    hyperplaneReflection (EuclideanSpace.single i (1 : ℝ)) 0 y =
      y - (2 * y i) • EuclideanSpace.single i (1 : ℝ) := by
  rw [hyperplaneReflection_apply]
  simp [EuclideanSpace.inner_single_right]

/-- The reflection in the coordinate hyperplane `{y | y i = 0}` negates the `i`-th coordinate. -/
@[simp]
theorem hyperplaneReflection_single_one_apply_self (i : ι) (y : EuclideanSpace ℝ ι) :
    hyperplaneReflection (EuclideanSpace.single i (1 : ℝ)) 0 y i = -y i := by
  rw [hyperplaneReflection_single_one_apply]
  simp
  ring

/-- The linear reflection in the coordinate hyperplane `{y | y i = 0}`, the linear part of
`TauCeti.hyperplaneReflection eᵢ 0`, is `m ↦ m - 2 mᵢ eᵢ`. -/
theorem reflection_single_one_apply (i : ι) (m : EuclideanSpace ℝ ι) :
    (ℝ ∙ EuclideanSpace.single i (1 : ℝ))ᗮ.reflection m =
      m - (2 * m i) • EuclideanSpace.single i (1 : ℝ) := by
  have h := hyperplaneReflection_eq_reflection_add (EuclideanSpace.single i (1 : ℝ)) 0 m
  simp only [zero_div, mul_zero, zero_smul, add_zero] at h
  exact h.symm.trans (hyperplaneReflection_single_one_apply i m)

/-- The orthogonal projection onto the coordinate hyperplane `{y | y i = 0}` is
`y ↦ y - yᵢ eᵢ`. -/
theorem coe_orthogonalProjectionOnto_single_one_apply (i : ι) (y : EuclideanSpace ℝ ι) :
    ((ℝ ∙ EuclideanSpace.single i (1 : ℝ))ᗮ.orthogonalProjectionOnto y : EuclideanSpace ℝ ι) =
      y - y i • EuclideanSpace.single i (1 : ℝ) := by
  rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ (by simp), real_inner_comm,
    EuclideanSpace.real_inner_single_one_right]

end TauCeti

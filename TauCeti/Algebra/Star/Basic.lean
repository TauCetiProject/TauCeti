/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Basic

/-!
# Right absorption on involution-closed subsets

In any magma `A` with an antimultiplicative involution (`StarMul A`), a subset closed under `star`
(`StarMemClass S A`) that absorbs multiplication by ambient elements on the left also absorbs
multiplication on the right via `x * a = star (star a * star x)`.

## Main results

* `StarMemClass.mul_mem_right_of_mul_mem_left`: left absorption implies right absorption on
  star-closed subsets.
-/

public section

/-- A subset closed under the involution and under left multiplication by ambient elements is also
closed under right multiplication, via `x * a = star (star a * star x)`. -/
theorem StarMemClass.mul_mem_right_of_mul_mem_left {S A : Type*} [Mul A] [StarMul A]
    [SetLike S A] [StarMemClass S A] {s : S}
    (hmul : ∀ a : A, ∀ x ∈ s, a * x ∈ s) (a : A) {x : A} (hx : x ∈ s) : x * a ∈ s := by
  simpa only [star_mul, star_star] using star_mem (hmul (star a) (star x) (star_mem hx))

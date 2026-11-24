/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Affine

/-!
# Affine homotopy into a convex subset

This file lifts Mathlib's `ContinuousMap.Homotopy.affine` to continuous maps taking values in a
convex subset `s` of a real topological vector space (`ContinuousMap.Homotopy.affineOfConvex`).
Every straight-line segment between points of `s` remains in `s`, so the affine homotopy takes
values in `s` and fixes every point where the two maps agree.

## Main declarations

* `ContinuousMap.Homotopy.affineOfConvex`: straight-line homotopy between two continuous maps into
  a convex set.
* `ContinuousMap.Homotopy.coe_affineOfConvex`: ambient formula for `affineOfConvex`.
* `ContinuousMap.Homotopy.affineOfConvex_eq_of_eq`: `affineOfConvex` is stationary where the two
  maps agree.
-/

public section

open scoped unitInterval

namespace ContinuousMap.Homotopy

variable {X E : Type*} [TopologicalSpace X]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousSMul ℝ E]

private theorem affine_mem_of_convex {s : Set E} (hs : Convex ℝ s) (f g : C(X, s))
    (p : I × X) :
    affine ((ContinuousMap.subtypeVal s).comp f)
      ((ContinuousMap.subtypeVal s).comp g) p ∈ s := by
  rw [affine_apply, ← Path.segment_apply]
  exact hs.segment_subset (f p.2).property (g p.2).property
    (Path.range_segment (f p.2 : E) (g p.2 : E) ▸ Set.mem_range_self p.1)

/-- The straight-line homotopy between two continuous maps into a convex subset `s` of a real
topological vector space. -/
def affineOfConvex {s : Set E} (hs : Convex ℝ s) (f g : C(X, s)) : f.Homotopy g where
  toFun p := ⟨affine ((ContinuousMap.subtypeVal s).comp f)
    ((ContinuousMap.subtypeVal s).comp g) p,
    affine_mem_of_convex hs f g p⟩
  continuous_toFun :=
    (affine ((ContinuousMap.subtypeVal s).comp f)
      ((ContinuousMap.subtypeVal s).comp g)).continuous.subtype_mk _
  map_zero_left x := Subtype.ext
    ((affine ((ContinuousMap.subtypeVal s).comp f)
      ((ContinuousMap.subtypeVal s).comp g)).apply_zero x)
  map_one_left x := Subtype.ext
    ((affine ((ContinuousMap.subtypeVal s).comp f)
      ((ContinuousMap.subtypeVal s).comp g)).apply_one x)

/-- Pointwise ambient value of `ContinuousMap.Homotopy.affineOfConvex`. -/
@[simp]
theorem coe_affineOfConvex {s : Set E} (hs : Convex ℝ s) (f g : C(X, s)) (p : I × X) :
    (affineOfConvex hs f g p : E) = AffineMap.lineMap (f p.2 : E) (g p.2 : E) (p.1 : ℝ) :=
  affine_apply _ _ p

/-- If two maps into a convex set agree at `x`, their straight-line homotopy fixes `f x` at all
times. -/
theorem affineOfConvex_eq_of_eq {s : Set E} (hs : Convex ℝ s) {f g : C(X, s)}
    (t : I) {x : X} (hx : f x = g x) :
    affineOfConvex hs f g (t, x) = f x := by
  ext
  simp [hx]

end ContinuousMap.Homotopy

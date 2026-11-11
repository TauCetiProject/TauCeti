/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# The equator of a unit sphere orthogonal to a vector

For a vector `u` of a real inner product space `V`, the points of the unit sphere orthogonal to
`u` form the equator `TauCeti.sphereEquator u`. A linear isometry `e` of a real inner product space
`W` onto the orthogonal complement `(ℝ ∙ u)ᗮ` carries the unit sphere of `W` bijectively and
continuously onto this equator.

## Main declarations

* `TauCeti.sphereEquator u`: the points of the unit sphere orthogonal to `u`, with membership
  characterized by `TauCeti.mem_sphereEquator`.
* `LinearIsometryEquiv.sphereToEquator e`: the unit sphere carried onto the equator through a
  linear isometry `e` onto `(ℝ ∙ u)ᗮ`, with `LinearIsometryEquiv.injective_sphereToEquator` and
  `LinearIsometryEquiv.surjective_sphereToEquator`.
-/

public section

noncomputable section

open Metric
open scoped RealInnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup W]
  [InnerProductSpace ℝ W]

namespace TauCeti

variable (u : V) in
/-- The equator of the unit sphere orthogonal to `u`: the unit vectors orthogonal to `u`. For a
unit vector `p` orthogonal to `u` it is the equator through `p` orthogonal to `u`. -/
def sphereEquator : Set (sphere (0 : V) 1) :=
  {q | ⟪(q : V), u⟫ = 0}

variable {u : V}

@[simp]
theorem mem_sphereEquator {q : sphere (0 : V) 1} : q ∈ sphereEquator u ↔ ⟪(q : V), u⟫ = 0 :=
  Iff.rfl

end TauCeti

namespace LinearIsometryEquiv

open TauCeti

variable {u : V}

/-- A linear isometry onto the orthogonal complement of `u` carries the unit sphere onto the equator
orthogonal to `u`. -/
def sphereToEquator (e : W ≃ₗᵢ[ℝ] (ℝ ∙ u)ᗮ) : C(sphere (0 : W) 1, sphereEquator u) where
  toFun s := ⟨⟨(e s : V), by
      rw [mem_sphere_zero_iff_norm, Submodule.norm_coe, LinearIsometryEquiv.norm_map,
        norm_eq_of_mem_sphere]⟩,
    mem_sphereEquator.2 (Submodule.mem_orthogonal_singleton_iff_inner_left.1 (e s).2)⟩
  continuous_toFun := by fun_prop

@[simp]
theorem coe_sphereToEquator (e : W ≃ₗᵢ[ℝ] (ℝ ∙ u)ᗮ) (s : sphere (0 : W) 1) :
    ((e.sphereToEquator s : sphere (0 : V) 1) : V) = e s :=
  (rfl)

/-- The map `LinearIsometryEquiv.sphereToEquator e` onto the equator is injective. -/
theorem injective_sphereToEquator (e : W ≃ₗᵢ[ℝ] (ℝ ∙ u)ᗮ) :
    Function.Injective e.sphereToEquator := fun _ _ h =>
  Subtype.ext (e.injective (Subtype.ext (congrArg (fun r : sphereEquator u =>
    ((r : sphere (0 : V) 1) : V)) h)))

/-- The map `LinearIsometryEquiv.sphereToEquator e` onto the equator is surjective. -/
theorem surjective_sphereToEquator (e : W ≃ₗᵢ[ℝ] (ℝ ∙ u)ᗮ) :
    Function.Surjective e.sphereToEquator := fun q =>
  ⟨⟨e.symm ⟨q.1.1, Submodule.mem_orthogonal_singleton_iff_inner_left.2
      (mem_sphereEquator.1 q.2)⟩, by simp [norm_eq_of_mem_sphere]⟩,
    Subtype.ext (Subtype.ext (by simp))⟩

end LinearIsometryEquiv

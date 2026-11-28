/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Star
public import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Continuous Euclidean coordinate functions on the unit sphere

For a finite index type `ι` and a topological `ℝ`-algebra `R`, let `S` be the unit sphere
`Metric.sphere (0 : EuclideanSpace ℝ ι) 1`. The Euclidean coordinate projections `x ↦ xᵢ` define
continuous `R`-valued functions `TauCeti.sphereCoord R i : C(S, R)` via `algebraMap ℝ R`.

## Main definitions

* `TauCeti.sphereCoord`: the continuous coordinate function `x ↦ algebraMap ℝ R (x i)` in `C(S, R)`.

## Main results

* `TauCeti.compLeftContinuous_sphereCoord`: post-composing `sphereCoord` with a continuous
  `ℝ`-algebra homomorphism changes the target coefficient semiring.
* `TauCeti.star_sphereCoord_apply`, `TauCeti.star_sphereCoord`: in any topological `⋆`-algebra
  over `ℝ`, the coordinate functions on the unit sphere are self-adjoint.
* `TauCeti.dotProduct_sphereCoord_self`, `TauCeti.sum_sphereCoord_sq`: the sum of the squares of
  the Euclidean coordinate functions on the unit sphere is `1`.
-/

public section

noncomputable section

open Metric
open scoped BigOperators

namespace TauCeti

variable (R : Type*) [Semiring R] [TopologicalSpace R] [Algebra ℝ R] [ContinuousSMul ℝ R]
  {ι : Type*} [Fintype ι]

/-- The `i`-th Euclidean coordinate on the unit sphere `S ⊂ ℝ^ι`, valued in a topological
`ℝ`-algebra `R` as an element of `C(S, R)`. For `R = ℝ` this is `x ↦ xᵢ`. -/
def sphereCoord (i : ι) : C(sphere (0 : EuclideanSpace ℝ ι) 1, R) where
  toFun x := algebraMap ℝ R (EuclideanSpace.proj i (x : EuclideanSpace ℝ ι))
  continuous_toFun :=
    (continuous_algebraMap ℝ R).comp
      ((EuclideanSpace.proj i).continuous.comp continuous_subtypeVal)

variable {R}

@[simp]
theorem sphereCoord_apply (i : ι) (x : sphere (0 : EuclideanSpace ℝ ι) 1) :
    sphereCoord R i x = algebraMap ℝ R ((x : EuclideanSpace ℝ ι) i) :=
  (rfl)

/-- Post-composing `sphereCoord` with a continuous `ℝ`-algebra homomorphism changes the target
coefficient ring. -/
@[simp]
theorem compLeftContinuous_sphereCoord [IsTopologicalSemiring R] {S : Type*} [Semiring S]
    [TopologicalSpace S] [IsTopologicalSemiring S] [Algebra ℝ S] [ContinuousSMul ℝ S]
    (φ : R →ₐ[ℝ] S) (hφ : Continuous φ) (i : ι) :
    (φ : R →+* S).compLeftContinuous _ hφ (sphereCoord R i) = sphereCoord S i := by
  ext x
  exact φ.commutes ((x : EuclideanSpace ℝ ι) i)

/-- In a topological `⋆`-algebra over `ℝ`, each coordinate function on the unit sphere is
self-adjoint. -/
@[simp]
theorem star_sphereCoord_apply [StarMul R] [ContinuousStar R] [StarModule ℝ R] (i : ι) :
    star (sphereCoord R i) = sphereCoord R i := by
  ext x
  simp only [ContinuousMap.star_apply, sphereCoord_apply, ← algebraMap_star_comm, star_trivial]

/-- In a topological `⋆`-algebra over `ℝ`, the coordinate vector `sphereCoord R` on the unit
sphere is self-adjoint. -/
@[simp]
theorem star_sphereCoord [StarMul R] [ContinuousStar R] [StarModule ℝ R] :
    star (sphereCoord (ι := ι) R) = sphereCoord R :=
  funext star_sphereCoord_apply

/-- On the unit sphere, the dot product of the coordinate vector `sphereCoord R` with itself is
`1`. -/
@[simp]
theorem dotProduct_sphereCoord_self [IsTopologicalSemiring R] :
    sphereCoord R ⬝ᵥ sphereCoord R = (1 : C(sphere (0 : EuclideanSpace ℝ ι) 1, R)) := by
  ext x
  simp only [dotProduct, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.mul_apply,
    sphereCoord_apply, ← map_mul, ← map_sum, ContinuousMap.one_apply]
  have hx : WithLp.ofLp (x : EuclideanSpace ℝ ι) ⬝ᵥ WithLp.ofLp (x : EuclideanSpace ℝ ι) = 1 :=
    EuclideanSpace.toLp_mem_sphere_zero_one_iff.mp x.property
  rw [dotProduct] at hx
  simpa only [hx] using map_one (algebraMap ℝ R)

/-- The sum of the squares of the Euclidean coordinate functions on the unit sphere is `1`. -/
theorem sum_sphereCoord_sq [IsTopologicalSemiring R] :
    ∑ i : ι, sphereCoord R i ^ 2 = 1 := by
  simpa only [dotProduct, sq] using dotProduct_sphereCoord_self (R := R) (ι := ι)

end TauCeti

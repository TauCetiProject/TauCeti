/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import TauCeti.Geometry.Manifold.ContMDiff.Pi
public import TauCeti.Geometry.Manifold.IsManifold.Pi

/-!
# Coordinate maps of finite products of manifolds

On a finite product `∀ i, M i` of manifolds, modelled on `ModelWithCorners.pi I`, the tangent space
at `x` is the product `∀ i, E i` of the model spaces of the factors. This file identifies the
derivatives of the two families of coordinate maps with the structure maps of this product:

* the coordinate projection `x ↦ x i` has derivative the projection `ContinuousLinearMap.proj i`
  (`TauCeti.mfderiv_apply`);
* the coordinate insertion `Function.update x i : M i → ∀ j, M j`, the inclusion of the
  coordinate fiber through `x`, has derivative the inclusion of the `i`-th factor
  (`TauCeti.mfderiv_update`).

These are the finite-product analogues of Mathlib's `mfderiv_fst` and `mfderiv_prodMk_left`. They
read forms and vector fields on a product, such as the coordinate time forms of a torus, through
the factors. The smoothness of the coordinate insertions is `TauCeti.contMDiff_update`.

## Main declarations

* `TauCeti.hasMFDerivAt_apply`, `TauCeti.mfderiv_apply`: the derivative of a coordinate
  projection.
* `TauCeti.hasMFDerivAt_update`, `TauCeti.mfderiv_update`: the derivative of a coordinate
  insertion.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Proposition 3.14 (the tangent space of a product manifold).
-/

public section

open Set Function
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {H : ι → Type*} [∀ i, TopologicalSpace (H i)] {I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)}
  {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]

/-- The coordinate projection `x ↦ x i` of a finite product of manifolds has derivative the
projection `ContinuousLinearMap.proj i` of the product of the model spaces. -/
theorem hasMFDerivAt_apply (i : ι) (x : ∀ i, M i) :
    HasMFDerivAt (ModelWithCorners.pi I) (I i) (fun x : ∀ i, M i ↦ x i) x
      (ContinuousLinearMap.proj i) := by
  refine ⟨(continuous_apply i).continuousAt, ?_⟩
  -- Read in the extended charts at `x` and `x i`, the projection is the projection of the model
  -- spaces, on the target of the product chart.
  have h : writtenInExtChartAt (ModelWithCorners.pi I) (I i) x (fun x : ∀ i, M i ↦ x i)
      =ᶠ[𝓝[range (ModelWithCorners.pi I)] extChartAt (ModelWithCorners.pi I) x x]
        fun y ↦ y i := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := ModelWithCorners.pi I) x] with y hy
    rw [extChartAt_pi] at hy
    simp only [writtenInExtChartAt, extChartAt_pi, Function.comp_apply, PartialEquiv.pi_symm,
      PartialEquiv.pi_apply]
    exact (extChartAt (I i) (x i)).right_inv (hy i (mem_univ i))
  convert (hasFDerivAt_apply i _).hasFDerivWithinAt.congr_of_eventuallyEq h ?_ using 1
  · -- The tangent spaces are the model spaces, identified by `tangentSpaceCastModel`, which is
    -- the identity by definition.
    ext
    rfl
  · rw [writtenInExtChartAt, comp_apply, comp_apply, extChartAt_to_inv, extChartAt_pi]
    rfl

/-- The derivative of the coordinate projection `x ↦ x i` of a finite product of manifolds is the
projection `ContinuousLinearMap.proj i`. -/
@[simp]
theorem mfderiv_apply (i : ι) (x : ∀ i, M i) :
    mfderiv (ModelWithCorners.pi I) (I i) (fun x : ∀ i, M i ↦ x i) x = ContinuousLinearMap.proj i :=
  (hasMFDerivAt_apply i x).mfderiv

variable [DecidableEq ι]

/-- The coordinate insertion `Function.update x i` has derivative the inclusion of the `i`-th
factor of the product of the model spaces. -/
theorem hasMFDerivAt_update (x : ∀ i, M i) (i : ι) (y : M i) :
    HasMFDerivAt (I i) (ModelWithCorners.pi I) (update x i) y
      (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id 𝕜 (E i)))) := by
  refine ⟨(contMDiff_update (I := I) (n := 0) x i).continuous.continuousAt, ?_⟩
  -- Read in the charts at `y` and at `update x i y`, the insertion is the insertion
  -- `update c i` of the model spaces, where `c` is the image of `update x i y`.
  set c := extChartAt (ModelWithCorners.pi I) (update x i y) (update x i y)
  have h : writtenInExtChartAt (I i) (ModelWithCorners.pi I) y (update x i)
      =ᶠ[𝓝[range (I i)] extChartAt (I i) y y] update c i := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I i) y] with z hz
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp only [writtenInExtChartAt, comp_apply, extChartAt_pi, PartialEquiv.pi_apply,
        Pi.map_apply, update_self]
      exact (extChartAt (I j) y).right_inv hz
    · simp [writtenInExtChartAt, c, hj]
  convert (hasFDerivAt_update c _).hasFDerivWithinAt.congr_of_eventuallyEq h ?_ using 1
  · -- The tangent spaces are the model spaces, identified by `tangentSpaceCastModel`, which is
    -- the identity by definition.
    ext
    rfl
  · funext j
    rcases eq_or_ne j i with rfl | hj
    · simp [writtenInExtChartAt, c]
    · simp [writtenInExtChartAt, c, hj]

/-- The derivative of the coordinate insertion `Function.update x i` is the inclusion of the `i`-th
factor of the product of the model spaces. -/
@[simp]
theorem mfderiv_update (x : ∀ i, M i) (i : ι) (y : M i) :
    mfderiv (I i) (ModelWithCorners.pi I) (update x i) y =
      ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id 𝕜 (E i))) :=
  (hasMFDerivAt_update x i y).mfderiv

end TauCeti

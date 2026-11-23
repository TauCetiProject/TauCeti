/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.AlgebraicTopology.Sphere.TwoFieldFamily
public import TauCeti.Geometry.Manifold.FiberBundle.LocallyTrivial
public import TauCeti.Geometry.Sphere.Quaternion

/-!
# The space of equators of two orthonormal tangent fields is a closed oriented manifold

Let `Sⁿ⁺²` be the unit sphere of a real inner product space `E` of dimension `n + 3`, and let `u`,
`v` be continuous tangent vector fields on it with `x`, `u x`, `v x` orthonormal at every point.
The space of equators `Σ = {(x, q) | q ⊥ u x, v x}` (`TauCeti.twoFieldEquators`) is the parameter
space of the family of two-spheres `σ : Σ → Map(S², Sⁿ⁺²)` of Barraud–Damian–Humilière–Oancea,
Example 6.20 (`TauCeti.twoFieldSphereFamily`). Their Definition 6.14 of a fibred family of
two-spheres asks `Σ` to be a closed oriented manifold, so that it has a fundamental class.

The projection `Σ → Sⁿ⁺²` is locally trivial with fibre `Sⁿ`
(`TauCeti.exists_trivialization_twoFieldEquators`). Its trivializations, followed by the
stereographic charts of the two spheres, chart `Σ` on `ℝⁿ⁺²⁺ⁿ`
(`TauCeti.twoFieldEquatorsChartedSpace`, an instance of
`TauCeti.euclideanChartedSpaceOfExistsTrivialization`). Being a closed subspace of
`Sⁿ⁺² × Sⁿ⁺²`, `Σ` is compact and Hausdorff (`TauCeti.compactSpace_twoFieldEquators`), so it is a
closed topological manifold of dimension `2n + 2`.

For `n ≥ 2` the base `Sⁿ⁺²` and the fibre `Sⁿ` are simply connected, hence so is `Σ`
(`TauCeti.simplyConnectedSpace_twoFieldEquators`), and `Σ` is orientable
(`TauCeti.nonempty_homologicalOrientation_twoFieldEquators`). An orientation gives the integral
fundamental class `[Σ] ∈ H₂ₙ₊₂(Σ; ℤ)` (`TauCeti.HomologicalOrientation.fundamentalClass`). This
covers the spheres `S^{4k-1}`, `k ≥ 2`, with two of their quaternionic fields. The case `n = 1`,
the three-sphere with fibres circles, is not covered by this argument, since `Σ` is then not simply
connected.

## Main definitions

* `TauCeti.twoFieldEquatorsChartedSpace`: the charts of `Σ` on `ℝⁿ⁺²⁺ⁿ`.

## Main results

* `TauCeti.twoFieldEquatorsChartedSpace_eq`: these charts are those of
  `TauCeti.euclideanChartedSpaceOfExistsTrivialization`.
* `TauCeti.exists_trivialization_twoFieldEquators_sphere`: `Σ → Sⁿ⁺²` is locally trivial with
  fibre the unit sphere `Sⁿ` of `ℝⁿ⁺¹`.
* `TauCeti.simplyConnectedSpace_twoFieldEquators`: for `n ≥ 2`, `Σ` is simply connected.
* `TauCeti.nonempty_homologicalOrientation_twoFieldEquators`: for `n ≥ 2`, `Σ` is orientable.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Definition 6.14 and
  Example 6.20.
-/

public section

open Metric Module

namespace TauCeti

section Charts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u v : sphere (0 : E) 1 → E}

variable {n : ℕ} [Fact (finrank ℝ E = n + 3)]

variable (hu : Continuous u) (hv : Continuous v) (huv : ∀ x, Orthonormal ℝ ![u x, v x])
include hu hv huv

/-- **The space of equators is a bundle of `n`-spheres over `Sⁿ⁺²`.** In a space `E` of dimension
`n + 3`, the projection `(x, q) ↦ x` of the space of equators is locally trivial with fibre the unit
sphere of `ℝⁿ⁺¹`. -/
theorem exists_trivialization_twoFieldEquators_sphere (x : sphere (0 : E) 1) :
    ∃ e : Bundle.Trivialization (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      (ContinuousMap.fst.comp (ContinuousMap.subtypeVal (twoFieldEquators u v))),
      x ∈ e.baseSet :=
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ (n := n + 2) Fact.out
  exists_trivialization_twoFieldEquators hu hv huv
    (by rw [finrank_euclideanSpace_fin, Fact.out (p := finrank ℝ E = n + 3)]) x

/-- **The charts of the space of equators.** In a space `E` of dimension `n + 3`, the
trivializations of the projection of the space of equators onto `Sⁿ⁺²`, followed by the
stereographic charts of `Sⁿ⁺²` and of the fibre `Sⁿ`, chart the space of equators on `ℝⁿ⁺²⁺ⁿ`. -/
@[instance_reducible]
noncomputable def twoFieldEquatorsChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + 2 + n))) (twoFieldEquators u v) :=
  euclideanChartedSpaceOfExistsTrivialization (n := n + 2) (m := n)
    (exists_trivialization_twoFieldEquators_sphere (n := n) hu hv huv)

/-- `TauCeti.twoFieldEquatorsChartedSpace` is the Euclidean atlas of the locally trivial projection
onto `Sⁿ⁺²`, so its charts are described by
`TauCeti.euclideanChartedSpaceOfExistsTrivialization_chartAt`. -/
theorem twoFieldEquatorsChartedSpace_eq :
    twoFieldEquatorsChartedSpace (n := n) hu hv huv =
      euclideanChartedSpaceOfExistsTrivialization (n := n + 2) (m := n)
        (exists_trivialization_twoFieldEquators_sphere (n := n) hu hv huv) :=
  (rfl)

/-- **The space of equators is simply connected** in a space `E` of dimension `n + 3` with
`n ≥ 2`, as a bundle of simply connected spheres `Sⁿ` over the simply connected sphere `Sⁿ⁺²`. -/
theorem simplyConnectedSpace_twoFieldEquators (hn : 2 ≤ n) :
    SimplyConnectedSpace (twoFieldEquators u v) := by
  have := simplyConnectedSpace_sphere_euclideanSpace hn
  have := simplyConnectedSpace_sphere_of_lt_finrank (E := E)
    (by rw [Fact.out (p := finrank ℝ E = n + 3)]; omega) 0 zero_le_one
  exact simplyConnectedSpace_of_exists_trivialization
    (exists_trivialization_twoFieldEquators_sphere (n := n) hu hv huv)

end Charts

section Orientation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u v : sphere (0 : E) 1 → E}
  {n : ℕ} [Fact (finrank ℝ E = n + 3)]

/-- **The space of equators is orientable.** In a space `E` of dimension `n + 3` with `n ≥ 2`, the
space of equators of two continuous tangent fields of `Sⁿ⁺²`, orthonormal at every point, charted
on `ℝⁿ⁺²⁺ⁿ` by `TauCeti.twoFieldEquatorsChartedSpace`, has a homological orientation in its
dimension `2n + 2`. It is compact (`TauCeti.compactSpace_twoFieldEquators`), so each orientation
has a fundamental class. -/
theorem nonempty_homologicalOrientation_twoFieldEquators (hn : 2 ≤ n) (hu : Continuous u)
    (hv : Continuous v) (huv : ∀ x, Orthonormal ℝ ![u x, v x]) :
    Nonempty (letI := twoFieldEquatorsChartedSpace (n := n) hu hv huv;
      HomologicalOrientation (twoFieldEquators u v) (EuclideanSpace ℝ (Fin (n + 2 + n)))
        (n + 2 + n)) := by
  have := simplyConnectedSpace_sphere_euclideanSpace hn
  have := simplyConnectedSpace_sphere_of_lt_finrank (E := E)
    (by rw [Fact.out (p := finrank ℝ E = n + 3)]; omega) 0 zero_le_one
  exact nonempty_homologicalOrientation_of_exists_trivialization
    (exists_trivialization_twoFieldEquators_sphere (n := n) hu hv huv)

end Orientation

section Quaternion

open Quaternion
open scoped RightActions

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Module ℍᵐᵒᵖ E]
  [NormSMulClass ℍᵐᵒᵖ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 3)] {i j : Fin 3}

/-- **The quaternionic spaces of equators are orientable.** If the quaternions act on the right on
`E`, isometrically, any two distinct quaternionic fields `x <• i`, `x <• j`, `x <• k` of the unit
sphere (`TauCeti.quaternionFrame`) are continuous and orthonormal at every point, and for
`dim E = n + 3` with `n ≥ 2` their space of equators has a homological orientation. For
`E = ℍᵏ⁺²` these are the spheres `S^{4k+7}` of Barraud–Damian–Humilière–Oancea, Example 6.20. -/
theorem nonempty_homologicalOrientation_twoFieldEquators_quaternionFrame (hn : 2 ≤ n)
    (hij : i ≠ j) :
    Nonempty
      (letI := twoFieldEquatorsChartedSpace (E := E) (n := n)
          (u := fun x ↦ quaternionFrame (x : E) i) (v := fun x ↦ quaternionFrame (x : E) j)
          ((continuous_quaternionFrame i).comp continuous_subtypeVal)
          ((continuous_quaternionFrame j).comp continuous_subtypeVal)
          (fun x : sphere (0 : E) 1 ↦
            orthonormal_quaternionFrame_pair_of_ne (norm_eq_of_mem_sphere x) hij);
        HomologicalOrientation
          (twoFieldEquators (fun x ↦ quaternionFrame (x : E) i) fun x ↦ quaternionFrame (x : E) j)
          (EuclideanSpace ℝ (Fin (n + 2 + n))) (n + 2 + n)) :=
  nonempty_homologicalOrientation_twoFieldEquators (E := E) hn _ _ _

end Quaternion

end TauCeti

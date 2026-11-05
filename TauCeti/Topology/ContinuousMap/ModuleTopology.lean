/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.ContinuousMap.Algebra
import TauCeti.LinearAlgebra.Basis.Algebra

/-!
# Coordinate decompositions of continuous maps under the module topology

When an `R`-module `M` carries the `R`-module topology (`IsModuleTopology R M`) over a semiring
`R` with continuous addition and multiplication, every coordinate functional `b.coord i` of an
`R`-basis `b : Module.Basis ι R M` is automatically continuous (`Module.Basis.coordCLM`), with no
finiteness assumption on the index type `ι`.

When `ι` is finite, postcomposing a continuous map `F : C(X, M)` with `b.coordCLM i` decomposes `F`
as the finite sum of scalar-valued continuous coordinate maps multiplying the constant basis maps
(`ContinuousMap.eq_sum_coordCLM_comp_smul_const`). When the target is a topological `R`-algebra `A`
carrying the `R`-module topology, each term rewrites via `algebraMap R A` so that `F` is an
`A`-linear combination of `R`-valued continuous functions composed with `algebraMap R A`
(`ContinuousMap.eq_sum_smul_algebraMap_comp_coordCLM`), and left multiplication by `c : A` expands
in coordinates through the algebra multiplication coefficients `b.coord i (c * b j)`
(`ContinuousMap.coordCLM_comp_smul`).

## Main definitions

* `Module.Basis.coordCLM`: the `i`-th coordinate functional `M →L[R] R` of a basis `b` of a module
  carrying the module topology.

## Main results

* `ContinuousMap.eq_sum_coordCLM_comp_smul_const`: finite-basis coordinate decomposition of
  `F : C(X, M)` under `IsModuleTopology R M`.
* `ContinuousMap.coordCLM_comp_algebraMap_comp`: coordinates of `algebraMap R A ∘ f` for
  `f : C(X, R)`.
* `ContinuousMap.eq_sum_smul_algebraMap_comp_coordCLM`: finite-basis decomposition of `F : C(X, A)`
  into `R`-valued coordinate maps composed with `algebraMap R A`.
* `ContinuousMap.coordCLM_comp_smul`: coordinate expansion of `c • F` for `c : A` and
  `F : C(X, A)`.
-/

public section

namespace Module.Basis

variable {ι R M : Type*} [Semiring R] [TopologicalSpace R] [ContinuousAdd R] [ContinuousMul R]
  [AddCommMonoid M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]

/-- The `i`-th coordinate functional of a basis of a module carrying the module topology, bundled
as a continuous linear map. -/
noncomputable def coordCLM (b : Module.Basis ι R M) (i : ι) : M →L[R] R :=
  ⟨b.coord i, IsModuleTopology.continuous_of_linearMap (b.coord i)⟩

/-- Evaluating `b.coordCLM i` gives the `i`-th coordinate `b.coord i`. -/
@[simp]
theorem coordCLM_apply (b : Module.Basis ι R M) (i : ι) (m : M) :
    b.coordCLM i m = b.coord i m :=
  (rfl)

/-- The underlying linear map of `b.coordCLM i` is `b.coord i`. -/
@[simp]
theorem toLinearMap_coordCLM (b : Module.Basis ι R M) (i : ι) :
    (b.coordCLM i).toLinearMap = b.coord i :=
  (rfl)

end Module.Basis

namespace ContinuousMap

section Module

variable {X ι R M : Type*} [TopologicalSpace X] [Fintype ι]
  [Semiring R] [TopologicalSpace R] [ContinuousAdd R] [ContinuousMul R]
  [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M] [Module R M] [IsModuleTopology R M]

/-- Every continuous map into a module carrying the module topology decomposes along a finite basis
into continuous scalar-valued coordinate maps multiplying the constant basis maps. -/
theorem eq_sum_coordCLM_comp_smul_const (F : C(X, M)) (b : Module.Basis ι R M) :
    F = ∑ i, ((b.coordCLM i : C(M, R)).comp F) • ContinuousMap.const X (b i) := by
  ext x
  simp [b.sum_repr]

end Module

section Algebra

variable {X ι R A : Type*} [TopologicalSpace X]
  [CommSemiring R] [TopologicalSpace R] [ContinuousAdd R] [ContinuousMul R]
  [Semiring A] [TopologicalSpace A] [Algebra R A] [IsModuleTopology R A]

/-- Postcomposing `algebraMap R A ∘ f` with the `i`-th coordinate functional scales `f : C(X, R)`
by `b.coord i 1`. -/
theorem coordCLM_comp_algebraMap_comp (f : C(X, R)) (b : Module.Basis ι R A) (i : ι) :
    (b.coordCLM i : C(A, R)).comp
        ((⟨algebraMap R A, continuous_algebraMap R A⟩ : C(R, A)).comp f) =
      b.coord i 1 • f := by
  ext x
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
    Module.Basis.coordCLM_apply, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]

variable [Fintype ι] [ContinuousMul A]

/-- Coordinate functions of `c • F` along a finite `R`-basis of a topological `R`-algebra `A`
carrying the `R`-module topology are `R`-linear combinations of the coordinate functions of `F`. -/
theorem coordCLM_comp_smul (F : C(X, A)) (b : Module.Basis ι R A) (i : ι) (c : A) :
    (b.coordCLM i : C(A, R)).comp (c • F) =
      ∑ j, b.coord i (c * b j) • (b.coordCLM j : C(A, R)).comp F := by
  ext x
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, ContinuousMap.smul_apply,
    smul_eq_mul, ContinuousMap.coe_sum, Finset.sum_apply, Module.Basis.coordCLM_apply]
  conv_lhs => rw [← b.sum_repr (F x), Finset.mul_sum]
  simp_rw [mul_smul_comm, map_sum, map_smul, Module.Basis.coord_apply, smul_eq_mul, mul_comm]

variable [ContinuousAdd A]

/-- Every continuous map into a topological `R`-algebra `A` carrying the `R`-module topology
decomposes along a finite `R`-basis of `A` into continuous `R`-valued coordinate maps composed with
`algebraMap R A`. -/
theorem eq_sum_smul_algebraMap_comp_coordCLM (F : C(X, A)) (b : Module.Basis ι R A) :
    F = ∑ i, b i • (⟨algebraMap R A, continuous_algebraMap R A⟩ : C(R, A)).comp
      ((b.coordCLM i : C(A, R)).comp F) := by
  ext x
  simpa [ContinuousMap.smul_apply'] using (b.sum_mul_algebraMap_coord (F x)).symm

end Algebra

section Examples

example {X R : Type*} [TopologicalSpace X] [CommSemiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] (f : C(X, R)) :
    ((Module.Basis.singleton PUnit R).coordCLM PUnit.unit : C(R, R)).comp f = f := by
  ext x
  simp

example {X R : Type*} [TopologicalSpace X] [CommSemiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] (f : C(X, R)) :
    f = ∑ i : PUnit, Module.Basis.singleton PUnit R i •
      (⟨algebraMap R R, continuous_algebraMap R R⟩ : C(R, R)).comp
        (((Module.Basis.singleton PUnit R).coordCLM i : C(R, R)).comp f) :=
  f.eq_sum_smul_algebraMap_comp_coordCLM (Module.Basis.singleton PUnit R)

end Examples

end ContinuousMap

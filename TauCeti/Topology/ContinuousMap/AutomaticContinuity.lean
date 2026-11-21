/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.Topology.Algebra.Module.AutomaticContinuity

/-!
# Finite-basis coordinate expansions of continuous maps over compact scalar semirings

Let `R` be a compact topological semiring and `M` a finitely generated Hausdorff topological
`R`-module with continuous addition and scalar action. By
`LinearMap.toContinuousLinearMapOfFiniteOfCompactSpace`, every coordinate functional
`b.coord i : M →ₗ[R] R` of a finite `R`-basis `b` of `M` is automatically a continuous linear map
`M →L[R] R`. Postcomposing a continuous map `f : C(X, M)` with these continuous coordinate forms
decomposes `f` in `C(X, M)` into a finite linear combination of continuous scalar-valued coordinate
functions (`ContinuousMap.eq_sum_smul_const`), and for a topological `R`-algebra `A` over a compact
commutative semiring `R` into `A`-multiples of `algebraMapCLM R A` postcomposed with those
coordinates (`ContinuousMap.eq_sum_smul_algebraMapCLM_comp`).
-/

public section

namespace ContinuousMap

/-- Every continuous map `f : C(X, M)` into a finitely generated Hausdorff topological module `M`
with continuous addition and scalar action over a compact topological semiring `R` decomposes along
any finite `R`-basis `b` of `M` into continuous `R`-valued coordinate functions multiplying the
constant basis maps. -/
theorem eq_sum_smul_const {X R M ι : Type*} [TopologicalSpace X]
    [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R] [CompactSpace R]
    [AddCommMonoid M] [TopologicalSpace M] [T2Space M] [ContinuousAdd M]
    [Module R M] [ContinuousSMul R M] [Module.Finite R M] [Fintype ι]
    (f : C(X, M)) (b : Module.Basis ι R M) :
    f = ∑ i : ι,
      (((b.coord i).toContinuousLinearMapOfFiniteOfCompactSpace : C(M, R)).comp f) •
        ContinuousMap.const X (b i) := by
  ext x
  simp only [coe_sum, Finset.sum_apply, smul_apply', comp_apply, ContinuousMap.coe_ofClass,
    LinearMap.coe_toContinuousLinearMapOfFiniteOfCompactSpace, Module.Basis.coord_apply,
    const_apply]
  exact (b.sum_repr (f x)).symm

/-- Every continuous map `f : C(X, A)` into a finitely generated Hausdorff topological `R`-algebra
`A` with continuous `R`-action over a compact topological commutative semiring `R` decomposes along
any finite `R`-basis `b` of `A` into `A`-multiples of `algebraMapCLM R A` postcomposed with the
continuous `R`-valued coordinate functions. -/
theorem eq_sum_smul_algebraMapCLM_comp {X R A ι : Type*} [TopologicalSpace X]
    [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] [CompactSpace R]
    [Semiring A] [TopologicalSpace A] [IsTopologicalSemiring A] [T2Space A]
    [Algebra R A] [ContinuousSMul R A] [Module.Finite R A] [Fintype ι]
    (f : C(X, A)) (b : Module.Basis ι R A) :
    f = ∑ i : ι, b i •
      (algebraMapCLM R A : C(R, A)).comp
        (((b.coord i).toContinuousLinearMapOfFiniteOfCompactSpace : C(A, R)).comp f) := by
  ext x
  simp only [coe_sum, coe_smul, Finset.sum_apply, Pi.smul_apply, comp_apply,
    ContinuousMap.coe_ofClass, algebraMapCLM_apply,
    LinearMap.coe_toContinuousLinearMapOfFiniteOfCompactSpace, Module.Basis.coord_apply,
    smul_eq_mul, ← Algebra.commutes, ← Algebra.smul_def]
  exact (b.sum_repr (f x)).symm

end ContinuousMap

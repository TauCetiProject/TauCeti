/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Universal kernels

A kernel `k : X → X → 𝕜` with values in a topological semiring `𝕜` is *universal*
(`TauCeti.IsUniversalKernel`) when its continuous sections `k x` span a dense `𝕜`-submodule of
`C(X, 𝕜)` for the compact-open topology. For real or complex scalars (`RCLike 𝕜`) on a compact
space the compact-open topology is that of uniform convergence, and for a continuous kernel the
condition is Steinwart's universality. On a finite discrete space every kernel with invertible
matrix is universal, over any topological semiring. For real or complex scalars this includes every
positive-definite kernel, while the constant kernel `1`, which is positive semidefinite, is not
universal on two points.

## Main definitions

* `TauCeti.IsUniversalKernel`: the continuous sections of a kernel span a dense subspace of
  `C(X, 𝕜)` for the compact-open topology.

## Main results

* `TauCeti.isUniversalKernel_of_isUnit`: on a finite discrete space, a kernel with invertible
  matrix over a topological semiring is universal.
* `Matrix.PosDef.isUniversalKernel`: on a finite discrete space, a positive-definite kernel with
  real or complex values is universal.

## References

* I. Steinwart, *On the influence of the kernel on the consistency of support vector machines*,
  J. Mach. Learn. Res. 2 (2001), 67--93, Definition 4.
-/

public section

open scoped ComplexOrder

namespace TauCeti

variable {𝕜 X : Type*} [Semiring 𝕜] [TopologicalSpace 𝕜] [IsTopologicalSemiring 𝕜]
  [TopologicalSpace X]

/-- A kernel `k : X → X → 𝕜` is *universal* when its continuous sections `k x` span a dense
subspace of `C(X, 𝕜)` for the compact-open topology; sections that are not continuous are
ignored. For real or complex scalars (`RCLike 𝕜`) on a compact space this says that every
continuous function is a uniform limit of finite linear combinations `∑ i, c i • k (x i)` of
sections, so for a continuous real or complex kernel on a compact space it is Steinwart's
universality. -/
def IsUniversalKernel (k : X → X → 𝕜) : Prop :=
  Dense (Submodule.span 𝕜 {f : C(X, 𝕜) | ∃ x, ⇑f = k x} : Set C(X, 𝕜))

theorem isUniversalKernel_def (k : X → X → 𝕜) :
    IsUniversalKernel k ↔ Dense (Submodule.span 𝕜 {f : C(X, 𝕜) | ∃ x, ⇑f = k x} : Set C(X, 𝕜)) :=
  Iff.rfl

open Matrix in
/-- On a finite discrete space, a kernel whose matrix is invertible is universal: its sections are
the rows of the matrix, which span every function. -/
theorem isUniversalKernel_of_isUnit [Fintype X] [DecidableEq X] [DiscreteTopology X]
    {k : X → X → 𝕜} (hk : IsUnit (Matrix.of k)) : IsUniversalKernel k := by
  have htop : Submodule.span 𝕜 {f : C(X, 𝕜) | ∃ x, ⇑f = k x} = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun f ↦ ?_
    -- `f` is the combination of the sections with coefficients `f ᵥ* k⁻¹`.
    have hf : f = ∑ x, (⇑f ᵥ* (↑hk.unit⁻¹ : Matrix X X 𝕜)) x •
        (⟨k x, continuous_of_discreteTopology⟩ : C(X, 𝕜)) := by
      ext y
      have h : (⇑f ᵥ* (↑hk.unit⁻¹ : Matrix X X 𝕜)) ᵥ* Matrix.of k = ⇑f := by
        rw [vecMul_vecMul, hk.val_inv_mul, vecMul_one]
      simpa [vecMul, dotProduct] using (congrFun h y).symm
    rw [hf]
    exact Submodule.sum_mem _ fun x _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  rw [isUniversalKernel_def, htop, Submodule.top_coe]
  exact dense_univ

end TauCeti

namespace Matrix.PosDef

variable {𝕜 X : Type*} [RCLike 𝕜] [TopologicalSpace X]

/-- On a finite discrete space, a positive-definite kernel is universal. A positive-semidefinite
kernel need not be: the constant kernel `1` on two points has only constant sections. -/
theorem isUniversalKernel [Finite X] [DiscreteTopology X] {k : X → X → 𝕜}
    (hk : Matrix.PosDef k) : TauCeti.IsUniversalKernel k := by
  classical
  have := Fintype.ofFinite X
  exact TauCeti.isUniversalKernel_of_isUnit hk.isUnit

end Matrix.PosDef

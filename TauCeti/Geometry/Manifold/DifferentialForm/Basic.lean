/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Defs

/-!
# Rough differential forms

A rough bundle-valued differential form assigns a continuous alternating map to each
tangent fiber, with values in an arbitrary family of real modules equipped with arbitrary
topologies. No regularity in the base point, global trivialization, connection, or fiber norm
is required.
Fixed-coefficient forms are the specialization to the trivial value bundle, and a function
`f : M → F` is the fixed-coefficient `0`-form `RoughForm.ofFunction I f`, and a real one-form `α`
has the kernel distribution `RoughForm.ker α`, `x ↦ ker α_x`.

This is the unbundled section description of differential forms from Lee,
*Introduction to Smooth Manifolds*, second edition, Chapter 14, using Mathlib's
`ContinuousAlternatingMap` carrier.
-/

public section

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]

/-- A rough degree-`k` form with values in the family `V` of real modules equipped with arbitrary
topologies. -/
abbrev RoughBundleForm (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] (k : ℕ) : Type _ :=
  (x : M) → TangentSpace I x [⋀^Fin k]→L[ℝ] V x

/-- A rough form with fixed coefficients, the trivial-value-bundle specialization. -/
abbrev RoughForm (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (F : Type*) [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (k : ℕ) : Type _ :=
  RoughBundleForm I M (Bundle.Trivial M F) k

/-- The `0`-form of a function: at each point, the alternating map of degree zero with value
`f x`. -/
noncomputable def RoughForm.ofFunction (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (f : M → F) : RoughForm I M F 0 :=
  fun x ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentSpace I x) (Fin 0) (f x)

/-- Evaluation of the `0`-form of a function on the empty tuple of tangent vectors. -/
@[simp]
theorem RoughForm.ofFunction_apply {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (f : M → F) (x : M) (v : Fin 0 → TangentSpace I x) :
    RoughForm.ofFunction I f x v = f x := (rfl)

/-- The `0`-form of a scalar multiple of a function is the scalar multiple of its `0`-form. -/
@[simp]
theorem RoughForm.ofFunction_smul {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    {S : Type*} [Monoid S] [DistribMulAction S F] [ContinuousConstSMul S F]
    [SMulCommClass ℝ S F] (c : S) (f : M → F) :
    RoughForm.ofFunction I (c • f) = c • RoughForm.ofFunction I f :=
  (rfl)

/-- Every `0`-form is the `0`-form of its values on the empty tuple of tangent vectors. -/
theorem RoughForm.eq_ofFunction {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (φ : RoughForm I M F 0) : φ = RoughForm.ofFunction I fun x ↦ φ x 0 := by
  funext x
  ext v
  rw [RoughForm.ofFunction_apply, Subsingleton.elim v 0]

section Kernel

variable {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace RoughForm

/-- The kernel distribution of a one-form `α`: at each point `x`, the subspace of tangent vectors
`v` with `α_x (v) = 0`. -/
noncomputable def ker (α : RoughForm I M ℝ 1) (x : M) : Submodule ℝ (TangentSpace I x) :=
  LinearMap.ker
    ((ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1)).symm (α x) :
      TangentSpace I x →ₗ[ℝ] ℝ)

@[simp]
theorem mem_ker {α : RoughForm I M ℝ 1} {x : M} {v : TangentSpace I x} :
    v ∈ α.ker x ↔ α x ![v] = 0 := by
  rw [ker, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply, Matrix.vec_single_eq_const]

/-- Rescaling a one-form by a function that does not vanish at `x` does not change its kernel
at `x`. -/
theorem ker_fun_smul {α : RoughForm I M ℝ 1} {f : M → ℝ} {x : M} (hfx : f x ≠ 0) :
    ker (fun y ↦ f y • α y) x = α.ker x := by
  ext v
  simp [hfx]

@[simp]
theorem ker_neg (α : RoughForm I M ℝ 1) (x : M) : (-α).ker x = α.ker x := by
  ext v
  simp

end RoughForm

end Kernel

end TauCeti

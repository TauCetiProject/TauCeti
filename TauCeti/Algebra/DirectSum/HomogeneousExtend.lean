/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Linear maps prescribed on homogeneous pieces

Linear maps `𝒰 i →ₗ[R] M` prescribed on the pieces of an internal direct-sum decomposition
of `U` extend uniquely to a linear map `U →ₗ[R] M`. The extension is the sum of the
prescribed values on the homogeneous components of its input, which is a finite sum.

## Main definitions

* `DirectSum.homogeneousExtend`: the extension of maps prescribed on all homogeneous pieces.

Adapted from `Mei/Algebra/DirectSum/Map.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

namespace DirectSum

variable {R U M ι : Type*} [Semiring R] [AddCommMonoid U] [Module R U]
  [AddCommMonoid M] [Module R M] [DecidableEq ι]
  (𝒰 : ι → Submodule R U) [Decomposition 𝒰]

/-- Extend linear maps on all homogeneous pieces to the decomposed module. -/
noncomputable def homogeneousExtend (f : ∀ i, 𝒰 i →ₗ[R] M) : U →ₗ[R] M :=
  (toModule R ι M f).comp (decomposeLinearEquiv 𝒰).toLinearMap

/-- A homogeneous extension agrees with its prescribed homogeneous map. -/
theorem homogeneousExtend_of_mem (f : ∀ i, 𝒰 i →ₗ[R] M) {i : ι} {a : U}
    (ha : a ∈ 𝒰 i) : homogeneousExtend 𝒰 f a = f i ⟨a, ha⟩ := by
  simp only [homogeneousExtend, LinearMap.comp_apply, LinearEquiv.coe_coe,
    decomposeLinearEquiv_apply, decompose_of_mem 𝒰 ha, ← lof_eq_of R, toModule_lof]

/-- Evaluate a homogeneous extension directly on a homogeneous subtype. -/
@[simp]
theorem homogeneousExtend_coe (f : ∀ i, 𝒰 i →ₗ[R] M) {i : ι} (a : 𝒰 i) :
    homogeneousExtend 𝒰 f a = f i a :=
  homogeneousExtend_of_mem 𝒰 f a.property

/-- A homogeneous extension is the finite sum of its values on the homogeneous components. -/
theorem homogeneousExtend_eq_sum [∀ i (a : 𝒰 i), Decidable (a ≠ 0)]
    (f : ∀ i, 𝒰 i →ₗ[R] M) (a : U) :
    homogeneousExtend 𝒰 f a = ∑ i ∈ (decompose 𝒰 a).support, f i (decompose 𝒰 a i) := by
  classical
  conv_lhs => rw [← sum_support_decompose 𝒰 a]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact homogeneousExtend_of_mem 𝒰 f (decompose 𝒰 a i).property

/-- Prescribed restrictions to the homogeneous pieces determine a linear map uniquely. -/
theorem homogeneousExtend_unique (f : ∀ i, 𝒰 i →ₗ[R] M) (g : U →ₗ[R] M)
    (hg : ∀ i, g.comp (𝒰 i).subtype = f i) : g = homogeneousExtend 𝒰 f := by
  apply decompose_lhom_ext 𝒰
  intro i
  rw [hg i]
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, homogeneousExtend_coe]

end DirectSum

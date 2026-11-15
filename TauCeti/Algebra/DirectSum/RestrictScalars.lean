/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.DirectSum.Internal
public import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Restriction of scalars for internal decompositions

Restricting scalars in each homogeneous submodule preserves an internal direct
sum decomposition. Its homogeneous projections have the same underlying values,
so a subobject is homogeneous before restriction exactly when it is homogeneous
after restriction. This lets graded constructions retain their components when
the coefficient semiring changes.

Adapted from `Mei/Algebra/DirectSum/RestrictScalars.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `68536122a97fed8e87bc6870b9427151971b9ab2` (Apache 2.0).
-/

public section

namespace DirectSum

variable {R S M ι : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
  [Module S M] [Module R M] [SMul R S] [IsScalarTower R S M]
  [DecidableEq ι] (ℳ : ι → Submodule S M) [Decomposition ℳ]

/-- Restricting the scalar action on every summand preserves its decomposition. -/
instance Decomposition.restrictScalars :
    Decomposition (fun i => (ℳ i).restrictScalars R) where
  decompose' := decompose ℳ
  left_inv := (decompose ℳ).left_inv
  right_inv := (decompose ℳ).right_inv

/-- Restriction of scalars leaves the homogeneous components unchanged. -/
@[simp]
theorem coe_decompose_restrictScalars (x : M) (i : ι) :
    (decompose (fun i => (ℳ i).restrictScalars R) x i : M) =
      (decompose ℳ x i : M) := by
  exact (map_decompose_shift ℳ (fun i => (ℳ i).restrictScalars R)
    (AddMonoidHom.id M) id Function.injective_id (fun _ _ h => h) i x).symm

/-- Homogeneity of any subobject is independent of the restricted scalar action. -/
@[simp]
theorem isHomogeneous_restrictScalars_iff {P : Type*} [SetLike P M] (p : P) :
    SetLike.IsHomogeneous (fun i => (ℳ i).restrictScalars R) p ↔
      SetLike.IsHomogeneous ℳ p := by
  simp only [SetLike.IsHomogeneous, coe_decompose_restrictScalars]

end DirectSum

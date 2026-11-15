/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.GradedCorrespondence.Basic
public import TauCeti.Algebra.DirectSum.RestrictScalars

/-!
# Restricting scalars in homogeneous correspondences

Restricting scalars preserves the span, its admissible lifts and its homogeneous
transfers. This allows coefficient maps between algebras over different rings
to be compared as linear morphisms over their common scalar ring.

We use `LinearMap.restrictScalars` and the existing scalar restriction of internal
decompositions; no new choice of homogeneous projection or lift is made.

Adapted from `Mei/LinearAlgebra/GradedCorrespondence/RestrictScalars.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

namespace TauCeti.GradedCorrespondence

variable {R S B U V ι κ : Type*} [Semiring R] [Semiring S] [SMul R S]
  [AddCommMonoid B] [Module S B] [Module R B] [IsScalarTower R S B]
  [AddCommMonoid U] [Module S U] [Module R U] [IsScalarTower R S U]
  [AddCommMonoid V] [Module S V] [Module R V] [IsScalarTower R S V]
  {𝒰 : ι → Submodule S U} {𝒱 : κ → Submodule S V} {I : Set ι} {J : Set κ}

/-- Forget part of the scalar action without changing the span or chosen lifts. -/
def restrictScalars (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) (R : Type*)
    [Semiring R] [SMul R S] [Module R B] [Module R U] [Module R V]
    [IsScalarTower R S B] [IsScalarTower R S U] [IsScalarTower R S V] :
    GradedCorrespondence (B := B) (fun i => (𝒰 i).restrictScalars R)
      (fun j => (𝒱 j).restrictScalars R) I J where
  left := C.left.restrictScalars R
  right := C.right.restrictScalars R
  liftLeft i := (C.liftLeft i).restrictScalars R
  liftRight j := (C.liftRight j).restrictScalars R
  left_liftLeft i := by ext x; exact C.left_liftLeft_apply i x
  right_liftRight j := by ext x; exact C.right_liftRight_apply j x

@[simp]
theorem restrictScalars_left (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) :
    (C.restrictScalars R).left = C.left.restrictScalars R := (rfl)

@[simp]
theorem restrictScalars_right (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) :
    (C.restrictScalars R).right = C.right.restrictScalars R := (rfl)

@[simp]
theorem restrictScalars_liftLeft_apply (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (i : I) (a : (𝒰 i).restrictScalars R) :
    (C.restrictScalars R).liftLeft i a = C.liftLeft i a :=
  LinearMap.restrictScalars_apply R (C.liftLeft i) a

@[simp]
theorem restrictScalars_liftRight_apply (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (j : J) (a : (𝒱 j).restrictScalars R) :
    (C.restrictScalars R).liftRight j a = C.liftRight j a :=
  LinearMap.restrictScalars_apply R (C.liftRight j) a

/-- Restricting scalars leaves the underlying value of each homogeneous transfer unchanged. -/
@[simp↓]
theorem restrictScalars_transfer_apply [DecidableEq κ] [DirectSum.Decomposition 𝒱]
    (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (i : I) (j : κ) (a : (𝒰 i).restrictScalars R) :
    ((C.restrictScalars R).transfer i j a : V) =
      (C.transfer i j ⟨a, a.property⟩ : V) := by
  -- The restricted lift has the same underlying function; repackage its input
  -- explicitly in the original homogeneous submodule.
  have hLift : (C.restrictScalars R).liftLeft i a = C.liftLeft i ⟨a, a.property⟩ := by
    rfl
  rw [transfer_apply, transfer_apply, hLift, restrictScalars_right,
    LinearMap.restrictScalars_apply]
  exact DirectSum.coe_decompose_restrictScalars (R := R) 𝒱
    (C.right (C.liftLeft i ⟨a, a.property⟩)) j

/-- Reversing a correspondence commutes with restriction of scalars. -/
@[simp]
theorem restrictScalars_symm (C : GradedCorrespondence (B := B) 𝒰 𝒱 I J) :
    C.symm.restrictScalars R = (C.restrictScalars R).symm := by
  ext <;> simp

end TauCeti.GradedCorrespondence

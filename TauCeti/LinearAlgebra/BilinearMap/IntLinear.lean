/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Biadditive maps as integer-bilinear maps

A biadditive map `μ : M →+ N →+ P` of additive commutative groups is `ℤ`-bilinear, since the
`ℤ`-module structure of an additive group is its own addition. This file packages that as
`AddMonoidHom.toIntLinearMap₂`, the two-variable counterpart of Mathlib's
`AddMonoidHom.toIntLinearMap`, so that constructions stated for bilinear maps over a ring can be
fed a biadditive pairing directly.
-/

public section

namespace AddMonoidHom

variable {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

/-- Reinterpret a biadditive map as a `ℤ`-bilinear map. -/
def toIntLinearMap₂ (μ : M →+ N →+ P) : M →ₗ[ℤ] N →ₗ[ℤ] P :=
  LinearMap.mk₂ ℤ (fun m n ↦ μ m n) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)
    (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp)

@[simp]
theorem toIntLinearMap₂_apply (μ : M →+ N →+ P) (m : M) (n : N) :
    μ.toIntLinearMap₂ m n = μ m n := by
  rw [toIntLinearMap₂, LinearMap.mk₂_apply]

end AddMonoidHom

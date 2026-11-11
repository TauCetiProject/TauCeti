/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Separating bilinear maps and torsion

A module carrying a map that is linear and separating in its first argument, with values in a
torsion-free module, is itself torsion-free: if `r` is regular and `r • x₁ = r • x₂`, then
`r • B (x₁ - x₂) y = B (r • x₁ - r • x₂) y = 0` forces `B (x₁ - x₂) y = 0` for every `y`, so
`x₁ = x₂`. For instance, an abelian group carrying a nondegenerate integral bilinear form is
torsion-free, hence flat over `ℤ`.

## Main results

* `LinearMap.SeparatingLeft.isTorsionFree`: a module with a left-separating map, linear in its
  first argument and semilinear in its second, into a torsion-free module is torsion-free.
-/

public section

namespace LinearMap

variable {R S M N P : Type*} [CommSemiring R] [CommSemiring S] [AddCommGroup M] [Module R M]
  [AddCommMonoid N] [Module S N] [AddCommGroup P] [Module R P] [Module.IsTorsionFree R P]
  {I : S →+* R}

/-- A module carrying a map that is linear in its first argument, semilinear in its second and
separates points in its first argument, with values in a torsion-free module, is torsion-free. -/
theorem SeparatingLeft.isTorsionFree {B : M →ₗ[R] N →ₛₗ[I] P} (hB : B.SeparatingLeft) :
    Module.IsTorsionFree R M where
  isSMulRegular _ hr x₁ x₂ h := sub_eq_zero.1 <| hB _ fun y ↦ hr.smul_eq_zero_iff_right.1 <| by
    rw [← map_smul₂, smul_sub, sub_eq_zero.2 h, map_zero₂]

end LinearMap

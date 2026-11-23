/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Matrix

/-!
# Lie modules in coordinates

Let a Lie algebra `L` act on a free module `M` through `ρ : L → End M`, and on the coordinate space
`n → R` through matrices `g : L → gl n R`, acting by multiplication on vectors
(`Matrix.lie_apply`). If `g x` is the matrix of `ρ x` in a basis `B` of `M` for every `x`, then
taking coordinates in `B` intertwines the two actions. `TauCeti.lieModuleEquivOfToMatrix` packages
this as an equivalence of Lie modules; it is how a representation given by explicit matrices is
identified with a pulled-back standard module.

## Main definitions

* `TauCeti.lieModuleEquivOfToMatrix`: taking coordinates in `B`, as an equivalence of Lie modules
  from `M`, acted on through `ρ`, to `n → R`, acted on through `g`.
-/

public section

open Module

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R L M n : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [Fintype n] [DecidableEq n]

/-- **Coordinates in a basis as an equivalence of Lie modules.** Let `L` act on `M` through `ρ`,
and on `n → R` through the matrices `g`. If `g x` is the matrix of `ρ x` in a basis `B` of `M` for
every `x`, then taking coordinates in `B` is an equivalence of Lie modules. -/
noncomputable def lieModuleEquivOfToMatrix (ρ : L →ₗ⁅R⁆ Module.End R M)
    (g : L →ₗ⁅R⁆ Matrix n n R) (B : Basis n R M)
    (hg : ∀ x, g x = LinearMap.toMatrix B B (ρ x)) :
    letI : LieRingModule L M := LieRingModule.compLieHom _ ρ
    letI : LieRingModule L (n → R) := LieRingModule.compLieHom _ g
    M ≃ₗ⁅R, L⁆ (n → R) :=
  letI : LieRingModule L M := LieRingModule.compLieHom _ ρ
  letI : LieRingModule L (n → R) := LieRingModule.compLieHom _ g
  { B.equivFun with
    map_lie' := fun {x s} ↦ by
      simp only [LieRingModule.compLieHom_apply, Matrix.lie_apply, Module.End.lie_apply,
        AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, hg,
        Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr] }

/-- The Lie module equivalence `lieModuleEquivOfToMatrix` takes coordinates in `B`. -/
@[simp]
theorem lieModuleEquivOfToMatrix_apply (ρ : L →ₗ⁅R⁆ Module.End R M)
    (g : L →ₗ⁅R⁆ Matrix n n R) (B : Basis n R M)
    (hg : ∀ x, g x = LinearMap.toMatrix B B (ρ x)) (s : M) :
    letI : LieRingModule L M := LieRingModule.compLieHom _ ρ
    letI : LieRingModule L (n → R) := LieRingModule.compLieHom _ g
    lieModuleEquivOfToMatrix ρ g B hg s = B.equivFun s :=
  (rfl)

/-- The inverse of the Lie module equivalence `lieModuleEquivOfToMatrix` reconstructs a vector
from its coordinates in `B`. -/
@[simp]
theorem lieModuleEquivOfToMatrix_symm_apply (ρ : L →ₗ⁅R⁆ Module.End R M)
    (g : L →ₗ⁅R⁆ Matrix n n R) (B : Basis n R M)
    (hg : ∀ x, g x = LinearMap.toMatrix B B (ρ x)) (v : n → R) :
    letI : LieRingModule L M := LieRingModule.compLieHom _ ρ
    letI : LieRingModule L (n → R) := LieRingModule.compLieHom _ g
    (lieModuleEquivOfToMatrix ρ g B hg).symm v = B.equivFun.symm v :=
  (rfl)

end TauCeti

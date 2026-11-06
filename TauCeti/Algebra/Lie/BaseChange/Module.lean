/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange

/-!
# Extension of scalars for Lie-module maps

A Lie-module map `f : M →ₗ⁅R,L⁆ N` remains equivariant after extending scalars from `R` to an
`R`-algebra `A` on both the Lie algebra and its modules, using Mathlib's Lie algebra structure on
`A ⊗[R] L` and its action on `A ⊗[R] M`. This transports an equivariant map together with the
action, for example from an integral form of a Lie algebra and its representations to their
reductions modulo a prime.

## Main definitions

* `LieModuleHom.baseChange`: the extension of scalars
  `A ⊗[R] M →ₗ⁅A,A ⊗[R] L⁆ A ⊗[R] N` of a Lie-module map, with underlying linear map
  `LinearMap.baseChange`.

## Main statements

* `LieModuleHom.baseChange_id` and `LieModuleHom.baseChange_comp`: extension of scalars is
  functorial.
-/

public section

open LieModule
open scoped TensorProduct

namespace LieModuleHom

variable {R L M N : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
  (A : Type*) [CommRing A] [Algebra R A]

/-- Extending scalars preserves the equivariance of a Lie-module map. -/
@[simp] theorem baseChange_map_lie (f : M →ₗ⁅R,L⁆ N) (x : A ⊗[R] L) (m : A ⊗[R] M) :
    f.toLinearMap.baseChange A ⁅x, m⁆ = ⁅x, f.toLinearMap.baseChange A m⁆ := by
  induction x with
  | add x y hx hy =>
    simp only [add_lie (M := A ⊗[R] M), add_lie (M := A ⊗[R] N), map_add, hx, hy]
  | tmul a x => induction m <;> simp_all

/-- Extend scalars on a Lie-module morphism, including its acting Lie algebra. -/
def baseChange (f : M →ₗ⁅R,L⁆ N) :
    (A ⊗[R] M) →ₗ⁅A,A ⊗[R] L⁆ (A ⊗[R] N) where
  toLinearMap := f.toLinearMap.baseChange A
  map_lie' {x m} := baseChange_map_lie A f x m

/-- The underlying linear map of scalar extension is the linear scalar extension. -/
@[simp] theorem toLinearMap_baseChange (f : M →ₗ⁅R,L⁆ N) :
    (f.baseChange A).toLinearMap = f.toLinearMap.baseChange A :=
  (rfl)

/-- On a pure tensor, scalar extension applies the map to the second factor. -/
@[simp] theorem baseChange_tmul (f : M →ₗ⁅R,L⁆ N) (a : A) (m : M) :
    f.baseChange A (a ⊗ₜ[R] m) = a ⊗ₜ[R] f m :=
  (rfl)

/-- As a function, scalar extension is the linear scalar extension. Not `@[simp]`: as for
`LieHom.baseChange`, the simp normal form keeps `LieModuleHom.baseChange` and evaluates it on pure
tensors by `LieModuleHom.baseChange_tmul`. -/
theorem coe_baseChange (f : M →ₗ⁅R,L⁆ N) :
    ⇑(f.baseChange A) = ⇑(f.toLinearMap.baseChange A) :=
  (rfl)

/-- Extension of scalars is functorial: it takes the identity to the identity. -/
@[simp]
theorem baseChange_id : (LieModuleHom.id : M →ₗ⁅R,L⁆ M).baseChange A = LieModuleHom.id := by
  ext x
  exact DFunLike.congr_fun (LinearMap.baseChange_id (R := R) (A := A) (M := M)) x

/-- Extension of scalars is functorial: it takes a composition to the composition. -/
theorem baseChange_comp {P : Type*} [AddCommGroup P] [Module R P] [LieRingModule L P]
    [LieModule R L P] (g : N →ₗ⁅R,L⁆ P) (f : M →ₗ⁅R,L⁆ N) :
    (g.comp f).baseChange A = (g.baseChange A).comp (f.baseChange A) := by
  ext x
  exact DFunLike.congr_fun (LinearMap.baseChange_comp (A := A) (f := f.toLinearMap)
    (g := g.toLinearMap)) x

end LieModuleHom

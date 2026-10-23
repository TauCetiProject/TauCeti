/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Representations as multiplicative automorphisms

`Representation.toMulAut` views a representation of a group on a module
as an action by automorphisms on its multiplicative type tag. This lets the representation act
on exponents in a group algebra via `MonoidAlgebra.domCongrAut`.
-/

public section

namespace Representation

variable {R G M : Type*} [Semiring R] [Group G] [AddCommMonoid M] [Module R M]

/-- A representation, acting by automorphisms in multiplicative notation. -/
noncomputable def toMulAut (rho : Representation R G M) :
    G →* MulAut (Multiplicative M) where
  toFun g :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R M
      ((MonoidHom.toHomUnits rho) g)).toAddEquiv.toMultiplicative
  map_one' := by
    ext m
    exact congrArg
      (fun f : M →ₗ[R] M => Multiplicative.ofAdd (f m.toAdd)) (map_one rho)
  map_mul' g h := by
    ext m
    exact congrArg
      (fun f : M →ₗ[R] M => Multiplicative.ofAdd (f m.toAdd)) (map_mul rho g h)

/-- The multiplicative automorphism acts by the representation on the underlying module. -/
@[simp]
theorem toMulAut_apply (rho : Representation R G M) (g : G)
    (m : Multiplicative M) :
    toMulAut rho g m = Multiplicative.ofAdd (rho g m.toAdd) := by
  exact congrArg (fun f : M →ₗ[R] M => Multiplicative.ofAdd (f m.toAdd))
    (MonoidHom.coe_toHomUnits rho g)

/-- The inverse multiplicative automorphism acts by the representation of the inverse element. -/
@[simp]
theorem toMulAut_symm_apply (rho : Representation R G M)
    (g : G) (m : Multiplicative M) :
    (toMulAut rho g).symm m = Multiplicative.ofAdd (rho g⁻¹ m.toAdd) := by
  have hinv : (↑(((MonoidHom.toHomUnits rho) g)⁻¹) : M →ₗ[R] M) = rho g⁻¹ := by
    rw [← map_inv, MonoidHom.coe_toHomUnits]
  exact congrArg (fun f : M →ₗ[R] M => Multiplicative.ofAdd (f m.toAdd)) hinv

end Representation

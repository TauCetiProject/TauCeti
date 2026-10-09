/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Scalar duals as right modules

The scalar dual of a left module over a `k`-algebra is a right module, with action
`(a • φ)(x) = φ(a.unop • x)`. Bundling this action in `ModuleCat` avoids installing a
competing module instance on every linear dual. Evaluation identifies a finite-dimensional
module with the scalar dual of this right module. This pairing is used to form `Tr D`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section I.3.
-/

public section

namespace ModuleCat

universe u v w

variable (k : Type u) {A : Type v} [Field k] [Ring A] [Algebra k A]

attribute [local instance] moduleOfAlgebraModule isScalarTower_of_algebra_moduleCat

/-- The `k`-linear dual of a left `A`-module, carrying its right `A`-action.

The body is exposed because the module compiler requires the carrier identification when
compiling `rightScalarDualEquiv` and `rightScalarDualIso`. Use their evaluation API downstream. -/
@[expose] def rightScalarDual (M : ModuleCat.{w} A) : ModuleCat.{max u w} Aᵐᵒᵖ := by
  let : Module Aᵐᵒᵖ (Module.Dual k M) := Module.compHom _
    { toFun := fun (a : Aᵐᵒᵖ) ↦ (Module.toModuleEnd k M a.unop).dualMap
      map_one' := by ext; simp
      map_mul' := fun _ _ ↦ by ext; simp [mul_smul]
      map_zero' := by ext; simp
      map_add' := fun _ _ ↦ by ext; simp [add_smul] }
  exact ModuleCat.of Aᵐᵒᵖ (Module.Dual k M)

/-- The underlying scalar space of the right dual is the ordinary linear dual. -/
def rightScalarDualEquiv (M : ModuleCat.{w} A) :
    rightScalarDual k M ≃ₗ[k] Module.Dual k M :=
  { toFun := fun φ ↦ φ
    invFun := fun φ ↦ φ
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun c φ ↦ by
      let ψ : Module.Dual k M := φ
      ext x
      -- The bundled scalar action restricts the new right action along the algebra map.
      change ψ ((algebraMap k A c) • x) = c • ψ x
      simp [algebraMap_smul] }

/-- The right action on the scalar dual is precomposition with the left action. -/
@[simp]
theorem rightScalarDualEquiv_smul (M : ModuleCat.{w} A) (a : Aᵐᵒᵖ)
    (φ : rightScalarDual k M) (x : M) :
    rightScalarDualEquiv k M (a • φ) x = rightScalarDualEquiv k M φ (a.unop • x) :=
  (rfl)

/-- The right scalar dual of a finite-dimensional module is finite-dimensional. -/
instance (M : ModuleCat.{w} A) [Module.Finite k M] :
    Module.Finite k (rightScalarDual k M) :=
  Module.Finite.equiv (rightScalarDualEquiv k M).symm

variable {k}

/-- An isomorphism of left modules induces an isomorphism of right scalar duals,
in the reverse direction. -/
def rightScalarDualIso {M N : ModuleCat.{w} A} (e : M ≅ N) :
    rightScalarDual k N ≅ rightScalarDual k M :=
  let d : rightScalarDual k N ≃ₗ[k] rightScalarDual k M :=
    (rightScalarDualEquiv k N).trans
      (((e.toLinearEquiv.restrictScalars k).dualMap).trans (rightScalarDualEquiv k M).symm)
  let f : rightScalarDual k N ≃ₗ[Aᵐᵒᵖ] rightScalarDual k M :=
    { toFun := d
      invFun := d.symm
      left_inv := d.left_inv
      right_inv := d.right_inv
      map_add' := d.map_add
      map_smul' := fun a φ ↦ by
        apply (rightScalarDualEquiv k M).injective
        ext x
        simp [d, rightScalarDualEquiv_smul, LinearEquiv.dualMap_apply] }
  f.toModuleIso

/-- The induced isomorphism of right duals acts by precomposition. -/
@[simp]
theorem rightScalarDualIso_hom_apply {M N : ModuleCat.{w} A} (e : M ≅ N)
    (φ : rightScalarDual k N) (x : M) :
    rightScalarDualEquiv k M ((rightScalarDualIso e).hom φ) x =
      rightScalarDualEquiv k N φ (e.hom x) := by
  simp [rightScalarDualIso, LinearEquiv.dualMap_apply]

variable (k)

/-- Evaluation pairs a finite-dimensional left module with its right scalar dual. -/
noncomputable def rightScalarDualEvalEquiv (M : ModuleCat.{w} A) [Module.Finite k M] :
    M ≃ₗ[k] Module.Dual k (rightScalarDual k M) :=
  (Module.evalEquiv k M).trans (rightScalarDualEquiv k M).dualMap

/-- Evaluation on the right scalar dual is application of the underlying functional. -/
@[simp]
theorem rightScalarDualEvalEquiv_apply (M : ModuleCat.{w} A)
    [Module.Finite k M]
    (x : M) (φ : rightScalarDual k M) :
    rightScalarDualEvalEquiv k M x φ = rightScalarDualEquiv k M φ x := by
  simp [rightScalarDualEvalEquiv, LinearEquiv.dualMap_apply]

/-- Evaluation respects the left action and its dual right action. -/
theorem rightScalarDualEvalEquiv_smul (M : ModuleCat.{w} A) [Module.Finite k M]
    (a : A) (x : M) (φ : rightScalarDual k M) :
    rightScalarDualEvalEquiv k M (a • x) φ =
      rightScalarDualEvalEquiv k M x (MulOpposite.op a • φ) := by
  simp

end ModuleCat

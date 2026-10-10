/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.LinearAlgebra.Dual.RightAction

/-!
# Scalar duals as right modules

The scalar dual of a left module `M` over a `k`-algebra `A` is a right module, with action
`(a • φ)(x) = φ(a.unop • x)`: this is `TauCeti.dualRightAction` for `M` viewed as a right
`Aᵐᵒᵖ`-module. Bundling this action in `ModuleCat` avoids installing a competing module instance
on every linear dual. The construction is a contravariant functor,
`ModuleCat.rightScalarDualFunctor`, acting on morphisms by precomposition. Evaluation identifies a
finite-dimensional module with the scalar dual of this right module. This pairing is used to form
`Tr D`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section I.3.
-/

public section

namespace ModuleCat

open CategoryTheory

universe u v w

variable (k : Type u) {A : Type v} [Field k] [Ring A] [Algebra k A]

attribute [local instance] moduleOfAlgebraModule isScalarTower_of_algebra_moduleCat

/-- A left `A`-module, viewed as a right `Aᵐᵒᵖ`-module. -/
private abbrev opOpModule (M : ModuleCat.{w} A) : Module Aᵐᵒᵖᵐᵒᵖ M :=
  Module.compHom M (RingEquiv.opOp A).symm.toRingHom

attribute [local instance] opOpModule

/-- The left `A`-action on `M` commutes with the `k`-action. -/
private theorem smulCommClass_opOp (M : ModuleCat.{w} A) : SMulCommClass Aᵐᵒᵖᵐᵒᵖ k M :=
  ⟨fun a c x ↦ smul_comm a.unop.unop c x⟩

attribute [local instance] smulCommClass_opOp

/-- The `k`-linear dual of a left `A`-module, carrying its right `A`-action
`(a • φ)(x) = φ(a.unop • x)`. -/
def rightScalarDual (M : ModuleCat.{w} A) : ModuleCat.{max u w} Aᵐᵒᵖ := by
  let : Module Aᵐᵒᵖ (Module.Dual k M) := Module.compHom _ (TauCeti.dualRightAction k M)
  exact ModuleCat.of Aᵐᵒᵖ (Module.Dual k M)

/-- The right action on the scalar dual, before identifying its carrier with the linear dual. -/
private theorem rightScalarDual_smul_apply (M : ModuleCat.{w} A) (a : Aᵐᵒᵖ)
    (φ : rightScalarDual k M) (x : M) :
    (show Module.Dual k M from a • φ) x = (show Module.Dual k M from φ) (a.unop • x) :=
  TauCeti.dualRightAction_apply_apply k M a φ x

/-- The underlying scalar space of the right dual is the ordinary linear dual. -/
-- Compiling this identity map would need the body of `rightScalarDual`, which stays unexposed.
noncomputable def rightScalarDualEquiv (M : ModuleCat.{w} A) :
    rightScalarDual k M ≃ₗ[k] Module.Dual k M :=
  { toFun := fun φ ↦ φ
    invFun := fun φ ↦ φ
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun c φ ↦ by
      ext x
      -- The bundled scalar action restricts the new right action along the algebra map.
      refine (rightScalarDual_smul_apply k M (algebraMap k Aᵐᵒᵖ c) φ x).trans ?_
      simp only [MulOpposite.algebraMap_apply, MulOpposite.unop_op, algebraMap_smul]
      exact (show Module.Dual k M from φ).map_smul c x }

/-- The right action on the scalar dual is precomposition with the left action. -/
@[simp]
theorem rightScalarDualEquiv_smul (M : ModuleCat.{w} A) (a : Aᵐᵒᵖ)
    (φ : rightScalarDual k M) (x : M) :
    rightScalarDualEquiv k M (a • φ) x = rightScalarDualEquiv k M φ (a.unop • x) :=
  rightScalarDual_smul_apply k M a φ x

/-- The right scalar dual of a finite-dimensional module is finite-dimensional. -/
instance (M : ModuleCat.{w} A) [Module.Finite k M] :
    Module.Finite k (rightScalarDual k M) :=
  Module.Finite.equiv (rightScalarDualEquiv k M).symm

/-- A morphism of left modules induces a morphism of right scalar duals, in the reverse
direction, by precomposition. -/
noncomputable def rightScalarDualMap {M N : ModuleCat.{w} A} (f : M ⟶ N) :
    rightScalarDual k N ⟶ rightScalarDual k M :=
  let d : rightScalarDual k N →ₗ[k] rightScalarDual k M :=
    (rightScalarDualEquiv k M).symm.toLinearMap ∘ₗ (f.hom.restrictScalars k).dualMap ∘ₗ
      (rightScalarDualEquiv k N).toLinearMap
  let g : rightScalarDual k N →ₗ[Aᵐᵒᵖ] rightScalarDual k M :=
    { toFun := d
      map_add' := d.map_add
      map_smul' := fun a φ ↦ by
        apply (rightScalarDualEquiv k M).injective
        ext x
        simp [d, LinearMap.dualMap_apply] }
  ModuleCat.ofHom (X := rightScalarDual k N) (Y := rightScalarDual k M) g

/-- The dual of a morphism acts by precomposition. -/
@[simp]
theorem rightScalarDualMap_apply {M N : ModuleCat.{w} A} (f : M ⟶ N)
    (φ : rightScalarDual k N) (x : M) :
    rightScalarDualEquiv k M (rightScalarDualMap k f φ) x = rightScalarDualEquiv k N φ (f x) :=
  (rfl)

/-- The right scalar dual as a contravariant functor from left to right modules. -/
@[expose, simps]
noncomputable def rightScalarDualFunctor :
    (ModuleCat.{w} A)ᵒᵖ ⥤ ModuleCat.{max u w} Aᵐᵒᵖ where
  obj M := rightScalarDual k M.unop
  map f := rightScalarDualMap k f.unop
  map_id M := by
    ext φ
    apply (rightScalarDualEquiv k M.unop).injective
    ext x
    simp
  map_comp f g := by
    ext φ
    apply (rightScalarDualEquiv k _).injective
    ext x
    simp

variable {k}

/-- An isomorphism of left modules induces an isomorphism of right scalar duals,
in the reverse direction. -/
noncomputable def rightScalarDualIso {M N : ModuleCat.{w} A} (e : M ≅ N) :
    rightScalarDual k N ≅ rightScalarDual k M :=
  (rightScalarDualFunctor k).mapIso e.op

/-- The induced isomorphism of right duals acts by precomposition. -/
@[simp]
theorem rightScalarDualIso_hom_apply {M N : ModuleCat.{w} A} (e : M ≅ N)
    (φ : rightScalarDual k N) (x : M) :
    rightScalarDualEquiv k M ((rightScalarDualIso e).hom φ) x =
      rightScalarDualEquiv k N φ (e.hom x) := by
  simp [rightScalarDualIso]

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

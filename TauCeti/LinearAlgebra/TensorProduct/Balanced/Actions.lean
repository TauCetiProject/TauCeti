/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic

/-!
# Outer actions on balanced tensor products

If `M` is a left `B`, right `A` bimodule and `N` is a left `A`, right `C`
bimodule, `M ⊗[A] N` inherits commuting left `B` and right `C` actions. These
actions make the balanced tensor product suitable for composition of bimodules.
Tensoring equivariant maps preserves the outer actions. The unit identifications
and their equivariance lemmas are in `Balanced.Unit`.

`leftAction` and `rightAction` describe the actions by ground-ring linear
endomorphisms. Install `leftModule` and `rightModule` explicitly with `letI` to
use scalar notation. They are not global instances: the same scalar ring can
act on both factors in different ways, so neither action should be selected
implicitly. `outerSMulCommClass` and the scalar-tower lemmas supply their
compatibilities. No flatness, grading, or differential is assumed here.

The construction uses `BalancedTensorProduct.map` and Mathlib's
`DistribMulAction.toModuleEnd` and `Module.compHom`. It follows the ordinary
bimodule tensor product in Keller, *Deriving DG categories*, Section 6.1.
-/

public section

namespace TauCeti.BalancedTensorProduct

open MulOpposite

variable (k A : Type*) [CommRing k] [Semiring A]
  (M N : Type*) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module A N]

section Left

variable (B : Type*) [Semiring B] [Module B M]
  [SMulCommClass B k M] [SMulCommClass B Aᵐᵒᵖ M]

/-- The left outer action induced from the first factor. -/
def leftAction : B →+* Module.End k (BalancedTensorProduct k A M N) where
  toFun b := map (DistribMulAction.toModuleEnd k M b) LinearMap.id
    (fun a m ↦ smul_comm b (op a) m) (fun _ _ ↦ rfl)
  map_one' := hom_ext fun m n ↦ by simp
  map_mul' b b' := hom_ext fun m n ↦ by simp [mul_smul]
  map_zero' := hom_ext fun m n ↦ by simp
  map_add' b b' := hom_ext fun m n ↦ by simp [add_smul, add_tmul]

@[simp]
theorem leftAction_tmul (b : B) (m : M) (n : N) :
    leftAction k A M N B b (tmul k A m n) = tmul k A (b • m) n := by
  simp [leftAction]

/-- The left outer module structure. Install it locally to select the first-factor action. -/
@[instance_reducible]
def leftModule : Module B (BalancedTensorProduct k A M N) :=
  Module.compHom _ (leftAction k A M N B)

attribute [local instance] leftModule

/-- Scalar notation for the left outer module is evaluation of `leftAction`. -/
theorem left_smul_def (b : B) (x : BalancedTensorProduct k A M N) :
    b • x = leftAction k A M N B b x := (rfl)

@[simp]
theorem left_smul_tmul (b : B) (m : M) (n : N) :
    b • tmul k A m n = tmul k A (b • m) n :=
  leftAction_tmul k A M N B b m n

/-- The left outer action commutes with ground-ring scalars. -/
theorem leftSMulCommClass : SMulCommClass B k (BalancedTensorProduct k A M N) where
  smul_comm b r x := (leftAction k A M N B b).map_smul r x

/-- The left outer action respects a ground-ring scalar tower on the first factor. -/
theorem leftScalarTower [SMul k B] [IsScalarTower k B M] :
    IsScalarTower k B (BalancedTensorProduct k A M N) where
  smul_assoc r b x := by
    induction x using induction_on with
    | ht m n => simp [smul_assoc]
    | ha x y hx hy => simp [smul_add, hx, hy]

end Left

section Right

variable (C : Type*) [Semiring C] [Module Cᵐᵒᵖ N]
  [SMulCommClass Cᵐᵒᵖ k N] [SMulCommClass Cᵐᵒᵖ A N]

/-- The right outer action induced from the second factor, represented by opposite scalars. -/
def rightAction : Cᵐᵒᵖ →+* Module.End k (BalancedTensorProduct k A M N) where
  toFun c := map LinearMap.id (DistribMulAction.toModuleEnd k N c)
    (fun _ _ ↦ rfl) (fun a n ↦ smul_comm c a n)
  map_one' := hom_ext fun m n ↦ by simp
  map_mul' c c' := hom_ext fun m n ↦ by simp [mul_smul]
  map_zero' := hom_ext fun m n ↦ by simp
  map_add' c c' := hom_ext fun m n ↦ by simp [add_smul, tmul_add]

@[simp]
theorem rightAction_tmul (c : Cᵐᵒᵖ) (m : M) (n : N) :
    rightAction k A M N C c (tmul k A m n) = tmul k A m (c • n) := by
  simp [rightAction]

/-- The right outer module structure. Install it locally to select the second-factor action. -/
@[instance_reducible]
def rightModule : Module Cᵐᵒᵖ (BalancedTensorProduct k A M N) :=
  Module.compHom _ (rightAction k A M N C)

attribute [local instance] rightModule

/-- Scalar notation for the right outer module is evaluation of `rightAction`. -/
theorem right_smul_def (c : Cᵐᵒᵖ) (x : BalancedTensorProduct k A M N) :
    c • x = rightAction k A M N C c x := (rfl)

@[simp]
theorem right_smul_tmul (c : Cᵐᵒᵖ) (m : M) (n : N) :
    c • tmul k A m n = tmul k A m (c • n) :=
  rightAction_tmul k A M N C c m n

/-- The right outer action commutes with ground-ring scalars. -/
theorem rightSMulCommClass : SMulCommClass Cᵐᵒᵖ k (BalancedTensorProduct k A M N) where
  smul_comm c r x := (rightAction k A M N C c).map_smul r x

/-- The right outer action respects a ground-ring scalar tower on the second factor. -/
theorem rightScalarTower [SMul k Cᵐᵒᵖ] [IsScalarTower k Cᵐᵒᵖ N] :
    IsScalarTower k Cᵐᵒᵖ (BalancedTensorProduct k A M N) where
  smul_assoc r c x := by
    induction x using induction_on with
    | ht m n => simp [smul_assoc]
    | ha x y hx hy => simp [smul_add, hx, hy]

end Right

section Bimodule

variable (B C : Type*) [Semiring B] [Semiring C]
  [Module B M] [SMulCommClass B k M] [SMulCommClass B Aᵐᵒᵖ M]
  [Module Cᵐᵒᵖ N] [SMulCommClass Cᵐᵒᵖ k N] [SMulCommClass Cᵐᵒᵖ A N]

attribute [local instance] leftModule rightModule

/-- The outer actions commute, so the tensor product is a left `B`, right `C` bimodule. -/
theorem outerSMulCommClass : SMulCommClass B Cᵐᵒᵖ (BalancedTensorProduct k A M N) where
  smul_comm b c x := by
    induction x using induction_on with
    | ht m n => simp
    | ha x y hx hy => simp [smul_add, hx, hy]

end Bimodule

section Map

variable {M' N' : Type*}
  [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M']
  [AddCommGroup N'] [Module k N'] [Module A N']

/-- Tensoring a map equivariant for the left outer action preserves that action. -/
@[simp]
theorem map_leftAction (B : Type*) [Semiring B]
    [Module B M] [SMulCommClass B k M] [SMulCommClass B Aᵐᵒᵖ M]
    [Module B M'] [SMulCommClass B k M'] [SMulCommClass B Aᵐᵒᵖ M']
    (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n)
    (hB : ∀ (b : B) m, f (b • m) = b • f m)
    (b : B) (x : BalancedTensorProduct k A M N) :
    map f g hf hg (leftAction k A M N B b x) =
      leftAction k A M' N' B b (map f g hf hg x) := by
  induction x using induction_on with
  | ht m n => simp [hB]
  | ha x y hx hy => simp [hx, hy]

/-- Tensoring a map equivariant for the right outer action preserves that action. -/
@[simp]
theorem map_rightAction (C : Type*) [Semiring C]
    [Module Cᵐᵒᵖ N] [SMulCommClass Cᵐᵒᵖ k N] [SMulCommClass Cᵐᵒᵖ A N]
    [Module Cᵐᵒᵖ N'] [SMulCommClass Cᵐᵒᵖ k N'] [SMulCommClass Cᵐᵒᵖ A N']
    (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n)
    (hC : ∀ (c : Cᵐᵒᵖ) n, g (c • n) = c • g n)
    (c : Cᵐᵒᵖ) (x : BalancedTensorProduct k A M N) :
    map f g hf hg (rightAction k A M N C c x) =
      rightAction k A M' N' C c (map f g hf hg x) := by
  induction x using induction_on with
  | ht m n => simp [hC]
  | ha x y hx hy => simp [hx, hy]

end Map

section Lift

variable {P : Type*} [AddCommGroup P] [Module k P]

/-- A balanced bilinear map equivariant in the first factor induces a left-equivariant map. -/
@[simp]
theorem lift_leftAction (B : Type*) [Semiring B]
    [Module B M] [SMulCommClass B k M] [SMulCommClass B Aᵐᵒᵖ M] [Module B P]
    (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (a : A) m n, f (op a • m) n = f m (a • n))
    (hB : ∀ (b : B) m n, f (b • m) n = b • f m n)
    (b : B) (x : BalancedTensorProduct k A M N) :
    lift f hf (leftAction k A M N B b x) = b • lift f hf x := by
  induction x using induction_on with
  | ht m n => simp [hB]
  | ha x y hx hy => simp [smul_add, hx, hy]

/-- A balanced bilinear map equivariant in the second factor induces a right-equivariant map. -/
@[simp]
theorem lift_rightAction (C : Type*) [Semiring C]
    [Module Cᵐᵒᵖ N] [SMulCommClass Cᵐᵒᵖ k N] [SMulCommClass Cᵐᵒᵖ A N]
    [Module Cᵐᵒᵖ P]
    (f : M →ₗ[k] N →ₗ[k] P)
    (hf : ∀ (a : A) m n, f (op a • m) n = f m (a • n))
    (hC : ∀ (c : Cᵐᵒᵖ) m n, f m (c • n) = c • f m n)
    (c : Cᵐᵒᵖ) (x : BalancedTensorProduct k A M N) :
    lift f hf (rightAction k A M N C c x) = c • lift f hf x := by
  induction x using induction_on with
  | ht m n => simp [hC]
  | ha x y hx hy => simp [smul_add, hx, hy]

end Lift

end TauCeti.BalancedTensorProduct

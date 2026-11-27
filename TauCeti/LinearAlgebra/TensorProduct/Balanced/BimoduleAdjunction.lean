/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Adjunction.Additive
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Actions

/-!
# The tensor–Hom adjunction for a bimodule

For an `(A, B)`-bimodule `M`, tensoring with `M` on the left sends left `B`-modules to left
`A`-modules. Its right adjoint sends `X` to the left `B`-module `Hom_A(M, X)`, where `b` acts
by precomposing with right multiplication by `b` on `M`. The balanced quotient over `ℤ`
allows arbitrary rings and equips the tensor with the outer action on `M`.

The adjunction sends `f` to `n ↦ (m ↦ f (m ⊗ n))`. See Wisbauer,
*Foundations of Module and Ring Theory*, §12.12, pp. 98–99.
-/

public section

universe v

open CategoryTheory MulOpposite

namespace TauCeti.BalancedTensorProduct

section HomAction

variable (A B : Type*) [Semiring A] [Semiring B] (M : Type*)
  [AddCommMonoid M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  (P : Type*) [AddCommMonoid P] [Module A P]

/-- The left action on `Hom_A(M, P)` induced by the right action on the bimodule `M`. -/
@[instance_reducible]
def bimodHomModule : Module B (M →ₗ[A] P) :=
  Module.compHom (R := DomMulAct Bᵐᵒᵖ) _ (RingEquiv.opOp B).toRingHom

/-- A scalar acts on a linear map by precomposition with right multiplication. -/
@[simp]
theorem bimodHomModule_smul_apply (b : B) (f : M →ₗ[A] P) (m : M) :
    letI := bimodHomModule A B M P
    (b • f) m = f (op b • m) :=
  DomMulAct.mk_smul_linearMap_apply (op b) f m

end HomAction

attribute [local instance 100] leftModule bimodHomModule

variable (A B : Type*) [Ring A] [Ring B] (M : Type v)
  [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]

private theorem bimodLeftLinearMap_ext {N : ModuleCat.{v} B}
    {P : Type*} [AddCommGroup P] [Module A P]
    {f g : BalancedTensorProduct ℤ B M N →ₗ[A] P}
    (h : ∀ m n, f (tmul ℤ B m n) = g (tmul ℤ B m n)) : f = g :=
  LinearMap.toAddMonoidHom_injective <|
    AddMonoidHom.toIntLinearMap_injective <| hom_ext h

/-- Tensoring left `B`-modules with the `(A, B)`-bimodule `M`, with the outer `A`-action. -/
def bimodLeftFunctor : ModuleCat.{v} B ⥤ ModuleCat.{v} A where
  obj N := ModuleCat.of A (BalancedTensorProduct ℤ B M N)
  map g := ModuleCat.ofHom
    { __ := (map LinearMap.id (g.hom.restrictScalars ℤ)
        (fun _ _ ↦ rfl) g.hom.map_smul).toAddMonoidHom
      map_smul' := fun a z ↦
        map_smul_left A LinearMap.id (g.hom.restrictScalars ℤ) (fun _ _ ↦ rfl)
          g.hom.map_smul (fun _ _ ↦ rfl) a z }
  map_id N := by
    apply ModuleCat.hom_ext
    apply bimodLeftLinearMap_ext A B M
    intro m n
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply bimodLeftLinearMap_ext A B M
    intro m n
    exact LinearMap.congr_fun
      (map_comp (A := B) (LinearMap.id : M →ₗ[ℤ] M) (f.hom.restrictScalars ℤ)
        LinearMap.id (g.hom.restrictScalars ℤ) (fun _ _ ↦ rfl) f.hom.map_smul
        (fun _ _ ↦ rfl) g.hom.map_smul) (tmul ℤ B m n)

/-- The Hom functor of a bimodule, with the left action induced by precomposition. -/
-- The compiler needs the linear-map carrier in the evaluation map.
@[expose]
def bimodHomRight : ModuleCat.{v} A ⥤ ModuleCat.{v} B where
  obj P := ModuleCat.of B (M →ₗ[A] P)
  map g := ModuleCat.ofHom
    { toFun := fun f ↦ g.hom.comp f
      map_add' := fun f f' ↦ LinearMap.ext fun m ↦ g.hom.map_add (f m) (f' m)
      map_smul' := fun b f ↦ by
        ext m
        simp }
  map_id P := by
    ext f m
    rfl
  map_comp f g := by
    ext h m
    rfl

/-- The tensor functor uses the balanced tensor product with its outer module structure. -/
theorem bimodLeftFunctor_obj (N : ModuleCat.{v} B) :
    (bimodLeftFunctor A B M).obj N =
      ModuleCat.of A (BalancedTensorProduct ℤ B M N) := (rfl)

/-- The pure tensor in the value of the left bimodule tensor functor. -/
def bimodLeftTmul (m : M) {N : ModuleCat.{v} B} (n : N) :
    (bimodLeftFunctor A B M).obj N :=
  tmul ℤ B m n

/-- Identify the value of the bimodule Hom functor with the group of `A`-linear maps. -/
def bimodHomRightAddEquiv {P : ModuleCat.{v} A} :
    (bimodHomRight A B M).obj P ≃+ (M →ₗ[A] P) :=
  AddEquiv.refl _

/-- The balancing relation for pure tensors of the bimodule tensor functor. -/
theorem bimodLeftTmul_balance {N : ModuleCat.{v} B} (b : B) (m : M) (n : N) :
    bimodLeftTmul A B M (op b • m) n = bimodLeftTmul A B M m (b • n) :=
  balance ℤ B b m n

/-- Pure tensors are additive in the bimodule factor. -/
@[simp]
theorem add_bimodLeftTmul {N : ModuleCat.{v} B} (m m' : M) (n : N) :
    bimodLeftTmul A B M (m + m') n = bimodLeftTmul A B M m n + bimodLeftTmul A B M m' n :=
  add_tmul ℤ B m m' n

/-- Pure tensors are additive in the left-module factor. -/
@[simp]
theorem bimodLeftTmul_add {N : ModuleCat.{v} B} (m : M) (n n' : N) :
    bimodLeftTmul A B M m (n + n') = bimodLeftTmul A B M m n + bimodLeftTmul A B M m n' :=
  tmul_add ℤ B m n n'

@[simp]
theorem zero_bimodLeftTmul {N : ModuleCat.{v} B} (n : N) :
    bimodLeftTmul A B M 0 n = 0 :=
  zero_tmul ℤ B n

@[simp]
theorem bimodLeftTmul_zero {N : ModuleCat.{v} B} (m : M) :
    bimodLeftTmul A B M m (0 : N) = 0 :=
  tmul_zero ℤ B m

/-- Integer multiplication on the underlying additive group acts on the first tensor factor. -/
@[simp]
theorem zsmul_bimodLeftTmul {N : ModuleCat.{v} B} (a : ℤ) (m : M) (n : N) :
    a • bimodLeftTmul A B M m n = bimodLeftTmul A B M (a • m) n := by
  let f : M →+ (bimodLeftFunctor A B M).obj N :=
    { toFun := fun m ↦ bimodLeftTmul A B M m n
      map_zero' := zero_bimodLeftTmul A B M n
      map_add' := fun m m' ↦ add_bimodLeftTmul A B M m m' n }
  exact (f.map_zsmul a m).symm

/-- An outer scalar acts on the first factor of a pure tensor. -/
@[simp]
theorem smul_bimodLeftTmul {N : ModuleCat.{v} B} (a : A) (m : M) (n : N) :
    a • bimodLeftTmul A B M m n = bimodLeftTmul A B M (a • m) n :=
  smul_tmul_left A a m n

/-- A scalar acts on the Hom functor by precomposition. -/
@[simp]
theorem bimodHomRightAddEquiv_smul_apply {P : ModuleCat.{v} A} (b : B)
    (f : (bimodHomRight A B M).obj P) (m : M) :
    bimodHomRightAddEquiv A B M (b • f) m = bimodHomRightAddEquiv A B M f (op b • m) :=
  bimodHomModule_smul_apply A B M P b f m

/-- The tensor functor acts on a pure tensor by applying the module map in the second factor. -/
@[simp]
theorem bimodLeftFunctor_map_tmul {N N' : ModuleCat.{v} B} (g : N ⟶ N') (m : M) (n : N) :
    (bimodLeftFunctor A B M).map g (bimodLeftTmul A B M m n) = bimodLeftTmul A B M m (g n) :=
  map_tmul LinearMap.id (g.hom.restrictScalars ℤ) (fun _ _ ↦ rfl) g.hom.map_smul m n

/-- Maps from a bimodule tensor are determined by their values on pure tensors. -/
@[ext]
theorem bimodLeftFunctor_hom_ext {N : ModuleCat.{v} B} {P : ModuleCat.{v} A}
    {f g : (bimodLeftFunctor A B M).obj N ⟶ P}
    (h : ∀ m n, f (bimodLeftTmul A B M m n) = g (bimodLeftTmul A B M m n)) : f = g :=
  ModuleCat.hom_ext (bimodLeftLinearMap_ext A B M h)

/-- The bimodule Hom functor maps a linear map by postcomposition. -/
@[simp]
theorem bimodHomRight_map_apply {P P' : ModuleCat.{v} A} (g : P ⟶ P')
    (f : (bimodHomRight A B M).obj P) (m : M) :
    bimodHomRightAddEquiv A B M ((bimodHomRight A B M).map g f) m =
      g (bimodHomRightAddEquiv A B M f m) := (rfl)

private def bimodCurry {N : ModuleCat.{v} B} {P : ModuleCat.{v} A}
    (f : (bimodLeftFunctor A B M).obj N ⟶ P) : N ⟶ (bimodHomRight A B M).obj P :=
  ModuleCat.ofHom
    { toFun := fun n ↦
        { toFun := fun m ↦ f (bimodLeftTmul A B M m n)
          map_add' := fun m m' ↦ by simp
          map_smul' := fun a m ↦ by
            rw [← smul_bimodLeftTmul A B M, map_smul]
            rfl }
      map_add' := fun n n' ↦ by ext m; simp
      map_smul' := fun b n ↦ by
        ext m
        simp [← bimodLeftTmul_balance] }

private theorem bimodCurry_apply {N : ModuleCat.{v} B} {P : ModuleCat.{v} A}
    (f : (bimodLeftFunctor A B M).obj N ⟶ P) (n : N) (m : M) :
    bimodHomRightAddEquiv A B M (bimodCurry A B M f n) m = f (bimodLeftTmul A B M m n) := (rfl)

private def bimodPairing {N : ModuleCat.{v} B} {P : ModuleCat.{v} A}
    (g : N ⟶ (bimodHomRight A B M).obj P) : M →ₗ[ℤ] N →ₗ[ℤ] P :=
  ((LinearMap.restrictScalarsₗ ℤ A M P ℤ).comp (g.hom.restrictScalars ℤ)).flip

@[simp]
private theorem bimodPairing_apply {N : ModuleCat.{v} B} {P : ModuleCat.{v} A}
    (g : N ⟶ (bimodHomRight A B M).obj P) (m : M) (n : N) :
    bimodPairing A B M g m n = bimodHomRightAddEquiv A B M (g n) m := (rfl)

private theorem bimodPairing_balanced {N : ModuleCat.{v} B} {P : ModuleCat.{v} A}
    (g : N ⟶ (bimodHomRight A B M).obj P) (b : B) (m : M) (n : N) :
    bimodPairing A B M g (op b • m) n = bimodPairing A B M g m (b • n) := by
  simp [map_smul]

private def bimodUncurry {N : ModuleCat.{v} B} {P : ModuleCat.{v} A}
    (g : N ⟶ (bimodHomRight A B M).obj P) : (bimodLeftFunctor A B M).obj N ⟶ P :=
  ModuleCat.ofHom
    { __ := (lift (bimodPairing A B M g) (bimodPairing_balanced A B M g)).toAddMonoidHom
      map_smul' := fun a z ↦
        lift_smul_left A _ _ (fun a m n ↦ by simp [map_smul]) a z }

private theorem bimodUncurry_tmul {N : ModuleCat.{v} B} {P : ModuleCat.{v} A}
    (g : N ⟶ (bimodHomRight A B M).obj P) (m : M) (n : N) :
    bimodUncurry A B M g (bimodLeftTmul A B M m n) = bimodHomRightAddEquiv A B M (g n) m := by
  exact (lift_tmul _ _ m n).trans (bimodPairing_apply A B M g m n)

private def bimodLeftHomEquiv (N : ModuleCat.{v} B) (P : ModuleCat.{v} A) :
    ((bimodLeftFunctor A B M).obj N ⟶ P) ≃ (N ⟶ (bimodHomRight A B M).obj P) where
  toFun := bimodCurry A B M
  invFun := bimodUncurry A B M
  left_inv f := bimodLeftFunctor_hom_ext A B M fun m n ↦ by
    rw [bimodUncurry_tmul, bimodCurry_apply]
  right_inv g := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun n ↦ (bimodHomRightAddEquiv A B M).injective ?_
    exact LinearMap.ext fun m ↦
      (bimodCurry_apply A B M _ n m).trans (bimodUncurry_tmul A B M g m n)

private def bimodLeftHomCoreEquiv :
    Adjunction.CoreHomEquiv (bimodLeftFunctor A B M) (bimodHomRight A B M) where
  homEquiv := bimodLeftHomEquiv A B M
  homEquiv_naturality_left_symm f g := bimodLeftFunctor_hom_ext A B M fun m n ↦ by
    dsimp only [bimodLeftHomEquiv, Equiv.symm_mk, Equiv.coe_fn_mk]
    rw [ModuleCat.comp_apply, bimodLeftFunctor_map_tmul, bimodUncurry_tmul, bimodUncurry_tmul]
    rfl
  homEquiv_naturality_right f g := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun n ↦ (bimodHomRightAddEquiv A B M).injective
      (LinearMap.ext fun m ↦ ?_)
    dsimp only [bimodLeftHomEquiv, Equiv.coe_fn_mk]
    calc
      _ = (f ≫ g) (bimodLeftTmul A B M m n) := bimodCurry_apply A B M _ _ _
      _ = g (bimodHomRightAddEquiv A B M (bimodCurry A B M f n) m) :=
        congrArg g (bimodCurry_apply A B M f n m).symm
      _ = _ := (bimodHomRight_map_apply A B M g (bimodCurry A B M f n) m).symm

/-- Tensoring with an `(A, B)`-bimodule on the left is left adjoint to its Hom functor. -/
def bimodLeftHomAdjunction : bimodLeftFunctor A B M ⊣ bimodHomRight A B M :=
  Adjunction.mkOfHomEquiv (bimodLeftHomCoreEquiv A B M)

/-- The adjunction sends a map out of the tensor to its curried evaluation on pure tensors. -/
@[simp]
theorem bimodLeftHomAdjunction_homEquiv_apply {N : ModuleCat.{v} B} {P : ModuleCat.{v} A}
    (f : (bimodLeftFunctor A B M).obj N ⟶ P) (n : N) (m : M) :
    bimodHomRightAddEquiv A B M ((bimodLeftHomAdjunction A B M).homEquiv N P f n) m =
      f (bimodLeftTmul A B M m n) := by
  rw [bimodLeftHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact bimodCurry_apply A B M f n m

/-- The inverse adjunction bijection evaluates the curried map on the two tensor factors. -/
@[simp]
theorem bimodLeftHomAdjunction_homEquiv_symm_tmul {N : ModuleCat.{v} B} {P : ModuleCat.{v} A}
    (g : N ⟶ (bimodHomRight A B M).obj P) (m : M) (n : N) :
    ((bimodLeftHomAdjunction A B M).homEquiv N P).symm g (bimodLeftTmul A B M m n) =
      bimodHomRightAddEquiv A B M (g n) m := by
  rw [bimodLeftHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact bimodUncurry_tmul A B M g m n

instance : (bimodHomRight A B M).Additive where
  map_add := by
    intro P P' f g
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun h ↦ (bimodHomRightAddEquiv A B M).injective
      (LinearMap.ext fun m ↦ ?_)
    exact LinearMap.add_apply f.hom g.hom (bimodHomRightAddEquiv A B M h m)

instance : (bimodLeftFunctor A B M).Additive :=
  (bimodLeftHomAdjunction A B M).left_adjoint_additive

instance : (bimodLeftFunctor A B M).IsLeftAdjoint :=
  (bimodLeftHomAdjunction A B M).isLeftAdjoint

instance : (bimodHomRight A B M).IsRightAdjoint :=
  (bimodLeftHomAdjunction A B M).isRightAdjoint

end TauCeti.BalancedTensorProduct

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.CategoryTheory.Adjunction.Limits
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic

/-!
# Functoriality and the balanced tensor–Hom adjunction

For an algebra `A` over a commutative ring `R`, the balanced tensor product over `A` is additive
in a right and a left `A`-module. The partial functor `- ⊗_A N` is left adjoint to
`Hom_R(N, -)`, where the right `A`-action on Hom is precomposition with the left action on `N`.
The adjunction sends `f` to `m ↦ (n ↦ f (m ⊗ n))`. Swapping the two entries identifies
`M ⊗_A N` with `N ⊗_{Aᵐᵒᵖ} M`. Consequently both partial tensor functors preserve colimits
when the modules lie in a common universe.

Open the scope `ModuleCat.Algebra` for the scalar action restricted along `algebraMap` on
bundled modules. Use `homRightAddEquiv` to evaluate an element of the right Hom module.

## References

* J. Lambek, *A module is flat if and only if its character module is injective*,
  Canad. Math. Bull. 7 (1964), pp. 240–241, for the specialization to character modules.
* T. Y. Lam, *A First Course in Noncommutative Rings*, §24, (24.20), for right exactness.
-/

public section

universe r a u v

open CategoryTheory MulOpposite
open scoped ModuleCat.Algebra

namespace TauCeti.BalancedTensorProduct

section RightTensor

variable (R : Type*) {A : Type*} (N : Type*) {M M' : Type*}
  [CommRing R] [Semiring A] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]
  [Module Aᵐᵒᵖ M] [Module Aᵐᵒᵖ M'] [Module A N] [Module R N] [Module R M] [Module R M']
  [Module R Aᵐᵒᵖ] [IsScalarTower R Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M']

/-- Tensoring a right `A`-module map with `N` on the right. -/
def rTensor (f : M →ₗ[Aᵐᵒᵖ] M') :
    BalancedTensorProduct R A M N →ₗ[R] BalancedTensorProduct R A M' N :=
  map (f.restrictScalars R) LinearMap.id (fun b m ↦ f.map_smul (op b) m) (fun _ _ ↦ rfl)

/-- On pure tensors, `rTensor` applies the given map to the right-module entry. -/
@[simp]
theorem rTensor_tmul (f : M →ₗ[Aᵐᵒᵖ] M') (m : M) (n : N) :
    rTensor R N f (tmul R A m n) = tmul R A (f m) n :=
  map_tmul _ _ _ _ _ _

end RightTensor

variable (R : Type r) (A : Type a) [CommRing R] [Ring A] [Algebra R A]

/-- The balanced tensor bifunctor, with the right module in the first variable. -/
-- Expose the object carriers so that morphisms can be evaluated directly on pure tensors.
abbrev functor : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{v} A ⥤ ModuleCat.{max u v} R where
  obj M :=
    { obj N := ModuleCat.of R (BalancedTensorProduct R A M N)
      map g := ModuleCat.ofHom (lTensor R M g.hom)
      map_id _ := ModuleCat.hom_ext (hom_ext fun _ _ ↦ by simp)
      map_comp _ _ := ModuleCat.hom_ext (hom_ext fun _ _ ↦ by simp) }
  map f :=
    { app N := ModuleCat.ofHom (rTensor R N f.hom)
      naturality _ _ _ := ModuleCat.hom_ext (hom_ext fun _ _ ↦ by simp) }
  map_id _ := NatTrans.ext (funext fun _ ↦ ModuleCat.hom_ext (hom_ext fun _ _ ↦ by simp))
  map_comp _ _ := NatTrans.ext (funext fun _ ↦ ModuleCat.hom_ext (hom_ext fun _ _ ↦ by simp))

instance (M : ModuleCat.{u} Aᵐᵒᵖ) : ((functor.{r, a, u, v} R A).obj M).Additive where
  map_add {N _} g g' := ModuleCat.hom_ext (hom_ext (M := M) (N := N) fun m n ↦ by
    simp only [ModuleCat.hom_add, LinearMap.add_apply]
    simpa only [ModuleCat.hom_ofHom, lTensor_tmul, LinearMap.add_apply] using
      tmul_add R A m (g n) (g' n))

instance : (functor.{r, a, u, v} R A).Additive where
  map_add {M _} f f' :=
    NatTrans.ext (funext fun N ↦ ModuleCat.hom_ext (hom_ext (M := M) (N := N) fun m n ↦ by
      simp only [NatTrans.app_add, ModuleCat.hom_add, LinearMap.add_apply]
      simpa only [ModuleCat.hom_ofHom, rTensor_tmul, LinearMap.add_apply] using
        add_tmul R A (f m) (f' m) n))

/-- The right action on Hom is Mathlib’s domain action on linear maps. -/
local instance homRightModule (N : ModuleCat.{u} A) (E : ModuleCat.{v} R) :
    Module Aᵐᵒᵖ (N →ₗ[R] E) :=
  (inferInstance : Module Aᵈᵐᵃ (N →ₗ[R] E))

/-- The `R`-linear maps out of a left `A`-module, with the right `A`-action by precomposition. -/
-- The compiler needs the concrete carrier in the definitions of the adjunction maps.
@[expose]
def homRight (N : ModuleCat.{u} A) : ModuleCat.{v} R ⥤ ModuleCat.{max u v} Aᵐᵒᵖ where
  obj E := ModuleCat.of Aᵐᵒᵖ (N →ₗ[R] E)
  map h := ConcreteCategory.ofHom (C := ModuleCat Aᵐᵒᵖ)
    { toFun := fun φ ↦ h.hom.comp φ
      map_add' := fun φ ψ ↦ LinearMap.ext fun n ↦ h.hom.map_add (φ n) (ψ n)
      map_smul' := fun _ _ ↦ LinearMap.ext fun _ ↦ rfl }
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl)
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl)

/-- The additive group of the right Hom module is the group of `R`-linear maps. -/
def homRightAddEquiv (N : ModuleCat.{u} A) (E : ModuleCat.{v} R) :
    (homRight R A N).obj E ≃+ (N →ₗ[R] E) :=
  AddEquiv.refl _

/-- The right action on Hom evaluates by acting first on the input. -/
@[simp]
theorem homRightAddEquiv_smul_apply (N : ModuleCat.{u} A) (E : ModuleCat.{v} R) (b : Aᵐᵒᵖ)
    (φ : (homRight R A N).obj E) (n : N) :
    homRightAddEquiv R A N E (b • φ) n = homRightAddEquiv R A N E φ (b.unop • n) := (rfl)

/-- The Hom functor acts by postcomposition. -/
@[simp]
theorem homRightAddEquiv_map_apply (N : ModuleCat.{u} A) {E E' : ModuleCat.{v} R} (h : E ⟶ E')
    (φ : (homRight R A N).obj E) (n : N) :
    homRightAddEquiv R A N E' ((homRight R A N).map h φ) n =
      h (homRightAddEquiv R A N E φ n) := (rfl)

instance (N : ModuleCat.{u} A) : (homRight.{r, a, u, v} R A N).Additive where
  map_add {_ _} _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl)

section Adjunction

variable (N : ModuleCat.{v} A) (M : ModuleCat.{v} Aᵐᵒᵖ) (E : ModuleCat.{v} R)

private def curry (f : ((functor R A).obj M).obj N ⟶ E) :
    M ⟶ (homRight R A N).obj E :=
  let bilinear : M →ₗ[R] N →ₗ[R] E := (mk R A).compr₂ f.hom
  let e := homRightAddEquiv R A N E
  have eval (m : M) (n : N) : bilinear m n = f (tmul R A m n) :=
    (LinearMap.compr₂_apply _ _ _ _).trans (congrArg f.hom (mk_apply R A m n))
  ConcreteCategory.ofHom (C := ModuleCat Aᵐᵒᵖ)
    { toFun := fun m ↦ e.symm (bilinear m)
      map_add' := fun m m' ↦ by rw [map_add, map_add]
      map_smul' := fun b m ↦ e.injective (LinearMap.ext fun n ↦ calc
        e (e.symm (bilinear (b • m))) n = f (tmul R A (b • m) n) :=
          (congrArg (fun φ : N →ₗ[R] E ↦ φ n) (e.apply_symm_apply _)).trans (eval _ _)
        _ = f (tmul R A m (b.unop • n)) :=
          congrArg f (by simpa only [op_unop] using balance R A b.unop m n)
        _ = e (e.symm (bilinear m)) (b.unop • n) :=
          (eval _ _).symm.trans (congrArg (fun φ : N →ₗ[R] E ↦ φ _) (e.apply_symm_apply _).symm)
        _ = e (b • e.symm (bilinear m)) n :=
          (homRightAddEquiv_smul_apply R A N E b _ n).symm) }

private theorem curry_apply (f : ((functor R A).obj M).obj N ⟶ E) (m : M) (n : N) :
    homRightAddEquiv R A N E (curry R A N M E f m) n = f (tmul R A m n) :=
  (LinearMap.compr₂_apply _ _ _ _).trans (congrArg f.hom (mk_apply R A m n))

private def uncurry (g : M ⟶ (homRight R A N).obj E) :
    ((functor R A).obj M).obj N ⟶ E :=
  let e := homRightAddEquiv R A N E
  let bilinear : M →ₗ[R] N →ₗ[R] E :=
    { toFun := fun m ↦ e (g m)
      map_add' := fun m m' ↦ (congrArg e (g.hom.map_add m m')).trans (e.map_add _ _)
      map_smul' := fun c m ↦ LinearMap.ext fun n ↦ by
        -- The ground scalar on `M` is induced by the algebra map into the opposite ring.
        change e (g (algebraMap R Aᵐᵒᵖ c • m)) n = c • e (g m) n
        rw [map_smul, homRightAddEquiv_smul_apply, MulOpposite.algebraMap_apply, unop_op,
          algebraMap_smul, map_smul] }
  ModuleCat.ofHom <| lift bilinear fun b m n ↦
    (congrArg (fun φ ↦ e φ n) (g.hom.map_smul (op b) m)).trans
      (homRightAddEquiv_smul_apply R A N E (op b) (g m) n)

private theorem uncurry_tmul (g : M ⟶ (homRight R A N).obj E) (m : M) (n : N) :
    uncurry R A N M E g (tmul R A m n) = homRightAddEquiv R A N E (g m) n :=
  lift_tmul _ _ m n

private def adjunctionHomEquiv :
    (((functor R A).obj M).obj N ⟶ E) ≃ (M ⟶ (homRight R A N).obj E) where
  toFun := curry R A N M E
  invFun := uncurry R A N M E
  left_inv f := ModuleCat.hom_ext (hom_ext fun m n ↦
    (uncurry_tmul R A N M E _ m n).trans (curry_apply R A N M E f m n))
  right_inv g := ModuleCat.hom_ext (LinearMap.ext fun m ↦
    (homRightAddEquiv R A N E).injective (LinearMap.ext fun n ↦
      (curry_apply R A N M E _ m n).trans (uncurry_tmul R A N M E g m n)))

/-- Tensoring with a fixed left module is left adjoint to taking the right module of linear maps
out of it. -/
def tensorHomAdjunction : (functor.{r, a, v, v} R A).flip.obj N ⊣ homRight R A N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M E ↦ adjunctionHomEquiv R A N M E
      homEquiv_naturality_left_symm := fun f g ↦ ModuleCat.hom_ext (hom_ext fun m n ↦
        (uncurry_tmul R A N _ _ (f ≫ g) m n).trans <|
          (uncurry_tmul R A N _ _ g (f m) n).symm.trans <|
            congrArg (uncurry R A N _ _ g) (rTensor_tmul R N f.hom m n).symm)
      homEquiv_naturality_right := fun f h ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦
        (homRightAddEquiv R A N _).injective (LinearMap.ext fun n ↦
          (curry_apply R A N _ _ (f ≫ h) m n).trans <|
            (congrArg h (curry_apply R A N _ _ f m n).symm).trans <|
              (homRightAddEquiv_map_apply R A N h _ n).symm)) }

-- Simplification rewrites the flipped functor in the implicit object arguments of these maps.
-- State the computation rules for explicit use at the original adjunction.
/-- The adjunction sends a map out of the tensor to its curried form. -/
theorem tensorHomAdjunction_homEquiv_apply
    (f : ((functor R A).obj M).obj N ⟶ E) (m : M) (n : N) :
    homRightAddEquiv R A N E ((tensorHomAdjunction R A N).homEquiv M E f m) n =
      f (tmul R A m n) := by
  rw [tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact curry_apply R A N M E f m n

/-- The inverse bijection evaluates the corresponding linear map on each pure tensor. -/
theorem tensorHomAdjunction_homEquiv_symm_apply_tmul
    (g : M ⟶ (homRight R A N).obj E) (m : M)
    (n : N) :
    (((tensorHomAdjunction R A N).homEquiv M E).symm g).hom (tmul R A m n) =
      homRightAddEquiv R A N E (g m) n := by
  rw [tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact uncurry_tmul R A N M E g m n

instance : ((functor.{r, a, v, v} R A).flip.obj N).IsLeftAdjoint :=
  (tensorHomAdjunction R A N).isLeftAdjoint

end Adjunction

section Swap

variable (M : ModuleCat.{u} Aᵐᵒᵖ) (N : ModuleCat.{v} A)

/-- Flipping the factors takes the balanced tensor over `A` to the balanced tensor over
`Aᵐᵒᵖ`. The left action on `N` is viewed as a right action of `Aᵐᵒᵖ`. -/
noncomputable def swap : BalancedTensorProduct R A M N ≃ₗ[R]
    BalancedTensorProduct R Aᵐᵒᵖ
      ((ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom).obj N) M :=
  let Nop := (ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom).obj N
  let forward : M →ₗ[R] N →ₗ[R] BalancedTensorProduct R Aᵐᵒᵖ Nop M :=
    (mk R Aᵐᵒᵖ (M := Nop) (N := M)).flip
  let backward : Nop →ₗ[R] M →ₗ[R] BalancedTensorProduct R A M N :=
    (mk R A (M := M) (N := N)).flip
  have forward_eval (m : M) (n : N) :
      forward m n = tmul R Aᵐᵒᵖ (M := Nop) (N := M) n m :=
    (LinearMap.flip_apply (mk R Aᵐᵒᵖ (M := Nop) (N := M)) n m).trans
      (mk_apply R Aᵐᵒᵖ (M := Nop) (N := M) n m)
  have backward_eval (n : Nop) (m : M) :
      backward n m = tmul R A (M := M) (N := N) m n :=
    (LinearMap.flip_apply (mk R A (M := M) (N := N)) m n).trans
      (mk_apply R A (M := M) (N := N) m n)
  let f := lift (A := A) forward fun b m n ↦
    (forward_eval _ _).trans <|
      ((balance R Aᵐᵒᵖ (M := Nop) (N := M) (op b) n m).symm).trans (forward_eval _ _).symm
  let g := lift (A := Aᵐᵒᵖ) backward fun b n m ↦ calc
    backward (op b • n) m = tmul R A (M := M) (N := N) m (b.unop • (n : N)) := backward_eval _ _
    _ = tmul R A (M := M) (N := N) (b • m) n :=
      (balance R A (M := M) (N := N) b.unop m (n : N)).symm.trans
        (congrArg (fun b' : Aᵐᵒᵖ ↦ tmul R A (M := M) (N := N) (b' • m) (n : N)) (op_unop b))
    _ = backward n (b • m) := (backward_eval _ _).symm
  have hf (m : M) (n : N) :
      f (tmul R A (M := M) (N := N) m n) = tmul R Aᵐᵒᵖ (M := Nop) (N := M) n m :=
    (lift_tmul forward _ m n).trans (forward_eval _ _)
  have hg (n : Nop) (m : M) :
      g (tmul R Aᵐᵒᵖ (M := Nop) (N := M) n m) = tmul R A (M := M) (N := N) m n :=
    (lift_tmul backward _ n m).trans (backward_eval _ _)
  LinearEquiv.ofLinearMap f g
    (hom_ext fun n m ↦ (congrArg f (hg n m)).trans (hf m n))
    (hom_ext fun m n ↦ (congrArg g (hf m n)).trans (hg n m))

-- Simplification rewrites the restriction homomorphism in the implicit object arguments.
/-- The swap sends a pure tensor to the pure tensor with the two entries reversed. -/
theorem swap_tmul (m : M) (n : N) :
    swap R A M N (tmul R A m n) =
      tmul R Aᵐᵒᵖ (M := (ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom).obj N)
        n m := by
  let Nop := (ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom).obj N
  let pair := mk R Aᵐᵒᵖ (M := Nop) (N := M)
  exact (lift_tmul (A := A) (M := M) (N := N) pair.flip _ m n).trans
    ((LinearMap.flip_apply pair n m).trans (mk_apply R Aᵐᵒᵖ (M := Nop) (N := M) n m))

/-- Swapping a pure tensor over the opposite ring recovers the original order. -/
theorem swap_symm_tmul (n : (ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom).obj N)
    (m : M) :
    (swap R A M N).symm (tmul R Aᵐᵒᵖ n m) = tmul R A m (n : N) :=
  (LinearEquiv.symm_apply_eq _).2 (swap_tmul R A M N m n).symm

/-- For a fixed right module, swapping tensors gives a natural isomorphism with the
opposite-ring partial tensor functor. -/
noncomputable def functorSwapIso : (functor.{r, a, u, v} R A).obj M ≅
    ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom ⋙
      (functor.{r, a, v, u} R Aᵐᵒᵖ).flip.obj M :=
  NatIso.ofComponents (fun N ↦ (swap R A M N).toModuleIso) fun f ↦
    ModuleCat.hom_ext (hom_ext fun m n ↦
      let fop := (ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom).map f
      (congrArg (swap R A M _) (lTensor_tmul f.hom m n)).trans <|
        (swap_tmul R A M _ m (f n)).trans <|
          (rTensor_tmul R M fop.hom n m).symm.trans <|
            congrArg _ (swap_tmul R A M _ m n).symm)

/-- The natural swap acts on pure tensors by exchanging their entries. -/
theorem functorSwapIso_hom_app_tmul (m : M) (n : N) :
    ((functorSwapIso.{r, a, u, v} R A M).hom.app N).hom (tmul R A m n) =
      tmul R Aᵐᵒᵖ (M := (ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom).obj N) n m :=
  swap_tmul R A M N m n

/-- The inverse natural swap returns the pure tensor over the original ring. -/
theorem functorSwapIso_inv_app_tmul (m : M)
    (n : (ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom).obj N) :
    ((functorSwapIso.{r, a, u, v} R A M).inv.app N).hom (tmul R Aᵐᵒᵖ n m) = tmul R A m (n : N) :=
  swap_symm_tmul R A M N n m

instance (M : ModuleCat.{v} Aᵐᵒᵖ) : ((functor.{r, a, v, v} R A).obj M).IsLeftAdjoint := by
  let e : ModuleCat.{v} A ≌ ModuleCat.{v} Aᵐᵒᵖᵐᵒᵖ :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A).symm
  have : (ModuleCat.restrictScalars.{v} (RingEquiv.opOp A).symm.toRingHom).IsLeftAdjoint :=
    e.isLeftAdjoint_functor
  exact Functor.isLeftAdjoint_of_iso (functorSwapIso R A M).symm

end Swap

end TauCeti.BalancedTensorProduct

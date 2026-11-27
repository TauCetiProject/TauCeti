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

variable (R : Type r) (A : Type a) [CommRing R] [Ring A] [Algebra R A]

/-- The balanced tensor bifunctor, with the right module in the first variable. -/
-- Expose the object carriers so that morphisms can be evaluated directly on pure tensors.
@[expose, implicit_reducible]
def functor : ModuleCat.{u} Aᵐᵒᵖ ⥤ ModuleCat.{v} A ⥤ ModuleCat.{max u v} R where
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

/-- The tensor functor acts on the left-module entry of a pure tensor by the given morphism. -/
@[simp]
theorem functor_obj_map_tmul (M : ModuleCat.{u} Aᵐᵒᵖ) {N N' : ModuleCat.{v} A} (g : N ⟶ N')
    (m : M) (n : N) :
    ((functor R A).obj M).map g (tmul R A m n) = tmul R A m (g n) :=
  lTensor_tmul g.hom m n

/-- The tensor natural transformation acts on the right-module entry by the given morphism. -/
@[simp]
theorem functor_map_app_tmul {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') (N : ModuleCat.{v} A)
    (m : M) (n : N) :
    ((functor R A).map f).app N (tmul R A m n) = tmul R A (f m) n :=
  rTensor_tmul f.hom m n

instance (M : ModuleCat.{u} Aᵐᵒᵖ) : ((functor.{r, a, u, v} R A).obj M).Additive where
  map_add {N _} g g' := ModuleCat.hom_ext (hom_ext (M := M) (N := N) fun m n ↦ by
    -- Use the concrete tensor carrier so the pure-tensor simp lemmas match.
    change lTensor R M (g + g').hom (tmul R A m n) =
      lTensor R M g.hom (tmul R A m n) + lTensor R M g'.hom (tmul R A m n)
    simp only [lTensor_tmul, ModuleCat.hom_add, LinearMap.add_apply, tmul_add])

instance : (functor.{r, a, u, v} R A).Additive where
  map_add {M _} f f' :=
    NatTrans.ext (funext fun N ↦ ModuleCat.hom_ext (hom_ext (M := M) (N := N) fun m n ↦ by
      -- Use the concrete tensor carrier so the pure-tensor simp lemmas match.
      change rTensor R N (f + f').hom (tmul R A m n) =
        rTensor R N f.hom (tmul R A m n) + rTensor R N f'.hom (tmul R A m n)
      simp only [rTensor_tmul, ModuleCat.hom_add, LinearMap.add_apply, add_tmul]))

/-- Tensoring with a fixed left module is additive in the right-module variable. -/
instance (N : ModuleCat.{v} A) : ((functor.{r, a, u, v} R A).flip.obj N).Additive where
  map_add {_ _} f g := by
    simpa only [Functor.flip_obj_map, NatTrans.app_add] using
      congrArg (fun α ↦ α.app N) ((functor.{r, a, u, v} R A).map_add (f := f) (g := g))

/-- The right action on Hom is Mathlib’s domain action on linear maps. -/
-- DomMulAct is defined as MulOpposite, so the two scalar types are definitionally equal.
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
      map_smul' := fun b φ ↦ LinearMap.ext fun n ↦
        (congrArg h.hom (DomMulAct.smul_linearMap_apply (b : Aᵈᵐᵃ) φ n)).trans
          (DomMulAct.smul_linearMap_apply (b : Aᵈᵐᵃ) (h.hom.comp φ) n).symm }
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
    homRightAddEquiv R A N E (b • φ) n = homRightAddEquiv R A N E φ (b.unop • n) :=
  DomMulAct.smul_linearMap_apply (b : Aᵈᵐᵃ) (homRightAddEquiv R A N E φ) n

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

private def balancedHomEquiv :
    {f : M →ₗ[R] N →ₗ[R] E // ∀ (b : A) m n, f (op b • m) n = f m (b • n)} ≃
      (M →ₗ[Aᵐᵒᵖ] (homRight R A N).obj E) where
  toFun f :=
    { toFun := fun m ↦ (homRightAddEquiv R A N E).symm (f.val m)
      map_add' := fun m m' ↦ by rw [map_add, map_add]
      map_smul' := fun b m ↦ (homRightAddEquiv R A N E).injective (LinearMap.ext fun n ↦ by
        simpa only [AddEquiv.apply_symm_apply, RingHom.id_apply, homRightAddEquiv_smul_apply,
          op_unop] using f.property b.unop m n) }
  invFun g :=
    ⟨{ toFun := fun m ↦ homRightAddEquiv R A N E (g m)
       map_add' := fun m m' ↦ by rw [map_add, map_add]
       map_smul' := fun c m ↦ LinearMap.ext fun n ↦ by
         -- The ground scalar on the bundled module is induced by the opposite algebra map.
         change homRightAddEquiv R A N E (g (algebraMap R Aᵐᵒᵖ c • m)) n =
           c • homRightAddEquiv R A N E (g m) n
         rw [map_smul, homRightAddEquiv_smul_apply, MulOpposite.algebraMap_apply, unop_op,
           algebraMap_smul, map_smul] },
      fun b m n ↦
        (congrArg (fun φ ↦ homRightAddEquiv R A N E φ n) (g.map_smul (op b) m)).trans
          (homRightAddEquiv_smul_apply R A N E (op b) (g m) n)⟩
  left_inv f := Subtype.ext (LinearMap.ext fun m ↦ (homRightAddEquiv R A N E).apply_symm_apply _)
  right_inv g := LinearMap.ext fun m ↦ (homRightAddEquiv R A N E).symm_apply_apply _

private def adjunctionHomEquiv :
    (((functor R A).obj M).obj N ⟶ E) ≃ (M ⟶ (homRight R A N).obj E) :=
  ModuleCat.homEquiv.trans
    (liftEquiv.symm.trans ((balancedHomEquiv R A N M E).trans ModuleCat.homEquiv.symm))

private theorem adjunctionHomEquiv_apply (f : ((functor R A).obj M).obj N ⟶ E) (m : M) (n : N) :
    homRightAddEquiv R A N E (adjunctionHomEquiv R A N M E f m) n = f (tmul R A m n) :=
  liftEquiv_symm_apply f.hom m n

private theorem adjunctionHomEquiv_symm_apply_tmul
    (g : M ⟶ (homRight R A N).obj E) (m : M) (n : N) :
    ((adjunctionHomEquiv R A N M E).symm g).hom (tmul R A m n) =
      homRightAddEquiv R A N E (g m) n := by
  let f := (balancedHomEquiv R A N M E).symm g.hom
  -- Expose the bare linear map so the universal property's evaluation lemma matches.
  change liftEquiv f (tmul R A m n) = f.val m n
  rw [liftEquiv_apply, lift_tmul]

/-- Tensoring with a fixed left module is left adjoint to taking the right module of linear maps
out of it. -/
def tensorHomAdjunction : (functor.{r, a, v, v} R A).flip.obj N ⊣ homRight R A N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M E ↦ adjunctionHomEquiv R A N M E
      homEquiv_naturality_left_symm := fun f g ↦ ModuleCat.hom_ext (hom_ext fun m n ↦
        (adjunctionHomEquiv_symm_apply_tmul R A N _ _ (f ≫ g) m n).trans <|
          (adjunctionHomEquiv_symm_apply_tmul R A N _ _ g (f m) n).symm.trans <|
            congrArg (fun x ↦ ((adjunctionHomEquiv R A N _ _).symm g).hom x)
              (rTensor_tmul f.hom m n).symm)
      homEquiv_naturality_right := fun f h ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦
        (homRightAddEquiv R A N _).injective (LinearMap.ext fun n ↦
          (adjunctionHomEquiv_apply R A N _ _ (f ≫ h) m n).trans <|
            (congrArg h (adjunctionHomEquiv_apply R A N _ _ f m n).symm).trans <|
              (homRightAddEquiv_map_apply R A N h _ n).symm)) }

-- Simplification rewrites the flipped functor in the implicit object arguments of these maps.
-- State the computation rules for explicit use at the original adjunction.
/-- The adjunction sends a map out of the tensor to its curried form. -/
theorem tensorHomAdjunction_homEquiv_apply
    (f : ((functor R A).obj M).obj N ⟶ E) (m : M) (n : N) :
    homRightAddEquiv R A N E ((tensorHomAdjunction R A N).homEquiv M E f m) n =
      f (tmul R A m n) := by
  rw [tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact adjunctionHomEquiv_apply R A N M E f m n

/-- The inverse bijection evaluates the corresponding linear map on each pure tensor. -/
theorem tensorHomAdjunction_homEquiv_symm_apply_tmul
    (g : M ⟶ (homRight R A N).obj E) (m : M)
    (n : N) :
    (((tensorHomAdjunction R A N).homEquiv M E).symm g).hom (tmul R A m n) =
      homRightAddEquiv R A N E (g m) n := by
  rw [tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact adjunctionHomEquiv_symm_apply_tmul R A N M E g m n

/-- The unit sends an element to the map that tensors it with the input. -/
theorem tensorHomAdjunction_unit_app_apply (m : M) (n : N) :
    homRightAddEquiv R A N _ ((tensorHomAdjunction R A N).unit.app M m) n = tmul R A m n := by
  rw [← Adjunction.homEquiv_id]
  exact tensorHomAdjunction_homEquiv_apply R A N M _ (𝟙 _) m n

/-- The counit evaluates a linear map on the second entry of a pure tensor. -/
theorem tensorHomAdjunction_counit_app_tmul (φ : (homRight R A N).obj E) (n : N) :
    ((tensorHomAdjunction R A N).counit.app E).hom (tmul R A φ n) =
      homRightAddEquiv R A N E φ n := by
  rw [← Adjunction.homEquiv_symm_id]
  exact tensorHomAdjunction_homEquiv_symm_apply_tmul R A N _ E (𝟙 _) φ n

instance : ((functor.{r, a, v, v} R A).flip.obj N).IsLeftAdjoint :=
  (tensorHomAdjunction R A N).isLeftAdjoint

end Adjunction

section Comm

variable (M : ModuleCat.{u} Aᵐᵒᵖ) (N : ModuleCat.{v} A)

private noncomputable def commLinearMap :
    BalancedTensorProduct R A M N →ₗ[R] BalancedTensorProduct R Aᵐᵒᵖ
      ((ModuleCat.restrictScalars.{v} (↑(RingEquiv.opOp A).symm : Aᵐᵒᵖᵐᵒᵖ →+* A)).obj N) M :=
  let Nop := (ModuleCat.restrictScalars.{v} (↑(RingEquiv.opOp A).symm : Aᵐᵒᵖᵐᵒᵖ →+* A)).obj N
  let pair := mk R Aᵐᵒᵖ (M := Nop) (N := M)
  have eval (m : M) (n : Nop) : pair.flip m n = tmul R Aᵐᵒᵖ n m := by
    simp only [LinearMap.flip_apply, pair, mk_apply]
  lift (A := A) pair.flip fun b m n ↦
    (eval _ _).trans ((balance R Aᵐᵒᵖ (M := Nop) (op b) n m).symm.trans (eval _ _).symm)

@[simp]
private theorem commLinearMap_tmul (m : M) (n : N) :
    commLinearMap R A M N (tmul R A m n) =
      tmul R Aᵐᵒᵖ
        (M := (ModuleCat.restrictScalars.{v} (↑(RingEquiv.opOp A).symm : Aᵐᵒᵖᵐᵒᵖ →+* A)).obj N)
        n m := by
  let Nop := (ModuleCat.restrictScalars.{v} (↑(RingEquiv.opOp A).symm : Aᵐᵒᵖᵐᵒᵖ →+* A)).obj N
  have h (x : Nop) : (mk R Aᵐᵒᵖ (M := Nop) (N := M)).flip m x = tmul R Aᵐᵒᵖ x m := by
    simp
  exact (lift_tmul (A := A) (M := M) (N := N) _ _ m n).trans (h n)

private noncomputable def commInverseLinearMap :
    BalancedTensorProduct R Aᵐᵒᵖ
      ((ModuleCat.restrictScalars.{v} (↑(RingEquiv.opOp A).symm : Aᵐᵒᵖᵐᵒᵖ →+* A)).obj N) M →ₗ[R]
        BalancedTensorProduct R A M N :=
  let Nop := (ModuleCat.restrictScalars.{v} (↑(RingEquiv.opOp A).symm : Aᵐᵒᵖᵐᵒᵖ →+* A)).obj N
  let pair := mk R A (M := M) (N := N)
  have eval (n : N) (m : M) : pair.flip n m = tmul R A m n := by
    simp only [LinearMap.flip_apply, pair, mk_apply]
  lift (A := Aᵐᵒᵖ) (M := Nop) pair.flip fun b n m ↦
    have h : tmul R A m (b.unop • (n : N)) = tmul R A (b • m) (n : N) := by
      simpa only [op_unop] using (balance R A b.unop m (n : N)).symm
    (eval _ _).trans (h.trans (eval _ _).symm)

@[simp]
private theorem commInverseLinearMap_tmul
    (n : (ModuleCat.restrictScalars.{v} (↑(RingEquiv.opOp A).symm : Aᵐᵒᵖᵐᵒᵖ →+* A)).obj N) (m : M) :
    commInverseLinearMap R A M N (tmul R Aᵐᵒᵖ n m) = tmul R A m (n : N) := by
  have h (x : N) : (mk R A (M := M) (N := N)).flip x m = tmul R A m x := by simp
  exact (lift_tmul (A := Aᵐᵒᵖ) _ _ n m).trans (h n)

/-- Flipping the factors takes the balanced tensor over `A` to the balanced tensor over
`Aᵐᵒᵖ`. The left action on `N` is viewed as a right action of `Aᵐᵒᵖ`. -/
noncomputable def comm : BalancedTensorProduct R A M N ≃ₗ[R]
    BalancedTensorProduct R Aᵐᵒᵖ
      ((ModuleCat.restrictScalars.{v} (↑(RingEquiv.opOp A).symm : Aᵐᵒᵖᵐᵒᵖ →+* A)).obj N) M :=
  LinearEquiv.ofLinearMap (commLinearMap R A M N) (commInverseLinearMap R A M N)
    (hom_ext fun n m ↦ by
      simp only [LinearMap.comp_apply, commInverseLinearMap_tmul, LinearMap.id_apply]
      exact commLinearMap_tmul R A M N m n)
    (hom_ext fun m n ↦ by
      simp only [LinearMap.comp_apply, commLinearMap_tmul, LinearMap.id_apply]
      exact commInverseLinearMap_tmul R A M N n m)

/-- The equivalence sends a pure tensor to the pure tensor with the two entries reversed. -/
theorem comm_tmul (m : M) (n : N) :
    comm R A M N (tmul R A m n) =
      tmul R Aᵐᵒᵖ
        (M := (ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom).obj N) n m :=
  commLinearMap_tmul R A M N m n

/-- Swapping a pure tensor over the opposite ring recovers the original order. -/
theorem comm_symm_tmul
    (n : (ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom).obj N) (m : M) :
    (comm R A M N).symm (tmul R Aᵐᵒᵖ n m) = tmul R A m (n : N) :=
  commInverseLinearMap_tmul R A M N n m

/-- For a fixed right module, swapping tensors gives a natural isomorphism with the
opposite-ring partial tensor functor. -/
noncomputable def functorCommIso : (functor.{r, a, u, v} R A).obj M ≅
    ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom ⋙
      (functor.{r, a, v, u} R Aᵐᵒᵖ).flip.obj M :=
  NatIso.ofComponents (fun N ↦ (comm R A M N).toModuleIso) fun f ↦
    ModuleCat.hom_ext (hom_ext fun m n ↦
      let fop := (ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom).map f
      (congrArg (comm R A M _) (lTensor_tmul f.hom m n)).trans <|
        (comm_tmul R A M _ m (f n)).trans <|
          (rTensor_tmul fop.hom n m).symm.trans <|
            congrArg _ (comm_tmul R A M _ m n).symm)

/-- The natural swap acts on pure tensors by exchanging their entries. -/
theorem functorCommIso_hom_app_tmul (m : M) (n : N) :
    ((functorCommIso.{r, a, u, v} R A M).hom.app N).hom (tmul R A m n) =
      tmul R Aᵐᵒᵖ
        (M := (ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom).obj N) n m :=
  comm_tmul R A M N m n

/-- The inverse natural swap returns the pure tensor over the original ring. -/
theorem functorCommIso_inv_app_tmul (m : M)
    (n : (ModuleCat.restrictScalars (RingEquiv.opOp A).symm.toRingHom).obj N) :
    ((functorCommIso.{r, a, u, v} R A M).inv.app N).hom (tmul R Aᵐᵒᵖ n m) = tmul R A m (n : N) :=
  comm_symm_tmul R A M N n m

instance (M : ModuleCat.{v} Aᵐᵒᵖ) : ((functor.{r, a, v, v} R A).obj M).IsLeftAdjoint := by
  let e : ModuleCat.{v} A ≌ ModuleCat.{v} Aᵐᵒᵖᵐᵒᵖ :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A).symm
  have : (ModuleCat.restrictScalars.{v} (RingEquiv.opOp A).symm.toRingHom).IsLeftAdjoint :=
    e.isLeftAdjoint_functor
  exact Functor.isLeftAdjoint_of_iso (functorCommIso.{r, a, v, v} R A M).symm

end Comm

end TauCeti.BalancedTensorProduct

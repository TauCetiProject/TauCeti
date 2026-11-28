/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Linear.LinearTensor.Basic

/-!
# Symmetry and opposites of `LinearTensor`

The tensor product of two linear categories admits linear equivalences that exchange its factors
or pass to the opposite of both factors. On morphisms the equivalences are induced by the
commutor of module tensor products and by applying `Quiver.Hom.unop` in both factors.
These comparisons apply to the categories used as domains of additive bimodule functors.

The tensor category construction in `TauCeti.LinearTensor` is the linear tensor product of
Mitchell, *Rings with several objects*, §2.
-/

public section

noncomputable section

open CategoryTheory Opposite

universe w v₁ v₂ u₁ u₂

namespace TauCeti

namespace LinearTensor

variable {R : Type w} [CommSemiring R]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]

section Symmetry

/-- The hom equivalence of the factor swap is induced by the commutor of module tensor products. -/
def swapHomEquiv (P Q : LinearTensor R C D) :
    (P ⟶ Q) ≃ₗ[R] ((⟨P.snd, P.fst⟩ : LinearTensor R D C) ⟶ ⟨Q.snd, Q.fst⟩) :=
  (homEquiv P Q).trans <| (TensorProduct.comm R _ _).trans
    (homEquiv (k := R) ⟨P.snd, P.fst⟩ ⟨Q.snd, Q.fst⟩).symm

/-- The hom equivalence exchanges the two pure tensor factors. -/
@[simp]
theorem swapHomEquiv_tmul {X Y : C} {X' Y' : D} (f : X ⟶ Y) (g : X' ⟶ Y') :
    swapHomEquiv _ _ (tmul (k := R) f g) = tmul (k := R) g f :=
  (rfl)

/-- The linear functor exchanging the factors of a tensor product. -/
@[expose, implicit_reducible]
def swapFunctor : LinearTensor R C D ⥤ LinearTensor R D C where
  obj P := ⟨P.snd, P.fst⟩
  map {P Q} := swapHomEquiv P Q
  map_id := fun ⟨X, Y⟩ ↦ by rw [← tmul_id_id X Y, swapHomEquiv_tmul, tmul_id_id]
  map_comp := by
    apply map_comp_of_tmul (fun P : LinearTensor R C D ↦ (⟨P.snd, P.fst⟩ : LinearTensor R D C))
      (fun P Q ↦ (swapHomEquiv P Q).toLinearMap)
    intro X Y Z X' Y' Z' f g f' g'
    simp only [LinearEquiv.coe_coe]
    rw [swapHomEquiv_tmul (R := R) (f ≫ f') (g ≫ g'), swapHomEquiv_tmul (R := R) f g,
      swapHomEquiv_tmul (R := R) f' g', tmul_comp_tmul]

/-- The swap functor exchanges the components of each object. -/
@[simp]
theorem swapFunctor_obj (P : LinearTensor R C D) :
    (swapFunctor (R := R)).obj P = ⟨P.snd, P.fst⟩ :=
  (rfl)

/-- The swap functor exchanges the factors of each pure tensor. -/
@[simp]
theorem swapFunctor_map_tmul {X Y : C} {X' Y' : D} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (swapFunctor (R := R)).map (tmul f g) = tmul (k := R) g f :=
  swapHomEquiv_tmul (R := R) f g

instance : (swapFunctor (R := R) (C := C) (D := D)).Additive :=
  ⟨fun {P Q f g} ↦ (swapHomEquiv (R := R) P Q).map_add f g⟩

instance : (swapFunctor (R := R) (C := C) (D := D)).Linear R :=
  ⟨fun {P Q} f r ↦ (swapHomEquiv (R := R) P Q).map_smul r f⟩

/-- Swapping the factors twice fixes each morphism. -/
@[simp]
theorem swapFunctor_map_swapFunctor_map {P Q : LinearTensor R C D} (t : P ⟶ Q) :
    swapFunctor.map (swapFunctor.map t) = t := by
  simp only [swapFunctor, swapHomEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, TensorProduct.comm_comm, LinearEquiv.symm_apply_apply]

/-- Exchanging the two factors of a linear tensor product gives an equivalence, with the same
exchange in the reverse direction. -/
@[expose, implicit_reducible, simps functor inverse]
def swapEquiv : LinearTensor R C D ≌ LinearTensor R D C where
  functor := swapFunctor
  inverse := swapFunctor
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro P Q t
    simp)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro P Q t
    simp)
  functor_unitIso_comp := by
    intro P
    simp [NatIso.ofComponents]

/-- The unit of the swap equivalence is the identity on each object. -/
@[simp]
theorem swapEquiv_unitIso_hom_app (P : LinearTensor R C D) :
    swapEquiv.unitIso.hom.app P = 𝟙 P :=
  rfl

/-- The inverse unit of the swap equivalence is the identity on each object. -/
@[simp]
theorem swapEquiv_unitIso_inv_app (P : LinearTensor R C D) :
    swapEquiv.unitIso.inv.app P = 𝟙 P :=
  rfl

/-- The counit of the swap equivalence is the identity on each object. -/
@[simp]
theorem swapEquiv_counitIso_hom_app (P : LinearTensor R D C) :
    swapEquiv.counitIso.hom.app P = 𝟙 P :=
  rfl

/-- The inverse counit of the swap equivalence is the identity on each object. -/
@[simp]
theorem swapEquiv_counitIso_inv_app (P : LinearTensor R D C) :
    swapEquiv.counitIso.inv.app P = 𝟙 P :=
  rfl

instance : (swapEquiv (R := R) (C := C) (D := D)).functor.Additive :=
  inferInstanceAs (swapFunctor (R := R) (C := C) (D := D)).Additive

instance : (swapEquiv (R := R) (C := C) (D := D)).functor.Linear R :=
  (inferInstance : (swapFunctor (R := R) (C := C) (D := D)).Linear R)

end Symmetry

section Opposite

/-- The hom equivalence relating the tensor of opposites to the opposite tensor, induced
by `Quiver.Hom.unop` on each factor. -/
def opHomEquiv (P Q : LinearTensor R Cᵒᵖ Dᵒᵖ) :
    (P ⟶ Q) ≃ₗ[R] ((op (⟨P.fst.unop, P.snd.unop⟩ : LinearTensor R C D)) ⟶
      op ⟨Q.fst.unop, Q.snd.unop⟩) :=
  let X : LinearTensor R C D := ⟨P.fst.unop, P.snd.unop⟩
  let Y : LinearTensor R C D := ⟨Q.fst.unop, Q.snd.unop⟩
  let e₁ : (P.fst ⟶ Q.fst) ≃ₗ[R] (Y.fst ⟶ X.fst) :=
    { toEquiv := CategoryTheory.opEquiv P.fst Q.fst
      map_add' := unop_add C
      map_smul' := Linear.unop_smul }
  let e₂ : (P.snd ⟶ Q.snd) ≃ₗ[R] (Y.snd ⟶ X.snd) :=
    { toEquiv := CategoryTheory.opEquiv P.snd Q.snd
      map_add' := unop_add D
      map_smul' := Linear.unop_smul }
  let e : (Y ⟶ X) ≃ₗ[R] (op X ⟶ op Y) :=
    { toEquiv := (CategoryTheory.opEquiv (op X) (op Y)).symm
      map_add' := op_add (LinearTensor R C D)
      map_smul' := Linear.op_smul }
  (homEquiv P Q).trans <| (TensorProduct.congr e₁ e₂).trans <| (homEquiv Y X).symm.trans e

/-- On pure tensors, the hom comparison removes the opposites on the factors
and takes the opposite of the resulting pure tensor. -/
@[simp]
theorem opHomEquiv_tmul {X Y : Cᵒᵖ} {X' Y' : Dᵒᵖ} (f : X ⟶ Y) (g : X' ⟶ Y') :
    opHomEquiv _ _ (tmul (k := R) f g) = (tmul (k := R) f.unop g.unop).op :=
  (rfl)

/-- The linear functor from the tensor of opposites to the opposite tensor. -/
@[expose, implicit_reducible]
def opFunctor : LinearTensor R Cᵒᵖ Dᵒᵖ ⥤ (LinearTensor R C D)ᵒᵖ where
  obj P := op ⟨P.fst.unop, P.snd.unop⟩
  map {P Q} := opHomEquiv P Q
  map_id := fun ⟨X, Y⟩ ↦ by rw [← tmul_id_id X Y, opHomEquiv_tmul]; simp
  map_comp := by
    apply map_comp_of_tmul
      (fun P : LinearTensor R Cᵒᵖ Dᵒᵖ ↦ op (⟨P.fst.unop, P.snd.unop⟩ : LinearTensor R C D))
      (fun P Q ↦ (opHomEquiv P Q).toLinearMap)
    intro X Y Z X' Y' Z' f g f' g'
    simp only [LinearEquiv.coe_coe]
    rw [opHomEquiv_tmul (R := R) (f ≫ f') (g ≫ g'), opHomEquiv_tmul (R := R) f g,
      opHomEquiv_tmul (R := R) f' g']
    simp only [unop_comp, ← op_comp, tmul_comp_tmul]

/-- The opposite comparison sends a pair of opposite objects to the opposite pair. -/
@[simp]
theorem opFunctor_obj (P : LinearTensor R Cᵒᵖ Dᵒᵖ) :
    (opFunctor (R := R)).obj P = op ⟨P.fst.unop, P.snd.unop⟩ :=
  (rfl)

/-- The opposite comparison sends a pure tensor of opposite arrows to the opposite of their
tensor. -/
@[simp]
theorem opFunctor_map_tmul {X Y : Cᵒᵖ} {X' Y' : Dᵒᵖ} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (opFunctor (R := R)).map (tmul f g) = (tmul (k := R) f.unop g.unop).op :=
  opHomEquiv_tmul (R := R) f g

instance : (opFunctor (R := R) (C := C) (D := D)).Additive :=
  ⟨fun {P Q f g} ↦ (opHomEquiv (R := R) P Q).map_add f g⟩

instance : (opFunctor (R := R) (C := C) (D := D)).Linear R :=
  ⟨fun {P Q} f r ↦ (opHomEquiv (R := R) P Q).map_smul r f⟩

/-- The inverse comparison from the opposite of a tensor product to the tensor of opposites. -/
@[expose, implicit_reducible]
def unopFunctor : (LinearTensor R C D)ᵒᵖ ⥤ LinearTensor R Cᵒᵖ Dᵒᵖ :=
  let obj (P : (LinearTensor R C D)ᵒᵖ) : LinearTensor R Cᵒᵖ Dᵒᵖ :=
    ⟨op P.unop.fst, op P.unop.snd⟩
  let fullyFaithful : (opFunctor (R := R) (C := C) (D := D)).FullyFaithful :=
    { preimage := fun {P Q} ↦ (opHomEquiv P Q).symm
      map_preimage := fun {P Q} ↦ (opHomEquiv P Q).apply_symm_apply
      preimage_map := fun {P Q} ↦ (opHomEquiv P Q).symm_apply_apply }
  { obj
    map := fun {P Q} ↦ fullyFaithful.preimage (X := obj P) (Y := obj Q)
    map_id := fun P ↦ fullyFaithful.preimage_id (X := obj P)
    map_comp := fun {P Q S} ↦ fullyFaithful.preimage_comp (X := obj P) (Y := obj Q) (Z := obj S) }

/-- The inverse comparison takes the opposite of each component of the pair. -/
@[simp]
theorem unopFunctor_obj (P : (LinearTensor R C D)ᵒᵖ) :
    (unopFunctor (R := R)).obj P = ⟨op P.unop.fst, op P.unop.snd⟩ :=
  (rfl)

/-- The inverse opposite comparison recovers the pure tensor of opposite morphisms. -/
@[simp]
theorem unopFunctor_map_op_tmul {X Y : C} {X' Y' : D} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (unopFunctor (R := R)).map (tmul f g).op = tmul (k := R) f.op g.op :=
  (opHomEquiv (R := R) ⟨op Y, op Y'⟩ ⟨op X, op X'⟩).symm_apply_eq.2
    (opHomEquiv_tmul (R := R) f.op g.op).symm

/-- The forward opposite comparison undoes the inverse comparison on morphisms. -/
@[simp]
theorem opFunctor_map_unopFunctor_map {P Q : (LinearTensor R C D)ᵒᵖ} (f : P ⟶ Q) :
    opFunctor.map (unopFunctor.map f) = f :=
  (opHomEquiv (unopFunctor.obj P) (unopFunctor.obj Q)).apply_symm_apply f

/-- The inverse opposite comparison undoes the forward comparison on morphisms. -/
@[simp]
theorem unopFunctor_map_opFunctor_map {P Q : LinearTensor R Cᵒᵖ Dᵒᵖ} (f : P ⟶ Q) :
    unopFunctor.map (opFunctor.map f) = f :=
  (opHomEquiv P Q).symm_apply_apply f

/-- The tensor product of the opposite categories is linearly equivalent to the opposite of
the tensor product. -/
@[expose, implicit_reducible, simps! functor inverse]
def opEquiv : LinearTensor R Cᵒᵖ Dᵒᵖ ≌ (LinearTensor R C D)ᵒᵖ :=
  CategoryTheory.Equivalence.mk opFunctor unopFunctor
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro P Q f
      simp only [Iso.refl_hom, Functor.id_map, Functor.comp_map, unopFunctor_map_opFunctor_map]
      exact (Category.comp_id f).trans (Category.id_comp f).symm))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro P Q f
      simp only [Iso.refl_hom, Functor.id_map, Functor.comp_map, opFunctor_map_unopFunctor_map]
      exact (Category.comp_id f).trans (Category.id_comp f).symm))

/-- The counit of the opposite comparison is the identity on each object. -/
@[simp]
theorem opEquiv_counitIso_hom_app (P : (LinearTensor R C D)ᵒᵖ) :
    opEquiv.counitIso.hom.app P = 𝟙 P :=
  rfl

/-- The inverse counit of the opposite comparison is the identity on each object. -/
@[simp]
theorem opEquiv_counitIso_inv_app (P : (LinearTensor R C D)ᵒᵖ) :
    opEquiv.counitIso.inv.app P = 𝟙 P :=
  rfl

/-- The unit of the opposite comparison is the identity on each object. -/
@[simp]
theorem opEquiv_unitIso_hom_app (P : LinearTensor R Cᵒᵖ Dᵒᵖ) :
    opEquiv.unitIso.hom.app P = 𝟙 P := by
  calc
    _ = opEquiv.inverse.map (opEquiv.counitIso.inv.app (opEquiv.functor.obj P)) :=
      opEquiv.unit_app_inverse (opEquiv.functor.obj P)
    _ = 𝟙 P := by
      rw [opEquiv_counitIso_inv_app]
      exact opEquiv.inverse.map_id (opEquiv.functor.obj P)

/-- The inverse unit of the opposite comparison is the identity on each object. -/
@[simp]
theorem opEquiv_unitIso_inv_app (P : LinearTensor R Cᵒᵖ Dᵒᵖ) :
    opEquiv.unitIso.inv.app P = 𝟙 P := by
  simpa only [opEquiv_unitIso_hom_app, Category.id_comp] using opEquiv.unitIso_hom_inv_id_app P

instance : (opEquiv (R := R) (C := C) (D := D)).functor.Additive :=
  (inferInstance : (opFunctor (R := R) (C := C) (D := D)).Additive)

instance : (opEquiv (R := R) (C := C) (D := D)).functor.Linear R :=
  (inferInstance : (opFunctor (R := R) (C := C) (D := D)).Linear R)

instance : (unopFunctor (R := R) (C := C) (D := D)).Additive :=
  (opEquiv (R := R) (C := C) (D := D)).inverse_additive

instance : (unopFunctor (R := R) (C := C) (D := D)).Linear R :=
  (opEquiv (R := R) (C := C) (D := D)).inverseLinear R

end Opposite

end LinearTensor

end TauCeti

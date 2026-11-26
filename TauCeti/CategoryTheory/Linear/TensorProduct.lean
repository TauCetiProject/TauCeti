/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import TauCeti.CategoryTheory.Linear.DeligneProduct.Basic

/-!
# Symmetry and opposites of linear tensor products

The tensor product of two linear categories admits linear equivalences that exchange its factors
or pass to the opposite of both factors. On morphisms the equivalences are induced by the
commutor of module tensor products and by applying `Quiver.Hom.unop` in both factors.
The product also preserves essential smallness in a common universe, so these comparisons
apply to the categories used as domains of additive bimodule functors. Fixing an object in
either factor gives a linear slice functor via `LinearTensor.bifunctor`.

For preadditive categories we use the same product over `ℤ`, via Mathlib's canonical
`CategoryTheory.Linear.preadditiveIntLinear` instances. The tensor category construction in
`TauCeti.LinearTensor` is the linear tensor product of Mitchell, *Rings with several objects*,
§2.
-/

public section

noncomputable section

open CategoryTheory Opposite

universe w v₁ v₂ v₃ u₁ u₂ u₃ s

namespace TauCeti

/-- The tensor product of preadditive categories, using their canonical integer linearity. -/
abbrev Preadditive.TensorProduct (C : Type u₁) (D : Type u₂) := LinearTensor ℤ C D

namespace LinearTensor

variable {R : Type w} [CommSemiring R]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]

section Transport

variable {E : Type u₃} [Category.{v₃} E] [Preadditive E] [Linear R E]
  (obj : LinearTensor R C D → E)
  (hom : ∀ P Q, (P ⟶ Q) ≃ₗ[R] (obj P ⟶ obj Q))

private theorem map_comp_of_tmul
    (comp : ∀ {X Y Z : C} {X' Y' Z' : D}
      (f : X ⟶ Y) (g : X' ⟶ Y') (f' : Y ⟶ Z) (g' : Y' ⟶ Z'),
      hom ⟨X, X'⟩ ⟨Z, Z'⟩ (tmul (f ≫ f') (g ≫ g')) =
        hom ⟨X, X'⟩ ⟨Y, Y'⟩ (tmul f g) ≫ hom ⟨Y, Y'⟩ ⟨Z, Z'⟩ (tmul f' g'))
    {P Q S : LinearTensor R C D} (a : P ⟶ Q) (b : Q ⟶ S) :
    hom P S (a ≫ b) = hom P Q a ≫ hom Q S b := by
  obtain ⟨X, X'⟩ := P
  obtain ⟨Y, Y'⟩ := Q
  obtain ⟨Z, Z'⟩ := S
  induction a using hom_induction_on with
  | add a₁ a₂ h₁ h₂ =>
    simp only [Preadditive.add_comp, map_add, h₁, h₂]
  | tmul f g =>
    induction b using hom_induction_on with
    | add b₁ b₂ h₁ h₂ =>
      simp only [Preadditive.comp_add, map_add, h₁, h₂]
    | tmul f' g' => simpa only [tmul_comp_tmul] using comp f g f' g'

end Transport

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
    apply map_comp_of_tmul
    intro X Y Z X' Y' Z' f g f' g'
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
    swapFunctor.map (swapFunctor.map t) = t :=
  TensorProduct.comm_comm R _ _ t

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
    intro X Y Z X' Y' Z' f g f' g'
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
  { obj
    map := fun {P Q} f ↦ (opHomEquiv (obj P) (obj Q)).symm f
    map_id := fun P ↦ by
      apply (opHomEquiv (obj P) (obj P)).injective
      rw [LinearEquiv.apply_symm_apply]
      exact (opFunctor.map_id (obj P)).symm
    map_comp := fun {P Q S} f g ↦ by
      apply (opHomEquiv (obj P) (obj S)).injective
      rw [LinearEquiv.apply_symm_apply]
      let e := opHomEquiv (obj P) (obj Q)
      let e' := opHomEquiv (obj Q) (obj S)
      have h := (opFunctor (R := R)).map_comp (e.symm f) (e'.symm g)
      exact (h.trans (congrArg₂ CategoryStruct.comp
        (e.apply_symm_apply f) (e'.apply_symm_apply g))).symm }

/-- The inverse comparison takes the opposite of each component of the pair. -/
@[simp]
theorem unopFunctor_obj (P : (LinearTensor R C D)ᵒᵖ) :
    (unopFunctor (R := R)).obj P = ⟨op P.unop.fst, op P.unop.snd⟩ :=
  (rfl)

/-- The inverse opposite comparison recovers the pure tensor of opposite morphisms. -/
@[simp]
theorem unopFunctor_map_op_tmul {X Y : C} {X' Y' : D} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (unopFunctor (R := R)).map (tmul f g).op = tmul (k := R) f.op g.op :=
  (rfl)

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

section Smallness

/-- The homs of the tensor product are small in any universe in which both factors have
small homs. -/
instance [LocallySmall.{s} C] [LocallySmall.{s} D] : LocallySmall.{s} (LinearTensor R C D) where
  hom_small P Q := small_map (homEquiv P Q).toEquiv

/-- The tensor product of two essentially small linear categories is essentially small in
the same universe. -/
instance [EssentiallySmall.{s} C] [EssentiallySmall.{s} D] :
    EssentiallySmall.{s} (LinearTensor R C D) := by
  refine (essentiallySmall_iff _).2 ⟨?_, inferInstance⟩
  refine small_of_surjective (f := fun p : Skeleton C × Skeleton D ↦
    toSkeleton (⟨(fromSkeleton C).obj p.1, (fromSkeleton D).obj p.2⟩ : LinearTensor R C D)) ?_
  intro P
  obtain ⟨⟨X, Y⟩, rfl⟩ := Quotient.exists_rep P
  exact ⟨(toSkeleton X, toSkeleton Y), congr_toSkeleton_of_iso
    (isoMk (fromSkeletonToSkeletonIso X) (fromSkeletonToSkeletonIso Y))⟩

end Smallness

end LinearTensor

end TauCeti

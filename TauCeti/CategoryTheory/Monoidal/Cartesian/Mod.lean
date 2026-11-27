/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# Actions on representing objects

Let `M` be a monoid object of a cartesian monoidal category `C` and `F` a presheaf of sets on `C`
on which the monoids `T ⟶ M` act, naturally in `T`. If `F` is represented by an object `X`, the
Yoneda lemma turns this action into an action of `M` on `X`
(`TauCeti.ModObj.ofRepresentableBy`): the action morphism `M ⊗ X ⟶ X` corresponds to the
element `fst • snd` of `F` over `M ⊗ X`. The representation is then equivariant, sending
`m • x` to `m • α.homEquiv x` (`TauCeti.ModObj.homEquiv_smul_ofRepresentableBy`).

This is the analogue for module objects of Mathlib's `CategoryTheory.MonObj.ofRepresentableBy`.
It is used to equip a scheme representing a torsor sheaf under a group scheme with its action.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped MonObj

namespace TauCeti.ModObj

universe w v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (M : C) [MonObj M]
  {F : Cᵒᵖ ⥤ Type w} [∀ T : C, MulAction (T ⟶ M) (F.obj (op T))] {X : C}

/-- The candidate action morphism `M ⊗ X ⟶ X` on an object `X` representing `F`: it
corresponds to the element `fst • snd` of `F` over `M ⊗ X`. -/
private noncomputable def smulOfRepresentableBy (α : F.RepresentableBy X) : M ⊗ X ⟶ X :=
  α.homEquiv.symm (fst M X • α.homEquiv (snd M X))

variable {M}

private lemma homEquiv_lift_comp_smulOfRepresentableBy
    (hF : ∀ ⦃T T' : C⦄ (f : T' ⟶ T) (m : T ⟶ M) (x : F.obj (op T)),
      F.map f.op (m • x) = (f ≫ m) • F.map f.op x)
    (α : F.RepresentableBy X) {T : C} (m : T ⟶ M) (x : T ⟶ X) :
    α.homEquiv (lift m x ≫ smulOfRepresentableBy M α) = m • α.homEquiv x := by
  rw [α.homEquiv_comp, smulOfRepresentableBy, Equiv.apply_symm_apply, hF, lift_fst,
    ← α.homEquiv_comp, lift_snd]

variable (M) in
/-- **Actions on a representing object.** If the monoids `T ⟶ M` act on the values of a presheaf
`F`, naturally in `T`, and `F` is represented by `X`, then `M` acts on `X`: the action morphism
`M ⊗ X ⟶ X` corresponds to the element `fst • snd` of `F` over `M ⊗ X`. The representation is
then equivariant (`homEquiv_smul_ofRepresentableBy`). -/
@[instance_reducible]
noncomputable def ofRepresentableBy
    (hF : ∀ ⦃T T' : C⦄ (f : T' ⟶ T) (m : T ⟶ M) (x : F.obj (op T)),
      F.map f.op (m • x) = (f ≫ m) • F.map f.op x)
    (α : F.RepresentableBy X) : ModObj M X where
  smul := smulOfRepresentableBy M α
  one_smul := by
    have h : η[M] ▷ X = lift (fst _ _ ≫ η[M]) (snd _ _) := by ext <;> simp
    apply α.homEquiv.injective
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionUnitIso]
    rw [h, homEquiv_lift_comp_smulOfRepresentableBy hF, leftUnitor_hom,
      toUnit_unique (fst _ _) (toUnit _), ← Hom.one_def, one_smul]
  mul_smul := by
    have h₁ : μ[M] ▷ X = lift (fst _ _ ≫ μ[M]) (snd _ _) := by ext <;> simp
    have h₂ : (α_ M M X).hom ≫ M ◁ smulOfRepresentableBy M α =
        lift (fst _ _ ≫ fst _ _) (lift (fst _ _ ≫ snd _ _) (snd _ _) ≫
          smulOfRepresentableBy M α) := by
      ext
      · simp
      · have h : (α_ M M X).hom ≫ snd M (M ⊗ X) = lift (fst _ _ ≫ snd _ _) (snd _ _) := by
          ext <;> simp
        simp [reassoc_of% h]
    have h₃ : fst (M ⊗ M) X ≫ μ[M] = (fst _ _ ≫ fst _ _) * (fst _ _ ≫ snd _ _) := by
      rw [Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
    apply α.homEquiv.injective
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight,
      selfLeftAction_actionAssocIso]
    rw [h₁, reassoc_of% h₂, homEquiv_lift_comp_smulOfRepresentableBy hF,
      homEquiv_lift_comp_smulOfRepresentableBy hF, homEquiv_lift_comp_smulOfRepresentableBy hF,
      h₃, mul_smul]

/-- For the action `ofRepresentableBy`, the representation sends `m • x` to `m • α.homEquiv x`. -/
lemma homEquiv_smul_ofRepresentableBy
    (hF : ∀ ⦃T T' : C⦄ (f : T' ⟶ T) (m : T ⟶ M) (x : F.obj (op T)),
      F.map f.op (m • x) = (f ≫ m) • F.map f.op x)
    (α : F.RepresentableBy X) {T : C} (m : T ⟶ M) (x : T ⟶ X) :
    letI := ofRepresentableBy M hF α
    α.homEquiv (m • x) = m • α.homEquiv x :=
  homEquiv_lift_comp_smulOfRepresentableBy hF α m x

end TauCeti.ModObj

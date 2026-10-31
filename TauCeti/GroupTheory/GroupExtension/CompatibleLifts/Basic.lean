/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic
public import TauCeti.GroupTheory.GroupExtension.Basic

/-!
# Compatible lifts of automorphisms of a group extension

For an extension `S` and an action `ρ` on its quotient, `S.compatibleLifts ρ` is the subgroup
of pairs consisting of an automorphism of the middle group and an element of the acting group.
The automorphism fixes the included kernel pointwise and induces the specified quotient action.
Its projection need not be surjective: `GroupExtension.compatibleLiftsToLiftable` restricts its
codomain to the subgroup of elements that have a lift.

The action `ρ` need not be faithful. In particular, the projection remembers the acting-group
element even when different elements induce the same quotient automorphism. Each compatible
lift also supplies a native equivalence with the quotient-relabeled extension.
-/

public section

namespace GroupExtension

variable {N E G A : Type*} [Group N] [Group E] [Group G] [Group A]
  (S : GroupExtension N E G) (ρ : A →* MulAut G)

/-- Automorphisms fixing the included kernel, paired with the element whose quotient action
they induce. -/
def compatibleLifts : Subgroup (MulAut E × A) where
  carrier := {x | (∀ n, x.1 (S.inl n) = S.inl n) ∧
    ∀ e, S.rightHom (x.1 e) = ρ x.2 (S.rightHom e)}
  one_mem' := ⟨fun _ => rfl, fun _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxn, hxg⟩ ⟨hyn, hyg⟩
    constructor
    · intro n
      simpa only [Prod.fst_mul, MulAut.mul_apply] using (congrArg x.1 (hyn n)).trans (hxn n)
    · intro e
      simp only [Prod.fst_mul, Prod.snd_mul, MulAut.mul_apply, hxg, hyg, map_mul]
  inv_mem' := by
    rintro x ⟨hxn, hxg⟩
    constructor
    · intro n
      simp only [Prod.fst_inv, MulAut.inv_apply]
      apply x.1.injective
      rw [MulEquiv.apply_symm_apply, hxn]
    · intro e
      simp only [Prod.fst_inv, Prod.snd_inv, MulAut.inv_apply]
      apply (ρ x.2).injective
      simpa only [map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply] using
        (hxg (x.1.symm e)).symm

@[simp]
theorem mem_compatibleLifts (x : MulAut E × A) :
    x ∈ S.compatibleLifts ρ ↔ (∀ n, x.1 (S.inl n) = S.inl n) ∧
      ∀ e, S.rightHom (x.1 e) = ρ x.2 (S.rightHom e) :=
  Iff.rfl

/-- The action of a compatible lift on the middle group. -/
def compatibleLiftsToMulAut : S.compatibleLifts ρ →* MulAut E :=
  (MonoidHom.fst (MulAut E) A).comp (S.compatibleLifts ρ).subtype

theorem compatibleLiftsToMulAut_apply (x : S.compatibleLifts ρ) :
    compatibleLiftsToMulAut S ρ x = x.val.1 :=
  (rfl)

/-- The quotient-action element recorded by a compatible lift. -/
def compatibleLiftsProjection : S.compatibleLifts ρ →* A :=
  (MonoidHom.snd (MulAut E) A).comp (S.compatibleLifts ρ).subtype

theorem compatibleLiftsProjection_apply (x : S.compatibleLifts ρ) :
    compatibleLiftsProjection S ρ x = x.val.2 :=
  (rfl)

/-- Compatible lifts are equal when their two components agree. -/
@[ext]
theorem compatibleLifts_ext {x y : S.compatibleLifts ρ}
    (hAut : compatibleLiftsToMulAut S ρ x = compatibleLiftsToMulAut S ρ y)
    (hAct : compatibleLiftsProjection S ρ x = compatibleLiftsProjection S ρ y) : x = y :=
  Subtype.ext (Prod.ext hAut hAct)

/-- The subgroup of acting-group elements that admit a compatible lift. -/
abbrev compatibleLiftsLiftableSubgroup : Subgroup A :=
  (compatibleLiftsProjection S ρ).range

theorem mem_compatibleLiftsLiftableSubgroup {a : A} :
    a ∈ compatibleLiftsLiftableSubgroup S ρ ↔ ∃ f : MulAut E, (f, a) ∈ S.compatibleLifts ρ := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨compatibleLiftsToMulAut S ρ x, x.property⟩
  · rintro ⟨f, hf⟩
    exact ⟨⟨(f, a), hf⟩, rfl⟩

/-- Projection onto the actual subgroup of elements admitting a lift. -/
abbrev compatibleLiftsToLiftable : S.compatibleLifts ρ →* compatibleLiftsLiftableSubgroup S ρ :=
  (compatibleLiftsProjection S ρ).rangeRestrict

@[simp]
theorem coe_compatibleLiftsToLiftable (x : S.compatibleLifts ρ) :
    (compatibleLiftsToLiftable S ρ x : A) = compatibleLiftsProjection S ρ x :=
  (rfl)

theorem compatibleLiftsToLiftable_surjective : Function.Surjective
    (compatibleLiftsToLiftable S ρ) :=
  (compatibleLiftsProjection S ρ).rangeRestrict_surjective

@[simp]
theorem compatibleLiftsToMulAut_inl (x : S.compatibleLifts ρ) (n : N) :
    compatibleLiftsToMulAut S ρ x (S.inl n) = S.inl n :=
  x.property.1 n

@[simp]
theorem rightHom_compatibleLiftsToMulAut (x : S.compatibleLifts ρ) (e : E) :
    S.rightHom (compatibleLiftsToMulAut S ρ x e) =
      ρ (compatibleLiftsProjection S ρ x) (S.rightHom e) :=
  x.property.2 e

@[simp]
theorem rightHom_compatibleLiftsToMulAut_symm (x : S.compatibleLifts ρ) (e : E) :
    S.rightHom ((compatibleLiftsToMulAut S ρ x).symm e) =
      (ρ (compatibleLiftsProjection S ρ x)).symm (S.rightHom e) := by
  apply (ρ (compatibleLiftsProjection S ρ x)).injective
  simpa only [MulEquiv.apply_symm_apply] using
    (rightHom_compatibleLiftsToMulAut S ρ x ((compatibleLiftsToMulAut S ρ x).symm e)).symm

/-- Conjugating a character twist pulls the character back by the inverse quotient action. -/
theorem compatibleLiftsToMulAut_conj_twist (hcentral : S.inl.range ≤ Subgroup.center E)
    (x : S.compatibleLifts ρ) (χ : G →* N) :
    compatibleLiftsToMulAut S ρ x * twist S hcentral χ * (compatibleLiftsToMulAut S ρ x)⁻¹ =
      twist S hcentral (χ.comp (ρ (compatibleLiftsProjection S ρ x)).symm.toMonoidHom) := by
  ext e
  simp [MulAut.mul_apply, MulAut.inv_apply]

/-- A compatible lift is an equivalence from the quotient-relabeled extension to the
original extension. -/
def compatibleLiftsToExtensionEquiv (x : S.compatibleLifts ρ) :
    (S.relabelQuotient (ρ (compatibleLiftsProjection S ρ x))).Equiv S where
  toMulEquiv := compatibleLiftsToMulAut S ρ x
  inl_comm := by
    ext n
    simpa only [Function.comp_apply, relabelQuotient_inl] using compatibleLiftsToMulAut_inl S ρ x n
  rightHom_comm := by
    ext e
    simpa only [Function.comp_apply, relabelQuotient_rightHom, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom] using rightHom_compatibleLiftsToMulAut S ρ x e

@[simp]
theorem compatibleLiftsToExtensionEquiv_apply (x : S.compatibleLifts ρ) (e : E) :
    compatibleLiftsToExtensionEquiv S ρ x e = compatibleLiftsToMulAut S ρ x e :=
  (rfl)

end GroupExtension

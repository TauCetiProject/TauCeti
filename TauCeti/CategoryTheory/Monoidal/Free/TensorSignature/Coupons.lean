/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Basic

/-!
# Coupon invariants and non-collapse on free monoidal categories

Because the monoidal-category axioms on `TauCeti.TensorSignature.FreeMonoidal S` only permute
coupons via the interchange law and never create or erase them, the multiset (list up to
permutation) of coupons occurring in a raw morphism is invariant under `FreeMonoidal.HomEquiv`.
Consequently, the total coupon count descends to an additive invariant `FreeMonoidal.couponCount`
on morphisms of `S.FreeMonoidal`, no coupon equals a structural transport `eqToHom`, and distinct
parallel coupons remain distinct in `S.FreeMonoidal`.

## Main definitions and results

* `TauCeti.TensorSignature.FreeMonoidal.Hom.coupons` and
  `TauCeti.TensorSignature.FreeMonoidal.HomEquiv.coupons_perm`: the list of coupons occurring in a
  formal morphism is invariant up to list permutation under the monoidal axioms.
* `TauCeti.TensorSignature.FreeMonoidal.coupons_perm_of_homMk_eq`: equal morphisms in
  `S.FreeMonoidal` have permuted coupon lists.
* `TauCeti.TensorSignature.FreeMonoidal.couponCount`: the number of coupons in a morphism of
  `S.FreeMonoidal`, additive under composition and tensor product and vanishing on identities,
  structural isomorphisms, and object-equality transports.
* `TauCeti.TensorSignature.FreeMonoidal.coupon_ne_eqToHom` and
  `TauCeti.TensorSignature.FreeMonoidal.coupon_eq_iff`: coupons never collapse to structural
  transports and parallel coupons are distinct whenever their labels are distinct.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1.
-/

public section

universe u v

open CategoryTheory MonoidalCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature.FreeMonoidal

variable {S : TensorSignature.{u, v}}

/-- The list of coupons occurring in a raw morphism expression, read left-to-right across
compositions and tensor products. -/
def Hom.coupons : ∀ {X Y : FreeMonoidalCategory S.Obj}, Hom X Y → List S.Coupon
  | _, _, .id _ => []
  | _, _, .α_hom _ _ _ => []
  | _, _, .α_inv _ _ _ => []
  | _, _, .l_hom _ => []
  | _, _, .l_inv _ => []
  | _, _, .ρ_hom _ => []
  | _, _, .ρ_inv _ => []
  | _, _, .coupon g => [g]
  | _, _, .comp f g => f.coupons ++ g.coupons
  | _, _, .whiskerLeft _ f => f.coupons
  | _, _, .whiskerRight f _ => f.coupons
  | _, _, .tensor f g => f.coupons ++ g.coupons

@[simp] theorem Hom.coupons_id (X) : (Hom.id (S := S) X).coupons = [] := (rfl)
@[simp] theorem Hom.coupons_α_hom (X Y Z) : (Hom.α_hom (S := S) X Y Z).coupons = [] := (rfl)
@[simp] theorem Hom.coupons_α_inv (X Y Z) : (Hom.α_inv (S := S) X Y Z).coupons = [] := (rfl)
@[simp] theorem Hom.coupons_l_hom (X) : (Hom.l_hom (S := S) X).coupons = [] := (rfl)
@[simp] theorem Hom.coupons_l_inv (X) : (Hom.l_inv (S := S) X).coupons = [] := (rfl)
@[simp] theorem Hom.coupons_ρ_hom (X) : (Hom.ρ_hom (S := S) X).coupons = [] := (rfl)
@[simp] theorem Hom.coupons_ρ_inv (X) : (Hom.ρ_inv (S := S) X).coupons = [] := (rfl)
@[simp] theorem Hom.coupons_coupon (g : S.Coupon) : (Hom.coupon g).coupons = [g] := (rfl)

@[simp]
theorem Hom.coupons_comp {X Y Z} (f : Hom (S := S) X Y) (g : Hom Y Z) :
    (f.comp g).coupons = f.coupons ++ g.coupons :=
  (rfl)

@[simp]
theorem Hom.coupons_whiskerLeft (X) {Y Z} (f : Hom (S := S) Y Z) :
    (f.whiskerLeft X).coupons = f.coupons :=
  (rfl)

@[simp]
theorem Hom.coupons_whiskerRight {X Y} (f : Hom (S := S) X Y) (Z) :
    (f.whiskerRight Z).coupons = f.coupons :=
  (rfl)

@[simp]
theorem Hom.coupons_tensor {W X Y Z} (f : Hom (S := S) W Y) (g : Hom X Z) :
    (f.tensor g).coupons = f.coupons ++ g.coupons :=
  (rfl)

@[simp]
theorem Hom.coupons_cast {X X' Y Y' : FreeMonoidalCategory S.Obj} (hX : X = X') (hY : Y = Y')
    (f : Hom (S := S) X Y) : (f.cast hX hY).coupons = f.coupons := by
  subst hX hY
  simp

/-- Equivalent formal morphisms contain the same coupons up to list permutation: the interchange
law permutes coupon lists, and no monoidal axiom creates or erases coupons. -/
theorem HomEquiv.coupons_perm {X Y : FreeMonoidalCategory S.Obj} {f g : Hom X Y}
    (h : HomEquiv f g) : f.coupons.Perm g.coupons := by
  induction h with
  | refl => exact List.Perm.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | comp _ _ ih₁ ih₂ => exact ih₁.append ih₂
  | whiskerLeft _ _ _ _ ih => exact ih
  | whiskerRight _ _ _ _ ih => exact ih
  | tensor _ _ ih₁ ih₂ => exact ih₁.append ih₂
  | tensorHom_def => exact List.Perm.refl _
  | comp_id => simp
  | id_comp => simp
  | assoc => simp
  | id_tensorHom_id => simp
  | tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ =>
    simp only [Hom.coupons_comp, Hom.coupons_tensor, List.append_assoc]
    exact List.Perm.append_left f₁.coupons (List.perm_append_comm_assoc f₂.coupons g₁.coupons _)
  | whiskerLeft_id => simp
  | id_whiskerRight => simp
  | α_hom_inv => simp
  | α_inv_hom => simp
  | associator_naturality => simp [List.append_assoc]
  | ρ_hom_inv => simp
  | ρ_inv_hom => simp
  | ρ_naturality => simp
  | l_hom_inv => simp
  | l_inv_hom => simp
  | l_naturality => simp
  | pentagon => simp
  | triangle => simp

/-- Two formal morphisms representing the same morphism in `S.FreeMonoidal` have permuted coupon
lists. -/
theorem coupons_perm_of_homMk_eq {X Y : S.FreeMonoidal} {f g : Hom X.as Y.as}
    (h : homMk f = homMk g) : f.coupons.Perm g.coupons :=
  HomEquiv.coupons_perm (Quotient.exact (s := setoidHom X.as Y.as) h)

/-- The number of coupons occurring in a morphism of `S.FreeMonoidal`. -/
def couponCount {X Y : S.FreeMonoidal} (f : X ⟶ Y) : ℕ :=
  Quotient.lift (fun r ↦ r.coupons.length) (fun _ _ h ↦ (HomEquiv.coupons_perm h).length_eq) f

@[simp]
theorem couponCount_homMk {X Y : S.FreeMonoidal} (f : Hom X.as Y.as) :
    couponCount (homMk f) = f.coupons.length :=
  (rfl)

@[simp]
theorem couponCount_id (X : S.FreeMonoidal) : couponCount (𝟙 X) = 0 := by
  rw [← homMk_id, couponCount_homMk, Hom.coupons_id, List.length_nil]

@[simp]
theorem couponCount_eqToHom {X Y : S.FreeMonoidal} (h : X = Y) : couponCount (eqToHom h) = 0 := by
  subst h
  simp

@[simp]
theorem couponCount_coupon (g : S.Coupon) : couponCount (coupon g) = 1 := by
  rw [← homMk_coupon, couponCount_homMk, Hom.coupons_coupon, List.length_singleton]

@[simp]
theorem couponCount_associator_hom (X Y Z : S.FreeMonoidal) :
    couponCount (α_ X Y Z).hom = 0 := by
  rw [← homMk_α_hom, couponCount_homMk, Hom.coupons_α_hom, List.length_nil]

@[simp]
theorem couponCount_associator_inv (X Y Z : S.FreeMonoidal) :
    couponCount (α_ X Y Z).inv = 0 := by
  rw [← homMk_α_inv, couponCount_homMk, Hom.coupons_α_inv, List.length_nil]

@[simp]
theorem couponCount_leftUnitor_hom (X : S.FreeMonoidal) :
    couponCount (λ_ X).hom = 0 := by
  rw [← homMk_l_hom, couponCount_homMk, Hom.coupons_l_hom, List.length_nil]

@[simp]
theorem couponCount_leftUnitor_inv (X : S.FreeMonoidal) :
    couponCount (λ_ X).inv = 0 := by
  rw [← homMk_l_inv, couponCount_homMk, Hom.coupons_l_inv, List.length_nil]

@[simp]
theorem couponCount_rightUnitor_hom (X : S.FreeMonoidal) :
    couponCount (ρ_ X).hom = 0 := by
  rw [← homMk_ρ_hom, couponCount_homMk, Hom.coupons_ρ_hom, List.length_nil]

@[simp]
theorem couponCount_rightUnitor_inv (X : S.FreeMonoidal) :
    couponCount (ρ_ X).inv = 0 := by
  rw [← homMk_ρ_inv, couponCount_homMk, Hom.coupons_ρ_inv, List.length_nil]

@[simp]
theorem couponCount_comp {X Y Z : S.FreeMonoidal} (f : X ⟶ Y) (g : Y ⟶ Z) :
    couponCount (f ≫ g) = couponCount f + couponCount g := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rw [← homMk_comp, couponCount_homMk, Hom.coupons_comp, List.length_append]
  rfl

@[simp]
theorem couponCount_whiskerLeft (X : S.FreeMonoidal) {Y Z : S.FreeMonoidal} (f : Y ⟶ Z) :
    couponCount (X ◁ f) = couponCount f := by
  induction f using Quotient.inductionOn
  rw [← homMk_whiskerLeft, couponCount_homMk, Hom.coupons_whiskerLeft]
  rfl

@[simp]
theorem couponCount_whiskerRight {X Y : S.FreeMonoidal} (f : X ⟶ Y) (Z : S.FreeMonoidal) :
    couponCount (f ▷ Z) = couponCount f := by
  induction f using Quotient.inductionOn
  rw [← homMk_whiskerRight, couponCount_homMk, Hom.coupons_whiskerRight]
  rfl

@[simp]
theorem couponCount_tensorHom {W X Y Z : S.FreeMonoidal} (f : W ⟶ Y) (g : X ⟶ Z) :
    couponCount (f ⊗ₘ g) = couponCount f + couponCount g := by
  induction f using Quotient.inductionOn
  induction g using Quotient.inductionOn
  rw [← homMk_tensor, couponCount_homMk, Hom.coupons_tensor, List.length_append]
  rfl

/-- A coupon in `S.FreeMonoidal` is never equal to an object-equality transport `eqToHom`,
in particular an endomorphism coupon is never equal to the identity morphism. -/
theorem coupon_ne_eqToHom (g : S.Coupon) (h : (⟨S.src g⟩ : S.FreeMonoidal) = ⟨S.tgt g⟩) :
    coupon g ≠ eqToHom h := by
  intro hg
  have hc := congrArg couponCount hg
  simp at hc

/-- Two coupons with matching source and target words determine equal morphisms in `S.FreeMonoidal`
(up to the canonical endpoint transports) if and only if they are the same coupon. -/
theorem coupon_eq_iff {g₁ g₂ : S.Coupon} (hsrc : S.src g₁ = S.src g₂)
    (htgt : S.tgt g₁ = S.tgt g₂) :
    coupon g₁ = eqToHom (congrArg FreeMonoidal.mk hsrc) ≫ coupon g₂ ≫
        eqToHom (congrArg FreeMonoidal.mk htgt.symm) ↔ g₁ = g₂ := by
  constructor
  · intro h
    have hcast : homMk (X := ⟨S.src g₁⟩) (Y := ⟨S.tgt g₁⟩) (Hom.coupon g₁) =
        homMk (X := ⟨S.src g₁⟩) (Y := ⟨S.tgt g₁⟩) ((Hom.coupon g₂).cast hsrc.symm htgt.symm) := by
      rw [homMk_coupon, homMk_cast, homMk_coupon, h]
    have hperm := coupons_perm_of_homMk_eq hcast
    simpa using hperm.mem_iff.mp (List.mem_singleton_self g₁)
  · rintro rfl
    simp

end TauCeti.TensorSignature.FreeMonoidal

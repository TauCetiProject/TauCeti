/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Braided.Basic

/-!
# Crossing-exponent sum and non-symmetry of the free braided monoidal category

For formal braided morphisms over a tensor signature `S`, `FreeBraided.Hom.exponentSum` weights
each positive crossing `β_hom X Y` by `+|X| * |Y|` (where `|X| = X.toList.length` is the number of
generating ports) and each negative crossing `β_inv X Y` by `-|X| * |Y|`, while identities,
associators, unitors, and coupons contribute `0`. Whenever all coupons occurring in a formal
morphism preserve port count, this integer invariant is preserved by all braided monoidal axioms:

* `FreeBraided.exponentSum`: the descended crossing-exponent sum on morphisms of `S.FreeBraided`
  when every coupon of `S` preserves port count, with `FreeBraided.length_toList_eq` and
  `FreeBraided.length_toList_eq_of_isEmpty`.
* `FreeBraided.braiding_comp_braiding_ne_id`: for arbitrary `S` (with no hypothesis on `S.Coupon`)
  and any `a b : S.Obj`, `(β_ (of a) (of b)).hom ≫ (β_ (of b) (of a)).hom ≠ 𝟙 (of a ⊗ of b)`.
-/

universe u v

open CategoryTheory MonoidalCategory BraidedCategory FreeMonoidalCategory

public section

namespace TauCeti.TensorSignature.FreeBraided

variable {S : TensorSignature.{u, v}}

/-- Raw crossing-exponent sum of a formal braided morphism: a positive crossing of `X` over `Y`
contributes `+|X| * |Y|`, a negative crossing contributes `-|X| * |Y|`, and monoidal structural
generators and coupons contribute `0`. -/
def Hom.exponentSum : ∀ {X Y : FreeMonoidalCategory S.Obj}, Hom X Y → ℤ
  | _, _, .id _ | _, _, .α_hom _ _ _ | _, _, .α_inv _ _ _ | _, _, .l_hom _ | _, _, .l_inv _
  | _, _, .ρ_hom _ | _, _, .ρ_inv _ | _, _, .coupon _ => 0
  | _, _, .β_hom X Y => (X.toList.length * Y.toList.length : ℕ)
  | _, _, .β_inv X Y => -((X.toList.length * Y.toList.length : ℕ) : ℤ)
  | _, _, .comp f g | _, _, .tensor f g => f.exponentSum + g.exponentSum
  | _, _, .whiskerLeft _ f | _, _, .whiskerRight f _ => f.exponentSum

@[simp] theorem Hom.exponentSum_id (X : FreeMonoidalCategory S.Obj) :
    (Hom.id X).exponentSum = 0 := (rfl)

@[simp] theorem Hom.exponentSum_β_hom (X Y : FreeMonoidalCategory S.Obj) :
    (Hom.β_hom X Y).exponentSum = (X.toList.length * Y.toList.length : ℕ) := (rfl)

@[simp] theorem Hom.exponentSum_β_inv (X Y : FreeMonoidalCategory S.Obj) :
    (Hom.β_inv X Y).exponentSum = -((X.toList.length * Y.toList.length : ℕ) : ℤ) := (rfl)

@[simp] theorem Hom.exponentSum_coupon (g : S.Coupon) : (Hom.coupon g).exponentSum = 0 := (rfl)

@[simp] theorem Hom.exponentSum_comp {X Y Z : FreeMonoidalCategory S.Obj}
    (f : Hom X Y) (g : Hom Y Z) : (f.comp g).exponentSum = f.exponentSum + g.exponentSum := (rfl)

@[simp] theorem Hom.exponentSum_whiskerLeft (X : FreeMonoidalCategory S.Obj)
    {Y Z : FreeMonoidalCategory S.Obj} (f : Hom Y Z) :
    (f.whiskerLeft X).exponentSum = f.exponentSum := (rfl)

@[simp] theorem Hom.exponentSum_whiskerRight {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y)
    (Z : FreeMonoidalCategory S.Obj) : (f.whiskerRight Z).exponentSum = f.exponentSum := (rfl)

@[simp] theorem Hom.exponentSum_tensor {W X Y Z : FreeMonoidalCategory S.Obj}
    (f : Hom W Y) (g : Hom X Z) :
    (f.tensor g).exponentSum = f.exponentSum + g.exponentSum := (rfl)

/-- Every coupon occurring in a formal braided morphism preserves port count. -/
private def Hom.CouponsPreserveLength : ∀ {X Y : FreeMonoidalCategory S.Obj}, Hom X Y → Prop
  | _, _, .id _ | _, _, .α_hom _ _ _ | _, _, .α_inv _ _ _ | _, _, .l_hom _ | _, _, .l_inv _
  | _, _, .ρ_hom _ | _, _, .ρ_inv _ | _, _, .β_hom _ _ | _, _, .β_inv _ _ => True
  | _, _, .coupon g => (S.src g).toList.length = (S.tgt g).toList.length
  | _, _, .comp f g | _, _, .tensor f g => f.CouponsPreserveLength ∧ g.CouponsPreserveLength
  | _, _, .whiskerLeft _ f | _, _, .whiskerRight f _ => f.CouponsPreserveLength

private theorem Hom.couponsPreserveLength_of_forall
    (hS : ∀ g : S.Coupon, (S.src g).toList.length = (S.tgt g).toList.length)
    {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) : f.CouponsPreserveLength := by
  induction f with
  | id | α_hom | α_inv | l_hom | l_inv | ρ_hom | ρ_inv | β_hom | β_inv => trivial
  | coupon g => exact hS g
  | comp _ _ hf hg | tensor _ _ hf hg => exact ⟨hf, hg⟩
  | whiskerLeft _ _ hf | whiskerRight _ _ hf => exact hf

private theorem Hom.length_toList_eq_of_couponsPreserveLength
    {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) (hf : f.CouponsPreserveLength) :
    X.toList.length = Y.toList.length := by
  induction f with
  | id => rfl
  | α_hom | α_inv | l_hom | l_inv | ρ_hom | ρ_inv => simp
  | β_hom | β_inv => simp [Nat.add_comm]
  | coupon => exact hf
  | comp _ _ ih₁ ih₂ => exact (ih₁ hf.1).trans (ih₂ hf.2)
  | whiskerLeft _ _ ih | whiskerRight _ _ ih => simp [ih hf]
  | tensor _ _ ih₁ ih₂ => simp [ih₁ hf.1, ih₂ hf.2]

private theorem HomEquiv.couponsPreserveLength_iff {X Y : FreeMonoidalCategory S.Obj}
    {f g : Hom X Y} (h : HomEquiv f g) : f.CouponsPreserveLength ↔ g.CouponsPreserveLength := by
  induction h with
  | refl | tensorHom_def => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂
  | whiskerLeft _ _ _ _ ih | whiskerRight _ _ _ _ ih => exact ih
  | assoc => exact and_assoc
  | tensorHom_comp_tensorHom => exact and_and_and_comm
  | comp_id | id_comp | id_tensorHom_id | whiskerLeft_id | id_whiskerRight
  | α_hom_inv | α_inv_hom | ρ_hom_inv | ρ_inv_hom | l_hom_inv | l_inv_hom
  | pentagon | triangle | β_hom_inv | β_inv_hom | hexagon_forward | hexagon_reverse =>
    simp [Hom.CouponsPreserveLength]
  | associator_naturality => simp only [Hom.CouponsPreserveLength, and_true, true_and, and_assoc]
  | ρ_naturality | l_naturality | braiding_naturality_right | braiding_naturality_left =>
    simp only [Hom.CouponsPreserveLength, and_true, true_and]

private theorem HomEquiv.exponentSum_eq_of_couponsPreserveLength
    {X Y : FreeMonoidalCategory S.Obj} {f g : Hom X Y}
    (h : HomEquiv f g) (hf : f.CouponsPreserveLength) : f.exponentSum = g.exponentSum := by
  induction h with
  | refl | tensorHom_def | id_tensorHom_id | whiskerLeft_id | id_whiskerRight
  | α_hom_inv | α_inv_hom | ρ_hom_inv | ρ_inv_hom | l_hom_inv | l_inv_hom
  | pentagon | triangle => rfl
  | symm _ _ h' ih => exact (ih ((HomEquiv.couponsPreserveLength_iff h').mpr hf)).symm
  | trans h₁ _ ih₁ ih₂ =>
    exact (ih₁ hf).trans (ih₂ ((HomEquiv.couponsPreserveLength_iff h₁).mp hf))
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ => exact congrArg₂ (· + ·) (ih₁ hf.1) (ih₂ hf.2)
  | whiskerLeft _ _ _ _ ih | whiskerRight _ _ _ _ ih => exact ih hf
  | comp_id | id_comp | assoc | tensorHom_comp_tensorHom | associator_naturality
  | ρ_naturality | l_naturality | β_hom_inv | β_inv_hom => dsimp [Hom.exponentSum]; omega
  | braiding_naturality_right _ f' | braiding_naturality_left f' _ =>
    dsimp [Hom.exponentSum]; rw [Hom.length_toList_eq_of_couponsPreserveLength f' hf.1]; omega
  | hexagon_forward =>
    simp only [Hom.exponentSum, tensor_eq_tensor, toList_tensor, List.length_append, Nat.mul_add]
    omega
  | hexagon_reverse =>
    simp only [Hom.exponentSum, tensor_eq_tensor, toList_tensor, List.length_append, Nat.add_mul]
    omega

section LengthPreservingCoupons

variable (hS : ∀ g : S.Coupon, (S.src g).toList.length = (S.tgt g).toList.length)

include hS in
/-- When every coupon preserves port count, every formal braided morphism preserves port count. -/
theorem Hom.length_toList_eq {X Y : FreeMonoidalCategory S.Obj} (f : Hom X Y) :
    X.toList.length = Y.toList.length :=
  Hom.length_toList_eq_of_couponsPreserveLength f (Hom.couponsPreserveLength_of_forall hS f)

include hS in
/-- When every coupon preserves port count, morphisms in `S.FreeBraided` exist only between tensor
words of equal port count. -/
theorem length_toList_eq {X Y : S.FreeBraided} (f : X ⟶ Y) :
    X.as.toList.length = Y.as.toList.length := by
  rcases f with ⟨f⟩; exact Hom.length_toList_eq hS f

include hS in
/-- When every coupon preserves port count, `Hom.exponentSum` is invariant under `HomEquiv`. -/
theorem HomEquiv.exponentSum_eq {X Y : FreeMonoidalCategory S.Obj} {f g : Hom X Y}
    (h : HomEquiv f g) : f.exponentSum = g.exponentSum :=
  HomEquiv.exponentSum_eq_of_couponsPreserveLength h (Hom.couponsPreserveLength_of_forall hS f)

/-- The crossing-exponent sum of a morphism in `S.FreeBraided`, defined when every coupon preserves
port count (in particular, vacuously when `S` has no coupons). -/
def exponentSum {X Y : S.FreeBraided} (f : X ⟶ Y) : ℤ :=
  Quotient.lift Hom.exponentSum (fun _ _ h ↦ HomEquiv.exponentSum_eq hS h) f

@[simp] theorem exponentSum_homMk {X Y : S.FreeBraided} (f : Hom X.as Y.as) :
    exponentSum hS (homMk f) = f.exponentSum := (rfl)

@[simp] theorem exponentSum_id (X : S.FreeBraided) : exponentSum hS (𝟙 X) = 0 := (rfl)

@[simp] theorem exponentSum_comp {X Y Z : S.FreeBraided} (f : X ⟶ Y) (g : Y ⟶ Z) :
    exponentSum hS (f ≫ g) = exponentSum hS f + exponentSum hS g :=
  Quotient.ind₂ (fun _ _ ↦ rfl) f g

@[simp] theorem exponentSum_whiskerLeft (X : S.FreeBraided) {Y Z : S.FreeBraided} (f : Y ⟶ Z) :
    exponentSum hS (X ◁ f) = exponentSum hS f := by rcases f with ⟨f⟩; rfl

@[simp] theorem exponentSum_whiskerRight {X Y : S.FreeBraided} (f : X ⟶ Y) (Z : S.FreeBraided) :
    exponentSum hS (f ▷ Z) = exponentSum hS f := by rcases f with ⟨f⟩; rfl

@[simp] theorem exponentSum_tensorHom {W X Y Z : S.FreeBraided} (f : W ⟶ Y) (g : X ⟶ Z) :
    exponentSum hS (f ⊗ₘ g) = exponentSum hS f + exponentSum hS g :=
  Quotient.ind₂ (fun _ _ ↦ rfl) f g

@[simp] theorem exponentSum_braiding_hom (X Y : S.FreeBraided) :
    exponentSum hS (β_ X Y).hom = (X.as.toList.length * Y.as.toList.length : ℕ) := (rfl)

@[simp] theorem exponentSum_braiding_inv (X Y : S.FreeBraided) :
    exponentSum hS (β_ X Y).inv = -((X.as.toList.length * Y.as.toList.length : ℕ) : ℤ) := (rfl)

@[simp] theorem exponentSum_coupon (g : S.Coupon) : exponentSum hS (coupon g) = 0 := (rfl)

end LengthPreservingCoupons

/-- In the coupon-free case, morphisms in `S.FreeBraided` exist only between tensor words of equal
strand count. -/
theorem length_toList_eq_of_isEmpty [IsEmpty S.Coupon] {X Y : S.FreeBraided} (f : X ⟶ Y) :
    X.as.toList.length = Y.as.toList.length :=
  length_toList_eq (fun g ↦ isEmptyElim g) f

/-- For any tensor signature `S` (regardless of its coupons) and any generating objects
`a b : S.Obj`, `(β_ (of a) (of b)).hom ≫ (β_ (of b) (of a)).hom ≠ 𝟙 (of a ⊗ of b)`. -/
theorem braiding_comp_braiding_ne_id (a b : S.Obj) :
    (β_ (of a) (of b)).hom ≫ (β_ (of b) (of a)).hom ≠ 𝟙 (of a ⊗ of b) := fun h ↦ by
  have hexp := HomEquiv.exponentSum_eq_of_couponsPreserveLength
    (Quotient.exact h) ⟨trivial, trivial⟩
  simp [Hom.exponentSum, of] at hexp

end TauCeti.TensorSignature.FreeBraided

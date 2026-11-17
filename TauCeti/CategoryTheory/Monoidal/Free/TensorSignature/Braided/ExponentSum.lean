/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.TensorSignature.Braided.Basic
import Mathlib.Algebra.Group.Int.TypeTags

/-!
# Word weights and crossing-and-coupon exponent sums on free braided categories

This file develops additive word weights and the weighted crossing-and-coupon exponent sum on the
free braided monoidal category `TauCeti.TensorSignature.FreeBraided S`.

Given an integer weight `w : S.Obj → ℤ`, `FreeBraided.wordWeight w` extends `w` additively to all
formal tensor words via `FreeMonoidalCategory.projectObj` into the discrete braided monoidal
category `Discrete (Multiplicative ℤ)`. Whenever every coupon preserves `wordWeight w`,
`FreeBraided.lift` into `Discrete (Multiplicative ℤ)` shows that every morphism preserves
`wordWeight w` (`FreeBraided.wordWeight_eq_of_hom`).

Likewise, lifting `S.FreeBraided` into a braided monoidal category of integer weights equipped with
an additive integer crossing exponent and an absorbing zero morphism yields both:
* `FreeBraided.exponentSum w fc hw`: the weighted crossing-and-coupon exponent sum on morphisms
  when every coupon preserves `wordWeight w`;
* `FreeBraided.braiding_comp_braiding_ne_id` and `FreeBraided.braiding_hom_ne_id`: for **every**
  tensor signature `S` (with or without coupons), double crossings and self-crossings on generating
  objects are distinct from the identity, witnessing that `S.FreeBraided` is genuinely braided and
  not symmetric.

## Main definitions and results

* `TauCeti.TensorSignature.FreeBraided.wordWeight` and `FreeBraided.wordWeight_eq_of_hom`:
  additive word weights and their invariance under morphisms when coupons preserve weight.
* `TauCeti.TensorSignature.FreeBraided.exponentSum`: the weighted crossing-and-coupon invariant on
  morphisms of `S.FreeBraided`, together with computation rules on identities, composites,
  whiskerings, tensor products, structural isomorphisms and coupons.
* `FreeBraided.braiding_comp_braiding_ne_id` and `FreeBraided.braiding_hom_ne_id`: double
  crossings `(β_ (of a) (of b)).hom ≫ (β_ (of b) (of a)).hom` and self-crossings
  `(β_ (of a) (of a)).hom` are distinct from the identity on any tensor signature `S`.
* `FreeBraided.coupon_ne_eqToHom`: every endomorphism coupon is distinct from the identity morphism
  on its boundary word.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §3.
* P. Selinger, *A survey of graphical languages for monoidal categories*, New Structures for
  Physics, Lecture Notes in Phys. 813 (2011), §3.3.
-/

public section

universe u v

open CategoryTheory MonoidalCategory BraidedCategory FreeMonoidalCategory

namespace TauCeti.TensorSignature.FreeBraided

variable {S : TensorSignature.{u, v}}

/-- Additive weight of a formal tensor word in `S.FreeBraided` induced by an integer weight `w` on
the generating objects: the unit has weight `0` and tensor products add weights. For `w = 1`, this
is the strand count of the boundary word. -/
def wordWeight (w : S.Obj → ℤ) (X : S.FreeBraided) : ℤ :=
  (projectObj (fun a ↦ Discrete.mk (Multiplicative.ofAdd (w a))) X.as).as.toAdd

/-- The weight of a generating object `of a` is `w a`. -/
@[simp]
theorem wordWeight_of (w : S.Obj → ℤ) (a : S.Obj) : wordWeight w (of a) = w a := (rfl)

/-- The weight of the tensor unit is `0`. -/
@[simp]
theorem wordWeight_tensorUnit (w : S.Obj → ℤ) : wordWeight w (𝟙_ S.FreeBraided) = 0 := (rfl)

/-- The weight of a tensor product is the sum of the weights of the factors. -/
@[simp]
theorem wordWeight_tensor (w : S.Obj → ℤ) (X Y : S.FreeBraided) :
    wordWeight w (X ⊗ Y) = wordWeight w X + wordWeight w Y := (rfl)

/-- Under the zero object weight, every formal tensor word has weight `0`. -/
@[simp]
theorem wordWeight_zero (X : S.FreeBraided) : wordWeight (fun _ ↦ 0) X = 0 := by
  rcases X with ⟨X⟩
  induction X with
  | of => rfl
  | unit => rfl
  | tensor X Y hX hY => exact (wordWeight_tensor _ ⟨X⟩ ⟨Y⟩).trans (by rw [hX, hY]; rfl)

/-- When every coupon preserves `wordWeight w`, every morphism of `S.FreeBraided` preserves
`wordWeight w`. In particular, on a coupon-free signature there are no morphisms between words of
different strand counts. -/
theorem wordWeight_eq_of_hom {w : S.Obj → ℤ}
    (hw : ∀ g : S.Coupon, wordWeight w ⟨S.src g⟩ = wordWeight w ⟨S.tgt g⟩)
    {X Y : S.FreeBraided} (f : X ⟶ Y) :
    wordWeight w X = wordWeight w Y :=
  congrArg Multiplicative.toAdd <| Discrete.eq_of_hom <|
    (lift (D := Discrete (Multiplicative ℤ))
      (fun a ↦ Discrete.mk (Multiplicative.ofAdd (w a))) fun g ↦
        Discrete.eqToHom (Multiplicative.toAdd.injective (hw g))).map f

section WeightedModel

/-- Objects of the auxiliary braided monoidal category of integer weights and crossing exponents. -/
private structure WeightedObj where
  val : ℤ

/-- Morphisms between integer weights: either an absorbing `zero` morphism between arbitrary
weights, or a non-zero morphism `of h exp` between equal weights carrying an additive integer
exponent `exp`. -/
private inductive WeightedHom (X Y : WeightedObj) : Type
  | zero
  | of (h : X.val = Y.val) (exp : ℤ)

private def WeightedHom.exp {X Y : WeightedObj} : WeightedHom X Y → ℤ
  | .zero => 0
  | .of _ e => e

private noncomputable instance : Category.{0} WeightedObj where
  Hom := WeightedHom
  id _ := .of rfl 0
  comp
    | .of h₁ e₁, .of h₂ e₂ => .of (h₁.trans h₂) (e₁ + e₂)
    | _, _ => .zero
  id_comp := by
    rintro _ _ (_ | ⟨h, e⟩)
    · rfl
    · simp
  comp_id := by
    rintro _ _ (_ | ⟨h, e⟩)
    · rfl
    · simp
  assoc := by
    rintro _ _ _ _ (_ | ⟨_, _⟩) (_ | ⟨_, _⟩) (_ | ⟨_, _⟩) <;> try rfl
    simp [Int.add_assoc]

private noncomputable instance : MonoidalCategory WeightedObj where
  tensorObj X Y := ⟨X.val + Y.val⟩
  tensorUnit := ⟨0⟩
  whiskerLeft X _ _
    | .of h e => .of (congrArg (X.val + ·) h) e
    | .zero => .zero
  whiskerRight
    | .of h e, Y => .of (congrArg (· + Y.val) h) e
    | .zero, _ => .zero
  tensorHom
    | .of h₁ e₁, .of h₂ e₂ => .of (congrArg₂ (· + ·) h₁ h₂) (e₁ + e₂)
    | _, _ => .zero
  associator X Y Z :=
    ⟨.of (Int.add_assoc X.val Y.val Z.val) 0, .of (Int.add_assoc X.val Y.val Z.val).symm 0,
      rfl, rfl⟩
  leftUnitor X :=
    ⟨.of (Int.zero_add X.val) 0, .of (Int.zero_add X.val).symm 0, rfl, rfl⟩
  rightUnitor X :=
    ⟨.of (Int.add_zero X.val) 0, .of (Int.add_zero X.val).symm 0, rfl, rfl⟩
  tensorHom_def := by
    rintro _ _ _ _ (_ | ⟨_, _⟩) (_ | ⟨_, _⟩) <;> rfl
  id_tensorHom_id _ _ := rfl
  tensorHom_comp_tensorHom := by
    rintro _ _ _ _ _ _ (_ | ⟨_, _⟩) (_ | ⟨_, _⟩) (_ | ⟨_, _⟩) (_ | ⟨_, _⟩) <;> try rfl
    exact congrArg (WeightedHom.of _) (by omega)
  whiskerLeft_id _ _ := rfl
  id_whiskerRight _ _ := rfl
  associator_naturality := by
    rintro _ _ _ _ _ _ (_ | ⟨_, _⟩) (_ | ⟨_, _⟩) (_ | ⟨_, _⟩) <;> try rfl
    exact congrArg (WeightedHom.of _) (by omega)
  leftUnitor_naturality := by
    rintro _ _ (_ | ⟨_, _⟩) <;> try rfl
    exact congrArg (WeightedHom.of _) (by omega)
  rightUnitor_naturality := by
    rintro _ _ (_ | ⟨_, _⟩) <;> try rfl
    exact congrArg (WeightedHom.of _) (by omega)
  pentagon _ _ _ _ := rfl
  triangle _ _ := rfl

private theorem weightedObj_tensor_val (X Y : WeightedObj) : (X ⊗ Y).val = X.val + Y.val := rfl

private theorem weightedHom_comp_of {X Y Z : WeightedObj}
    (h₁ : X.val = Y.val) (e₁ : ℤ) (h₂ : Y.val = Z.val) (e₂ : ℤ) :
    (WeightedHom.of (X := X) (Y := Y) h₁ e₁ ≫
      WeightedHom.of (X := Y) (Y := Z) h₂ e₂ : X ⟶ Z) =
      WeightedHom.of (h₁.trans h₂) (e₁ + e₂) := rfl

private theorem weightedHom_whiskerLeft_of (X : WeightedObj) {Y Z : WeightedObj}
    (h : Y.val = Z.val) (e : ℤ) :
    (X ◁ (WeightedHom.of h e : Y ⟶ Z)) = WeightedHom.of (congrArg (X.val + ·) h) e := rfl

private theorem weightedHom_whiskerRight_of {X Y : WeightedObj}
    (h : X.val = Y.val) (e : ℤ) (Z : WeightedObj) :
    ((WeightedHom.of h e : X ⟶ Y) ▷ Z) = WeightedHom.of (congrArg (· + Z.val) h) e := rfl

private theorem weightedHom_associator_hom (X Y Z : WeightedObj) :
    (α_ X Y Z).hom = WeightedHom.of (Int.add_assoc X.val Y.val Z.val) 0 := rfl

private theorem weightedHom_associator_inv (X Y Z : WeightedObj) :
    (α_ X Y Z).inv = WeightedHom.of (Int.add_assoc X.val Y.val Z.val).symm 0 := rfl

private noncomputable instance : BraidedCategory WeightedObj where
  braiding X Y :=
    ⟨.of (Int.add_comm X.val Y.val) (X.val * Y.val),
      .of (Int.add_comm Y.val X.val) (-(X.val * Y.val)),
      congrArg (WeightedHom.of _) (by omega),
      congrArg (WeightedHom.of _) (by omega)⟩
  braiding_naturality_right _ _ _ := by
    rintro (_ | ⟨h, _⟩)
    · rfl
    · exact congrArg (WeightedHom.of _) (by rw [h]; omega)
  braiding_naturality_left := by
    rintro _ _ (_ | ⟨h, _⟩) _
    · rfl
    · exact congrArg (WeightedHom.of _) (by rw [h]; omega)
  hexagon_forward X Y Z := by
    simp only [weightedHom_associator_hom, weightedHom_whiskerLeft_of, weightedHom_whiskerRight_of,
      weightedHom_comp_of, weightedObj_tensor_val]
    exact congrArg (WeightedHom.of _) (by rw [Int.mul_add]; omega)
  hexagon_reverse X Y Z := by
    simp only [weightedHom_associator_inv, weightedHom_whiskerLeft_of, weightedHom_whiskerRight_of,
      weightedHom_comp_of, weightedObj_tensor_val]
    exact congrArg (WeightedHom.of _) (by rw [Int.add_mul]; omega)

private theorem weightedObj_projectObj (w : S.Obj → ℤ) (X : FreeMonoidalCategory S.Obj) :
    (projectObj (fun a ↦ (⟨w a⟩ : WeightedObj)) X).val = wordWeight w ⟨X⟩ := by
  induction X with
  | of a => rfl
  | unit => rfl
  | tensor X Y hX hY =>
    simp only [projectObj, weightedObj_tensor_val, hX, hY]
    exact (wordWeight_tensor w ⟨X⟩ ⟨Y⟩).symm

private noncomputable def exponentFunctor (w : S.Obj → ℤ) (fc : S.Coupon → ℤ)
    (hw : ∀ g : S.Coupon, wordWeight w ⟨S.src g⟩ = wordWeight w ⟨S.tgt g⟩) :
    S.FreeBraided ⥤ WeightedObj :=
  lift (fun a ↦ ⟨w a⟩) fun g ↦
    WeightedHom.of
      ((weightedObj_projectObj w (S.src g)).trans
        ((hw g).trans (weightedObj_projectObj w (S.tgt g)).symm))
      (fc g)

private theorem exponentFunctor_map_whiskerLeft (w : S.Obj → ℤ) (fc : S.Coupon → ℤ)
    (hw : ∀ g : S.Coupon, wordWeight w ⟨S.src g⟩ = wordWeight w ⟨S.tgt g⟩)
    (X : S.FreeBraided) {Y Z : S.FreeBraided} (f : Y ⟶ Z) :
    (exponentFunctor w fc hw).map (X ◁ f) =
      (exponentFunctor w fc hw).obj X ◁ (exponentFunctor w fc hw).map f :=
  lift_map_whiskerLeft _ _ X f

private theorem exponentFunctor_map_whiskerRight (w : S.Obj → ℤ) (fc : S.Coupon → ℤ)
    (hw : ∀ g : S.Coupon, wordWeight w ⟨S.src g⟩ = wordWeight w ⟨S.tgt g⟩)
    {X Y : S.FreeBraided} (f : X ⟶ Y) (Z : S.FreeBraided) :
    (exponentFunctor w fc hw).map (f ▷ Z) =
      (exponentFunctor w fc hw).map f ▷ (exponentFunctor w fc hw).obj Z :=
  lift_map_whiskerRight _ _ f Z

/-- Weighted crossing-and-coupon exponent sum of a morphism in `S.FreeBraided`. When every coupon
preserves `wordWeight w`, each positive braiding `(β_ X Y).hom` contributes
`wordWeight w X * wordWeight w Y`, its inverse contributes the negation, each coupon `g`
contributes `fc g`, and identities, associators and unitors contribute `0`. -/
noncomputable def exponentSum (w : S.Obj → ℤ) (fc : S.Coupon → ℤ)
    (hw : ∀ g : S.Coupon, wordWeight w ⟨S.src g⟩ = wordWeight w ⟨S.tgt g⟩)
    {X Y : S.FreeBraided} (f : X ⟶ Y) : ℤ :=
  ((exponentFunctor w fc hw).map f).exp

private theorem exponentFunctor_map_eq_of (w : S.Obj → ℤ) (fc : S.Coupon → ℤ)
    (hw : ∀ g : S.Coupon, wordWeight w ⟨S.src g⟩ = wordWeight w ⟨S.tgt g⟩)
    {X Y : S.FreeBraided} (f : X ⟶ Y) :
    ∃ h, (exponentFunctor w fc hw).map f = .of h (exponentSum w fc hw f) := by
  induction f using Hom.inductionOn with
  | id X => exact ⟨rfl, by simp only [exponentSum, Functor.map_id]; rfl⟩
  | α_hom X Y Z =>
    exact ⟨_, by simp only [exponentSum, exponentFunctor, lift_map_associator_hom]; rfl⟩
  | α_inv X Y Z =>
    exact ⟨_, by simp only [exponentSum, exponentFunctor, lift_map_associator_inv]; rfl⟩
  | l_hom X =>
    exact ⟨_, by simp only [exponentSum, exponentFunctor, lift_map_leftUnitor_hom]; rfl⟩
  | l_inv X =>
    exact ⟨_, by simp only [exponentSum, exponentFunctor, lift_map_leftUnitor_inv]; rfl⟩
  | ρ_hom X =>
    exact ⟨_, by simp only [exponentSum, exponentFunctor, lift_map_rightUnitor_hom]; rfl⟩
  | ρ_inv X =>
    exact ⟨_, by simp only [exponentSum, exponentFunctor, lift_map_rightUnitor_inv]; rfl⟩
  | β_hom X Y =>
    exact ⟨_, by simp only [exponentSum, exponentFunctor, lift_map_braiding_hom]; rfl⟩
  | β_inv X Y =>
    exact ⟨_, by simp only [exponentSum, exponentFunctor, lift_map_braiding_inv]; rfl⟩
  | coupon g =>
    exact ⟨_, by simp only [exponentSum, exponentFunctor, lift_map_coupon]; rfl⟩
  | comp f g hf hg =>
    obtain ⟨h₁, hf⟩ := hf
    obtain ⟨h₂, hg⟩ := hg
    refine ⟨h₁.trans h₂, ?_⟩
    dsimp only [exponentSum]
    rw [Functor.map_comp, hf, hg, weightedHom_comp_of]
    rfl
  | whiskerLeft X f hf =>
    obtain ⟨h, hf⟩ := hf
    refine ⟨congrArg (((exponentFunctor w fc hw).obj X).val + ·) h, ?_⟩
    dsimp only [exponentSum]
    rw [exponentFunctor_map_whiskerLeft, hf, weightedHom_whiskerLeft_of]
    rfl
  | whiskerRight f Z hf =>
    obtain ⟨h, hf⟩ := hf
    refine ⟨congrArg (· + ((exponentFunctor w fc hw).obj Z).val) h, ?_⟩
    dsimp only [exponentSum]
    rw [exponentFunctor_map_whiskerRight, hf, weightedHom_whiskerRight_of]
    rfl

section ExponentSumLemmas

variable (w : S.Obj → ℤ) (fc : S.Coupon → ℤ)
  (hw : ∀ g : S.Coupon, wordWeight w ⟨S.src g⟩ = wordWeight w ⟨S.tgt g⟩)

/-- Identity morphisms have exponent sum `0`. -/
@[simp]
theorem exponentSum_id (X : S.FreeBraided) : exponentSum w fc hw (𝟙 X) = 0 := by
  simp only [exponentSum, Functor.map_id]
  rfl

/-- Exponent sum is additive under composition. -/
@[simp]
theorem exponentSum_comp {X Y Z : S.FreeBraided} (f : X ⟶ Y) (g : Y ⟶ Z) :
    exponentSum w fc hw (f ≫ g) = exponentSum w fc hw f + exponentSum w fc hw g := by
  obtain ⟨_, hf⟩ := exponentFunctor_map_eq_of w fc hw f
  obtain ⟨_, hg⟩ := exponentFunctor_map_eq_of w fc hw g
  rw [exponentSum, Functor.map_comp, hf, hg, weightedHom_comp_of]
  rfl

/-- Left whiskering preserves the exponent sum. -/
@[simp]
theorem exponentSum_whiskerLeft (X : S.FreeBraided) {Y Z : S.FreeBraided} (f : Y ⟶ Z) :
    exponentSum w fc hw (X ◁ f) = exponentSum w fc hw f := by
  obtain ⟨_, hf⟩ := exponentFunctor_map_eq_of w fc hw f
  rw [exponentSum, exponentFunctor_map_whiskerLeft, hf, weightedHom_whiskerLeft_of]
  rfl

/-- Right whiskering preserves the exponent sum. -/
@[simp]
theorem exponentSum_whiskerRight {X Y : S.FreeBraided} (f : X ⟶ Y) (Z : S.FreeBraided) :
    exponentSum w fc hw (f ▷ Z) = exponentSum w fc hw f := by
  obtain ⟨_, hf⟩ := exponentFunctor_map_eq_of w fc hw f
  rw [exponentSum, exponentFunctor_map_whiskerRight, hf, weightedHom_whiskerRight_of]
  rfl

/-- Exponent sum is additive under tensor products of morphisms. -/
@[simp]
theorem exponentSum_tensorHom {W X Y Z : S.FreeBraided} (f : W ⟶ X) (g : Y ⟶ Z) :
    exponentSum w fc hw (f ⊗ₘ g) = exponentSum w fc hw f + exponentSum w fc hw g := by
  rw [tensorHom_def, exponentSum_comp, exponentSum_whiskerRight, exponentSum_whiskerLeft]

/-- Forward associators have exponent sum `0`. -/
@[simp]
theorem exponentSum_associator_hom (X Y Z : S.FreeBraided) :
    exponentSum w fc hw (α_ X Y Z).hom = 0 := by
  simp only [exponentSum, exponentFunctor, lift_map_associator_hom]
  rfl

/-- Inverse associators have exponent sum `0`. -/
@[simp]
theorem exponentSum_associator_inv (X Y Z : S.FreeBraided) :
    exponentSum w fc hw (α_ X Y Z).inv = 0 := by
  simp only [exponentSum, exponentFunctor, lift_map_associator_inv]
  rfl

/-- Forward left unitors have exponent sum `0`. -/
@[simp]
theorem exponentSum_leftUnitor_hom (X : S.FreeBraided) :
    exponentSum w fc hw (λ_ X).hom = 0 := by
  simp only [exponentSum, exponentFunctor, lift_map_leftUnitor_hom]
  rfl

/-- Inverse left unitors have exponent sum `0`. -/
@[simp]
theorem exponentSum_leftUnitor_inv (X : S.FreeBraided) :
    exponentSum w fc hw (λ_ X).inv = 0 := by
  simp only [exponentSum, exponentFunctor, lift_map_leftUnitor_inv]
  rfl

/-- Forward right unitors have exponent sum `0`. -/
@[simp]
theorem exponentSum_rightUnitor_hom (X : S.FreeBraided) :
    exponentSum w fc hw (ρ_ X).hom = 0 := by
  simp only [exponentSum, exponentFunctor, lift_map_rightUnitor_hom]
  rfl

/-- Inverse right unitors have exponent sum `0`. -/
@[simp]
theorem exponentSum_rightUnitor_inv (X : S.FreeBraided) :
    exponentSum w fc hw (ρ_ X).inv = 0 := by
  simp only [exponentSum, exponentFunctor, lift_map_rightUnitor_inv]
  rfl

/-- A positive braiding `(β_ X Y).hom` has exponent sum `wordWeight w X * wordWeight w Y`. -/
@[simp]
theorem exponentSum_braiding_hom (X Y : S.FreeBraided) :
    exponentSum w fc hw (β_ X Y).hom = wordWeight w X * wordWeight w Y := by
  simp only [exponentSum, exponentFunctor, lift_map_braiding_hom]
  exact congrArg₂ (· * ·) (weightedObj_projectObj w X.as) (weightedObj_projectObj w Y.as)

/-- An inverse braiding `(β_ X Y).inv` has exponent sum `-(wordWeight w X * wordWeight w Y)`. -/
@[simp]
theorem exponentSum_braiding_inv (X Y : S.FreeBraided) :
    exponentSum w fc hw (β_ X Y).inv = -(wordWeight w X * wordWeight w Y) := by
  simp only [exponentSum, exponentFunctor, lift_map_braiding_inv]
  exact congrArg Neg.neg
    (congrArg₂ (· * ·) (weightedObj_projectObj w X.as) (weightedObj_projectObj w Y.as))

/-- A coupon `g` has exponent sum `fc g`. -/
@[simp]
theorem exponentSum_coupon (g : S.Coupon) :
    exponentSum w fc hw (coupon g) = fc g := by
  simp only [exponentSum, exponentFunctor, lift_map_coupon]
  rfl

/-- `eqToHom` morphisms have exponent sum `0`. -/
@[simp]
theorem exponentSum_eqToHom {X Y : S.FreeBraided} (h : X = Y) :
    exponentSum w fc hw (eqToHom h) = 0 := by
  cases h
  simp

end ExponentSumLemmas

/-- On any tensor signature `S`, the double crossing
`(β_ (of a) (of b)).hom ≫ (β_ (of b) (of a)).hom` is distinct from the identity:
`S.FreeBraided` does not satisfy the symmetry equation. -/
theorem braiding_comp_braiding_ne_id (a b : S.Obj) :
    (β_ (of a) (of b)).hom ≫ (β_ (of b) (of a)).hom ≠ 𝟙 (of a ⊗ of b) := by
  intro h
  have hexp := congrArg (fun f ↦
    ((lift (fun _ ↦ (⟨1⟩ : WeightedObj)) (fun _ ↦ WeightedHom.zero)).map f).exp) h
  simp only [Functor.map_comp, Functor.map_id, lift_map_braiding_hom, lift_obj_tensor,
    lift_obj_of] at hexp
  exact absurd hexp (by decide)

/-- On any tensor signature `S`, a self-crossing `(β_ (of a) (of a)).hom` is distinct from the
identity. -/
theorem braiding_hom_ne_id (a : S.Obj) :
    (β_ (of a) (of a)).hom ≠ 𝟙 (of a ⊗ of a) :=
  fun h ↦ braiding_comp_braiding_ne_id a a (by rw [h, Category.comp_id])

/-- Every endomorphism coupon in `S.FreeBraided` is distinct from the identity morphism on its
boundary word. -/
theorem coupon_ne_eqToHom (g : S.Coupon) (h : S.src g = S.tgt g) :
    coupon g ≠ eqToHom (congrArg FreeBraided.mk h) := by
  classical
  intro hEq
  have hexp := congrArg
    (exponentSum (fun _ ↦ 0) (fun c ↦ if c = g then 1 else 0) (fun _ ↦ by simp)) hEq
  simp at hexp

end WeightedModel

end TauCeti.TensorSignature.FreeBraided

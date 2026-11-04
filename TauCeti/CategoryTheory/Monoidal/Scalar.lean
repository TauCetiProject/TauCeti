/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.CategoryTheory.Preadditive.Schur

/-!
# Scalars in a monoidal category

A *scalar* in a monoidal category `C` is an endomorphism `a : 𝟙_ C ⟶ 𝟙_ C` of the unit. Whiskering
an object by a scalar is compatible with every morphism to or from the unit: a scalar acting on
the unit factor of `Y ⊗ 𝟙_ C` can be moved past any morphism `Y ⊗ 𝟙_ C ⟶ 𝟙_ C`
(`TauCeti.whiskerLeft_scalar_comp`), and dually a scalar acting on the unit factor of `𝟙_ C ⊗ Y`
can be moved past any morphism `𝟙_ C ⟶ 𝟙_ C ⊗ Y` (`TauCeti.comp_scalar_whiskerRight`). In
particular scalars commute with each other (`TauCeti.scalar_comm`).

A scalar `a` acts on every object `Y` in two ways, from the left as
`(λ_ Y).inv ≫ a ▷ Y ≫ (λ_ Y).hom` and from the right as `(ρ_ Y).inv ≫ Y ◁ a ≫ (ρ_ Y).hom`. The two
actions need not agree in a general monoidal category, but they do in a braided one
(`TauCeti.leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom`). They also agree in a linear one
over an algebraically closed field whose unit is simple with finite-dimensional endomorphisms,
where every scalar is a multiple of the identity
(`TauCeti.leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_simple`).

`TauCeti.CirclesCommuteAt d X` records agreement of the two actions of a particular scalar `d`
on a particular object `X`. These objects form a replete monoidal full subcategory: agreement
holds at the unit, is preserved by isomorphisms, and is closed under tensor products. Thus a
circle value central on a generating object is central on every interpreted tensor word in that
object, without requiring it to be central on every object of the ambient category. Agreement is
also closed under composition of scalars, so any finite number of such circles can be moved
between the two sides.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §2.2.
-/

public section

open CategoryTheory MonoidalCategory

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A scalar acting on the unit factor of `Y ⊗ 𝟙_ C` can be moved past any morphism to the unit:
`Y ◁ a ≫ e = e ≫ a`. -/
@[reassoc]
theorem whiskerLeft_scalar_comp {Y : C} (a : 𝟙_ C ⟶ 𝟙_ C) (e : Y ⊗ 𝟙_ C ⟶ 𝟙_ C) :
    Y ◁ a ≫ e = e ≫ a := by
  -- On the unit, `a` is conjugate to `𝟙_ C ◁ a` by the right unitor, which commutes with `Y ◁ a`.
  have ha : a = (ρ_ (𝟙_ C)).inv ≫ 𝟙_ C ◁ a ≫ (ρ_ (𝟙_ C)).hom := by
    rw [← unitors_equal, ← unitors_inv_equal, leftUnitor_naturality, Iso.inv_hom_id_assoc]
  conv_rhs => rw [ha, rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]
  simp

/-- A scalar acting on the unit factor of `𝟙_ C ⊗ Y` can be moved past any morphism from the
unit: `e ≫ a ▷ Y = a ≫ e`. -/
@[reassoc]
theorem comp_scalar_whiskerRight {Y : C} (a : 𝟙_ C ⟶ 𝟙_ C) (e : 𝟙_ C ⟶ 𝟙_ C ⊗ Y) :
    e ≫ a ▷ Y = a ≫ e := by
  -- On the unit, `a` is conjugate to `a ▷ 𝟙_ C` by the left unitor, which commutes with `a ▷ Y`.
  have ha : a = (λ_ (𝟙_ C)).inv ≫ a ▷ 𝟙_ C ≫ (λ_ (𝟙_ C)).hom := by
    rw [unitors_equal, unitors_inv_equal, rightUnitor_naturality, Iso.inv_hom_id_assoc]
  conv_rhs => rw [ha, Category.assoc, Category.assoc, ← leftUnitor_naturality,
    ← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  simp

/-- **Scalars commute**: the endomorphisms of the unit form a commutative monoid. -/
theorem scalar_comm (a b : 𝟙_ C ⟶ 𝟙_ C) : a ≫ b = b ≫ a := by
  rw [← cancel_epi (λ_ (𝟙_ C)).hom, ← leftUnitor_naturality_assoc, unitors_equal,
    whiskerLeft_scalar_comp, Category.assoc]

/-- In a braided monoidal category, a scalar acts on every object in the same way from the left
and from the right. -/
theorem leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom [BraidedCategory C]
    (a : 𝟙_ C ⟶ 𝟙_ C) (Y : C) :
    (λ_ Y).inv ≫ a ▷ Y ≫ (λ_ Y).hom = (ρ_ Y).inv ≫ Y ◁ a ≫ (ρ_ Y).hom := by
  -- The braiding `𝟙_ C ⊗ Y ≅ Y ⊗ 𝟙_ C` is natural and identifies the two unitors.
  rw [← braiding_rightUnitor, BraidedCategory.braiding_naturality_left_assoc,
    leftUnitor_inv_braiding_assoc]

/-- If the tensor unit is simple with finite-dimensional endomorphisms over an algebraically
closed field, a scalar acts on every object in the same way from the left and from the right. -/
theorem leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom_of_simple (k : Type w) [Field k]
    [IsAlgClosed k] [Preadditive C] [MonoidalPreadditive C] [Linear k C] [MonoidalLinear k C]
    [Limits.HasKernels C] [Simple (𝟙_ C)] [FiniteDimensional k (𝟙_ C ⟶ 𝟙_ C)]
    (a : 𝟙_ C ⟶ 𝟙_ C) (Y : C) :
    (λ_ Y).inv ≫ a ▷ Y ≫ (λ_ Y).hom = (ρ_ Y).inv ≫ Y ◁ a ≫ (ρ_ Y).hom := by
  obtain ⟨c, rfl⟩ := endomorphism_simple_eq_smul_id k a
  simp

/-! ### Centrality at an object -/

/-- A scalar `d` acts in the same way on the right and on the left of `X`. For the value of a
closed circle, this is the condition allowing that circle to be moved past `X`. It is a condition
at `X` alone, not at all objects of the category. -/
def CirclesCommuteAt (d : 𝟙_ C ⟶ 𝟙_ C) (X : C) : Prop :=
  (ρ_ X).inv ≫ X ◁ d ≫ (ρ_ X).hom = (λ_ X).inv ≫ d ▷ X ≫ (λ_ X).hom

/-- The two scalar actions whose agreement defines `CirclesCommuteAt`. -/
theorem circlesCommuteAt_iff (d : 𝟙_ C ⟶ 𝟙_ C) (X : C) :
    CirclesCommuteAt d X ↔
      (ρ_ X).inv ≫ X ◁ d ≫ (ρ_ X).hom = (λ_ X).inv ≫ d ▷ X ≫ (λ_ X).hom := Iff.rfl

/-- The objects at which a fixed scalar is central form a monoidal full subcategory. In
particular, centrality holds at the unit and propagates from generators to their tensor words
by `CategoryTheory.ObjectProperty.prop_projectObj`. -/
instance circlesCommuteAt_isMonoidal (d : 𝟙_ C ⟶ 𝟙_ C) :
    ObjectProperty.IsMonoidal (CirclesCommuteAt d) where
  prop_unit := by simp [circlesCommuteAt_iff, ← unitors_equal, ← unitors_inv_equal]
  prop_tensor X Y hX hY := by
    rw [circlesCommuteAt_iff] at hX hY ⊢
    -- Move the scalar from the far right, through `Y`, across the middle unit, and through `X`.
    calc
      (ρ_ (X ⊗ Y)).inv ≫ (X ⊗ Y) ◁ d ≫ (ρ_ (X ⊗ Y)).hom =
          X ◁ ((ρ_ Y).inv ≫ Y ◁ d ≫ (ρ_ Y).hom) := by monoidal
      _ = X ◁ ((λ_ Y).inv ≫ d ▷ Y ≫ (λ_ Y).hom) := congrArg (X ◁ ·) hY
      _ = ((ρ_ X).inv ≫ X ◁ d ≫ (ρ_ X).hom) ▷ Y := by monoidal
      _ = ((λ_ X).inv ≫ d ▷ X ≫ (λ_ X).hom) ▷ Y := congrArg (· ▷ Y) hX
      _ = (λ_ (X ⊗ Y)).inv ≫ d ▷ (X ⊗ Y) ≫ (λ_ (X ⊗ Y)).hom := by monoidal

/-- Centrality of a scalar at an object is invariant under isomorphism. The full monoidal
subcategory of central objects is therefore replete. -/
instance circlesCommuteAt_isClosedUnderIsomorphisms (d : 𝟙_ C ⟶ 𝟙_ C) :
    ObjectProperty.IsClosedUnderIsomorphisms (CirclesCommuteAt d) where
  of_iso e h := by
    rw [circlesCommuteAt_iff] at h ⊢
    rw [← cancel_epi e.hom]
    calc
      e.hom ≫ (ρ_ _).inv ≫ _ ◁ d ≫ (ρ_ _).hom =
          ((ρ_ _).inv ≫ _ ◁ d ≫ (ρ_ _).hom) ≫ e.hom := by
        rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
          rightUnitor_naturality]
        simp
      _ = ((λ_ _).inv ≫ d ▷ _ ≫ (λ_ _).hom) ≫ e.hom := congrArg (· ≫ e.hom) h
      _ = e.hom ≫ (λ_ _).inv ≫ d ▷ _ ≫ (λ_ _).hom := by
        rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, leftUnitor_naturality]
        simp

/-- The identity scalar is central at every object. -/
@[simp]
theorem circlesCommuteAt_id (X : C) : CirclesCommuteAt (𝟙 (𝟙_ C)) X := by
  simp [circlesCommuteAt_iff]

/-- Two scalars central at `X` have composite central at `X`. This allows repeated circles to
be moved past the same object. -/
theorem CirclesCommuteAt.comp {d e : 𝟙_ C ⟶ 𝟙_ C} {X : C}
    (hd : CirclesCommuteAt d X) (he : CirclesCommuteAt e X) :
    CirclesCommuteAt (d ≫ e) X := by
  rw [circlesCommuteAt_iff] at hd he ⊢
  calc
    (ρ_ X).inv ≫ X ◁ (d ≫ e) ≫ (ρ_ X).hom =
        ((ρ_ X).inv ≫ X ◁ d ≫ (ρ_ X).hom) ≫
          ((ρ_ X).inv ≫ X ◁ e ≫ (ρ_ X).hom) := by simp
    _ = ((λ_ X).inv ≫ d ▷ X ≫ (λ_ X).hom) ≫
          ((λ_ X).inv ≫ e ▷ X ≫ (λ_ X).hom) := by rw [hd, he]
    _ = (λ_ X).inv ≫ (d ≫ e) ▷ X ≫ (λ_ X).hom := by simp

/-- A scalar multiple of the identity of the unit is central at every object of a monoidal
linear category. Thus prescribing a loop value `δ • 𝟙` needs no separate centrality assumption. -/
@[simp]
theorem circlesCommuteAt_smul_id {R : Type*} [Semiring R] [Preadditive C] [Linear R C]
    [MonoidalPreadditive C] [MonoidalLinear R C] (r : R) (X : C) :
    CirclesCommuteAt (r • 𝟙 (𝟙_ C)) X := by
  simp [circlesCommuteAt_iff]

/-- In a braided target, the existing scalar-action identity supplies local centrality. -/
example [BraidedCategory C] (d : 𝟙_ C ⟶ 𝟙_ C) (X : C) : CirclesCommuteAt d X :=
  (leftUnitor_inv_scalar_whiskerRight_leftUnitor_hom d X).symm

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Stable equivalence and stable object classes modulo an object property

For a nonempty object property `A` closed under binary products in a category `C` with zero
morphisms and binary biproducts, two objects `X` and `Y` are stably equivalent modulo `A`
(`TauCeti.StableEquiv A X Y`) when `X ⊞ A₁ ≅ Y ⊞ A₂` for some `A₁, A₂` satisfying `A`.

The quotient `TauCeti.StableClasses A` is a commutative monoid under binary biproducts, with
universal property `TauCeti.StableClasses.lift` characterizing additive homomorphisms out of
`StableClasses A` in terms of isomorphism-invariant, biproduct-additive functions vanishing on `A`.
When `A` is stable under a shift `n`, `TauCeti.StableEquiv.shift` shows that `X ↦ X⟦n⟧` descends
to stable equivalence, giving `TauCeti.StableClasses.shift`.

## Main definitions

* `TauCeti.StableEquiv A`: the equivalence relation identifying `X` and `Y` when `X ⊞ A₁ ≅ Y ⊞ A₂`
  for some `A₁, A₂` in `A`.
* `TauCeti.StableClasses A`: the commutative monoid of stable classes of objects modulo `A`, with
  quotient map `TauCeti.StableClasses.mk` and universal property `TauCeti.StableClasses.lift`.
* `TauCeti.StableClasses.shift`: the shift action on `TauCeti.StableClasses A`.

## Main results

* `TauCeti.StableEquiv.shift` and `TauCeti.StableClasses.shift_mk`: stable equivalence and stable
  classes are compatible with shifts leaving `A` stable.
* `TauCeti.StableClasses.mk_eq_zero_of_prop`: every object satisfying `A` has zero stable class
  modulo `A`.
* `TauCeti.StableClasses.lift_mk` and `TauCeti.StableClasses.lift_unique`: computation and
  uniqueness for the universal property of `TauCeti.StableClasses A`.
-/

public section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

namespace TauCeti

section StableEquiv

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- Two objects `X` and `Y` are stably equivalent modulo an object property `A` when
`X ⊞ A₁ ≅ Y ⊞ A₂` for some `A₁, A₂` satisfying `A`. -/
def StableEquiv (A : ObjectProperty C) (X Y : C) : Prop :=
  ∃ (A₁ A₂ : C), A A₁ ∧ A A₂ ∧ Nonempty (X ⊞ A₁ ≅ Y ⊞ A₂)

/-- Characterization of `TauCeti.StableEquiv`. -/
theorem stableEquiv_iff (A : ObjectProperty C) (X Y : C) :
    StableEquiv A X Y ↔ ∃ (A₁ A₂ : C), A A₁ ∧ A A₂ ∧ Nonempty (X ⊞ A₁ ≅ Y ⊞ A₂) :=
  (Iff.rfl)

namespace StableEquiv

variable {A : ObjectProperty C}

/-- Isomorphic objects are stably equivalent modulo any nonempty property. -/
theorem of_iso [A.Nonempty] {X Y : C} (e : X ≅ Y) : StableEquiv A X Y :=
  (stableEquiv_iff A X Y).mpr ⟨A.arbitrary, A.arbitrary, A.prop_arbitrary, A.prop_arbitrary,
    ⟨biprod.mapIso e (Iso.refl A.arbitrary)⟩⟩

/-- Stable equivalence is reflexive when `A` is nonempty. -/
theorem refl [A.Nonempty] (X : C) : StableEquiv A X X :=
  of_iso (Iso.refl X)

/-- Stable equivalence is symmetric. -/
theorem symm {X Y : C} (h : StableEquiv A X Y) : StableEquiv A Y X := by
  obtain ⟨A₁, A₂, h₁, h₂, ⟨e⟩⟩ := (stableEquiv_iff A X Y).mp h
  exact (stableEquiv_iff A Y X).mpr ⟨A₂, A₁, h₂, h₁, ⟨e.symm⟩⟩

/-- Stable equivalence is transitive when `A` is closed under binary products. -/
theorem trans [A.IsClosedUnderBinaryProducts] {X Y Z : C}
    (h₁ : StableEquiv A X Y) (h₂ : StableEquiv A Y Z) : StableEquiv A X Z := by
  obtain ⟨A₁, A₂, hA₁, hA₂, ⟨e₁⟩⟩ := (stableEquiv_iff A X Y).mp h₁
  obtain ⟨A₃, A₄, hA₃, hA₄, ⟨e₂⟩⟩ := (stableEquiv_iff A Y Z).mp h₂
  refine (stableEquiv_iff A X Z).mpr ⟨A₁ ⊞ A₃, A₄ ⊞ A₂,
    A.prop_biprod_of_isClosedUnderBinaryProducts hA₁ hA₃,
    A.prop_biprod_of_isClosedUnderBinaryProducts hA₄ hA₂,
    ⟨?_⟩⟩
  exact (biprod.associator X A₁ A₃).symm
    ≪≫ biprod.mapIso e₁ (Iso.refl A₃)
    ≪≫ biprod.associator Y A₂ A₃
    ≪≫ biprod.mapIso (Iso.refl Y) (biprod.braiding A₂ A₃)
    ≪≫ (biprod.associator Y A₃ A₂).symm
    ≪≫ biprod.mapIso e₂ (Iso.refl A₂)
    ≪≫ biprod.associator Z A₄ A₂

/-- Stable equivalence is compatible with binary biproducts when `A` is closed under binary
products. -/
theorem biprod [A.IsClosedUnderBinaryProducts] {X₁ Y₁ X₂ Y₂ : C}
    (h₁ : StableEquiv A X₁ Y₁) (h₂ : StableEquiv A X₂ Y₂) :
    StableEquiv A (X₁ ⊞ X₂) (Y₁ ⊞ Y₂) := by
  obtain ⟨A₁, B₁, hA₁, hB₁, ⟨e₁⟩⟩ := (stableEquiv_iff A X₁ Y₁).mp h₁
  obtain ⟨A₂, B₂, hA₂, hB₂, ⟨e₂⟩⟩ := (stableEquiv_iff A X₂ Y₂).mp h₂
  refine (stableEquiv_iff A (X₁ ⊞ X₂) (Y₁ ⊞ Y₂)).mpr ⟨A₁ ⊞ A₂, B₁ ⊞ B₂,
    A.prop_biprod_of_isClosedUnderBinaryProducts hA₁ hA₂,
    A.prop_biprod_of_isClosedUnderBinaryProducts hB₁ hB₂,
    ⟨biprodFourMiddleIso X₁ X₂ A₁ A₂ ≪≫ biprod.mapIso e₁ e₂ ≪≫
      (biprodFourMiddleIso Y₁ Y₂ B₁ B₂).symm⟩⟩

end StableEquiv

/-- Stable equivalence modulo a nonempty property closed under binary products is an equivalence
relation. -/
theorem equivalence_stableEquiv (A : ObjectProperty C) [A.Nonempty]
    [A.IsClosedUnderBinaryProducts] : Equivalence (StableEquiv A) where
  refl := StableEquiv.refl
  symm := StableEquiv.symm
  trans := StableEquiv.trans

/-- The setoid of stable equivalence modulo `A`. -/
private def stableSetoid (A : ObjectProperty C) [A.Nonempty] [A.IsClosedUnderBinaryProducts] :
    Setoid C where
  r := StableEquiv A
  iseqv := equivalence_stableEquiv A

/-- The quotient of the objects of `C` by stable equivalence modulo `A`: two objects receive the
same class when they become isomorphic after adding summands from `A`. -/
def StableClasses (A : ObjectProperty C) [A.Nonempty] [A.IsClosedUnderBinaryProducts] : Type u :=
  Quotient (stableSetoid A)

namespace StableClasses

variable (A : ObjectProperty C) [A.Nonempty] [A.IsClosedUnderBinaryProducts]

/-- The stable class of an object modulo `A`. -/
def mk (X : C) : StableClasses A :=
  Quotient.mk (stableSetoid A) X

variable {A}

/-- Two objects have the same stable class modulo `A` if and only if they are stably equivalent
modulo `A`. -/
theorem mk_eq_iff {X Y : C} : mk A X = mk A Y ↔ StableEquiv A X Y :=
  Quotient.eq (r := stableSetoid A)

/-- Isomorphic objects have the same stable class modulo `A`. -/
theorem mk_congr {X Y : C} (e : X ≅ Y) : mk A X = mk A Y :=
  mk_eq_iff.2 (StableEquiv.of_iso e)

/-- The canonical projection `mk A` is surjective. -/
theorem mk_surjective : Function.Surjective (mk A) :=
  Quotient.mk_surjective

/-- Induction principle for stable classes modulo `A`. -/
@[elab_as_elim]
theorem induction_on {motive : StableClasses A → Prop} (x : StableClasses A)
    (h : ∀ X : C, motive (mk A X)) : motive x :=
  Quotient.inductionOn x h

/-- Descend a function on objects to `TauCeti.StableClasses A`. -/
def liftOn {α : Sort*} (x : StableClasses A) (f : C → α)
    (hf : ∀ X Y : C, StableEquiv A X Y → f X = f Y) : α :=
  Quotient.liftOn x f hf

/-- Evaluating `TauCeti.StableClasses.liftOn` on a stable class recovers the function value. -/
@[simp]
theorem liftOn_mk {α : Sort*} (f : C → α) (hf : ∀ X Y : C, StableEquiv A X Y → f X = f Y)
    (X : C) : (mk A X).liftOn f hf = f X :=
  (rfl)

/-- Descend a binary function on objects to `TauCeti.StableClasses A`. -/
def liftOn₂ {α : Sort*} (x y : StableClasses A) (f : C → C → α)
    (hf : ∀ X₁ X₂ Y₁ Y₂ : C, StableEquiv A X₁ Y₁ → StableEquiv A X₂ Y₂ → f X₁ X₂ = f Y₁ Y₂) :
    α :=
  Quotient.liftOn₂ x y f hf

/-- Evaluating `TauCeti.StableClasses.liftOn₂` on two stable classes recovers the function value. -/
@[simp]
theorem liftOn₂_mk {α : Sort*} (f : C → C → α)
    (hf : ∀ X₁ X₂ Y₁ Y₂ : C, StableEquiv A X₁ Y₁ → StableEquiv A X₂ Y₂ → f X₁ X₂ = f Y₁ Y₂)
    (X Y : C) : liftOn₂ (mk A X) (mk A Y) f hf = f X Y :=
  (rfl)

/-- Addition on `TauCeti.StableClasses A`, induced by binary biproducts. -/
noncomputable instance : Add (StableClasses A) :=
  ⟨fun x y => liftOn₂ x y (fun X Y => mk A (X ⊞ Y)) fun _ _ _ _ h₁ h₂ =>
    mk_eq_iff.2 (StableEquiv.biprod h₁ h₂)⟩

/-- The stable class of a binary biproduct is the sum of the stable classes. -/
@[simp]
theorem mk_biprod (X Y : C) : mk A (X ⊞ Y) = mk A X + mk A Y :=
  (rfl)

end StableClasses

section AddCommMonoid

variable [HasZeroObject C] (A : ObjectProperty C) [A.Nonempty]
  [A.IsClosedUnderBinaryProducts]

namespace StableClasses

/-- The neutral stable class, represented by the zero object. -/
noncomputable instance : Zero (StableClasses A) :=
  ⟨mk A 0⟩

/-- The stable class of the zero object is `0`. -/
@[simp]
theorem mk_zero : mk A (0 : C) = 0 :=
  (rfl)

/-- The commutative monoid structure on `TauCeti.StableClasses A`, with addition given by binary
biproducts and zero given by the class of `0`. -/
noncomputable instance : AddCommMonoid (StableClasses A) :=
  addCommMonoidOfBiprod (mk A) mk_surjective (fun _ _ => mk_congr) mk_biprod (mk_zero A)

variable {A}

/-- Every zero object has zero stable class. -/
@[simp]
theorem mk_eq_zero_of_isZero {X : C} (hX : IsZero X) : mk A X = 0 := by
  rw [mk_congr (hX.iso (isZero_zero C)), mk_zero]

/-- Every object satisfying `A` has zero stable class modulo `A`. -/
@[simp]
theorem mk_eq_zero_of_prop {X : C} (hX : A X) : mk A X = 0 := by
  rw [← mk_zero, mk_eq_iff]
  exact (stableEquiv_iff A X 0).mpr ⟨A.arbitrary, X ⊞ A.arbitrary, A.prop_arbitrary,
    A.prop_biprod_of_isClosedUnderBinaryProducts hX A.prop_arbitrary,
    ⟨isoZeroBiprod (isZero_zero C)⟩⟩

/-- Two additive homomorphisms out of `TauCeti.StableClasses A` agreeing on object classes are
equal. -/
@[ext]
theorem hom_ext {G : Type*} [AddMonoid G] {f g : StableClasses A →+ G}
    (h : ∀ X : C, f (mk A X) = g (mk A X)) : f = g := by
  ext x
  induction x using induction_on with | h X =>
  exact h X

variable (A) in
/-- **Universal property of `TauCeti.StableClasses A`**: an isomorphism-invariant,
biproduct-additive function into an additive monoid that vanishes on `A` descends uniquely to an
additive homomorphism out of `TauCeti.StableClasses A`. -/
def lift {G : Type*} [AddMonoid G] (f : C → G)
    (hiso : ∀ ⦃X Y : C⦄, (X ≅ Y) → f X = f Y)
    (hbiprod : ∀ X Y : C, f (X ⊞ Y) = f X + f Y)
    (hA : ∀ ⦃X : C⦄, A X → f X = 0) : StableClasses A →+ G where
  toFun x := x.liftOn f fun X Y h => by
    obtain ⟨A₁, A₂, h₁, h₂, ⟨e⟩⟩ := (stableEquiv_iff A X Y).mp h
    simpa only [hbiprod, hA h₁, hA h₂, add_zero] using hiso e
  map_zero' := by
    rw [← mk_zero, liftOn_mk]
    simpa only [hbiprod, hA A.prop_arbitrary, add_zero] using
      (hiso (isoZeroBiprod (isZero_zero C) : A.arbitrary ≅ 0 ⊞ A.arbitrary)).symm
  map_add' x y := by
    induction x using induction_on with | h X =>
    induction y using induction_on with | h Y =>
    simp only [← mk_biprod, liftOn_mk]
    exact hbiprod X Y

/-- Evaluating the descended homomorphism on a stable class recovers the original invariant. -/
@[simp]
theorem lift_mk {G : Type*} [AddMonoid G] (f : C → G)
    (hiso : ∀ ⦃X Y : C⦄, (X ≅ Y) → f X = f Y)
    (hbiprod : ∀ X Y : C, f (X ⊞ Y) = f X + f Y)
    (hA : ∀ ⦃X : C⦄, A X → f X = 0) (X : C) :
    lift A f hiso hbiprod hA (mk A X) = f X :=
  (rfl)

/-- Uniqueness in the universal property of `TauCeti.StableClasses A`. -/
theorem lift_unique {G : Type*} [AddMonoid G] (f : C → G)
    (hiso : ∀ ⦃X Y : C⦄, (X ≅ Y) → f X = f Y)
    (hbiprod : ∀ X Y : C, f (X ⊞ Y) = f X + f Y)
    (hA : ∀ ⦃X : C⦄, A X → f X = 0) (φ : StableClasses A →+ G)
    (hφ : ∀ X : C, φ (mk A X) = f X) :
    φ = lift A f hiso hbiprod hA :=
  hom_ext fun X => by rw [hφ, lift_mk]

/-- The stable classes modulo the top object property form a subsingleton. -/
instance : Subsingleton (StableClasses (⊤ : ObjectProperty C)) where
  allEq x y := by
    induction x using induction_on with | h X =>
    induction y using induction_on with | h Y =>
    rw [mk_eq_zero_of_prop (A := ⊤) trivial, mk_eq_zero_of_prop (A := ⊤) trivial]

end StableClasses

end AddCommMonoid

end StableEquiv

section Shift

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {M : Type*} [AddGroup M] [HasShift C M]

/-- Stable equivalence is preserved by a shift `n` when `A` is stable under `⟦n⟧`. -/
theorem StableEquiv.shift {A : ObjectProperty C} (n : M) [A.IsStableUnderShiftBy n]
    [(shiftFunctor C n).PreservesZeroMorphisms] {X Y : C} (h : StableEquiv A X Y) :
    StableEquiv A (X⟦n⟧) (Y⟦n⟧) := by
  obtain ⟨A₁, A₂, h₁, h₂, ⟨e⟩⟩ := (stableEquiv_iff A X Y).mp h
  let : PreservesBinaryBiproducts (shiftFunctor C n) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  refine (stableEquiv_iff A (X⟦n⟧) (Y⟦n⟧)).mpr
    ⟨A₁⟦n⟧, A₂⟦n⟧, A.le_shift n _ h₁, A.le_shift n _ h₂, ⟨?_⟩⟩
  exact ((shiftFunctor C n).mapBiprod X A₁).symm
    ≪≫ (shiftFunctor C n).mapIso e
    ≪≫ (shiftFunctor C n).mapBiprod Y A₂

/-- The shift `n` on `TauCeti.StableClasses A` induced by `shiftFunctor C n` when `A` is stable
under `⟦n⟧`. -/
def StableClasses.shift {A : ObjectProperty C} [A.Nonempty] [A.IsClosedUnderBinaryProducts]
    (n : M) [A.IsStableUnderShiftBy n] [(shiftFunctor C n).PreservesZeroMorphisms]
    (x : StableClasses A) : StableClasses A :=
  x.liftOn (fun X => StableClasses.mk A (X⟦n⟧)) fun _ _ h =>
    StableClasses.mk_eq_iff.2 (h.shift n)

/-- Shifting the stable class of an object computes as the stable class of its shift. -/
@[simp]
theorem StableClasses.shift_mk {A : ObjectProperty C} [A.Nonempty]
    [A.IsClosedUnderBinaryProducts] (n : M) [A.IsStableUnderShiftBy n]
    [(shiftFunctor C n).PreservesZeroMorphisms] (X : C) :
    StableClasses.shift n (StableClasses.mk A X) = StableClasses.mk A (X⟦n⟧) :=
  StableClasses.liftOn_mk ..

end Shift

end TauCeti

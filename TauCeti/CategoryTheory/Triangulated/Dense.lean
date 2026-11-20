/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import TauCeti.CategoryTheory.Triangulated.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Biproducts
import TauCeti.CategoryTheory.ObjectProperty

/-!
# Dense triangulated subcategories and stable object classes

In a pretriangulated category `C`, every monomorphism (and in particular every retract) splits as a
binary biproduct summand (`CategoryTheory.Pretriangulated.exists_iso_biprod_of_mono`,
`CategoryTheory.Retract.exists_iso_biprod`). Consequently, if `P` is a strictly full triangulated
subcategory of `C` and `X` lies in the retract closure `P.retractClosure`, then `X ⊞ X⟦1⟧` lies in
`P` (`CategoryTheory.ObjectProperty.prop_biprod_shift_one_of_retractClosure`), and for any
distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` whose outer terms lie in `P.retractClosure`, the
stabilized middle term `Y ⊞ (X⟦1⟧ ⊞ Z⟦1⟧)` lies in `P`
(`CategoryTheory.ObjectProperty.prop_biprod_shift_one_of_distTriang`).

For an object property `A` containing a zero object and closed under binary products, two objects
`X` and `Y` are stably equivalent modulo `A` (`TauCeti.StableEquiv A X Y`) when
`X ⊞ A₁ ≅ Y ⊞ A₂` for some `A₁, A₂` satisfying `A`. The quotient `TauCeti.StableClasses A` is a
commutative monoid under binary biproducts, and when `A` is a strictly full triangulated
subcategory, the zero-class criterion holds: `StableClasses.mk A X = 0` if and only if `A X`
(`TauCeti.StableClasses.mk_eq_zero_iff`). When `A` is moreover dense (`A.retractClosure = ⊤`), the
shift `X ↦ X⟦1⟧` supplies additive inverses (`TauCeti.StableClasses.addCommGroup`) and the
distinguished triangle relation `[Y] = [X] + [Z]` holds in `TauCeti.StableClasses A`
(`TauCeti.StableClasses.mk_distTriang`).

## Main definitions

* `TauCeti.StableEquiv A`: the equivalence relation identifying `X` and `Y` when `X ⊞ A₁ ≅ Y ⊞ A₂`
  for some `A₁, A₂` in `A`.
* `TauCeti.StableClasses A`: the commutative monoid of stable classes of objects modulo `A`, with
  quotient map `TauCeti.StableClasses.mk` and universal property `TauCeti.StableClasses.lift`.
* `TauCeti.StableClasses.addCommGroup`: the abelian group structure on `TauCeti.StableClasses A`
  when `A` is a dense strictly full triangulated subcategory.

## Main results

* `CategoryTheory.Pretriangulated.exists_iso_biprod_of_mono` and
  `CategoryTheory.Retract.exists_iso_biprod`: monomorphisms and retracts split as direct summands
  in any pretriangulated category.
* `CategoryTheory.ObjectProperty.prop_biprod_shift_one_of_retractClosure` and
  `CategoryTheory.ObjectProperty.prop_biprod_shift_one_of_distTriang`: Thomason's stabilization
  lemmas for retracts of objects in a strictly full triangulated subcategory.
* `TauCeti.StableClasses.mk_eq_zero_iff`: the zero-class criterion `mk A X = 0 ↔ A X`.
* `TauCeti.StableClasses.mk_distTriang`: distinguished triangle additivity in
  `TauCeti.StableClasses A`.

## References

* R. W. Thomason, *The classification of triangulated subcategories*, Compositio Math. **105**
  (1997), no. 1, 1–27, Lemma 2.2.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe v u

namespace CategoryTheory

section PretriangulatedRetract

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Splitting of monomorphisms in a pretriangulated category**: every monomorphism `f : X ⟶ Y`
identifies `Y` with a binary biproduct `X ⊞ Z` compatibly with `biprod.inl`. -/
theorem Pretriangulated.exists_iso_biprod_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    ∃ (Z : C) (e : Y ≅ X ⊞ Z), f ≫ e.hom = biprod.inl := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  obtain ⟨e, he, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ hT
    (Triangle.mor₃_eq_zero_of_mono₁ _ hT ‹_›)
  exact ⟨Z, e, he⟩

/-- **Splitting of retracts in a pretriangulated category**: every retract `r : Retract X Y`
identifies `Y` with a binary biproduct `X ⊞ Z` compatibly with `biprod.inl`. -/
theorem Retract.exists_iso_biprod {X Y : C} (r : Retract X Y) :
    ∃ (Z : C) (e : Y ≅ X ⊞ Z), r.i ≫ e.hom = biprod.inl :=
  Pretriangulated.exists_iso_biprod_of_mono r.i

end PretriangulatedRetract

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) [P.IsTriangulatedClosed₂] [P.IsStableUnderShiftBy (1 : ℤ)]
  [P.IsClosedUnderIsomorphisms]

/-- **Thomason's shift stabilization lemma**: if `X` is a retract of an object in a strictly full
extension-closed subcategory `P` stable under `⟦1⟧`, then `X ⊞ X⟦1⟧` belongs to `P`. -/
theorem prop_biprod_shift_one_of_retractClosure {X : C} (hX : P.retractClosure X) :
    P (X ⊞ X⟦(1 : ℤ)⟧) := by
  obtain ⟨A₀, hA₀, ⟨r⟩⟩ := hX
  obtain ⟨Z, e, -⟩ := r.exists_iso_biprod
  have hXZ : P (X ⊞ Z) := P.prop_of_iso e hA₀
  let : PreservesBinaryBiproducts (shiftFunctor C (1 : ℤ)) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have hXZ₁ : P (X⟦(1 : ℤ)⟧ ⊞ Z⟦(1 : ℤ)⟧) :=
    P.prop_of_iso ((shiftFunctor C (1 : ℤ)).mapBiprod X Z) (P.le_shift (1 : ℤ) _ hXZ)
  have hmid : P ((X ⊞ X⟦(1 : ℤ)⟧) ⊞ (0 : C)) :=
    P.prop_biprod_obj₂_of_distTriang
      (binaryBiproductTriangle_distinguished X (X⟦(1 : ℤ)⟧))
      (contractible_distinguished₂ Z) hXZ hXZ₁
  exact P.prop_of_iso (isoBiprodZero (isZero_zero C)).symm hmid

/-- **Thomason's triangle stabilization lemma**: if `T` is a distinguished triangle whose outer
terms lie in the retract closure of a strictly full extension-closed subcategory `P` stable under
`⟦1⟧`, then `T.obj₂ ⊞ (T.obj₁⟦1⟧ ⊞ T.obj₃⟦1⟧)` belongs to `P`. -/
theorem prop_biprod_shift_one_of_distTriang {T : Triangle C} (hT : T ∈ distTriang C)
    (h₁ : P.retractClosure T.obj₁) (h₃ : P.retractClosure T.obj₃) :
    P (T.obj₂ ⊞ (T.obj₁⟦(1 : ℤ)⟧ ⊞ T.obj₃⟦(1 : ℤ)⟧)) :=
  P.prop_biprod_obj₂_of_distTriang hT
    (binaryBiproductTriangle_distinguished (T.obj₁⟦(1 : ℤ)⟧) (T.obj₃⟦(1 : ℤ)⟧))
    (P.prop_biprod_shift_one_of_retractClosure h₁)
    (P.prop_biprod_shift_one_of_retractClosure h₃)

end ObjectProperty

end CategoryTheory

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
  ⟨A.arbitrary, A.arbitrary, A.prop_arbitrary, A.prop_arbitrary,
    ⟨biprod.mapIso e (Iso.refl A.arbitrary)⟩⟩

/-- Stable equivalence is reflexive when `A` is nonempty. -/
theorem refl [A.Nonempty] (X : C) : StableEquiv A X X :=
  of_iso (Iso.refl X)

/-- Stable equivalence is symmetric. -/
theorem symm {X Y : C} (h : StableEquiv A X Y) : StableEquiv A Y X := by
  obtain ⟨A₁, A₂, h₁, h₂, ⟨e⟩⟩ := h
  exact ⟨A₂, A₁, h₂, h₁, ⟨e.symm⟩⟩

/-- Stable equivalence is transitive when `A` is closed under binary products. -/
theorem trans [A.IsClosedUnderBinaryProducts] {X Y Z : C}
    (h₁ : StableEquiv A X Y) (h₂ : StableEquiv A Y Z) : StableEquiv A X Z := by
  obtain ⟨A₁, A₂, hA₁, hA₂, ⟨e₁⟩⟩ := h₁
  obtain ⟨A₃, A₄, hA₃, hA₄, ⟨e₂⟩⟩ := h₂
  refine ⟨A₁ ⊞ A₃, A₄ ⊞ A₂,
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
  obtain ⟨A₁, B₁, hA₁, hB₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨A₂, B₂, hA₂, hB₂, ⟨e₂⟩⟩ := h₂
  refine ⟨A₁ ⊞ A₂, B₁ ⊞ B₂,
    A.prop_biprod_of_isClosedUnderBinaryProducts hA₁ hA₂,
    A.prop_biprod_of_isClosedUnderBinaryProducts hB₁ hB₂,
    ⟨?_⟩⟩
  exact (biprod.associator X₁ X₂ (A₁ ⊞ A₂))
    ≪≫ biprod.mapIso (Iso.refl X₁) ((biprod.associator X₂ A₁ A₂).symm
      ≪≫ biprod.mapIso (biprod.braiding X₂ A₁) (Iso.refl A₂)
      ≪≫ biprod.associator A₁ X₂ A₂)
    ≪≫ (biprod.associator X₁ A₁ (X₂ ⊞ A₂)).symm
    ≪≫ biprod.mapIso e₁ e₂
    ≪≫ biprod.associator Y₁ B₁ (Y₂ ⊞ B₂)
    ≪≫ biprod.mapIso (Iso.refl Y₁) ((biprod.associator B₁ Y₂ B₂).symm
      ≪≫ biprod.mapIso (biprod.braiding B₁ Y₂) (Iso.refl B₂)
      ≪≫ biprod.associator Y₂ B₁ B₂)
    ≪≫ (biprod.associator Y₁ Y₂ (B₁ ⊞ B₂)).symm

end StableEquiv

/-- Stable equivalence modulo a nonempty property closed under binary products is an equivalence
relation. -/
theorem equivalence_stableEquiv (A : ObjectProperty C) [A.Nonempty]
    [A.IsClosedUnderBinaryProducts] : Equivalence (StableEquiv A) where
  refl := StableEquiv.refl
  symm := StableEquiv.symm
  trans := StableEquiv.trans

/-- The setoid of stable equivalence modulo `A`. -/
def stableSetoid (A : ObjectProperty C) [A.Nonempty] [A.IsClosedUnderBinaryProducts] :
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

variable [HasZeroObject C] (A : ObjectProperty C) [A.ContainsZero]
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
noncomputable instance : AddCommMonoid (StableClasses A) where
  add_assoc x y z := by
    induction x using induction_on with | h X =>
    induction y using induction_on with | h Y =>
    induction z using induction_on with | h Z =>
    rw [← mk_biprod, ← mk_biprod, ← mk_biprod, ← mk_biprod]
    exact mk_congr (biprod.associator X Y Z)
  zero_add x := by
    induction x using induction_on with | h X =>
    rw [← mk_zero, ← mk_biprod]
    exact mk_congr (isoZeroBiprod (isZero_zero C)).symm
  add_zero x := by
    induction x using induction_on with | h X =>
    rw [← mk_zero, ← mk_biprod]
    exact mk_congr (isoBiprodZero (isZero_zero C)).symm
  add_comm x y := by
    induction x using induction_on with | h X =>
    induction y using induction_on with | h Y =>
    rw [← mk_biprod, ← mk_biprod]
    exact mk_congr (biprod.braiding X Y)
  nsmul := nsmulRec

variable {A}

/-- Every zero object has zero stable class. -/
@[simp]
theorem mk_eq_zero_of_isZero {X : C} (hX : IsZero X) : mk A X = 0 := by
  rw [mk_congr (hX.iso (isZero_zero C)), mk_zero]

/-- Every object satisfying `A` has zero stable class modulo `A`. -/
theorem mk_eq_zero_of_prop {X : C} (hX : A X) : mk A X = 0 := by
  obtain ⟨Z, _, hAZ⟩ := A.exists_prop_of_containsZero
  rw [← mk_zero, mk_eq_iff]
  exact ⟨Z, X ⊞ Z, hAZ, A.prop_biprod_of_isClosedUnderBinaryProducts hX hAZ,
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
  toFun x := x.liftOn f fun X Y ⟨A₁, A₂, h₁, h₂, ⟨e⟩⟩ => by
    have h := hiso e
    rw [hbiprod, hbiprod, hA h₁, hA h₂, add_zero, add_zero] at h
    exact h
  map_zero' := by
    rw [← mk_zero, liftOn_mk]
    obtain ⟨Z, hZ, hAZ⟩ := A.exists_prop_of_containsZero
    exact (hiso ((isZero_zero C).iso hZ)).trans (hA hAZ)
  map_add' x y := by
    induction x using induction_on with | h X =>
    induction y using induction_on with | h Y =>
    rw [← mk_biprod, liftOn_mk, liftOn_mk, liftOn_mk]
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
  obtain ⟨A₁, A₂, h₁, h₂, ⟨e⟩⟩ := h
  let : PreservesBinaryBiproducts (shiftFunctor C n) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  refine ⟨A₁⟦n⟧, A₂⟦n⟧, A.le_shift n _ h₁, A.le_shift n _ h₂, ⟨?_⟩⟩
  exact ((shiftFunctor C n).mapBiprod X A₁).symm
    ≪≫ (shiftFunctor C n).mapIso e
    ≪≫ (shiftFunctor C n).mapBiprod Y A₂

end Shift

section Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace StableClasses

/-- **Zero-class criterion**: in a pretriangulated category, an object has zero stable class modulo
a strictly full triangulated subcategory `A` if and only if it belongs to `A`. -/
theorem mk_eq_zero_iff {A : ObjectProperty C} [A.ContainsZero] [A.IsClosedUnderIsomorphisms]
    [A.IsClosedUnderBinaryProducts] [A.IsTriangulatedClosed₁] {X : C} :
    mk A X = 0 ↔ A X := by
  refine ⟨fun h => ?_, mk_eq_zero_of_prop⟩
  rw [← mk_zero, mk_eq_iff] at h
  obtain ⟨A₁, A₂, hA₁, hA₂, ⟨e⟩⟩ := h
  have hXA₁ : A (X ⊞ A₁) :=
    A.prop_of_iso ((isoZeroBiprod (isZero_zero C)).trans e.symm) hA₂
  exact A.prop_left_of_biprod hXA₁ hA₁

variable {A : ObjectProperty C} [A.IsTriangulated] [A.IsClosedUnderIsomorphisms]

/-- If `X` lies in the retract closure of a strictly full triangulated subcategory `A`, then
`mk A X + mk A (X⟦1⟧) = 0`. -/
theorem mk_add_mk_shift_one {X : C} (hX : A.retractClosure X) :
    mk A X + mk A (X⟦(1 : ℤ)⟧) = 0 := by
  rw [← mk_biprod]
  exact mk_eq_zero_of_prop (A.prop_biprod_shift_one_of_retractClosure hX)

/-- If `X` lies in the retract closure of a strictly full triangulated subcategory `A`, then
`mk A (X⟦1⟧) + mk A X = 0`. -/
theorem mk_shift_one_add_mk {X : C} (hX : A.retractClosure X) :
    mk A (X⟦(1 : ℤ)⟧) + mk A X = 0 := by
  rw [add_comm]
  exact mk_add_mk_shift_one hX

/-- **Distinguished triangle additivity in `TauCeti.StableClasses A`**: for a distinguished triangle
`X ⟶ Y ⟶ Z ⟶ X⟦1⟧` whose outer terms lie in the retract closure of a strictly full triangulated
subcategory `A`, `mk A Y = mk A X + mk A Z`. -/
theorem mk_distTriang {T : Triangle C} (hT : T ∈ distTriang C)
    (h₁ : A.retractClosure T.obj₁) (h₃ : A.retractClosure T.obj₃) :
    mk A T.obj₂ = mk A T.obj₁ + mk A T.obj₃ := by
  have hmid : mk A T.obj₂ + (mk A (T.obj₁⟦(1 : ℤ)⟧) + mk A (T.obj₃⟦(1 : ℤ)⟧)) = 0 := by
    rw [← mk_biprod, ← mk_biprod]
    exact mk_eq_zero_of_prop (A.prop_biprod_shift_one_of_distTriang hT h₁ h₃)
  calc
    mk A T.obj₂ = mk A T.obj₂ + 0 + 0 := by simp
    _ = mk A T.obj₂ + (mk A (T.obj₁⟦(1 : ℤ)⟧) + mk A T.obj₁) +
          (mk A (T.obj₃⟦(1 : ℤ)⟧) + mk A T.obj₃) := by
        rw [mk_shift_one_add_mk h₁, mk_shift_one_add_mk h₃]
    _ = (mk A T.obj₂ + (mk A (T.obj₁⟦(1 : ℤ)⟧) + mk A (T.obj₃⟦(1 : ℤ)⟧))) +
          (mk A T.obj₁ + mk A T.obj₃) := by
        ac_rfl
    _ = mk A T.obj₁ + mk A T.obj₃ := by
        rw [hmid, zero_add]

variable (A) in
/-- **Abelian group structure on stable classes modulo a dense triangulated subcategory**
(Thomason 1997, Lemma 2.2): when `A` is a dense strictly full triangulated subcategory of `C`,
`TauCeti.StableClasses A` is an abelian group whose negation sends `mk A X` to `mk A (X⟦1⟧)`.

Exposed alongside `instance_reducible` so that downstream callers installing this instance locally
get definitional agreement of its underlying `AddCommMonoid` with the global instance. -/
@[expose, instance_reducible]
noncomputable def addCommGroup (hdense : A.retractClosure = ⊤) : AddCommGroup (StableClasses A) :=
  let negFn : StableClasses A → StableClasses A := fun x =>
    x.liftOn (fun X => mk A (X⟦(1 : ℤ)⟧)) fun _ _ h => mk_eq_iff.2 (h.shift (1 : ℤ))
  let _ : Neg (StableClasses A) := ⟨negFn⟩
  { (inferInstance : AddCommMonoid (StableClasses A)) with
    neg := negFn
    sub := fun x y => x + negFn y
    sub_eq_add_neg := fun _ _ => rfl
    zsmul := zsmulRec
    neg_add_cancel := fun x => by
      induction x using induction_on with | h X =>
      exact mk_shift_one_add_mk (hdense.symm ▸ trivial) }

/-- In the abelian group structure `TauCeti.StableClasses.addCommGroup`, negation sends the class
of `X` to the class of `X⟦1⟧`. -/
@[simp]
theorem addCommGroup_neg_mk (hdense : A.retractClosure = ⊤) (X : C) :
    (addCommGroup A hdense).neg (mk A X) = mk A (X⟦(1 : ℤ)⟧) :=
  (rfl)

end StableClasses

end Pretriangulated

end TauCeti

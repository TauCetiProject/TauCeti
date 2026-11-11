/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
public import TauCeti.CategoryTheory.ObjectProperty

/-!
# The additive closure of an object

Let `C` be a preadditive category with finite biproducts and `M` an object of `C`. The
**additive closure** `add M` (`TauCeti.additiveClosure M`) consists of the direct summands
(retracts) of finite biproducts `Mⁿ`: it is the retract closure (Mathlib's
`CategoryTheory.ObjectProperty.retractClosure`) of the objects `Mⁿ`.

## Main definitions

* `TauCeti.additiveClosure M`: the direct summands of finite biproducts of copies of `M`.

## Main results

* `TauCeti.additiveClosure_le_iff`: `add M` is the smallest property holding for `M` that is
  stable under retracts and closed under finite products.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- The **additive closure** `add M` of an object `M`: the objects that are direct summands
(retracts) of a finite biproduct `Mⁿ` of copies of `M`. -/
abbrev additiveClosure (M : C) : ObjectProperty C :=
  (ObjectProperty.ofObj fun n : ℕ ↦ ⨁ fun _ : Fin n ↦ M).retractClosure

variable {M : C}

theorem additiveClosure_iff {X : C} :
    additiveClosure M X ↔ ∃ n : ℕ, Nonempty (Retract X (⨁ fun _ : Fin n ↦ M)) :=
  ⟨fun ⟨_, ⟨n⟩, e⟩ ↦ ⟨n, e⟩, fun ⟨n, e⟩ ↦ ⟨_, ⟨n⟩, e⟩⟩

theorem additiveClosure_biproduct (n : ℕ) : additiveClosure M (⨁ fun _ : Fin n ↦ M) :=
  ObjectProperty.le_retractClosure _ _ (ObjectProperty.ofObj_apply _ n)

variable (M) in
theorem additiveClosure_self : additiveClosure M M :=
  ObjectProperty.prop_retractClosure (ObjectProperty.ofObj_apply _ 1)
    { i := biproduct.ι (fun _ : Fin 1 ↦ M) 0, r := biproduct.π _ 0 }

section Biprod

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

private theorem additiveClosure_biprod {X Y : C} (hX : additiveClosure M X)
    (hY : additiveClosure M Y) : additiveClosure M (X ⊞ Y) := by
  obtain ⟨n, ⟨e⟩⟩ := additiveClosure_iff.mp hX
  obtain ⟨m, ⟨e'⟩⟩ := additiveClosure_iff.mp hY
  exact additiveClosure_iff.mpr ⟨n + m, ⟨Retract.trans
    { i := biprod.map e.i e'.i, r := biprod.map e.r e'.r }
    ((biproductSumIso _ _).symm ≪≫ biproduct.whiskerEquiv finSumFinEquiv fun
      | .inl _ => Iso.refl M
      | .inr _ => Iso.refl M).retract⟩⟩

instance : (additiveClosure M).IsClosedUnderFiniteProducts :=
  have : (additiveClosure M).IsClosedUnderBinaryProducts :=
    ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun _ _ ↦ additiveClosure_biprod
  .mk'

end Biprod

/-- The additive closure of `M` is the smallest property of objects that holds for `M`, is stable
under retracts and is closed under finite products. -/
theorem additiveClosure_le_iff {Q : ObjectProperty C} [Q.IsStableUnderRetracts]
    [Q.IsClosedUnderFiniteProducts] : additiveClosure M ≤ Q ↔ Q M := by
  refine ⟨fun h ↦ h _ (additiveClosure_self M), fun hM ↦ ?_⟩
  rw [ObjectProperty.retractClosure_le_iff, ObjectProperty.ofObj_le_iff]
  exact fun _ ↦ Q.prop_of_isLimit (biproduct.isLimit _) fun _ ↦ hM

end TauCeti

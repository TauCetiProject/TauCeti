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
public import TauCeti.CategoryTheory.ObjectProperty.FiniteProducts
public import TauCeti.CategoryTheory.ObjectProperty.Retract

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
* `TauCeti.additiveClosure_iff_exists_sum_comp_eq_id`: `X ∈ add M` exactly when `𝟙 X` is a finite
  sum of composites `X ⟶ M ⟶ X`.
* `CategoryTheory.Retract.additiveClosure_le`: `add M ≤ add N` when `M` is a direct summand of `N`.
* `CategoryTheory.Functor.additiveClosure_le_inverseImage`: a functor preserving finite products
  carries `add M` into `add (F M)`.
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

/-- **Additive closures grow along retracts**: if `M` is a direct summand of `N`, then
`add M ≤ add N`. -/
theorem _root_.CategoryTheory.Retract.additiveClosure_le {N : C} (h : Retract M N) :
    additiveClosure M ≤ additiveClosure N :=
  additiveClosure_le_iff.2 ((additiveClosure N).prop_of_retract h (additiveClosure_self N))

/-- **Additive closures through sums of composites**: `X` lies in `add M` exactly when the identity
of `X` is a finite sum of composites `X ⟶ M ⟶ X`. This form mentions no biproducts. -/
theorem additiveClosure_iff_exists_sum_comp_eq_id {X : C} :
    additiveClosure M X ↔
      ∃ (n : ℕ) (a : Fin n → (X ⟶ M)) (b : Fin n → (M ⟶ X)), ∑ j, a j ≫ b j = 𝟙 X := by
  rw [additiveClosure_iff]
  refine ⟨fun ⟨n, ⟨h⟩⟩ ↦ ⟨n, fun j ↦ h.i ≫ biproduct.π (fun _ : Fin n ↦ M) j,
    fun j ↦ biproduct.ι (fun _ : Fin n ↦ M) j ≫ h.r, ?_⟩, fun ⟨n, a, b, h⟩ ↦
      ⟨n, ⟨⟨biproduct.lift a, biproduct.desc b, by rw [biproduct.lift_desc, h]⟩⟩⟩⟩
  have hs : ∑ j, (h.i ≫ biproduct.π (fun _ : Fin n ↦ M) j) ≫
      biproduct.ι (fun _ : Fin n ↦ M) j ≫ h.r =
      h.i ≫ (∑ j, biproduct.π (fun _ : Fin n ↦ M) j ≫ biproduct.ι (fun _ : Fin n ↦ M) j) ≫
        h.r := by
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  rw [hs, biproduct.total, Category.id_comp, h.retract]

/-- A functor preserving finite products carries `add M` into `add (F M)`. -/
theorem _root_.CategoryTheory.Functor.additiveClosure_le_inverseImage {D : Type*} [Category* D]
    [Preadditive D] [HasFiniteBiproducts D] (F : C ⥤ D) [PreservesFiniteProducts F] (M : C) :
    additiveClosure M ≤ (additiveClosure (F.obj M)).inverseImage F :=
  additiveClosure_le_iff.2 (additiveClosure_self _)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Linear biproduct decompositions of Ext

In a linear abelian category, Ext from or to a finite biproduct is the product of the
corresponding Ext modules. These linear refinements of Mathlib's `Ext.biproductAddEquiv` and
`Ext.addEquivBiproduct` allow dimension and support calculations summand by summand. They apply
to any limiting bicone, including one transported through an additive equivalence.
-/

public section

namespace CategoryTheory.Abelian.Ext

open CategoryTheory.Limits

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (R : Type t) [Ring R] [Linear R C] {J : Type*} [Fintype J]

/-- Ext from a finite biproduct is linearly equivalent to the product of Ext from its
summands. This refines `Ext.biproductAddEquiv`. -/
noncomputable def biproductLinearEquiv {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) (Y : C) (n : ℕ) :
    Ext.{w} c.pt Y n ≃ₗ[R] ∀ i, Ext.{w} (X i) Y n where
  __ := biproductAddEquiv hc Y n
  map_smul' r x := by
    ext i
    simp [biproductAddEquiv]

/-- The Ext component at a summand is restriction along its inclusion. -/
@[simp]
theorem biproductLinearEquiv_apply {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) (Y : C) (n : ℕ) (x : Ext.{w} c.pt Y n) (i : J) :
    biproductLinearEquiv R hc Y n x i = (mk₀ (c.ι i)).comp x (zero_add n) :=
  (rfl)

/-- Assemble Ext components by precomposing with the projections and adding. -/
@[simp]
theorem biproductLinearEquiv_symm_apply {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) (Y : C) (n : ℕ) (x : ∀ i, Ext.{w} (X i) Y n) :
    (biproductLinearEquiv R hc Y n).symm x =
      ∑ i, (mk₀ (c.π i)).comp (x i) (zero_add n) :=
  (rfl)

/-- Ext to a finite biproduct is linearly equivalent to the product of Ext to its
summands. This refines `Ext.addEquivBiproduct`. -/
noncomputable def linearEquivBiproduct (X : C) {Y : J → C} {c : Bicone Y}
    (hc : c.IsBilimit) (n : ℕ) :
    Ext.{w} X c.pt n ≃ₗ[R] ∀ i, Ext.{w} X (Y i) n where
  __ := addEquivBiproduct X hc n
  map_smul' r x := by
    ext i
    simp [addEquivBiproduct]

/-- The Ext component at a summand is projection to it. -/
@[simp]
theorem linearEquivBiproduct_apply (X : C) {Y : J → C} {c : Bicone Y}
    (hc : c.IsBilimit) (n : ℕ) (x : Ext.{w} X c.pt n) (i : J) :
    linearEquivBiproduct R X hc n x i = x.comp (mk₀ (c.π i)) (add_zero n) :=
  (rfl)

/-- Assemble Ext components by postcomposing with the inclusions and adding. -/
@[simp]
theorem linearEquivBiproduct_symm_apply (X : C) {Y : J → C} {c : Bicone Y}
    (hc : c.IsBilimit) (n : ℕ) (x : ∀ i, Ext.{w} X (Y i) n) :
    (linearEquivBiproduct R X hc n).symm x =
      ∑ i, (x i).comp (mk₀ (c.ι i)) (add_zero n) :=
  (rfl)

end CategoryTheory.Abelian.Ext

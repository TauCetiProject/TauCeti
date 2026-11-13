/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.Finiteness

/-!
# Finite generation of free products

The free product of two finitely generated monoids is finitely generated, and so is the free
product of a finite family of finitely generated monoids: the images of the factors generate the
free product. Since a group is finitely generated exactly when it is finitely generated as a
monoid, the instances apply to free products of groups as well.

## Main declarations

* `Monoid.Coprod.instFG`: the free product of two finitely generated monoids is finitely
  generated.
* `Monoid.CoprodI.instFG`: the free product of a finite family of finitely generated monoids is
  finitely generated.
-/

public section

namespace Monoid

/-- The free product of two finitely generated monoids is finitely generated. -/
instance Coprod.instFG {M N : Type*} [Monoid M] [Monoid N] [Monoid.FG M] [Monoid.FG N] :
    Monoid.FG (Coprod M N) := by
  rw [Monoid.fg_def, ← Coprod.mrange_inl_sup_mrange_inr]
  exact .sup inferInstance inferInstance

/-- The free product of a finite family of finitely generated monoids is finitely generated. -/
instance CoprodI.instFG {ι : Type*} [Finite ι] {M : ι → Type*} [∀ i, Monoid (M i)]
    [∀ i, Monoid.FG (M i)] : Monoid.FG (CoprodI M) := by
  rw [Monoid.fg_def, ← CoprodI.iSup_mrange_of]
  exact .iSup _ fun _ => inferInstance

end Monoid

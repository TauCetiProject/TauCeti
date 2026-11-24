/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic

/-!
# Products of quasicategories

A product of quasicategories is a quasicategory: an inner horn in the product is filled
componentwise. This is used to state the Segal condition of symmetric monoidal quasicategories,
which compares a fiber with a finite power of the underlying quasicategory.

## Main results

* `SSet.quasicategory_piObj`: the product `∏ᶜ X` of a family of quasicategories is a
  quasicategory.
-/

public section

universe u

open CategoryTheory Limits Simplicial

namespace SSet

/-- The product of a family of quasicategories is a quasicategory: an inner horn is filled by
filling each of its components. -/
instance quasicategory_piObj {ι : Type*} (X : ι → SSet.{u}) [HasProduct X]
    [∀ i, Quasicategory (X i)] : Quasicategory (∏ᶜ X) where
  hornFilling' _ _ σ₀ h0 hn := by
    choose σ hσ using fun i ↦ Quasicategory.hornFilling' (σ₀ ≫ Pi.π X i) h0 hn
    exact ⟨Pi.lift σ, Pi.hom_ext _ _ fun i ↦ by
      rw [Category.assoc, limit.lift_π, Fan.mk_π_app, hσ i]⟩

end SSet

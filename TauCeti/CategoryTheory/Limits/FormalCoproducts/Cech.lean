/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy

/-!
# Naturality of the Čech object of a formal coproduct

Mathlib identifies the Čech object `U.cech` of a formal coproduct `U` with the Čech nerve of the
morphism from `U` to a terminal object (`CategoryTheory.Limits.FormalCoproduct.cechIsoCechNerve`).
This file records that the identification is natural in `U`: the map of Čech objects induced by a
morphism `φ : X ⟶ Y` corresponds to the map of Čech nerves induced by the morphism of arrows with
components `φ` and the identity of the terminal object. It also records how the map
`FormalCoproduct.powerMap φ α` induced on powers interacts with the projections.

## Main results

* `CategoryTheory.Limits.FormalCoproduct.powerMap_π`: `powerMap φ α` followed by the `a`-th
  projection is the `a`-th projection followed by `φ`.
* `CategoryTheory.Limits.FormalCoproduct.cechFunctor_map_comp_cechIsoCechNerve_hom`: the
  naturality of `cechIsoCechNerve`.
-/

public section

universe w v u

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- The map `powerMap φ α` induced by `φ : X ⟶ Y` on powers commutes with the projections: followed
by the `a`-th projection of `Y.power α` it is the `a`-th projection of `X.power α` followed by
`φ`. -/
@[reassoc (attr := simp)]
theorem powerMap_π {X Y : FormalCoproduct.{w} C} (φ : X ⟶ Y) (α : Type)
    [HasProductsOfShape α C] (a : α) :
    powerMap φ α ≫ Y.powerπ a = X.powerπ a ≫ φ :=
  hom_ext rfl fun x ↦ by
    simp only [category_comp_φ, powerMap_φ, powerπ_φ]
    exact (Pi.map_π (fun b ↦ φ.φ (x b)) a =≫ _).trans (Category.comp_id _)

variable [HasFiniteProducts C] {T : C} (hT : IsTerminal T)

/-- **Naturality of `cechIsoCechNerve`.** Under the identification of the Čech object of a formal
coproduct with the Čech nerve of its morphism to the terminal object, the map induced by
`φ : X ⟶ Y` on Čech objects is the map `Arrow.mapCechNerve` induced by the morphism of arrows
with components `φ` and `𝟙 T`. -/
theorem cechFunctor_map_comp_cechIsoCechNerve_hom {X Y : FormalCoproduct.{w} C} (φ : X ⟶ Y) :
    cechFunctor.map φ ≫ (Y.cechIsoCechNerve hT).hom = (X.cechIsoCechNerve hT).hom ≫
      Arrow.mapCechNerve (Arrow.homMk (f := Arrow.mk ((isTerminalIncl _ hT).from X))
        (g := Arrow.mk ((isTerminalIncl _ hT).from Y)) φ (𝟙 _)
          ((isTerminalIncl _ hT).hom_ext _ _)) := by
  refine NatTrans.ext (funext fun n ↦ WidePullback.hom_ext _ _ _ (fun j ↦ ?_) ?_)
  · -- both sides are the `j`-th projection of `X.cech` followed by `φ`
    simp [cechFunctor]
  · exact (isTerminalIncl _ hT).hom_ext _ _

end CategoryTheory.Limits.FormalCoproduct

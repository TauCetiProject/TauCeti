/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.CategoryTheory.Equivalence.Artin
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Action

/-!
# Transfer of the zigzag Artin action through a supplied equivalence

An equivalence from the homotopy category of graded zigzag modules to a category `D`
transports `zigzagBraidArtinAction` to `D`. Its standard generators are represented by
conjugates of the canonical braid autoequivalences. The existing generic transport API
supplies the natural intertwining isomorphisms.

The source is the cochain homotopy category of graded zigzag modules. The generic
`Equivalence.comp_autoequivalenceClassCongr_eq_iff` compares the transported action with
any supplied target action through natural intertwiners of generator functors. The
isomorphism on autoequivalence classes preserves and reflects injectivity of the action.
-/

public section
noncomputable section

namespace TauCeti

open CategoryTheory

universe u w vD uD

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

variable {D : Type uD} [Category.{vD} D]
  (e : HomotopyCategory
    (GradedModuleCat.{max u w} (zigzagAlgebraInternalGrading k G).piece) (.up ℤ) ≌ D)

/-- The zigzag Artin action transported through a supplied equivalence of categories. -/
def zigzagBraidArtinActionOfEquivalence :
    ArtinGroup G.coxeterMatrix →* AutoequivalenceClass D :=
  e.autoequivalenceClassCongr.toMonoidHom.comp (zigzagBraidArtinAction k G)

/-- Every group element acts by transport of its original autoequivalence class. -/
@[simp]
theorem zigzagBraidArtinActionOfEquivalence_apply (g : ArtinGroup G.coxeterMatrix) :
    zigzagBraidArtinActionOfEquivalence k G e g =
      e.autoequivalenceClassCongr (zigzagBraidArtinAction k G g) :=
  (rfl)

/-- A standard generator acts by the conjugate of the canonical braid autoequivalence. -/
theorem zigzagBraidArtinActionOfEquivalence_gen (i : V) :
    zigzagBraidArtinActionOfEquivalence k G e (ArtinGroup.gen G.coxeterMatrix i) =
      ((e.symm.trans (zigzagBraidAutoequivalence k G i)).trans e).toAutoequivalenceClass := by
  rw [zigzagBraidArtinActionOfEquivalence_apply, zigzagBraidArtinAction_gen,
    Equivalence.autoequivalenceClassCongr_toAutoequivalenceClass]

end TauCeti

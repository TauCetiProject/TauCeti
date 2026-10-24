/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.CategoryTheory.Equivalence.Transport
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Action

/-!
# Transfer of the zigzag Artin action through a supplied equivalence

An equivalence from the homotopy category of graded zigzag modules to a category `D`
transports `zigzagBraidArtinAction` to `D`. Its standard generators are represented by
conjugates of the canonical braid autoequivalences. The existing generic transport API
supplies the natural intertwining isomorphisms.

For a target Artin action whose generators have specified autoequivalence representatives,
`zigzagBraidArtinActionOfEquivalence_eq_iff` identifies that action with the transported
action exactly when the supplied equivalence intertwines the generator functors. This
reduces comparison with a separately constructed action to natural isomorphisms of the
actual generator functors.

The group isomorphism on autoequivalence classes preserves and reflects injectivity of
the action. A Morita comparison supplies an equivalence on homotopy categories. The source
here remains the homotopy category: derived descent and the derived-Koszul comparison need
separate constructions. No faithfulness theorem is asserted.
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

/-- A standard generator acts by the conjugate of the canonical braid autoequivalence. -/
@[simp]
theorem zigzagBraidArtinActionOfEquivalence_gen (i : V) :
    zigzagBraidArtinActionOfEquivalence k G e (ArtinGroup.gen G.coxeterMatrix i) =
      ((e.symm.trans (zigzagBraidAutoequivalence k G i)).trans e).toAutoequivalenceClass := by
  change e.autoequivalenceClassCongr
    (zigzagBraidArtinAction k G (ArtinGroup.gen G.coxeterMatrix i)) = _
  rw [zigzagBraidArtinAction_gen,
    Equivalence.autoequivalenceClassCongr_toAutoequivalenceClass]

/-- A target action agrees with transport precisely when its generator representatives
are naturally intertwined with the zigzag braid functors by the supplied equivalence. -/
theorem zigzagBraidArtinActionOfEquivalence_eq_iff
    (ρ : ArtinGroup G.coxeterMatrix →* AutoequivalenceClass D) (F : V → (D ≌ D))
    (hF : ∀ i, ρ (ArtinGroup.gen G.coxeterMatrix i) = (F i).toAutoequivalenceClass) :
    zigzagBraidArtinActionOfEquivalence k G e = ρ ↔
      ∀ i, Nonempty (e.functor ⋙ (F i).functor ≅
        (zigzagBraidAutoequivalence k G i).functor ⋙ e.functor) := by
  constructor
  · intro h i
    apply (Equivalence.autoequivalenceClassCongr_eq_iff e _ _).1
    rw [← zigzagBraidArtinAction_gen k G i]
    change zigzagBraidArtinActionOfEquivalence k G e
      (ArtinGroup.gen G.coxeterMatrix i) = _
    rw [h, hF i]
  · intro h
    apply ArtinGroup.hom_ext
    intro i
    rw [hF i]
    change e.autoequivalenceClassCongr
      (zigzagBraidArtinAction k G (ArtinGroup.gen G.coxeterMatrix i)) = _
    rw [zigzagBraidArtinAction_gen]
    exact (Equivalence.autoequivalenceClassCongr_eq_iff e _ _).2 (h i)

/-- Transport through an equivalence preserves and reflects faithfulness of the action. -/
theorem zigzagBraidArtinActionOfEquivalence_injective_iff :
    Function.Injective (zigzagBraidArtinActionOfEquivalence k G e) ↔
      Function.Injective (zigzagBraidArtinAction k G) :=
  e.autoequivalenceClassCongr.injective.of_comp_iff (zigzagBraidArtinAction k G)

end TauCeti

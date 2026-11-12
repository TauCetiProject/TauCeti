/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Module.Derived.Relations

/-!
# The derived Artin action and supplied-equivalence transfer

The graph Artin group has a homomorphism to the group of natural-isomorphism classes of
autoequivalences of the ordinary derived category of internally graded zigzag modules.
Each standard generator maps to the class of its positive derived vertex autoequivalence;
its inverse maps to the class of the inverse autoequivalence.

A supplied equivalence `e : C ≌ D` transports this homomorphism to autoequivalence classes of
`D` by conjugation. For a supplied target action with specified generator representatives,
agreement with the transported action is equivalent to natural intertwiners between the
actual source and target generator functors through `e`.

The source category `C` is chosen through `HasDerivedCategory`, over a commutative coefficient
ring and finite simple graph. Internal module grading and external cohomological degree
remain independent. Morita or derived-Koszul applications supply the equivalence and the
required generator intertwiners as data.
-/

public section
noncomputable section

namespace TauCeti

open CategoryTheory

universe u w z uD vD

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

-- The chosen derived category is supplied at the same universes as the vertex functors.
variable [HasDerivedCategory.{z}
  (GradedModuleCat.{max u w} (zigzagAlgebraInternalGrading k G).piece)]

/-- The graph Artin group acts on natural-isomorphism classes of the derived vertex
autoequivalences, through the existing Artin presentation. -/
def zigzagBraidDerivedArtinAction :
    ArtinGroup G.coxeterMatrix →*
      AutoequivalenceClass (_root_.DerivedCategory.{z}
        (GradedModuleCat.{max u w} (zigzagAlgebraInternalGrading k G).piece)) :=
  G.artinAutoequivalenceAction (zigzagBraidDerivedAutoequivalence k G)
    (fun hij hadj ↦ ⟨by
      simpa only [Equivalence.trans_functor, zigzagBraidDerivedAutoequivalence_functor] using
        zigzagBraidDerivedFunctorCommIso k G hij hadj⟩)
    (fun h ↦ ⟨by
      simpa only [Equivalence.trans_functor, zigzagBraidDerivedAutoequivalence_functor] using
        zigzagBraidDerivedFunctorBraidIso k G h⟩)

/-- A standard generator acts by the actual derived vertex autoequivalence. -/
@[simp]
theorem zigzagBraidDerivedArtinAction_gen (i : V) :
    zigzagBraidDerivedArtinAction k G (ArtinGroup.gen G.coxeterMatrix i) =
      (zigzagBraidDerivedAutoequivalence k G i).toAutoequivalenceClass :=
  SimpleGraph.artinAutoequivalenceAction_gen _ _ _ _ i

/-- An inverse standard generator acts by the inverse derived vertex autoequivalence. -/
-- The generic map_inv rule is the simp-normal form; keep this formula as a named rewrite.
theorem zigzagBraidDerivedArtinAction_gen_inv (i : V) :
    zigzagBraidDerivedArtinAction k G (ArtinGroup.gen G.coxeterMatrix i)⁻¹ =
      (zigzagBraidDerivedAutoequivalence k G i).symm.toAutoequivalenceClass :=
  SimpleGraph.artinAutoequivalenceAction_gen_inv _ _ _ _ i

variable {D : Type uD} [Category.{vD} D]
  (e : _root_.DerivedCategory.{z}
    (GradedModuleCat.{max u w} (zigzagAlgebraInternalGrading k G).piece) ≌ D)

/-- Transport the actual derived Artin action through a supplied category equivalence. -/
def zigzagBraidDerivedArtinActionOfEquivalence :
    ArtinGroup G.coxeterMatrix →* AutoequivalenceClass D :=
  e.autoequivalenceClassCongr.toMonoidHom.comp (zigzagBraidDerivedArtinAction k G)

/-- Every Artin group element acts by transport of its original derived action class. -/
@[simp]
theorem zigzagBraidDerivedArtinActionOfEquivalence_apply (g : ArtinGroup G.coxeterMatrix) :
    zigzagBraidDerivedArtinActionOfEquivalence k G e g =
      e.autoequivalenceClassCongr (zigzagBraidDerivedArtinAction k G g) :=
  (rfl)

/-- A transported standard generator is the conjugate of its actual derived autoequivalence. -/
theorem zigzagBraidDerivedArtinActionOfEquivalence_gen (i : V) :
    zigzagBraidDerivedArtinActionOfEquivalence k G e (ArtinGroup.gen G.coxeterMatrix i) =
      ((e.symm.trans (zigzagBraidDerivedAutoequivalence k G i)).trans
        e).toAutoequivalenceClass := by
  rw [zigzagBraidDerivedArtinActionOfEquivalence_apply, zigzagBraidDerivedArtinAction_gen,
    Equivalence.autoequivalenceClassCongr_toAutoequivalenceClass]

/-- The transported derived action equals a supplied target action exactly when the
supplied equivalence naturally intertwines their actual generator functors. -/
theorem zigzagBraidDerivedArtinActionOfEquivalence_eq_iff
    (ρ : ArtinGroup G.coxeterMatrix →* AutoequivalenceClass D) (F : V → (D ≌ D))
    (hF : ∀ i, ρ (ArtinGroup.gen G.coxeterMatrix i) = (F i).toAutoequivalenceClass) :
    zigzagBraidDerivedArtinActionOfEquivalence k G e = ρ ↔
      ∀ i, Nonempty (e.functor ⋙ (F i).functor ≅
        zigzagBraidDerivedFunctor k G i ⋙ e.functor) := by
  simpa only [zigzagBraidDerivedArtinActionOfEquivalence,
    zigzagBraidDerivedAutoequivalence_functor] using
    e.autoequivalenceClassCongr_comp_artin_eq_iff
      (zigzagBraidDerivedArtinAction k G) (zigzagBraidDerivedAutoequivalence k G)
      (zigzagBraidDerivedArtinAction_gen k G) ρ F hF

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Equivalence.Transport
public import TauCeti.GroupTheory.Coxeter.Graph

/-!
# Artin actions by autoequivalences

A family of autoequivalences indexed by the vertices of a simple graph determines an action of
the graph Artin group as soon as nonadjacent generators commute and adjacent generators satisfy
the three-term braid relation, both up to natural isomorphism.  Passing to
`TauCeti.AutoequivalenceClass` turns these natural isomorphisms into equalities, so the graph
Artin presentation supplies an honest group homomorphism.

This is the categorical form in which braid complexes act on a homotopy or derived category:
one first proves the generator functors are autoequivalences and constructs the two rank-two
natural isomorphisms, then applies `SimpleGraph.artinAutoequivalenceAction`.

For an arbitrary Coxeter matrix, two supplied Artin actions agree after transport through
a category equivalence precisely when that equivalence naturally intertwines their
specified generator functors.

## Main definitions

* `SimpleGraph.artinAutoequivalenceAction`: the action on natural-isomorphism classes of
  autoequivalences.

## Main results

* `SimpleGraph.artinAutoequivalenceAction_gen`: a standard Artin generator acts by the
  corresponding autoequivalence.
* `SimpleGraph.artinAutoequivalenceAction_gen_inv`: the inverse standard generator acts by the
  inverse autoequivalence.
-/

public section

noncomputable section

namespace SimpleGraph

open CategoryTheory TauCeti

universe u v w

variable {V : Type u} (G : SimpleGraph V) {C : Type v} [Category.{w} C]

/-- A family of autoequivalences satisfying the graph's commuting and braid relations up to
natural isomorphism determines a homomorphism from the graph Artin group to the group of
autoequivalence classes.

The relation hypotheses are parenthesized using `Equivalence.trans`.  Thus the adjacent relation
compares the functors represented by `Eᵢ ⋙ (Eⱼ ⋙ Eᵢ)` and `Eⱼ ⋙ (Eᵢ ⋙ Eⱼ)`; no strict
associativity of functor composition is assumed. -/
def artinAutoequivalenceAction (E : V → (C ≌ C))
    (commute : ∀ {i j}, i ≠ j → ¬G.Adj i j →
      Nonempty (((E i).trans (E j)).functor ≅ ((E j).trans (E i)).functor))
    (braid : ∀ {i j}, G.Adj i j →
      Nonempty (((E i).trans ((E j).trans (E i))).functor ≅
        ((E j).trans ((E i).trans (E j))).functor)) :
    ArtinGroup G.coxeterMatrix →* AutoequivalenceClass C :=
  G.artinGroupLift (fun i ↦ (E i).toAutoequivalenceClass)
    (fun {i j} hij hadj ↦ by
      calc
        (E i).toAutoequivalenceClass * (E j).toAutoequivalenceClass =
            ((E j).trans (E i)).toAutoequivalenceClass :=
          (Equivalence.toAutoequivalenceClass_trans (E j) (E i)).symm
        _ = ((E i).trans (E j)).toAutoequivalenceClass :=
          (Equivalence.toAutoequivalenceClass_eq_iff _ _).2
            (Nonempty.map Iso.symm (commute hij hadj))
        _ = (E j).toAutoequivalenceClass * (E i).toAutoequivalenceClass :=
          Equivalence.toAutoequivalenceClass_trans (E i) (E j))
    (fun {i j} hadj ↦ by
      calc
        (E i).toAutoequivalenceClass * (E j).toAutoequivalenceClass *
            (E i).toAutoequivalenceClass =
            ((E i).trans ((E j).trans (E i))).toAutoequivalenceClass := by
          rw [Equivalence.toAutoequivalenceClass_trans,
            Equivalence.toAutoequivalenceClass_trans]
        _ = ((E j).trans ((E i).trans (E j))).toAutoequivalenceClass :=
          (Equivalence.toAutoequivalenceClass_eq_iff _ _).2 (braid hadj)
        _ = (E j).toAutoequivalenceClass * (E i).toAutoequivalenceClass *
            (E j).toAutoequivalenceClass := by
          rw [Equivalence.toAutoequivalenceClass_trans,
            Equivalence.toAutoequivalenceClass_trans])

/-- The Artin action sends a standard generator to the class of its indexing
autoequivalence. -/
@[simp]
theorem artinAutoequivalenceAction_gen (E : V → (C ≌ C)) (commute braid) (i : V) :
    G.artinAutoequivalenceAction E commute braid (ArtinGroup.gen G.coxeterMatrix i) =
      (E i).toAutoequivalenceClass := by
  simp only [artinAutoequivalenceAction, artinGroupLift_gen]

/-- The inverse of a standard Artin generator acts by the inverse autoequivalence. -/
@[simp]
theorem artinAutoequivalenceAction_gen_inv (E : V → (C ≌ C)) (commute braid) (i : V) :
    G.artinAutoequivalenceAction E commute braid (ArtinGroup.gen G.coxeterMatrix i)⁻¹ =
      (E i).symm.toAutoequivalenceClass := by
  rw [map_inv, artinAutoequivalenceAction_gen,
    Equivalence.toAutoequivalenceClass_symm]

end SimpleGraph

namespace CategoryTheory

open TauCeti

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Transport of an Artin action agrees with a target action precisely when the supplied
equivalence naturally intertwines their generator representatives. -/
theorem Equivalence.comp_autoequivalenceClassCongr_eq_iff
    {B : Type*} {M : CoxeterMatrix B} (e : C ≌ D)
    (ρ₀ : ArtinGroup M →* AutoequivalenceClass C) (S : B → (C ≌ C))
    (hS : ∀ i, ρ₀ (ArtinGroup.gen M i) = (S i).toAutoequivalenceClass)
    (ρ : ArtinGroup M →* AutoequivalenceClass D) (F : B → (D ≌ D))
    (hF : ∀ i, ρ (ArtinGroup.gen M i) = (F i).toAutoequivalenceClass) :
    e.autoequivalenceClassCongr.toMonoidHom.comp ρ₀ = ρ ↔
      ∀ i, Nonempty (e.functor ⋙ (F i).functor ≅ (S i).functor ⋙ e.functor) := by
  constructor
  · intro h i
    apply (Equivalence.autoequivalenceClassCongr_eq_iff e _ _).1
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hS i, hF i] using
      DFunLike.congr_fun h (ArtinGroup.gen M i)
  · intro h
    apply ArtinGroup.hom_ext
    intro i
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hS i, hF i]
    exact (Equivalence.autoequivalenceClassCongr_eq_iff e _ _).2 (h i)

end CategoryTheory

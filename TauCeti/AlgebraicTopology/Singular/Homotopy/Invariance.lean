/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Basic

/-!
# Homotopy invariance of relative singular homology

A homotopy between maps of topological pairs induces a chain homotopy between the induced maps
of relative singular chain complexes, so homotopic maps of pairs induce the same map on relative
singular homology, and maps of pairs that are inverse to each other up to homotopy induce
isomorphisms on it.  This is the homotopy axiom of Eilenberg--Steenrod for the relative singular
theory.

The homotopy is transported to the singular simplicial sets of the two spaces, where the
compatibility of the two simplicial homotopies over the inclusion of the subspace descends the
chain homotopy to the relative chain complexes.  The absolute case is
`Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean` (F. Odermatt, J. Riou),
whose proof plan through `TopCat.Homotopy.toSSet` this file follows for pairs.

The source is Eilenberg--Steenrod, *Foundations of Algebraic Topology*, Chapter VII, where the
homotopy axiom is verified for the singular theory; see also Hatcher, *Algebraic Topology*, §2.1,
Theorem 2.10 and its relative form.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopPair.Homotopy

variable {P P' : TopPair.{w}} {f g : P ⟶ P'} (H : Homotopy f g)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

/-- A homotopy between maps of topological pairs induces a chain homotopy between the induced
maps of relative singular chain complexes. -/
@[no_expose]
def singularChainComplexMap :
    _root_.Homotopy (P.singularChainComplexMap f R) (P.singularChainComplexMap g R) :=
  H.toSSetPair.chainComplexMap R

lemma singularChainComplexMap_def :
    H.singularChainComplexMap R = H.toSSetPair.chainComplexMap R := (rfl)

@[reassoc (attr := simp)]
lemma singularChainComplexMap_hom (p q : ℕ) :
    (P.singularChainComplexπ R).f p ≫ (H.singularChainComplexMap R).hom p q =
      (H.fst.toSSet.chainComplexMap R).hom p q ≫ (P'.singularChainComplexπ R).f q :=
  H.toSSetPair.chainComplexMap_hom R p q

include H in
/-- Homotopic maps of topological pairs induce the same map on relative singular homology. -/
lemma congr_singularHomologyMap [CategoryWithHomology C] (n : ℕ) :
    P.singularHomologyMap f R n = P.singularHomologyMap g R n :=
  H.toSSetPair.congr_homologyMap R n

end TopPair.Homotopy

namespace TopPair

variable {P P' : TopPair.{w}} {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C]

/-- Maps of topological pairs which are inverse to each other up to homotopy induce isomorphisms
on relative singular homology. -/
lemma isIso_singularHomologyMap (f : P ⟶ P') (f' : P' ⟶ P) (H : Homotopy (f ≫ f') (𝟙 P))
    (H' : Homotopy (f' ≫ f) (𝟙 P')) (R : C) (n : ℕ) :
    IsIso (P.singularHomologyMap f R n) := by
  refine SSetPair.isIso_homologyMap _ (toSSetPair.map f') ?_ ?_ R n
  · rw [← Functor.map_comp, ← CategoryTheory.Functor.map_id]
    exact H.toSSetPair
  · rw [← Functor.map_comp, ← CategoryTheory.Functor.map_id]
    exact H'.toSSetPair

end TopPair

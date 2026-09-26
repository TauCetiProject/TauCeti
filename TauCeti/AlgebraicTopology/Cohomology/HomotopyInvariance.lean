/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-!
# Homotopy invariance of singular cohomology

Singular cochains are obtained from singular chains by applying `Hom(-, M)`, and an additive
functor carries chain homotopies to chain homotopies.  So the chain homotopy that a homotopy of
maps induces on singular chains gives a cochain homotopy on singular cochains, and homotopic
maps induce the same map on singular cohomology.  Maps that are inverse to each other up to
homotopy therefore induce isomorphisms on singular cohomology.  This is the homotopy axiom of
Eilenberg--Steenrod for the singular cohomology theory, in both its absolute and its relative
form.  The chain homotopies it is deduced from are Mathlib's `SSet.Homotopy.chainComplexMap`,
applied to the simplicial homotopy `TopCat.Homotopy.toSSet`, for a space, and
`TopPair.Homotopy.singularChainComplexMap` for a pair.  The homology counterparts of the results
below are `Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean`
(F. Odermatt, J. Riou) for a space and
`TauCeti/AlgebraicTopology/Singular/Homotopy/Invariance.lean` for a pair.

## Main results

* `TopCat.Homotopy.singularCochainComplexMap` and `TopPair.Homotopy.singularCochainComplexMap`:
  the cochain homotopy induced by a homotopy of maps of spaces, respectively of pairs.
* `TopCat.Homotopy.congr_singularCohomologyMap` and
  `TopPair.Homotopy.congr_singularCohomologyMap`: homotopic maps induce the same map on singular
  cohomology.
* `TopCat.isIso_singularCohomologyMap` and `TopPair.isIso_singularCohomologyMap`: a map with a
  homotopy inverse induces an isomorphism on singular cohomology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapter VII.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopCat.Homotopy

variable {X Y : TopCat.{w}} {f g : X ⟶ Y} (H : Homotopy f g)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)

/-- A homotopy between continuous maps induces a cochain homotopy between the induced maps of
singular cochain complexes. -/
@[no_expose]
def singularCochainComplexMap :
    _root_.Homotopy (singularCochainComplexMap (R := R) (k := k) (M := M) f)
      (singularCochainComplexMap g) :=
  (H.toSSet.chainComplexMap R).linearYonedaFunctorMap k M

/-- The cochain homotopy induced by a homotopy of continuous maps is precomposition with the
chain homotopy it induces on singular chains. -/
@[simp]
lemma singularCochainComplexMap_hom_apply (p q : ℕ) (x : (Y.singularCochainComplex R k M).X p) :
    ConcreteCategory.hom ((H.singularCochainComplexMap R k M).hom p q) x =
        (H.toSSet.chainComplexMap R).hom q p ≫ x :=
  (H.toSSet.chainComplexMap R).linearYonedaFunctorMap_hom_apply k M p q x

include H in
/-- Homotopic continuous maps induce the same map on singular cohomology. -/
lemma congr_singularCohomologyMap (n : ℕ) :
    TopCat.singularCohomologyMap (R := R) (k := k) (M := M) f n =
      TopCat.singularCohomologyMap g n :=
  (H.singularCochainComplexMap R k M).homologyMap_eq n

end TopCat.Homotopy

namespace TopCat

variable {X Y : TopCat.{w}} {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- Continuous maps which are inverse to each other up to homotopy induce isomorphisms on
singular cohomology. -/
lemma isIso_singularCohomologyMap (f : X ⟶ Y) (f' : Y ⟶ X) (H : Homotopy (f ≫ f') (𝟙 X))
    (H' : Homotopy (f' ≫ f) (𝟙 Y)) (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) f n) := by
  refine ⟨TopCat.singularCohomologyMap f' n, ?_, ?_⟩
  · rw [← singularCohomologyMap_comp, H'.congr_singularCohomologyMap R k M n,
      singularCohomologyMap_id]
  · rw [← singularCohomologyMap_comp, H.congr_singularCohomologyMap R k M n,
      singularCohomologyMap_id]

end TopCat

namespace TopPair.Homotopy

variable {P P' : TopPair.{w}} {f g : P ⟶ P'} (H : Homotopy f g)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)

/-- A homotopy between maps of topological pairs induces a cochain homotopy between the induced
maps of relative singular cochain complexes. -/
@[no_expose]
def singularCochainComplexMap :
    _root_.Homotopy (singularCochainComplexMap (R := R) (k := k) (M := M) f)
      (singularCochainComplexMap g) :=
  (H.singularChainComplexMap R).linearYonedaFunctorMap k M

/-- The cochain homotopy induced by a homotopy of maps of pairs is precomposition with the chain
homotopy it induces on relative singular chains. -/
@[simp]
lemma singularCochainComplexMap_hom_apply (p q : ℕ) (x : (P'.singularCochainComplex R k M).X p) :
    ConcreteCategory.hom ((H.singularCochainComplexMap R k M).hom p q) x =
        (H.singularChainComplexMap R).hom q p ≫ x :=
  (H.singularChainComplexMap R).linearYonedaFunctorMap_hom_apply k M p q x

include H in
/-- Homotopic maps of topological pairs induce the same map on relative singular cohomology. -/
lemma congr_singularCohomologyMap (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n =
      TopPair.singularCohomologyMap g n :=
  (H.singularCochainComplexMap R k M).homologyMap_eq n

end TopPair.Homotopy

namespace TopPair

variable {P P' : TopPair.{w}} {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- Maps of topological pairs which are inverse to each other up to homotopy induce isomorphisms
on relative singular cohomology. -/
lemma isIso_singularCohomologyMap (f : P ⟶ P') (f' : P' ⟶ P) (H : Homotopy (f ≫ f') (𝟙 P))
    (H' : Homotopy (f' ≫ f) (𝟙 P')) (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n) := by
  refine ⟨TopPair.singularCohomologyMap f' n, ?_, ?_⟩
  · rw [← singularCohomologyMap_comp, H'.congr_singularCohomologyMap R k M n,
      singularCohomologyMap_id]
  · rw [← singularCohomologyMap_comp, H.congr_singularCohomologyMap R k M n,
      singularCohomologyMap_id]

end TopPair

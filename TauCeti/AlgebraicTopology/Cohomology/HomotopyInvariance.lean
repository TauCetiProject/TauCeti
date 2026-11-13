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
* `TopPair.isIso_singularCohomologyMap_ofSubsetMap_id_of_homotopy`: enlarging the subspace of a
  pair to a neighbourhood which deforms back into it does not change relative cohomology.
* `ContinuousMap.HomotopyEquiv.isIso_singularCohomologyMap` and
  `ContinuousMap.HomotopyEquiv.singularCohomologyIso`: the induced isomorphism on singular
  cohomology for a bundled homotopy equivalence of spaces.

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

namespace ContinuousMap.HomotopyEquiv

variable {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
  (e : ContinuousMap.HomotopyEquiv X Y)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)

/-- A homotopy equivalence induces isomorphisms on singular cohomology in every degree. -/
lemma isIso_singularCohomologyMap (n : ℕ) :
    IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) (TopCat.ofHom e.toFun) n) :=
  TopCat.isIso_singularCohomologyMap _ (TopCat.ofHom e.invFun) e.left_inv.some e.right_inv.some
    R k M n

/-- A homotopy equivalence induces an isomorphism on singular cohomology in every degree, with
forward map induced by pullback along `e` and inverse induced by pullback along `e.symm`. -/
@[no_expose]
def singularCohomologyIso (n : ℕ) :
    (TopCat.of Y).singularCohomology R k M n ≅ (TopCat.of X).singularCohomology R k M n where
  hom := TopCat.singularCohomologyMap (TopCat.ofHom e.toFun) n
  inv := TopCat.singularCohomologyMap (TopCat.ofHom e.invFun) n
  hom_inv_id := by
    rw [← TopCat.singularCohomologyMap_comp, ← TopCat.singularCohomologyMap_id]
    exact TopCat.Homotopy.congr_singularCohomologyMap e.right_inv.some R k M n
  inv_hom_id := by
    rw [← TopCat.singularCohomologyMap_comp, ← TopCat.singularCohomologyMap_id]
    exact TopCat.Homotopy.congr_singularCohomologyMap e.left_inv.some R k M n

/-- The forward map of `ContinuousMap.HomotopyEquiv.singularCohomologyIso` is pullback along `e`. -/
@[simp]
lemma singularCohomologyIso_hom (n : ℕ) :
    (e.singularCohomologyIso R k M n).hom =
      TopCat.singularCohomologyMap (TopCat.ofHom e.toFun) n := (rfl)

/-- The inverse map of `ContinuousMap.HomotopyEquiv.singularCohomologyIso` is pullback along
`e.symm`. -/
@[simp]
lemma singularCohomologyIso_inv (n : ℕ) :
    (e.singularCohomologyIso R k M n).inv =
      TopCat.singularCohomologyMap (TopCat.ofHom e.invFun) n := (rfl)

end ContinuousMap.HomotopyEquiv

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

/-- **Enlarging the subspace along a deformation.** Let `B ⊆ N` be subsets of `X` and let `H` be a
homotopy from the identity of `X` to a map `ρ` carrying `N` into `B`.  If `H` keeps `B` inside `B`
and `N` inside `N` at every time, the inclusion `(X, B) ⟶ (X, N)` induces isomorphisms on relative
singular cohomology: `ρ` is a homotopy inverse as a map of pairs.  This is the cohomology form of
`TopPair.isIso_singularHomologyMap_ofSubsetMap_id_of_homotopy`. -/
lemma isIso_singularCohomologyMap_ofSubsetMap_id_of_homotopy {X : TopCat.{w}} {B N : Set X}
    (hBN : Set.MapsTo (𝟙 X) B N) {ρ : X ⟶ X} (H : (TopCat.Hom.hom (𝟙 X)).Homotopy ρ.hom)
    (hB : ∀ (τ : unitInterval) (x : X), x ∈ B → H (τ, x) ∈ B)
    (hN : ∀ (τ : unitInterval) (x : X), x ∈ N → H (τ, x) ∈ N) (hρ : Set.MapsTo ρ N B) (R : C)
    (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (ofSubsetMap (𝟙 X) hBN) n) := by
  refine isIso_singularCohomologyMap _ (ofSubsetMap ρ hρ) ?_ ?_ R k M n
  · rw [← ofSubsetMap_comp _ _ hBN hρ (hρ.comp hBN), ← ofSubsetMap_id (B := B) fun _ hx ↦ hx]
    simpa only [Category.id_comp] using (ofSubsetHomotopy H hB).symm
  · rw [← ofSubsetMap_comp _ _ hρ hBN (hBN.comp hρ), ← ofSubsetMap_id (B := N) fun _ hx ↦ hx]
    simpa only [Category.comp_id] using (ofSubsetHomotopy H hN).symm

end TopPair

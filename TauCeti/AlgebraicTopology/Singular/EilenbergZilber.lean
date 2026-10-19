/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.EilenbergZilber
public import TauCeti.AlgebraicTopology.Singular.Shuffle

/-!
# The Eilenberg–Zilber theorem for singular chains

For topological spaces `X` and `Y`, the Alexander–Whitney map
`C(X × Y; R ⊗ S) ⟶ C(X; R) ⊗ C(Y; S)` on singular chains is a chain homotopy equivalence with
homotopy inverse the shuffle map (`TopCat.eilenbergZilberHomotopyEquiv`).

The composite `shuffle ∘ AW` is the simplicial composite for `Sing X` and `Sing Y`, conjugated by
the canonical isomorphism `Sing (X × Y) ≅ Sing X × Sing Y` (`TopCat.alexanderWhitney_shuffle`), so
its homotopy to the identity (`TopCat.alexanderWhitneyShuffleHomotopy`) is the simplicial one,
`SSet.alexanderWhitneyShuffleHomotopy`, transported along this isomorphism.  The composite
`AW ∘ shuffle` is the simplicial composite itself (`TopCat.shuffle_alexanderWhitney`), so its
homotopy to the identity (`TopCat.shuffleAlexanderWhitneyHomotopy`) is
`SSet.shuffleAlexanderWhitneyHomotopy`.

## References

* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

/-- **The Eilenberg–Zilber homotopy on singular chains**: the Alexander–Whitney map
`C(X × Y; R ⊗ S) ⟶ C(X; R) ⊗ C(Y; S)` followed by the shuffle map is chain homotopic to the
identity of `C(X × Y; R ⊗ S)`. -/
def alexanderWhitneyShuffleHomotopy (X Y : TopCat.{w}) (R S : C) :
    Homotopy (alexanderWhitney X Y R S ≫ shuffle X Y R S) (𝟙 _) :=
  (Homotopy.ofEq (by simp only [alexanderWhitney_shuffle, Category.assoc])).trans <|
    (((SSet.alexanderWhitneyShuffleHomotopy (toSSet.obj X) (toSSet.obj Y) R S).compLeft
      (SSet.chainComplexMap (CartesianMonoidalCategory.prodComparison toSSet X Y)
        (R ⊗ S))).compRight
        (SSet.chainComplexMap (Functor.LaxMonoidal.μ toSSet X Y) (R ⊗ S))).trans <|
      -- the two comparison maps between `Sing (X × Y)` and `Sing X × Sing Y` are inverse
      Homotopy.ofEq <| by
        rw [Category.comp_id, ← Functor.map_comp,
          ← Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory, Functor.Monoidal.δ_μ,
          CategoryTheory.Functor.map_id]

/-- **The Eilenberg–Zilber homotopy on singular chains**: the shuffle map
`C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)` followed by the Alexander–Whitney map is chain homotopic to
the identity of `C(X; R) ⊗ C(Y; S)`. -/
def shuffleAlexanderWhitneyHomotopy (X Y : TopCat.{w}) (R S : C) :
    Homotopy (shuffle X Y R S ≫ alexanderWhitney X Y R S) (𝟙 _) :=
  (Homotopy.ofEq (shuffle_alexanderWhitney X Y R S)).trans
    (SSet.shuffleAlexanderWhitneyHomotopy (toSSet.obj X) (toSSet.obj Y) R S)

/-- **The Eilenberg–Zilber theorem for singular chains**: the Alexander–Whitney map
`C(X × Y; R ⊗ S) ⟶ C(X; R) ⊗ C(Y; S)` is a chain homotopy equivalence, with homotopy inverse the
shuffle map. -/
def eilenbergZilberHomotopyEquiv (X Y : TopCat.{w}) (R S : C) :
    HomotopyEquiv ((toSSet.obj (X ⊗ Y)).chainComplex (R ⊗ S))
      ((toSSet.obj X).chainComplex R ⊗ (toSSet.obj Y).chainComplex S) where
  hom := alexanderWhitney X Y R S
  inv := shuffle X Y R S
  homotopyHomInvId := alexanderWhitneyShuffleHomotopy X Y R S
  homotopyInvHomId := shuffleAlexanderWhitneyHomotopy X Y R S

@[simp]
lemma eilenbergZilberHomotopyEquiv_hom (X Y : TopCat.{w}) (R S : C) :
    (eilenbergZilberHomotopyEquiv X Y R S).hom = alexanderWhitney X Y R S :=
  (rfl)

@[simp]
lemma eilenbergZilberHomotopyEquiv_inv (X Y : TopCat.{w}) (R S : C) :
    (eilenbergZilberHomotopyEquiv X Y R S).inv = shuffle X Y R S :=
  (rfl)

end TopCat

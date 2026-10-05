/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.EilenbergZilber
public import TauCeti.AlgebraicTopology.Singular.Shuffle

/-!
# The shuffle map after the Alexander–Whitney map on singular chains

For topological spaces `X` and `Y`, the Alexander–Whitney map
`C(X × Y; R ⊗ S) ⟶ C(X; R) ⊗ C(Y; S)` on singular chains followed by the shuffle map is chain
homotopic to the identity of `C(X × Y; R ⊗ S)` (`TopCat.alexanderWhitneyShuffleHomotopy`).

The singular composite is the simplicial composite for `Sing X` and `Sing Y`, conjugated by the
canonical isomorphism `Sing (X × Y) ≅ Sing X × Sing Y` (`TopCat.alexanderWhitney_shuffle`), so the
homotopy is the simplicial one, `SSet.alexanderWhitneyShuffleHomotopy`, transported along this
isomorphism.

## References

* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology

universe w v u

namespace TopCat

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

end TopCat

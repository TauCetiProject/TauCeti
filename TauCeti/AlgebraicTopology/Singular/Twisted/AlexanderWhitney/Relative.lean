/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.AlexanderWhitney.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality

/-!
# The relative Alexander–Whitney diagonal with local coefficients

For a pair `(X, A)`, the front face of a simplex of `A` lies in `A`, so the twisted
Alexander–Whitney diagonal followed by the quotient onto relative chains in its first factor
descends to the relative diagonal `C(X, A; L ⊗ K) ⟶ C(X, A; L) ⊗ C(X; K)`
(`TopPair.twistedAlexanderWhitneyDiagonal`). It supplies the diagonal for cap products with
relative cochains.

## Main definitions and results

* `TopPair.twistedAlexanderWhitneyDiagonal`: the relative twisted diagonal, characterized by
  `TopPair.twistedChainComplexπ_twistedAlexanderWhitneyDiagonal`.
* `TopPair.twistedAlexanderWhitneyDiagonal_naturality`: it is natural in both local coefficient
  systems.
* `TopPair.twistedAlexanderWhitneyDiagonal_space_naturality`: it is natural in maps of pairs.

## References

* A. Hatcher, *Algebraic Topology*, Sections 3.3 and 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Chapters VII–VIII.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe v w

namespace TopPair

open TauCeti TauCeti.LocalCoefficientSystem

variable {R : Type (max v w)} [CommRing R] (P : TopPair.{v})
  (L K : LocalCoefficientSystem.{max v w, v, max v w} R P.fst)

/-- The twisted Alexander–Whitney diagonal, followed by the quotient onto relative chains in its
first factor, vanishes on the chains of the subspace: the front face of a simplex of the subspace
lies in the subspace. -/
private lemma twistedChainComplexMap_twistedAlexanderWhitneyDiagonal_twistedChainComplexπ :
    LocalCoefficientSystem.twistedChainComplexMap P.map (L ⊗ K) ≫
      L.twistedAlexanderWhitneyDiagonal K ≫
        (P.twistedChainComplexπ L ⊗ₘ 𝟙 K.twistedChainComplex) = 0 := by
  have h₀ : (0 : ((LocalCoefficientSystem.pullback P.map.hom).obj L).twistedChainComplex ⟶
      P.twistedChainComplex L) ⊗ₘ
        (LocalCoefficientSystem.twistedChainComplexMap P.map K ≫ 𝟙 K.twistedChainComplex) = 0 :=
    HomologicalComplex.zero_tensorHom _
  rw [twistedAlexanderWhitneyDiagonal_space_naturality_assoc, tensorHom_comp_tensorHom,
    P.twistedChainComplexMap_comp_twistedChainComplexπ L, h₀, comp_zero, comp_zero]

/-- **The relative twisted Alexander–Whitney diagonal** `C(X, A; L ⊗ K) ⟶ C(X, A; L) ⊗ C(X; K)` of
a pair `(X, A)`: the twisted diagonal, read in relative chains in its first factor, which descends
to the relative chains twisted by `L ⊗ K`. -/
def twistedAlexanderWhitneyDiagonal :
    P.twistedChainComplex (L ⊗ K) ⟶ P.twistedChainComplex L ⊗ K.twistedChainComplex :=
  P.twistedChainComplexDesc (L ⊗ K)
    (L.twistedAlexanderWhitneyDiagonal K ≫ (P.twistedChainComplexπ L ⊗ₘ 𝟙 K.twistedChainComplex))
    (twistedChainComplexMap_twistedAlexanderWhitneyDiagonal_twistedChainComplexπ P L K)

/-- The relative diagonal is the absolute diagonal read in relative chains. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_twistedAlexanderWhitneyDiagonal :
    P.twistedChainComplexπ (L ⊗ K) ≫ P.twistedAlexanderWhitneyDiagonal L K =
      L.twistedAlexanderWhitneyDiagonal K ≫
        (P.twistedChainComplexπ L ⊗ₘ 𝟙 K.twistedChainComplex) :=
  P.twistedChainComplexπ_comp_twistedChainComplexDesc _ _ _

variable {P L K} {L' K' : LocalCoefficientSystem.{max v w, v, max v w} R P.fst}

/-- The relative diagonal commutes with changes of both local coefficient systems. -/
@[reassoc]
lemma twistedAlexanderWhitneyDiagonal_naturality (η : L ⟶ L') (θ : K ⟶ K') :
    P.twistedChainComplexCoefficientMap (η ⊗ₘ θ) ≫ P.twistedAlexanderWhitneyDiagonal L' K' =
      P.twistedAlexanderWhitneyDiagonal L K ≫
        (P.twistedChainComplexCoefficientMap η ⊗ₘ
          LocalCoefficientSystem.twistedChainComplexCoefficientMap θ) := by
  ext : 1
  simp [twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
    LocalCoefficientSystem.twistedAlexanderWhitneyDiagonal_naturality_assoc,
    tensorHom_comp_tensorHom, -tensorHom_id]

section Space

variable {Q : TopPair.{v}} (f : P ⟶ Q)
  (L K : LocalCoefficientSystem.{max v w, v, max v w} R Q.fst)

/-- **The relative diagonal is natural in maps of pairs**: for `f : (X, A) ⟶ (Y, B)`, pushing
relative chains forward along `f` and applying the diagonal of `(Y, B)` is applying the diagonal of
`(X, A)`, with the pulled-back coefficient systems, and pushing both factors forward. -/
@[reassoc]
lemma twistedAlexanderWhitneyDiagonal_space_naturality :
    twistedChainComplexMap f (L ⊗ K) ≫ Q.twistedAlexanderWhitneyDiagonal L K =
      P.twistedChainComplexCoefficientMap (pullbackTensorIso (Hom.fst f).hom L K).hom ≫
        P.twistedAlexanderWhitneyDiagonal
          ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L)
          ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj K) ≫
          (twistedChainComplexMap f L ⊗ₘ
            LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) K) := by
  ext : 1
  rw [twistedChainComplexπ_comp_twistedChainComplexMap_assoc,
    twistedChainComplexπ_twistedAlexanderWhitneyDiagonal,
    LocalCoefficientSystem.twistedAlexanderWhitneyDiagonal_space_naturality_assoc,
    twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
    twistedChainComplexπ_twistedAlexanderWhitneyDiagonal_assoc, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom, twistedChainComplexπ_comp_twistedChainComplexMap, Category.id_comp,
    Category.comp_id]

end Space

end TopPair

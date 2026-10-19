/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Adjacent.Contraction
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Commuting
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Inverse.Forward
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Inverse.Reverse
public import TauCeti.Algebra.Homology.Bifunctor.Homotopy

/-!
# Transfer of the zigzag braid relations through a supplied equivalence

The zigzag braid complexes satisfy the Khovanov-Seidel relations: the two one-sided
inverse products are homotopy equivalent to the regular bimodule concentrated in
cohomological degree zero, the nonadjacent factors commute, and the adjacent factors
satisfy the braid relation. This file packages the relations for an arbitrary family of
complexes with prescribed inverses and unit, and transfers them through a supplied
additive functor on graded modules.

The transfer is driven by the pointwise homotopy-monoidal datum `η` of the prolongation
`Φ` of the additive functor `H` to complexes of graded modules: for every pair of
complexes `X` and `Y` the datum supplies a homotopy equivalence
`η X Y : T (Φ X) (Φ Y) ≃ Φ (T X Y)` comparing the prolonged tensor product with the
prolongation of the tensor product, together with the unit datum `ε : Φ Z₀ ≃ Z₀`
comparing the prolonged unit complex with the unit complex. With supplied homotopy
equivalences `a i : Φ (B i) ≃ C i` and `a' i : Φ (B' i) ≃ C' i`, these transfer the
three Khovanov-Seidel relations to the family `C` with prescribed inverses `C'`.

The pointwise datum `η` records the monoidality of the prolongation up to chain
homotopy; the braid relation is obtained by applying it twice around the adjacent
relation. Naturality of the transferred relations up to chain homotopy, which is needed
to assemble an action of the Artin braid group on a conjugated category, is deliberately
not claimed here; the action packaging is a separate roadmap layer.

## References

* M. Khovanov and P. Seidel, *Quivers, Floer cohomology, and braid group actions*,
  [arXiv:math/0006056](https://arxiv.org/abs/math/0006056).
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

/-- The regular graded zigzag bimodule concentrated in cohomological degree zero: the
common target of the two one-sided inverse-product equivalences of the braid family. -/
abbrev zigzagBraidUnitComplex :
    HomologicalComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
      (ComplexShape.up ℤ) :=
  (HomologicalComplex.single (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
    (ComplexShape.up ℤ) 0).obj (zigzagGradedBimodule k G)

local notation "F" => zigzagBimoduleTensor k G
local notation "Z₀" => zigzagBraidUnitComplex k G
local notation "c" => ComplexShape.up ℤ
local notation "T" => fun X Y => HomologicalComplex.mapBifunctor X Y F c
local notation "B" => zigzagBraidComplex k G
local notation "B'" => zigzagBraidInverseComplex k G

/-- The three Khovanov-Seidel relations for a family `C` of complexes of graded modules
with prescribed inverses `C'`: both one-sided inverse products `C i ⊗ C' i` and
`C' i ⊗ C i` are homotopy equivalent to the unit complex, the nonadjacent factors
commute up to chain homotopy, and the adjacent factors satisfy the braid relation up to
chain homotopy. -/
structure KhovanovSeidelRelations
    (C C' : V → HomologicalComplex (GradedModuleCat.{max u w}
      (zigzagEnvelopingGrading k G).piece) (ComplexShape.up ℤ)) where
  /-- The forward inverse product `C i ⊗ C' i` is homotopy equivalent to the unit. -/
  inverseForward (i : V) : HomotopyEquiv (T (C i) (C' i)) Z₀
  /-- The reverse inverse product `C' i ⊗ C i` is homotopy equivalent to the unit. -/
  inverseReverse (i : V) : HomotopyEquiv (T (C' i) (C i)) Z₀
  /-- Nonadjacent factors commute up to chain homotopy. -/
  commute (i j : V) : i ≠ j → ¬ G.Adj i j →
    HomotopyEquiv (T (C i) (C j)) (T (C j) (C i))
  /-- Adjacent factors satisfy the braid relation up to chain homotopy. -/
  braid {i j : V} : G.Adj j i →
    HomotopyEquiv (T (T (C i) (C j)) (C i)) (T (T (C j) (C i)) (C j))

/-- The zigzag braid complexes satisfy the Khovanov-Seidel relations, with the inverse
complexes as prescribed inverses and the regular bimodule concentrated in cohomological
degree zero as the unit. -/
def zigzagBraidComplexRelations :
    KhovanovSeidelRelations k G (zigzagBraidComplex k G) (zigzagBraidInverseComplex k G) where
  inverseForward i := zigzagBraidComplexTensorInverseHomotopyEquiv k G i
  inverseReverse i := zigzagBraidInverseTensorComplexHomotopyEquiv k G i
  commute := zigzagBraidComplexTensorCommHomotopyEquiv k G
  braid h := zigzagBraidComplexAdjacentHomotopyEquiv k G h

section Transfer

variable (H : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece ⥤
  GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) [H.Additive]

/-- The prolongation of the additive functor `H` on graded zigzag modules to the category
of complexes of graded zigzag modules. -/
abbrev zigzagBraidProlongation :
    HomologicalComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) c ⥤
    HomologicalComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) c :=
  H.mapHomologicalComplex c

/-- The complex prolonged from `X` by the prolongation of the additive functor `H`. -/
abbrev zigzagBraidProlonged (X : HomologicalComplex (GradedModuleCat.{max u w}
    (zigzagEnvelopingGrading k G).piece) c) :
    HomologicalComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) c :=
  (zigzagBraidProlongation k G H).obj X

/-- The pointwise homotopy-monoidal datum of the prolongation of `H`: for every pair of
complexes `X` and `Y` of graded zigzag modules, a homotopy equivalence
`T (Φ X) (Φ Y) ≃ Φ (T X Y)` comparing the prolonged tensor product with the prolongation
of the tensor product. -/
abbrev zigzagBraidMonoidalDatum := ∀ (X Y : HomologicalComplex (GradedModuleCat.{max u w}
    (zigzagEnvelopingGrading k G).piece) c),
  [HomologicalComplex.HasMapBifunctor X Y F c] →
  [HomologicalComplex.HasMapBifunctor (zigzagBraidProlonged k G H X)
    (zigzagBraidProlonged k G H Y) F c] →
  HomotopyEquiv (T (zigzagBraidProlonged k G H X) (zigzagBraidProlonged k G H Y))
    (zigzagBraidProlonged k G H (T X Y))

/-- Transfer of the forward inverse relation of the zigzag braid complexes through the
supplied equivalences: the tensor product `C i ⊗ C' i` is homotopy equivalent to the
unit complex. -/
def zigzagBraidInverseForwardTransfer (i : V)
    {C C' : V → HomologicalComplex (GradedModuleCat.{max u w}
      (zigzagEnvelopingGrading k G).piece) c}
    (η : zigzagBraidMonoidalDatum k G H)
    (a : ∀ i, HomotopyEquiv (zigzagBraidProlonged k G H (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv (zigzagBraidProlonged k G H (B' i)) (C' i))
    (ε : HomotopyEquiv (zigzagBraidProlonged k G H Z₀) Z₀) :
    HomotopyEquiv (T (C i) (C' i)) Z₀ :=
  (HomotopyEquiv.mapBifunctor F c (a i).symm (a' i).symm).trans
    ((η (B i) (B' i)).trans
      ((H.mapHomotopyEquiv (zigzagBraidComplexTensorInverseHomotopyEquiv k G i)).trans ε))

/-- Transfer of the reverse inverse relation of the zigzag braid complexes through the
supplied equivalences: the tensor product `C' i ⊗ C i` is homotopy equivalent to the
unit complex. -/
def zigzagBraidInverseReverseTransfer (i : V)
    {C C' : V → HomologicalComplex (GradedModuleCat.{max u w}
      (zigzagEnvelopingGrading k G).piece) c}
    (η : zigzagBraidMonoidalDatum k G H)
    (a : ∀ i, HomotopyEquiv (zigzagBraidProlonged k G H (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv (zigzagBraidProlonged k G H (B' i)) (C' i))
    (ε : HomotopyEquiv (zigzagBraidProlonged k G H Z₀) Z₀) :
    HomotopyEquiv (T (C' i) (C i)) Z₀ :=
  (HomotopyEquiv.mapBifunctor F c (a' i).symm (a i).symm).trans
    ((η (B' i) (B i)).trans
      ((H.mapHomotopyEquiv (zigzagBraidInverseTensorComplexHomotopyEquiv k G i)).trans ε))

/-- Transfer of the commutation relation of the zigzag braid complexes through the
supplied equivalences: the tensor products `C i ⊗ C j` and `C j ⊗ C i` are homotopy
equivalent for nonadjacent vertices. -/
def zigzagBraidCommuteTransfer (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j)
    {C : V → HomologicalComplex (GradedModuleCat.{max u w}
      (zigzagEnvelopingGrading k G).piece) c}
    (η : zigzagBraidMonoidalDatum k G H)
    (a : ∀ i, HomotopyEquiv (zigzagBraidProlonged k G H (B i)) (C i)) :
    HomotopyEquiv (T (C i) (C j)) (T (C j) (C i)) :=
  (HomotopyEquiv.mapBifunctor F c (a i).symm (a j).symm).trans
    ((η (B i) (B j)).trans
      ((H.mapHomotopyEquiv (zigzagBraidComplexTensorCommHomotopyEquiv k G i j hij hadj)).trans
        (((η (B j) (B i)).symm).trans
          (HomotopyEquiv.mapBifunctor F c (a j) (a i)))))

/-- The first conjugation step of the transferred braid relation: the triple tensor
product of the supplied family `C` is compared with the triple tensor product of the
prolonged braid complexes. -/
def zigzagBraidAdjacentLeftConj {i j : V}
    {C : V → HomologicalComplex (GradedModuleCat.{max u w}
      (zigzagEnvelopingGrading k G).piece) c}
    (a : ∀ i, HomotopyEquiv (zigzagBraidProlonged k G H (B i)) (C i)) :
    HomotopyEquiv (T (T (C i) (C j)) (C i))
      (T (T (zigzagBraidProlonged k G H (B i)) (zigzagBraidProlonged k G H (B j)))
        (zigzagBraidProlonged k G H (B i))) :=
  HomotopyEquiv.mapBifunctor F c
    (HomotopyEquiv.mapBifunctor F c (a i).symm (a j).symm) (a i).symm

/-- The first bridge step of the transferred braid relation: the prolonged tensor
product of two prolonged braid complexes is compared with the prolongation of the tensor
product of the braid complexes. -/
def zigzagBraidAdjacentBridgeLeft {i j : V}
    (η : zigzagBraidMonoidalDatum k G H) :
    HomotopyEquiv
      (T (T (zigzagBraidProlonged k G H (B i)) (zigzagBraidProlonged k G H (B j)))
        (zigzagBraidProlonged k G H (B i)))
      (zigzagBraidProlonged k G H (T (T (B i) (B j)) (B i))) :=
  (HomotopyEquiv.mapBifunctor F c (η (B i) (B j))
    (HomotopyEquiv.refl (zigzagBraidProlonged k G H (B i)))).trans
    (η (T (B i) (B j)) (B i))

/-- The middle step of the transferred braid relation: the prolonged adjacent braid
relation of the zigzag braid complexes. -/
def zigzagBraidAdjacentMiddle {i j : V} (h : G.Adj j i) :
    HomotopyEquiv (zigzagBraidProlonged k G H (T (T (B i) (B j)) (B i)))
      (zigzagBraidProlonged k G H (T (T (B j) (B i)) (B j))) :=
  H.mapHomotopyEquiv
    (zigzagBraidComplexAdjacentHomotopyEquiv (k := k) (G := G) (i := i) (j := j) h)

/-- The second bridge step of the transferred braid relation: the prolongation of the
tensor product of the braid complexes is compared with the tensor product of the
prolonged braid complexes. -/
def zigzagBraidAdjacentBridgeRight {i j : V}
    (η : zigzagBraidMonoidalDatum k G H) :
    HomotopyEquiv (zigzagBraidProlonged k G H (T (T (B j) (B i)) (B j)))
      (T (T (zigzagBraidProlonged k G H (B j)) (zigzagBraidProlonged k G H (B i)))
        (zigzagBraidProlonged k G H (B j))) :=
  ((HomotopyEquiv.mapBifunctor F c (η (B j) (B i))
    (HomotopyEquiv.refl (zigzagBraidProlonged k G H (B j)))).trans
    (η (T (B j) (B i)) (B j))).symm

/-- The last conjugation step of the transferred braid relation: the triple tensor
product of the prolonged braid complexes is compared with the triple tensor product of
the supplied family `C`. -/
def zigzagBraidAdjacentRightConj {i j : V}
    {C : V → HomologicalComplex (GradedModuleCat.{max u w}
      (zigzagEnvelopingGrading k G).piece) c}
    (a : ∀ i, HomotopyEquiv (zigzagBraidProlonged k G H (B i)) (C i)) :
    HomotopyEquiv
      (T (T (zigzagBraidProlonged k G H (B j)) (zigzagBraidProlonged k G H (B i)))
        (zigzagBraidProlonged k G H (B j)))
      (T (T (C j) (C i)) (C j)) :=
  HomotopyEquiv.mapBifunctor F c
    (HomotopyEquiv.mapBifunctor F c (a j) (a i)) (a j)

/-- Transfer of the braid relation of the zigzag braid complexes through the supplied
equivalences: the triple tensor products `C i ⊗ C j ⊗ C i` and `C j ⊗ C i ⊗ C j` are
homotopy equivalent at adjacent vertices. -/
def zigzagBraidAdjacentTransfer {i j : V} (h : G.Adj j i)
    {C : V → HomologicalComplex (GradedModuleCat.{max u w}
      (zigzagEnvelopingGrading k G).piece) c}
    (η : zigzagBraidMonoidalDatum k G H)
    (a : ∀ i, HomotopyEquiv (zigzagBraidProlonged k G H (B i)) (C i)) :
    HomotopyEquiv (T (T (C i) (C j)) (C i)) (T (T (C j) (C i)) (C j)) :=
  (zigzagBraidAdjacentLeftConj k G H a).trans
    ((zigzagBraidAdjacentBridgeLeft k G H η).trans
      ((zigzagBraidAdjacentMiddle k G H h).trans
        ((zigzagBraidAdjacentBridgeRight k G H η).trans
          (zigzagBraidAdjacentRightConj k G H a))))

/-- Transfer of the Khovanov-Seidel relations of the zigzag braid complexes through a
supplied equivalence. For an additive functor `H` on graded zigzag modules whose
prolongation `zigzagBraidProlongation k G H` carries the pointwise homotopy-monoidal
datum `η` (homotopy equivalences `T (Φ X) (Φ Y) ≃ Φ (T X Y)`), the unit datum
`ε : Φ Z₀ ≃ Z₀`, and supplied homotopy equivalences `a i : Φ (B i) ≃ C i` and
`a' i : Φ (B' i) ≃ C' i`, the family `C` satisfies the Khovanov-Seidel relations with
inverses `C'`. -/
def zigzagBraidRelationsTransfer
    (η : zigzagBraidMonoidalDatum k G H)
    (ε : HomotopyEquiv (zigzagBraidProlonged k G H Z₀) Z₀)
    {C C' : V → HomologicalComplex (GradedModuleCat.{max u w}
      (zigzagEnvelopingGrading k G).piece) c}
    (a : ∀ i, HomotopyEquiv (zigzagBraidProlonged k G H (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv (zigzagBraidProlonged k G H (B' i)) (C' i)) :
    KhovanovSeidelRelations k G C C' where
  inverseForward i := zigzagBraidInverseForwardTransfer k G H i η a a' ε
  inverseReverse i := zigzagBraidInverseReverseTransfer k G H i η a a' ε
  commute i j hij hadj := zigzagBraidCommuteTransfer k G H i j hij hadj η a
  braid h := zigzagBraidAdjacentTransfer k G H h η a

/-- The prolongation images of the zigzag braid complexes satisfy the Khovanov-Seidel
relations: the conjugated version of the transfer theorem, obtained with the identity
supplied equivalences. -/
def zigzagBraidComplexProlongationRelations
    (η : zigzagBraidMonoidalDatum k G H)
    (ε : HomotopyEquiv (zigzagBraidProlonged k G H Z₀) Z₀) :
    KhovanovSeidelRelations k G
      (fun i => zigzagBraidProlonged k G H (B i))
      (fun i => zigzagBraidProlonged k G H (B' i)) :=
  zigzagBraidRelationsTransfer k G H η ε (fun _ => HomotopyEquiv.refl _)
    (fun _ => HomotopyEquiv.refl _)

end Transfer

end TauCeti

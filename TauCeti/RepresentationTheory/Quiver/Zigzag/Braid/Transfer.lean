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
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Unit
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Unit
public import TauCeti.Algebra.Homology.Bifunctor.Homotopy

/-!
# A monoidal transfer principle for the Khovanov-Seidel braid relations

The zigzag braid complexes satisfy the Khovanov-Seidel relations: the two one-sided inverse
products are homotopy equivalent to the regular graded bimodule concentrated in cohomological
degree zero, the nonadjacent factors commute up to chain homotopy, and the adjacent factors
satisfy the braid relation up to chain homotopy.

This file states those relations for an arbitrary family of complexes in a *graded bimodule
setting* and proves a transfer principle between two such settings. A graded bimodule setting
is a graded algebra `A` with an internal grading `Ξ`: its graded bimodules are the graded
modules over the enveloping grading `Ξ.tensorProduct Ξ.opposite`, they are combined by the
balanced bimodule tensor `GradedBimoduleTensor`, and the unit complex of the setting is
`GradedBimoduleUnitComplex k Ξ`, the regular graded bimodule
`GradedModuleCat.bimoduleUnit Ξ` placed in cohomological degree zero. The setting of the
zigzag braid complexes is the setting of the zigzag algebra with its signed path-length
grading; a second setting, over a second graded algebra, is what a transfer reaches.

`KhovanovSeidelRelations` records the three relations for a family `C` of complexes with
prescribed inverses `C'` in a graded bimodule setting. The unit of the relations is the
unit complex *of that setting*; it is not a free parameter, so the two inverse relations are
statements about the actual unit of the tensor. For the zigzag setting, the regular graded
zigzag bimodule is that unit: `zigzagBraidUnitComplexEquiv` identifies the zigzag unit complex
with the unit complex of the zigzag setting.

`KhovanovSeidelRelationsTransfer` is the transfer principle. A functor `H` from a source
graded bimodule setting to a target graded bimodule setting, together with

* a pointwise homotopy-monoidal datum `η`, a homotopy equivalence for every pair of source
  complexes `X` and `Y` comparing the target tensor product of the prolonged complexes with
  the prolongation of the source tensor product, and
* a unit datum `ε`, a homotopy equivalence comparing the prolonged source unit complex with
  the target unit complex,

transports the three relations from the source setting to the target setting, provided the
prolonged source complexes are identified with a target family by the homotopy equivalences
`a` and `a'`. The two settings need not agree: the target is a second graded algebra, and
`H` need not be an equivalence.

## Scope

The principle is stated for a functor `H` of *bimodule categories*, applied to complexes
degree by degree through `H.mapHomologicalComplex`. This is the shape of a Morita-type
equivalence realised by a single bimodule: such an equivalence is an equivalence of bimodule
categories, and its action on a complex of bimodules is the degreewise action of that
equivalence.

A *derived* transfer, in which the target setting is reached by conjugating bimodules with a
tilting bimodule complex, is **not** covered by this principle. Conjugation by a tilting
complex is not an additive functor on bimodules, so it is not an instance of `H` here, and
the principle cannot be applied to it. Such a transfer would have to be stated for a functor
between the (homotopy) categories of complexes, with the monoidal and unit data stated for
that functor; no such statement is made here.

Naturality of the transferred relations up to chain homotopy, the derived-Koszul comparison,
spherical twists and graded-`K₀` statements are out of scope.

## References

* M. Khovanov and P. Seidel, *Quivers, Floer cohomology, and braid group actions*,
  [arXiv:math/0006056](https://arxiv.org/abs/math/0006056).
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u w uA uB

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

local notation "c" => ComplexShape.up ℤ

/-- The category of graded bimodules over the graded algebra `A` with internal grading `Ξ`:
the graded modules over the enveloping grading `Ξ.tensorProduct Ξ.opposite`. -/
abbrev GradedBimoduleCat (k : Type w) [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
    (Ξ : InternalGrading k A) :=
  GradedModuleCat.{max uA w} (Ξ.tensorProduct Ξ.opposite).piece

/-- The balanced bimodule tensor of the graded bimodule setting of `Ξ`. This is
`GradedModuleCat.bimoduleTensor Ξ Ξ Ξ`: the tensor of two graded bimodules of the graded
algebra `A`, balanced over `A` itself. -/
abbrev GradedBimoduleTensor (k : Type w) [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
    (Ξ : InternalGrading k A) [GradedAlgebra Ξ.piece] :
    GradedBimoduleCat k Ξ ⥤ GradedBimoduleCat k Ξ ⥤ GradedBimoduleCat k Ξ :=
  GradedModuleCat.bimoduleTensor Ξ Ξ Ξ

/-- The unit complex of the graded bimodule setting of `Ξ`: the regular graded bimodule
`GradedModuleCat.bimoduleUnit Ξ` placed in cohomological degree zero. -/
noncomputable def GradedBimoduleUnitComplex (k : Type w) [CommRing k] {A : Type uA}
    [Ring A] [Algebra k A] (Ξ : InternalGrading k A) [GradedAlgebra Ξ.piece] :
    HomologicalComplex (GradedBimoduleCat k Ξ) c :=
  (HomologicalComplex.single (GradedBimoduleCat k Ξ) c 0).obj
    (GradedModuleCat.bimoduleUnit.{w} Ξ)

/-- The regular graded zigzag bimodule concentrated in cohomological degree zero: the
common target of the two one-sided inverse-product equivalences of the braid family. -/
abbrev zigzagBraidUnitComplex :
    HomologicalComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) c :=
  (HomologicalComplex.single (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
    c 0).obj (zigzagGradedBimodule k G)

/-- The regular graded zigzag bimodule is the unit complex of the graded bimodule setting of
the zigzag algebra: the homotopy equivalence between the regular graded bimodule in
cohomological degree zero and `GradedBimoduleUnitComplex` of that setting. It is the
transport of `zigzagGradedBimoduleUnitIsoLift` to the single-degree complex. -/
def zigzagBraidUnitComplexEquiv :
    HomotopyEquiv (zigzagBraidUnitComplex k G)
      (GradedBimoduleUnitComplex k (zigzagAlgebraInternalGrading k G)) :=
  HomotopyEquiv.ofIso
    ((HomologicalComplex.single (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
      c 0).mapIso (zigzagGradedBimoduleUnitIsoLift k G).symm)

/-- The three Khovanov-Seidel relations for a family `C` of complexes of graded bimodules in
the graded bimodule setting of `Ξ`, with prescribed inverses `C'`: both one-sided inverse
products `C i ⊗ C' i` and `C' i ⊗ C i` are homotopy equivalent to the unit complex of the
setting, the nonadjacent factors commute up to chain homotopy, and the adjacent factors
satisfy the braid relation up to chain homotopy. -/
structure KhovanovSeidelRelations
    {A : Type uA} [Ring A] [Algebra k A]
    (Ξ : InternalGrading k A) [GradedAlgebra Ξ.piece]
    (C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ) c) where
  /-- The forward inverse product `C i ⊗ C' i` is homotopy equivalent to the unit. -/
  inverseForward (i : V) : HomotopyEquiv
    (HomologicalComplex.mapBifunctor (C i) (C' i) (GradedBimoduleTensor k Ξ) c)
    (GradedBimoduleUnitComplex k Ξ)
  /-- The reverse inverse product `C' i ⊗ C i` is homotopy equivalent to the unit. -/
  inverseReverse (i : V) : HomotopyEquiv
    (HomologicalComplex.mapBifunctor (C' i) (C i) (GradedBimoduleTensor k Ξ) c)
    (GradedBimoduleUnitComplex k Ξ)
  /-- Nonadjacent factors commute up to chain homotopy. -/
  commute (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) : HomotopyEquiv
    (HomologicalComplex.mapBifunctor (C i) (C j) (GradedBimoduleTensor k Ξ) c)
    (HomologicalComplex.mapBifunctor (C j) (C i) (GradedBimoduleTensor k Ξ) c)
  /-- Adjacent factors satisfy the braid relation up to chain homotopy. -/
  braid {i j : V} (h : G.Adj j i) : HomotopyEquiv
    (HomologicalComplex.mapBifunctor
      (HomologicalComplex.mapBifunctor (C i) (C j) (GradedBimoduleTensor k Ξ) c) (C i)
      (GradedBimoduleTensor k Ξ) c)
    (HomologicalComplex.mapBifunctor
      (HomologicalComplex.mapBifunctor (C j) (C i) (GradedBimoduleTensor k Ξ) c) (C j)
      (GradedBimoduleTensor k Ξ) c)

/-- The zigzag braid complexes satisfy the Khovanov-Seidel relations, with the inverse
complexes as prescribed inverses and the regular graded bimodule concentrated in cohomological
degree zero as the unit. -/
def zigzagBraidComplexRelations :
    KhovanovSeidelRelations k G (zigzagAlgebraInternalGrading k G)
      (zigzagBraidComplex k G) (zigzagBraidInverseComplex k G) where
  inverseForward i := (zigzagBraidComplexTensorInverseHomotopyEquiv k G i).trans
    (zigzagBraidUnitComplexEquiv k G)
  inverseReverse i := (zigzagBraidInverseTensorComplexHomotopyEquiv k G i).trans
    (zigzagBraidUnitComplexEquiv k G)
  commute := zigzagBraidComplexTensorCommHomotopyEquiv k G
  braid h := zigzagBraidComplexAdjacentHomotopyEquiv k G h

section Transfer

variable {A₁ : Type uA} [Ring A₁] [Algebra k A₁]
variable {A₂ : Type uB} [Ring A₂] [Algebra k A₂]
variable (Ξ₁ : InternalGrading k A₁) [GradedAlgebra Ξ₁.piece]
variable (Ξ₂ : InternalGrading k A₂) [GradedAlgebra Ξ₂.piece]
variable (H : GradedBimoduleCat k Ξ₁ ⥤ GradedBimoduleCat k Ξ₂) [H.Additive]

/-- The complex prolonged from `X` by the prolongation of the functor `H` to the complexes of
the target graded bimodule setting. -/
abbrev GradedBimoduleProlongation (X : HomologicalComplex (GradedBimoduleCat k Ξ₁) c) :
    HomologicalComplex (GradedBimoduleCat k Ξ₂) c :=
  (H.mapHomologicalComplex c).obj X

/-- The pointwise homotopy-monoidal datum of the functor `H` between the source and the target
graded bimodule setting: for every pair of source complexes `X` and `Y`, a homotopy
equivalence comparing the target tensor product of the prolonged complexes with the
prolongation of the source tensor product. -/
abbrev GradedBimoduleMonoidalDatum :=
  ∀ (X Y : HomologicalComplex (GradedBimoduleCat k Ξ₁) c),
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (GradedBimoduleProlongation k Ξ₁ Ξ₂ H X)
        (GradedBimoduleProlongation k Ξ₁ Ξ₂ H Y) (GradedBimoduleTensor k Ξ₂) c)
      (GradedBimoduleProlongation k Ξ₁ Ξ₂ H
        (HomologicalComplex.mapBifunctor X Y (GradedBimoduleTensor k Ξ₁) c))

/-- Transfer of the forward inverse relation of the source family to the target setting: the
target tensor product `C i ⊗ C' i` is homotopy equivalent to the target unit complex. -/
private def transferInverseForward (i : V)
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H)
    (ε : HomotopyEquiv
      (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (GradedBimoduleUnitComplex k Ξ₁))
      (GradedBimoduleUnitComplex k Ξ₂))
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (a : ∀ i, HomotopyEquiv (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B' i)) (C' i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (C i) (C' i) (GradedBimoduleTensor k Ξ₂) c)
      (GradedBimoduleUnitComplex k Ξ₂) :=
  (HomotopyEquiv.mapBifunctor (GradedBimoduleTensor k Ξ₂) c (a i).symm (a' i).symm).trans
    ((η (B i) (B' i)).trans
      ((H.mapHomotopyEquiv (rel.inverseForward i)).trans ε))

/-- Transfer of the reverse inverse relation of the source family to the target setting: the
target tensor product `C' i ⊗ C i` is homotopy equivalent to the target unit complex. -/
private def transferInverseReverse (i : V)
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H)
    (ε : HomotopyEquiv
      (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (GradedBimoduleUnitComplex k Ξ₁))
      (GradedBimoduleUnitComplex k Ξ₂))
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (a : ∀ i, HomotopyEquiv (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B' i)) (C' i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (C' i) (C i) (GradedBimoduleTensor k Ξ₂) c)
      (GradedBimoduleUnitComplex k Ξ₂) :=
  (HomotopyEquiv.mapBifunctor (GradedBimoduleTensor k Ξ₂) c (a' i).symm (a i).symm).trans
    ((η (B' i) (B i)).trans
      ((H.mapHomotopyEquiv (rel.inverseReverse i)).trans ε))

/-- Transfer of the commutation relation of the source family to the target setting: the
target tensor products `C i ⊗ C j` and `C j ⊗ C i` are homotopy equivalent for nonadjacent
vertices. -/
private def transferCommute (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j)
    {B : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H)
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (a : ∀ i, HomotopyEquiv (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B i)) (C i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (C i) (C j) (GradedBimoduleTensor k Ξ₂) c)
      (HomologicalComplex.mapBifunctor (C j) (C i) (GradedBimoduleTensor k Ξ₂) c) :=
  (HomotopyEquiv.mapBifunctor (GradedBimoduleTensor k Ξ₂) c (a i).symm (a j).symm).trans
    ((η (B i) (B j)).trans
      ((H.mapHomotopyEquiv (rel.commute i j hij hadj)).trans
        (((η (B j) (B i)).symm).trans
          (HomotopyEquiv.mapBifunctor (GradedBimoduleTensor k Ξ₂) c (a j) (a i)))))

/-- The first conjugation step of the transferred braid relation: the triple tensor product of
the target family is compared with the triple tensor product of the prolonged source
complexes. -/
private def transferAdjacentLeftConj {i j : V}
    {B : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (a : ∀ i, HomotopyEquiv (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B i)) (C i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (C i) (C j) (GradedBimoduleTensor k Ξ₂) c) (C i)
        (GradedBimoduleTensor k Ξ₂) c)
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B i))
          (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B j)) (GradedBimoduleTensor k Ξ₂) c)
        (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B i)) (GradedBimoduleTensor k Ξ₂) c) :=
  HomotopyEquiv.mapBifunctor (GradedBimoduleTensor k Ξ₂) c
    (HomotopyEquiv.mapBifunctor (GradedBimoduleTensor k Ξ₂) c (a i).symm (a j).symm)
    (a i).symm

/-- The first bridge step of the transferred braid relation: the target tensor product of two
prolonged source complexes is compared with the prolongation of the source tensor product. -/
private def transferAdjacentBridgeLeft {i j : V}
    {B : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B i))
          (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B j)) (GradedBimoduleTensor k Ξ₂) c)
        (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B i)) (GradedBimoduleTensor k Ξ₂) c)
      (GradedBimoduleProlongation k Ξ₁ Ξ₂ H
        (HomologicalComplex.mapBifunctor
          (HomologicalComplex.mapBifunctor (B i) (B j) (GradedBimoduleTensor k Ξ₁) c) (B i)
          (GradedBimoduleTensor k Ξ₁) c)) :=
  (HomotopyEquiv.mapBifunctor (GradedBimoduleTensor k Ξ₂) c (η (B i) (B j))
    (HomotopyEquiv.refl (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B i)))).trans
    (η (HomologicalComplex.mapBifunctor (B i) (B j) (GradedBimoduleTensor k Ξ₁) c) (B i))

/-- The middle step of the transferred braid relation: the prolonged braid relation of the
source family. -/
private def transferAdjacentMiddle {i j : V} (h : G.Adj j i)
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B') :
    HomotopyEquiv
      (GradedBimoduleProlongation k Ξ₁ Ξ₂ H
        (HomologicalComplex.mapBifunctor
          (HomologicalComplex.mapBifunctor (B i) (B j) (GradedBimoduleTensor k Ξ₁) c) (B i)
          (GradedBimoduleTensor k Ξ₁) c))
      (GradedBimoduleProlongation k Ξ₁ Ξ₂ H
        (HomologicalComplex.mapBifunctor
          (HomologicalComplex.mapBifunctor (B j) (B i) (GradedBimoduleTensor k Ξ₁) c) (B j)
          (GradedBimoduleTensor k Ξ₁) c)) :=
  H.mapHomotopyEquiv (rel.braid h)

/-- The second bridge step of the transferred braid relation: the prolongation of the source
tensor product is compared with the target tensor product of the prolonged source complexes. -/
private def transferAdjacentBridgeRight {i j : V}
    {B : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H) :
    HomotopyEquiv
      (GradedBimoduleProlongation k Ξ₁ Ξ₂ H
        (HomologicalComplex.mapBifunctor
          (HomologicalComplex.mapBifunctor (B j) (B i) (GradedBimoduleTensor k Ξ₁) c) (B j)
          (GradedBimoduleTensor k Ξ₁) c))
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B j))
          (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B i)) (GradedBimoduleTensor k Ξ₂) c)
        (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B j)) (GradedBimoduleTensor k Ξ₂) c) :=
  ((HomotopyEquiv.mapBifunctor (GradedBimoduleTensor k Ξ₂) c (η (B j) (B i))
    (HomotopyEquiv.refl (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B j)))).trans
    (η (HomologicalComplex.mapBifunctor (B j) (B i) (GradedBimoduleTensor k Ξ₁) c) (B j))).symm

/-- The last conjugation step of the transferred braid relation: the triple tensor product of
the prolonged source complexes is compared with the triple tensor product of the target
family. -/
private def transferAdjacentRightConj {i j : V}
    {B : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (a : ∀ i, HomotopyEquiv (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B i)) (C i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B j))
          (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B i)) (GradedBimoduleTensor k Ξ₂) c)
        (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B j)) (GradedBimoduleTensor k Ξ₂) c)
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (C j) (C i) (GradedBimoduleTensor k Ξ₂) c) (C j)
        (GradedBimoduleTensor k Ξ₂) c) :=
  HomotopyEquiv.mapBifunctor (GradedBimoduleTensor k Ξ₂) c
    (HomotopyEquiv.mapBifunctor (GradedBimoduleTensor k Ξ₂) c (a j) (a i)) (a j)

/-- Transfer of the braid relation of the source family to the target setting: the target
triple tensor products `C i ⊗ C j ⊗ C i` and `C j ⊗ C i ⊗ C j` are homotopy equivalent at
adjacent vertices. -/
private def transferAdjacent {i j : V} (h : G.Adj j i)
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H)
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (a : ∀ i, HomotopyEquiv (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B i)) (C i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (C i) (C j) (GradedBimoduleTensor k Ξ₂) c) (C i)
        (GradedBimoduleTensor k Ξ₂) c)
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (C j) (C i) (GradedBimoduleTensor k Ξ₂) c) (C j)
        (GradedBimoduleTensor k Ξ₂) c) :=
  (transferAdjacentLeftConj k Ξ₁ Ξ₂ H a).trans
    ((transferAdjacentBridgeLeft k Ξ₁ Ξ₂ H η).trans
      ((transferAdjacentMiddle k G Ξ₁ Ξ₂ H h rel).trans
        ((transferAdjacentBridgeRight k Ξ₁ Ξ₂ H η).trans
          (transferAdjacentRightConj k Ξ₁ Ξ₂ H a))))

/-- Transfer of the Khovanov-Seidel relations of a source family to a target graded bimodule
setting. Let `H` be an additive functor from the source setting of `Ξ₁` to the target setting
of `Ξ₂`, let `η` be its pointwise homotopy-monoidal datum comparing the target tensor product
of prolonged complexes with the prolongation of the source tensor product, and let `ε` compare
the prolonged source unit complex with the target unit complex. If the source family `B` with
its inverses `B'` satisfies the Khovanov-Seidel relations in the source setting, and the
prolonged source complexes are identified with a target family `C` with inverses `C'` by the
homotopy equivalences `a` and `a'`, then the target family satisfies the Khovanov-Seidel
relations in the target setting. -/
def KhovanovSeidelRelationsTransfer
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H)
    (ε : HomotopyEquiv
      (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (GradedBimoduleUnitComplex k Ξ₁))
      (GradedBimoduleUnitComplex k Ξ₂))
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (a : ∀ i, HomotopyEquiv (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv (GradedBimoduleProlongation k Ξ₁ Ξ₂ H (B' i)) (C' i)) :
    KhovanovSeidelRelations k G Ξ₂ C C' where
  inverseForward i := transferInverseForward k G Ξ₁ Ξ₂ H i η ε rel a a'
  inverseReverse i := transferInverseReverse k G Ξ₁ Ξ₂ H i η ε rel a a'
  commute i j hij hadj := transferCommute k G Ξ₁ Ξ₂ H i j hij hadj η rel a
  braid h := transferAdjacent k G Ξ₁ Ξ₂ H h η rel a

end Transfer

section ZigzagTransfer

variable {A : Type uA} [Ring A] [Algebra k A]
variable (Ξ : InternalGrading k A) [GradedAlgebra Ξ.piece]
variable (H : GradedBimoduleCat k (zigzagAlgebraInternalGrading k G) ⥤ GradedBimoduleCat k Ξ)
  [H.Additive]

/-- Transfer of the Khovanov-Seidel relations of the zigzag braid complexes to a family of
complexes in a second graded bimodule setting, the setting of the graded algebra `A` with
internal grading `Ξ`. The functor `H` is an additive functor from the setting of the zigzag
braid complexes to that second setting, `η` is its pointwise homotopy-monoidal datum, `ε`
compares the prolonged unit complex of the zigzag setting with the unit complex of the
target setting, and `a` and `a'` identify the prolonged zigzag braid complexes with the
target family. -/
def zigzagBraidRelationsTransfer
    (η : GradedBimoduleMonoidalDatum k (zigzagAlgebraInternalGrading k G) Ξ H)
    (ε : HomotopyEquiv
      (GradedBimoduleProlongation k (zigzagAlgebraInternalGrading k G) Ξ H
        (GradedBimoduleUnitComplex k (zigzagAlgebraInternalGrading k G)))
      (GradedBimoduleUnitComplex k Ξ))
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ) c}
    (a : ∀ i, HomotopyEquiv (GradedBimoduleProlongation k (zigzagAlgebraInternalGrading k G)
      Ξ H (zigzagBraidComplex k G i)) (C i))
    (a' : ∀ i, HomotopyEquiv (GradedBimoduleProlongation k (zigzagAlgebraInternalGrading k G)
      Ξ H (zigzagBraidInverseComplex k G i)) (C' i)) :
    KhovanovSeidelRelations k G Ξ C C' :=
  KhovanovSeidelRelationsTransfer k G (zigzagAlgebraInternalGrading k G) Ξ H η ε
    (zigzagBraidComplexRelations k G) a a'

/-- The prolonged zigzag braid complexes satisfy the Khovanov-Seidel relations in the target
graded bimodule setting: the conjugated version of the transfer theorem, obtained with the
identity supplied equivalences. -/
def zigzagBraidProlongedRelations
    (η : GradedBimoduleMonoidalDatum k (zigzagAlgebraInternalGrading k G) Ξ H)
    (ε : HomotopyEquiv
      (GradedBimoduleProlongation k (zigzagAlgebraInternalGrading k G) Ξ H
        (GradedBimoduleUnitComplex k (zigzagAlgebraInternalGrading k G)))
      (GradedBimoduleUnitComplex k Ξ)) :
    KhovanovSeidelRelations k G Ξ
      (fun i => GradedBimoduleProlongation k (zigzagAlgebraInternalGrading k G) Ξ H
        (zigzagBraidComplex k G i))
      (fun i => GradedBimoduleProlongation k (zigzagAlgebraInternalGrading k G) Ξ H
        (zigzagBraidInverseComplex k G i)) :=
  zigzagBraidRelationsTransfer k G Ξ H η ε (fun _ => HomotopyEquiv.refl _)
    (fun _ => HomotopyEquiv.refl _)

end ZigzagTransfer

end TauCeti

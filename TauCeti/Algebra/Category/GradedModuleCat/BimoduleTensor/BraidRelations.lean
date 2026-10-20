/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Unit
public import TauCeti.Algebra.Category.GradedModuleCat.Coproducts.Basic
public import TauCeti.Algebra.Homology.Bifunctor.Homotopy

/-!
# A transfer principle for the Khovanov-Seidel braid relations

The Khovanov-Seidel braid relations are relations between complexes of bimodules in a *graded
bimodule setting*: the two one-sided inverse products are homotopy equivalent to the unit of
the setting, the nonadjacent factors commute up to chain homotopy, and the adjacent factors
satisfy the braid relation up to chain homotopy. A graded bimodule setting is a graded algebra
`A` with an internal grading `Ξ`: its graded bimodules are the graded modules over the
enveloping grading `Ξ.tensorProduct Ξ.opposite`, they are combined by the balanced bimodule
tensor `gradedBimoduleTensor`, and the unit complex of the setting is
`gradedBimoduleUnitComplex k Ξ`, the regular graded bimodule
`GradedModuleCat.bimoduleUnit Ξ` placed in cohomological degree zero. The category
`GradedBimoduleCat` and the tensor `gradedBimoduleTensor` of such a setting are defined in
`TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Basic`, and the unit complex
`gradedBimoduleUnitComplex` in `TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Unit`,
next to `GradedModuleCat.bimoduleUnit`.

`KhovanovSeidelRelations` records the three relations for a family `C` of complexes with
prescribed inverses `C'` in a graded bimodule setting. The unit of the relations is the unit
complex *of that setting*; it is not a free parameter, so the two inverse relations are
statements about the actual unit of the tensor.

`KhovanovSeidelRelations.transfer` is the transfer principle. A functor `H` from a source
graded bimodule setting to a target graded bimodule setting, together with

* a pointwise homotopy-monoidal datum `η`, a homotopy equivalence for every pair of source
  complexes `X` and `Y` comparing the target tensor product of the image complexes with the
  image of the source tensor product, and
* a unit datum `ε`, a homotopy equivalence comparing the image of the source unit complex
  with the target unit complex,

transports the three relations from the source setting to the target setting, provided the
image complexes are identified with a target family by the homotopy equivalences `a` and `a'`.
The two settings need not agree: the target is a second graded algebra, and `H` need not be an
equivalence.

The four field values of the transferred relations are the public declarations
`transferInverseForward`, `transferInverseReverse`, `transferCommute` and `transferAdjacent`,
and the four projection lemmas `transfer_inverseForward`, `transfer_inverseReverse`,
`transfer_commute` and `transfer_braid` read those values off the transferred relations.

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

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V)

local notation "c" => ComplexShape.up ℤ

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
    (HomologicalComplex.mapBifunctor (C i) (C' i) (gradedBimoduleTensor k Ξ) c)
    (gradedBimoduleUnitComplex k Ξ)
  /-- The reverse inverse product `C' i ⊗ C i` is homotopy equivalent to the unit. -/
  inverseReverse (i : V) : HomotopyEquiv
    (HomologicalComplex.mapBifunctor (C' i) (C i) (gradedBimoduleTensor k Ξ) c)
    (gradedBimoduleUnitComplex k Ξ)
  /-- Nonadjacent factors commute up to chain homotopy. -/
  commute (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) : HomotopyEquiv
    (HomologicalComplex.mapBifunctor (C i) (C j) (gradedBimoduleTensor k Ξ) c)
    (HomologicalComplex.mapBifunctor (C j) (C i) (gradedBimoduleTensor k Ξ) c)
  /-- Adjacent factors satisfy the braid relation up to chain homotopy. -/
  braid {i j : V} (h : G.Adj j i) : HomotopyEquiv
    (HomologicalComplex.mapBifunctor
      (HomologicalComplex.mapBifunctor (C i) (C j) (gradedBimoduleTensor k Ξ) c) (C i)
      (gradedBimoduleTensor k Ξ) c)
    (HomologicalComplex.mapBifunctor
      (HomologicalComplex.mapBifunctor (C j) (C i) (gradedBimoduleTensor k Ξ) c) (C j)
      (gradedBimoduleTensor k Ξ) c)

section Transfer

variable {A₁ : Type uA} [Ring A₁] [Algebra k A₁]
variable {A₂ : Type uB} [Ring A₂] [Algebra k A₂]
variable (Ξ₁ : InternalGrading k A₁) [GradedAlgebra Ξ₁.piece]
variable (Ξ₂ : InternalGrading k A₂) [GradedAlgebra Ξ₂.piece]
variable (H : GradedBimoduleCat k Ξ₁ ⥤ GradedBimoduleCat k Ξ₂) [H.Additive]

/-- The pointwise homotopy-monoidal datum of the functor `H` between the source and the target
graded bimodule setting: for every pair of source complexes `X` and `Y`, a homotopy
equivalence comparing the target tensor product of the image complexes with the image of the
source tensor product. -/
abbrev GradedBimoduleMonoidalDatum :=
  ∀ (X Y : HomologicalComplex (GradedBimoduleCat k Ξ₁) c),
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor ((H.mapHomologicalComplex c).obj X)
        ((H.mapHomologicalComplex c).obj Y) (gradedBimoduleTensor k Ξ₂) c)
      ((H.mapHomologicalComplex c).obj
        (HomologicalComplex.mapBifunctor X Y (gradedBimoduleTensor k Ξ₁) c))

namespace KhovanovSeidelRelations

/-- The first conjugation step of the transferred braid relation: the triple tensor product of
the target family is compared with the triple tensor product of the image complexes. -/
private def transferAdjacentLeftConj {i j : V}
    {B : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (C i) (C j) (gradedBimoduleTensor k Ξ₂) c) (C i)
        (gradedBimoduleTensor k Ξ₂) c)
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor ((H.mapHomologicalComplex c).obj (B i))
          ((H.mapHomologicalComplex c).obj (B j)) (gradedBimoduleTensor k Ξ₂) c)
        ((H.mapHomologicalComplex c).obj (B i)) (gradedBimoduleTensor k Ξ₂) c) :=
  HomotopyEquiv.mapBifunctor (gradedBimoduleTensor k Ξ₂) c
    (HomotopyEquiv.mapBifunctor (gradedBimoduleTensor k Ξ₂) c (a i).symm (a j).symm)
    (a i).symm

/-- The first bridge step of the transferred braid relation: the target tensor product of two
image complexes is compared with the image of the source tensor product. -/
private def transferAdjacentBridgeLeft {i j : V}
    {B : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor ((H.mapHomologicalComplex c).obj (B i))
          ((H.mapHomologicalComplex c).obj (B j)) (gradedBimoduleTensor k Ξ₂) c)
        ((H.mapHomologicalComplex c).obj (B i)) (gradedBimoduleTensor k Ξ₂) c)
      ((H.mapHomologicalComplex c).obj
        (HomologicalComplex.mapBifunctor
          (HomologicalComplex.mapBifunctor (B i) (B j) (gradedBimoduleTensor k Ξ₁) c) (B i)
          (gradedBimoduleTensor k Ξ₁) c)) :=
  (HomotopyEquiv.mapBifunctor (gradedBimoduleTensor k Ξ₂) c (η (B i) (B j))
    (HomotopyEquiv.refl ((H.mapHomologicalComplex c).obj (B i)))).trans
    (η (HomologicalComplex.mapBifunctor (B i) (B j) (gradedBimoduleTensor k Ξ₁) c) (B i))

/-- The middle step of the transferred braid relation: the image of the braid relation of the
source family. -/
private def transferAdjacentMiddle {i j : V} (h : G.Adj j i)
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B') :
    HomotopyEquiv
      ((H.mapHomologicalComplex c).obj
        (HomologicalComplex.mapBifunctor
          (HomologicalComplex.mapBifunctor (B i) (B j) (gradedBimoduleTensor k Ξ₁) c) (B i)
          (gradedBimoduleTensor k Ξ₁) c))
      ((H.mapHomologicalComplex c).obj
        (HomologicalComplex.mapBifunctor
          (HomologicalComplex.mapBifunctor (B j) (B i) (gradedBimoduleTensor k Ξ₁) c) (B j)
          (gradedBimoduleTensor k Ξ₁) c)) :=
  H.mapHomotopyEquiv (rel.braid h)

/-- The second bridge step of the transferred braid relation: the image of the source tensor
product is compared with the target tensor product of the image complexes. It is the reversed
first bridge step at the swapped vertices. -/
private def transferAdjacentBridgeRight {i j : V}
    {B : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H) :
    HomotopyEquiv
      ((H.mapHomologicalComplex c).obj
        (HomologicalComplex.mapBifunctor
          (HomologicalComplex.mapBifunctor (B j) (B i) (gradedBimoduleTensor k Ξ₁) c) (B j)
          (gradedBimoduleTensor k Ξ₁) c))
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor ((H.mapHomologicalComplex c).obj (B j))
          ((H.mapHomologicalComplex c).obj (B i)) (gradedBimoduleTensor k Ξ₂) c)
        ((H.mapHomologicalComplex c).obj (B j)) (gradedBimoduleTensor k Ξ₂) c) :=
  (transferAdjacentBridgeLeft k Ξ₁ Ξ₂ H (i := j) (j := i) η).symm

/-- The last conjugation step of the transferred braid relation: the triple tensor product of
the image complexes is compared with the triple tensor product of the target family. It is the
reversed first conjugation step at the swapped vertices. -/
private def transferAdjacentRightConj {i j : V}
    {B : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor ((H.mapHomologicalComplex c).obj (B j))
          ((H.mapHomologicalComplex c).obj (B i)) (gradedBimoduleTensor k Ξ₂) c)
        ((H.mapHomologicalComplex c).obj (B j)) (gradedBimoduleTensor k Ξ₂) c)
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (C j) (C i) (gradedBimoduleTensor k Ξ₂) c) (C j)
        (gradedBimoduleTensor k Ξ₂) c) :=
  (transferAdjacentLeftConj k Ξ₁ Ξ₂ H (i := j) (j := i) a).symm

/-- Transfer of the forward inverse relation of the source family to the target setting: the
target tensor product `C i ⊗ C' i` is homotopy equivalent to the target unit complex. -/
def transferInverseForward (i : V)
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H)
    (ε : HomotopyEquiv
      ((H.mapHomologicalComplex c).obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B' i)) (C' i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (C i) (C' i) (gradedBimoduleTensor k Ξ₂) c)
      (gradedBimoduleUnitComplex k Ξ₂) :=
  (HomotopyEquiv.mapBifunctor (gradedBimoduleTensor k Ξ₂) c (a i).symm (a' i).symm).trans
    ((η (B i) (B' i)).trans
      ((H.mapHomotopyEquiv (rel.inverseForward i)).trans ε))

/-- Transfer of the reverse inverse relation of the source family to the target setting: the
target tensor product `C' i ⊗ C i` is homotopy equivalent to the target unit complex. -/
def transferInverseReverse (i : V)
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H)
    (ε : HomotopyEquiv
      ((H.mapHomologicalComplex c).obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B' i)) (C' i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (C' i) (C i) (gradedBimoduleTensor k Ξ₂) c)
      (gradedBimoduleUnitComplex k Ξ₂) :=
  (HomotopyEquiv.mapBifunctor (gradedBimoduleTensor k Ξ₂) c (a' i).symm (a i).symm).trans
    ((η (B' i) (B i)).trans
      ((H.mapHomotopyEquiv (rel.inverseReverse i)).trans ε))

/-- Transfer of the commutation relation of the source family to the target setting: the
target tensor products `C i ⊗ C j` and `C j ⊗ C i` are homotopy equivalent for nonadjacent
vertices. -/
def transferCommute (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j)
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H)
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (C i) (C j) (gradedBimoduleTensor k Ξ₂) c)
      (HomologicalComplex.mapBifunctor (C j) (C i) (gradedBimoduleTensor k Ξ₂) c) :=
  (HomotopyEquiv.mapBifunctor (gradedBimoduleTensor k Ξ₂) c (a i).symm (a j).symm).trans
    ((η (B i) (B j)).trans
      ((H.mapHomotopyEquiv (rel.commute i j hij hadj)).trans
        (((η (B j) (B i)).symm).trans
          (HomotopyEquiv.mapBifunctor (gradedBimoduleTensor k Ξ₂) c (a j) (a i)))))

/-- Transfer of the braid relation of the source family to the target setting: the target
triple tensor products `C i ⊗ C j ⊗ C i` and `C j ⊗ C i ⊗ C j` are homotopy equivalent at
adjacent vertices. -/
def transferAdjacent {i j : V} (h : G.Adj j i)
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H)
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (C i) (C j) (gradedBimoduleTensor k Ξ₂) c) (C i)
        (gradedBimoduleTensor k Ξ₂) c)
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (C j) (C i) (gradedBimoduleTensor k Ξ₂) c) (C j)
        (gradedBimoduleTensor k Ξ₂) c) :=
  (transferAdjacentLeftConj k Ξ₁ Ξ₂ H a).trans
    ((transferAdjacentBridgeLeft k Ξ₁ Ξ₂ H η).trans
      ((transferAdjacentMiddle k G Ξ₁ Ξ₂ H h rel).trans
        ((transferAdjacentBridgeRight k Ξ₁ Ξ₂ H η).trans
          (transferAdjacentRightConj k Ξ₁ Ξ₂ H a))))

/-- Transfer of the Khovanov-Seidel relations of a source family to a target graded bimodule
setting. Let `H` be an additive functor from the source setting of `Ξ₁` to the target setting
of `Ξ₂`, let `η` be its pointwise homotopy-monoidal datum comparing the target tensor product
of image complexes with the image of the source tensor product, and let `ε` compare the image
of the source unit complex with the target unit complex. If the source family `B` with its
inverses `B'` satisfies the Khovanov-Seidel relations in the source setting, and the image
complexes are identified with a target family `C` with inverses `C'` by the homotopy
equivalences `a` and `a'`, then the target family satisfies the Khovanov-Seidel relations in
the target setting. -/
-- The body is not exposed: the four field values of the transferred relations are the
-- public declarations `transferInverseForward`, `transferInverseReverse`, `transferCommute`
-- and `transferAdjacent`, which state them without unfolding this definition; the four
-- projection lemmas `transfer_inverseForward` and its three siblings read them off the
-- transferred relations.
def transfer {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V}
    {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂] [Algebra k A₂]
    {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {H : GradedBimoduleCat k Ξ₁ ⥤ GradedBimoduleCat k Ξ₂} [H.Additive]
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H)
    (ε : HomotopyEquiv
      ((H.mapHomologicalComplex c).obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B' i)) (C' i)) :
    KhovanovSeidelRelations k G Ξ₂ C C' where
  inverseForward i := transferInverseForward k G Ξ₁ Ξ₂ H i η ε rel a a'
  inverseReverse i := transferInverseReverse k G Ξ₁ Ξ₂ H i η ε rel a a'
  commute i j hij hadj := transferCommute k G Ξ₁ Ξ₂ H i j hij hadj η rel a
  braid h := transferAdjacent k G Ξ₁ Ξ₂ H h η rel a

-- The four field values of `transfer` are read off by the four projection lemmas below.
-- Their proofs are written `(rfl)` and not `rfl`: a theorem whose proof is syntactically `rfl`
-- is tagged `@[defeq]`, and the module system refuses to export a `@[defeq]` theorem whose proof
-- needs the body of a definition that is not exposed.
/-- The forward inverse relation of the transferred relations is the forward inverse transfer
`transferInverseForward`. -/
@[simp] theorem transfer_inverseForward {k : Type w} [CommRing k] {V : Type u}
    {G : SimpleGraph V} {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂]
    [Algebra k A₂] {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {H : GradedBimoduleCat k Ξ₁ ⥤ GradedBimoduleCat k Ξ₂} [H.Additive]
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H)
    (ε : HomotopyEquiv
      ((H.mapHomologicalComplex c).obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B' i)) (C' i))
    (i : V) :
    (rel.transfer η ε a a').inverseForward i
      = transferInverseForward k G Ξ₁ Ξ₂ H i η ε rel a a' := (rfl)

/-- The reverse inverse relation of the transferred relations is the reverse inverse transfer
`transferInverseReverse`. -/
@[simp] theorem transfer_inverseReverse {k : Type w} [CommRing k] {V : Type u}
    {G : SimpleGraph V} {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂]
    [Algebra k A₂] {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {H : GradedBimoduleCat k Ξ₁ ⥤ GradedBimoduleCat k Ξ₂} [H.Additive]
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H)
    (ε : HomotopyEquiv
      ((H.mapHomologicalComplex c).obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B' i)) (C' i))
    (i : V) :
    (rel.transfer η ε a a').inverseReverse i
      = transferInverseReverse k G Ξ₁ Ξ₂ H i η ε rel a a' := (rfl)

/-- The commutation relation of the transferred relations is the commutation transfer
`transferCommute`. -/
@[simp] theorem transfer_commute {k : Type w} [CommRing k] {V : Type u}
    {G : SimpleGraph V} {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂]
    [Algebra k A₂] {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {H : GradedBimoduleCat k Ξ₁ ⥤ GradedBimoduleCat k Ξ₂} [H.Additive]
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H)
    (ε : HomotopyEquiv
      ((H.mapHomologicalComplex c).obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B' i)) (C' i))
    (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    (rel.transfer η ε a a').commute i j hij hadj
      = transferCommute k G Ξ₁ Ξ₂ H i j hij hadj η rel a := (rfl)

/-- The braid relation of the transferred relations is the adjacent transfer `transferAdjacent`. -/
@[simp] theorem transfer_braid {k : Type w} [CommRing k] {V : Type u}
    {G : SimpleGraph V} {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂]
    [Algebra k A₂] {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {H : GradedBimoduleCat k Ξ₁ ⥤ GradedBimoduleCat k Ξ₂} [H.Additive]
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ H)
    (ε : HomotopyEquiv
      ((H.mapHomologicalComplex c).obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B' i)) (C' i))
    {i j : V} (h : G.Adj j i) :
    (rel.transfer η ε a a').braid h
      = transferAdjacent k G Ξ₁ Ξ₂ H h η rel a := (rfl)

end KhovanovSeidelRelations

end Transfer

end TauCeti

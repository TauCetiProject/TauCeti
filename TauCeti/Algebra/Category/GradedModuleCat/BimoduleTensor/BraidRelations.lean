/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
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
tensor `GradedModuleCat.bimoduleTensor Ξ Ξ Ξ`, and the unit complex of the setting is
`gradedBimoduleUnitComplex k Ξ`, the regular graded bimodule
`GradedModuleCat.bimoduleUnit Ξ` placed in cohomological degree zero. The category
`GradedBimoduleCat` of such a setting is defined in
`TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Basic`, next to
`GradedModuleCat.bimoduleTensor`, and the unit complex
`gradedBimoduleUnitComplex` in `TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Unit`,
next to `GradedModuleCat.bimoduleUnit`.

`KhovanovSeidelRelations` records the three relations for a family `C` of complexes with
prescribed inverses `C'` in a graded bimodule setting. The unit of the relations is the unit
complex `gradedBimoduleUnitComplex k Ξ` of that setting, so the two inverse relations are
statements about the actual unit of the tensor.

`KhovanovSeidelRelations.transfer` is the transfer principle. It is stated for a functor `Φ`
on *complexes* of graded bimodules from a source graded bimodule setting to a target graded
bimodule setting, together with

* a datum `hΦ`, carrying every homotopy equivalence of source complexes to a homotopy
  equivalence of image complexes,
* a pointwise homotopy-monoidal datum `η`, a homotopy equivalence for every pair of source
  complexes `X` and `Y` comparing the target tensor product of the image complexes with the
  image of the source tensor product, and
* a unit datum `ε`, a homotopy equivalence comparing the image of the source unit complex
  with the target unit complex,

and transports the three relations from the source setting to the target setting, provided the
image complexes are identified with a target family by the homotopy equivalences `a` and `a'`.
The two settings need not agree: the target is a second graded algebra, and `Φ` need not be an
equivalence.

`KhovanovSeidelRelations.transferDegreewise` is the degreewise specialisation of the
principle: it is the transfer at the functor `H.mapHomologicalComplex` of an additive functor
`H` of graded bimodule categories. This is the shape of a Morita-type equivalence realised by a
single bimodule: such an equivalence is an equivalence of bimodule categories, and its action
on a complex of bimodules is the degreewise action of that equivalence.

The four field values of the transferred relations are the public declarations
`transferInverseForward`, `transferInverseReverse`, `transferCommute` and `transferAdjacent`,
and the four projection lemmas `transfer_inverseForward`, `transfer_inverseReverse`,
`transfer_commute` and `transfer_braid` read those values off the transferred relations; the
four projection lemmas `transferDegreewise_inverseForward` and its three siblings read them off
the degreewise transferred relations.

## Scope

The principle is stated for a functor `Φ` on complexes of graded bimodules, with the datum `hΦ`
that it carries homotopy equivalences to homotopy equivalences. That is the shape a *derived*
transfer needs: conjugation of bimodules with a tilting bimodule complex is a functor on
complexes of bimodules and not an additive functor on bimodules, so it is not an instance of
the degreewise specialisation `transferDegreewise`, but it is an instance of `Φ`.

No derived case is instantiated in this file: `η` and `ε` — the monoidal and unit
compatibility that a transfer has to establish — remain hypotheses of the principle, to be
discharged at each instantiation.

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
    (HomologicalComplex.mapBifunctor (C i) (C' i) (GradedModuleCat.bimoduleTensor Ξ Ξ Ξ) c)
    (gradedBimoduleUnitComplex k Ξ)
  /-- The reverse inverse product `C' i ⊗ C i` is homotopy equivalent to the unit. -/
  inverseReverse (i : V) : HomotopyEquiv
    (HomologicalComplex.mapBifunctor (C' i) (C i) (GradedModuleCat.bimoduleTensor Ξ Ξ Ξ) c)
    (gradedBimoduleUnitComplex k Ξ)
  /-- Nonadjacent factors commute up to chain homotopy. -/
  commute (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) : HomotopyEquiv
    (HomologicalComplex.mapBifunctor (C i) (C j) (GradedModuleCat.bimoduleTensor Ξ Ξ Ξ) c)
    (HomologicalComplex.mapBifunctor (C j) (C i) (GradedModuleCat.bimoduleTensor Ξ Ξ Ξ) c)
  /-- Adjacent factors satisfy the braid relation up to chain homotopy. -/
  braid {i j : V} (h : G.Adj j i) : HomotopyEquiv
    (HomologicalComplex.mapBifunctor
      (HomologicalComplex.mapBifunctor (C i) (C j) (GradedModuleCat.bimoduleTensor Ξ Ξ Ξ) c) (C i)
      (GradedModuleCat.bimoduleTensor Ξ Ξ Ξ) c)
    (HomologicalComplex.mapBifunctor
      (HomologicalComplex.mapBifunctor (C j) (C i) (GradedModuleCat.bimoduleTensor Ξ Ξ Ξ) c) (C j)
      (GradedModuleCat.bimoduleTensor Ξ Ξ Ξ) c)

section Transfer

variable {A₁ : Type uA} [Ring A₁] [Algebra k A₁]
variable {A₂ : Type uB} [Ring A₂] [Algebra k A₂]
variable (Ξ₁ : InternalGrading k A₁) [GradedAlgebra Ξ₁.piece]
variable (Ξ₂ : InternalGrading k A₂) [GradedAlgebra Ξ₂.piece]
variable (Φ : HomologicalComplex (GradedBimoduleCat k Ξ₁) c ⥤
    HomologicalComplex (GradedBimoduleCat k Ξ₂) c)
variable (hΦ : ∀ {X Y}, HomotopyEquiv X Y → HomotopyEquiv (Φ.obj X) (Φ.obj Y))

/-- The pointwise homotopy-monoidal datum of the functor `Φ` on complexes of graded bimodules
between the source and the target graded bimodule setting: for every pair of source complexes
`X` and `Y`, a homotopy equivalence comparing the target tensor product of the image
complexes with the image of the source tensor product. -/
abbrev GradedBimoduleMonoidalDatum :=
  ∀ (X Y : HomologicalComplex (GradedBimoduleCat k Ξ₁) c),
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (Φ.obj X) (Φ.obj Y)
        (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c)
      (Φ.obj (HomologicalComplex.mapBifunctor X Y
        (GradedModuleCat.bimoduleTensor Ξ₁ Ξ₁ Ξ₁) c))

namespace KhovanovSeidelRelations

/-- The first conjugation step of the transferred braid relation: the triple tensor product of
the target family is compared with the triple tensor product of the image complexes. -/
private def transferAdjacentLeftConj {i j : V}
    {B : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (a : ∀ i, HomotopyEquiv (Φ.obj (B i)) (C i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (C i) (C j)
          (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c) (C i)
        (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c)
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (Φ.obj (B i)) (Φ.obj (B j))
          (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c)
        (Φ.obj (B i)) (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c) :=
  HomotopyEquiv.mapBifunctor (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c
    (HomotopyEquiv.mapBifunctor (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c (a i).symm (a j).symm)
    (a i).symm

/-- The first bridge step of the transferred braid relation: the target tensor product of two
image complexes is compared with the image of the source tensor product. -/
private def transferAdjacentBridgeLeft {i j : V}
    {B : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ Φ) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (Φ.obj (B i)) (Φ.obj (B j))
          (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c)
        (Φ.obj (B i)) (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c)
      (Φ.obj (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (B i) (B j)
          (GradedModuleCat.bimoduleTensor Ξ₁ Ξ₁ Ξ₁) c) (B i)
        (GradedModuleCat.bimoduleTensor Ξ₁ Ξ₁ Ξ₁) c)) :=
  (HomotopyEquiv.mapBifunctor (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c (η (B i) (B j))
    (HomotopyEquiv.refl (Φ.obj (B i)))).trans
    (η (HomologicalComplex.mapBifunctor (B i) (B j)
      (GradedModuleCat.bimoduleTensor Ξ₁ Ξ₁ Ξ₁) c) (B i))

/-- The middle step of the transferred braid relation: the image of the braid relation of the
source family. -/
private def transferAdjacentMiddle {i j : V} (h : G.Adj j i)
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B') :
    HomotopyEquiv
      (Φ.obj (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (B i) (B j)
          (GradedModuleCat.bimoduleTensor Ξ₁ Ξ₁ Ξ₁) c) (B i)
        (GradedModuleCat.bimoduleTensor Ξ₁ Ξ₁ Ξ₁) c))
      (Φ.obj (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (B j) (B i)
          (GradedModuleCat.bimoduleTensor Ξ₁ Ξ₁ Ξ₁) c) (B j)
        (GradedModuleCat.bimoduleTensor Ξ₁ Ξ₁ Ξ₁) c)) :=
  hΦ (rel.braid h)

/-- The second bridge step of the transferred braid relation: the image of the source tensor
product is compared with the target tensor product of the image complexes. It is the reversed
first bridge step at the swapped vertices. -/
private def transferAdjacentBridgeRight {i j : V}
    {B : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ Φ) :
    HomotopyEquiv
      (Φ.obj (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (B j) (B i)
          (GradedModuleCat.bimoduleTensor Ξ₁ Ξ₁ Ξ₁) c) (B j)
        (GradedModuleCat.bimoduleTensor Ξ₁ Ξ₁ Ξ₁) c))
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (Φ.obj (B j)) (Φ.obj (B i))
          (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c)
        (Φ.obj (B j)) (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c) :=
  (transferAdjacentBridgeLeft k Ξ₁ Ξ₂ Φ (i := j) (j := i) η).symm

/-- The last conjugation step of the transferred braid relation: the triple tensor product of
the image complexes is compared with the triple tensor product of the target family. It is the
reversed first conjugation step at the swapped vertices. -/
private def transferAdjacentRightConj {i j : V}
    {B : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (a : ∀ i, HomotopyEquiv (Φ.obj (B i)) (C i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (Φ.obj (B j)) (Φ.obj (B i))
          (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c)
        (Φ.obj (B j)) (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c)
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (C j) (C i)
          (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c) (C j)
        (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c) :=
  (transferAdjacentLeftConj k Ξ₁ Ξ₂ Φ (i := j) (j := i) a).symm

/-- Transfer of the forward inverse relation of the source family to the target setting: the
target tensor product `C i ⊗ C' i` is homotopy equivalent to the target unit complex. -/
def transferInverseForward {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V}
    {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂] [Algebra k A₂]
    {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {Φ : HomologicalComplex (GradedBimoduleCat k Ξ₁) c ⥤
      HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (i : V)
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (hΦ : ∀ {X Y}, HomotopyEquiv X Y → HomotopyEquiv (Φ.obj X) (Φ.obj Y))
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ Φ)
    (ε : HomotopyEquiv (Φ.obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (a : ∀ i, HomotopyEquiv (Φ.obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv (Φ.obj (B' i)) (C' i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (C i) (C' i) (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c)
      (gradedBimoduleUnitComplex k Ξ₂) :=
  (HomotopyEquiv.mapBifunctor (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c
    (a i).symm (a' i).symm).trans
    ((η (B i) (B' i)).trans
      ((hΦ (rel.inverseForward i)).trans ε))

/-- Transfer of the reverse inverse relation of the source family to the target setting: the
target tensor product `C' i ⊗ C i` is homotopy equivalent to the target unit complex. -/
def transferInverseReverse {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V}
    {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂] [Algebra k A₂]
    {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {Φ : HomologicalComplex (GradedBimoduleCat k Ξ₁) c ⥤
      HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (i : V)
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (hΦ : ∀ {X Y}, HomotopyEquiv X Y → HomotopyEquiv (Φ.obj X) (Φ.obj Y))
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ Φ)
    (ε : HomotopyEquiv (Φ.obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (a : ∀ i, HomotopyEquiv (Φ.obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv (Φ.obj (B' i)) (C' i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (C' i) (C i) (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c)
      (gradedBimoduleUnitComplex k Ξ₂) :=
  (HomotopyEquiv.mapBifunctor (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c
    (a' i).symm (a i).symm).trans
    ((η (B' i) (B i)).trans
      ((hΦ (rel.inverseReverse i)).trans ε))

/-- Transfer of the commutation relation of the source family to the target setting: the
target tensor products `C i ⊗ C j` and `C j ⊗ C i` are homotopy equivalent for nonadjacent
vertices. -/
def transferCommute {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V}
    {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂] [Algebra k A₂]
    {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {Φ : HomologicalComplex (GradedBimoduleCat k Ξ₁) c ⥤
      HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j)
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (hΦ : ∀ {X Y}, HomotopyEquiv X Y → HomotopyEquiv (Φ.obj X) (Φ.obj Y))
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ Φ)
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (a : ∀ i, HomotopyEquiv (Φ.obj (B i)) (C i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (C i) (C j) (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c)
      (HomologicalComplex.mapBifunctor (C j) (C i) (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c) :=
  (HomotopyEquiv.mapBifunctor (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c
    (a i).symm (a j).symm).trans
    ((η (B i) (B j)).trans
      ((hΦ (rel.commute i j hij hadj)).trans
        (((η (B j) (B i)).symm).trans
          (HomotopyEquiv.mapBifunctor (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c (a j) (a i)))))

/-- Transfer of the braid relation of the source family to the target setting: the target
triple tensor products `C i ⊗ C j ⊗ C i` and `C j ⊗ C i ⊗ C j` are homotopy equivalent at
adjacent vertices. -/
def transferAdjacent {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V}
    {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂] [Algebra k A₂]
    {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {Φ : HomologicalComplex (GradedBimoduleCat k Ξ₁) c ⥤
      HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    {i j : V} (h : G.Adj j i)
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (hΦ : ∀ {X Y}, HomotopyEquiv X Y → HomotopyEquiv (Φ.obj X) (Φ.obj Y))
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ Φ)
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (a : ∀ i, HomotopyEquiv (Φ.obj (B i)) (C i)) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (C i) (C j)
          (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c) (C i)
        (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c)
      (HomologicalComplex.mapBifunctor
        (HomologicalComplex.mapBifunctor (C j) (C i)
          (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c) (C j)
        (GradedModuleCat.bimoduleTensor Ξ₂ Ξ₂ Ξ₂) c) :=
  (transferAdjacentLeftConj k Ξ₁ Ξ₂ Φ a).trans
    ((transferAdjacentBridgeLeft k Ξ₁ Ξ₂ Φ η).trans
      ((transferAdjacentMiddle k G Ξ₁ Ξ₂ Φ hΦ h rel).trans
        ((transferAdjacentBridgeRight k Ξ₁ Ξ₂ Φ η).trans
          (transferAdjacentRightConj k Ξ₁ Ξ₂ Φ a))))

/-- Transfer of the Khovanov-Seidel relations of a source family to a target graded bimodule
setting. Let `Φ` be a functor on complexes of graded bimodules from the source setting of `Ξ₁`
to the target setting of `Ξ₂`, let `hΦ` carry the homotopy equivalences of source complexes
to homotopy equivalences of image complexes, let `η` be the pointwise homotopy-monoidal datum
of `Φ` comparing the target tensor product of image complexes with the image of the source
tensor product, and let `ε` compare the image of the source unit complex with the target unit
complex. If the source family `B` with its inverses `B'` satisfies the Khovanov-Seidel
relations in the source setting, and the image complexes are identified with a target family `C`
with inverses `C'` by the homotopy equivalences `a` and `a'`, then the target family satisfies
the Khovanov-Seidel relations in the target setting. -/
-- The body is not exposed: the four field values of the transferred relations are the
-- public declarations `transferInverseForward`, `transferInverseReverse`, `transferCommute`
-- and `transferAdjacent`, which state them without unfolding this definition; the four
-- projection lemmas `transfer_inverseForward` and its three siblings read them off the
-- transferred relations.
def transfer {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V}
    {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂] [Algebra k A₂]
    {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {Φ : HomologicalComplex (GradedBimoduleCat k Ξ₁) c ⥤
      HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (hΦ : ∀ {X Y}, HomotopyEquiv X Y → HomotopyEquiv (Φ.obj X) (Φ.obj Y))
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ Φ)
    (ε : HomotopyEquiv (Φ.obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv (Φ.obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv (Φ.obj (B' i)) (C' i)) :
    KhovanovSeidelRelations k G Ξ₂ C C' where
  inverseForward i := transferInverseForward i hΦ η ε rel a a'
  inverseReverse i := transferInverseReverse i hΦ η ε rel a a'
  commute i j hij hadj := transferCommute i j hij hadj hΦ η rel a
  braid h := transferAdjacent h hΦ η rel a

/-- The degreewise specialisation of the transfer principle: the transfer at the functor
`H.mapHomologicalComplex` of an additive functor `H` of graded bimodule categories, whose
homotopy equivalences are carried along by `H.mapHomotopyEquiv`. This is the transfer through
a Morita-type equivalence realised by a single bimodule, whose action on a complex of
bimodules is the degreewise action of that equivalence. -/
-- The body is not exposed, as for `transfer`: the four field values of the degreewise
-- transferred relations are the public declarations `transferInverseForward`,
-- `transferInverseReverse`, `transferCommute` and `transferAdjacent` at the degreewise
-- instance, and the four projection lemmas `transferDegreewise_inverseForward` and its three
-- siblings read them off.
def transferDegreewise {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V}
    {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂] [Algebra k A₂]
    {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {H : GradedBimoduleCat k Ξ₁ ⥤ GradedBimoduleCat k Ξ₂} [H.Additive]
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ (H.mapHomologicalComplex c))
    (ε : HomotopyEquiv
      ((H.mapHomologicalComplex c).obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B' i)) (C' i)) :
    KhovanovSeidelRelations k G Ξ₂ C C'
where
  inverseForward i := transferInverseForward i H.mapHomotopyEquiv η ε rel a a'
  inverseReverse i := transferInverseReverse i H.mapHomotopyEquiv η ε rel a a'
  commute i j hij hadj := transferCommute i j hij hadj H.mapHomotopyEquiv η rel a
  braid h := transferAdjacent h H.mapHomotopyEquiv η rel a

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
    {Φ : HomologicalComplex (GradedBimoduleCat k Ξ₁) c ⥤
      HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (hΦ : ∀ {X Y}, HomotopyEquiv X Y → HomotopyEquiv (Φ.obj X) (Φ.obj Y))
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ Φ)
    (ε : HomotopyEquiv (Φ.obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv (Φ.obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv (Φ.obj (B' i)) (C' i))
    (i : V) :
    (rel.transfer hΦ η ε a a').inverseForward i
      = transferInverseForward i hΦ η ε rel a a' := (rfl)

/-- The reverse inverse relation of the transferred relations is the reverse inverse transfer
`transferInverseReverse`. -/
@[simp] theorem transfer_inverseReverse {k : Type w} [CommRing k] {V : Type u}
    {G : SimpleGraph V} {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂]
    [Algebra k A₂] {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {Φ : HomologicalComplex (GradedBimoduleCat k Ξ₁) c ⥤
      HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (hΦ : ∀ {X Y}, HomotopyEquiv X Y → HomotopyEquiv (Φ.obj X) (Φ.obj Y))
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ Φ)
    (ε : HomotopyEquiv (Φ.obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv (Φ.obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv (Φ.obj (B' i)) (C' i))
    (i : V) :
    (rel.transfer hΦ η ε a a').inverseReverse i
      = transferInverseReverse i hΦ η ε rel a a' := (rfl)

/-- The commutation relation of the transferred relations is the commutation transfer
`transferCommute`. -/
@[simp] theorem transfer_commute {k : Type w} [CommRing k] {V : Type u}
    {G : SimpleGraph V} {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂]
    [Algebra k A₂] {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {Φ : HomologicalComplex (GradedBimoduleCat k Ξ₁) c ⥤
      HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (hΦ : ∀ {X Y}, HomotopyEquiv X Y → HomotopyEquiv (Φ.obj X) (Φ.obj Y))
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ Φ)
    (ε : HomotopyEquiv (Φ.obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv (Φ.obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv (Φ.obj (B' i)) (C' i))
    (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    (rel.transfer hΦ η ε a a').commute i j hij hadj
      = transferCommute i j hij hadj hΦ η rel a := (rfl)

/-- The braid relation of the transferred relations is the adjacent transfer `transferAdjacent`. -/
@[simp] theorem transfer_braid {k : Type w} [CommRing k] {V : Type u}
    {G : SimpleGraph V} {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂]
    [Algebra k A₂] {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {Φ : HomologicalComplex (GradedBimoduleCat k Ξ₁) c ⥤
      HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (hΦ : ∀ {X Y}, HomotopyEquiv X Y → HomotopyEquiv (Φ.obj X) (Φ.obj Y))
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ Φ)
    (ε : HomotopyEquiv (Φ.obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv (Φ.obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv (Φ.obj (B' i)) (C' i))
    {i j : V} (h : G.Adj j i) :
    (rel.transfer hΦ η ε a a').braid h
      = transferAdjacent h hΦ η rel a := (rfl)

-- The four field values of `transferDegreewise` are read off by the four projection lemmas
-- below. Their proofs are written `(rfl)` and not `rfl`, as above.

/-- The forward inverse relation of the degreewise transferred relations is the forward inverse
transfer `transferInverseForward`. -/
@[simp] theorem transferDegreewise_inverseForward {k : Type w} [CommRing k] {V : Type u}
    {G : SimpleGraph V} {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂]
    [Algebra k A₂] {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {H : GradedBimoduleCat k Ξ₁ ⥤ GradedBimoduleCat k Ξ₂} [H.Additive]
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ (H.mapHomologicalComplex c))
    (ε : HomotopyEquiv
      ((H.mapHomologicalComplex c).obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B' i)) (C' i))
    (i : V) :
    (rel.transferDegreewise η ε a a').inverseForward i
      = transferInverseForward i H.mapHomotopyEquiv η ε rel a a' := (rfl)

/-- The reverse inverse relation of the degreewise transferred relations is the reverse inverse
transfer `transferInverseReverse`. -/
@[simp] theorem transferDegreewise_inverseReverse {k : Type w} [CommRing k] {V : Type u}
    {G : SimpleGraph V} {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂]
    [Algebra k A₂] {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {H : GradedBimoduleCat k Ξ₁ ⥤ GradedBimoduleCat k Ξ₂} [H.Additive]
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ (H.mapHomologicalComplex c))
    (ε : HomotopyEquiv
      ((H.mapHomologicalComplex c).obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B' i)) (C' i))
    (i : V) :
    (rel.transferDegreewise η ε a a').inverseReverse i
      = transferInverseReverse i H.mapHomotopyEquiv η ε rel a a' := (rfl)

/-- The commutation relation of the degreewise transferred relations is the commutation
transfer `transferCommute`. -/
@[simp] theorem transferDegreewise_commute {k : Type w} [CommRing k] {V : Type u}
    {G : SimpleGraph V} {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂]
    [Algebra k A₂] {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {H : GradedBimoduleCat k Ξ₁ ⥤ GradedBimoduleCat k Ξ₂} [H.Additive]
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ (H.mapHomologicalComplex c))
    (ε : HomotopyEquiv
      ((H.mapHomologicalComplex c).obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B' i)) (C' i))
    (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    (rel.transferDegreewise η ε a a').commute i j hij hadj
      = transferCommute i j hij hadj H.mapHomotopyEquiv η rel a := (rfl)

/-- The braid relation of the degreewise transferred relations is the adjacent transfer
`transferAdjacent`. -/
@[simp] theorem transferDegreewise_braid {k : Type w} [CommRing k] {V : Type u}
    {G : SimpleGraph V} {A₁ : Type uA} [Ring A₁] [Algebra k A₁] {A₂ : Type uB} [Ring A₂]
    [Algebra k A₂] {Ξ₁ : InternalGrading k A₁} [GradedAlgebra Ξ₁.piece]
    {Ξ₂ : InternalGrading k A₂} [GradedAlgebra Ξ₂.piece]
    {H : GradedBimoduleCat k Ξ₁ ⥤ GradedBimoduleCat k Ξ₂} [H.Additive]
    {B B' : V → HomologicalComplex (GradedBimoduleCat k Ξ₁) c}
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ₂) c}
    (rel : KhovanovSeidelRelations k G Ξ₁ B B')
    (η : GradedBimoduleMonoidalDatum k Ξ₁ Ξ₂ (H.mapHomologicalComplex c))
    (ε : HomotopyEquiv
      ((H.mapHomologicalComplex c).obj (gradedBimoduleUnitComplex k Ξ₁))
      (gradedBimoduleUnitComplex k Ξ₂))
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B i)) (C i))
    (a' : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (B' i)) (C' i))
    {i j : V} (h : G.Adj j i) :
    (rel.transferDegreewise η ε a a').braid h
      = transferAdjacent h H.mapHomotopyEquiv η rel a := (rfl)

end KhovanovSeidelRelations

end Transfer

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.BraidRelations
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Adjacent.Contraction
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Commuting
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Inverse.Forward
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Inverse.Reverse
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Unit

/-!
# The zigzag braid complexes as a family of Khovanov-Seidel relations

The zigzag braid complexes satisfy the Khovanov-Seidel relations: the two one-sided inverse
products are homotopy equivalent to the regular graded bimodule concentrated in cohomological
degree zero, the nonadjacent factors commute up to chain homotopy, and the adjacent factors
satisfy the braid relation up to chain homotopy.

This file instantiates the abstract relations and the abstract transfer principle of
`TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.BraidRelations` for the zigzag
algebra. The unit complex of the graded bimodule setting of the zigzag algebra is the regular
graded zigzag bimodule in cohomological degree zero, and
`zigzagBraidUnitComplexHomotopyEquiv` identifies it with the unit complex of that setting.

`zigzagBraidRelationsTransfer` transports those relations to a second graded bimodule setting,
the setting of a graded algebra `A` with internal grading `Ξ`, and
`zigzagBraidMapHomologicalComplexRelations` records the relations for the image complexes
`H(zigzagBraidComplex i)` themselves.

## Scope

The transfer principle used here is the one of the general module: it is stated for a functor
of *bimodule categories*, applied to complexes degree by degree through
`H.mapHomologicalComplex`. This is the shape of a Morita-type equivalence realised by a single
bimodule: such an equivalence is an equivalence of bimodule categories, and its action on a
complex of bimodules is the degreewise action of that equivalence.

A *derived* transfer, in which the target setting is reached by conjugating bimodules with a
tilting bimodule complex, is **not** covered. Conjugation by a tilting complex is not an
additive functor on bimodules, so it is not an instance of `H` here, and the principle cannot
be applied to it.

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

universe u w uA

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V)

local notation "c" => ComplexShape.up ℤ

section Zigzag

variable [Finite V]

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

/-- The regular graded zigzag bimodule concentrated in cohomological degree zero: the
common target of the two one-sided inverse-product equivalences of the braid family. -/
abbrev zigzagBraidUnitComplex :
    HomologicalComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) c :=
  (HomologicalComplex.single (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
    c 0).obj (zigzagGradedBimodule k G)

/-- The regular graded zigzag bimodule is the unit complex of the graded bimodule setting of
the zigzag algebra: the homotopy equivalence between the regular graded bimodule in
cohomological degree zero and the unit complex of that setting. It is the transport of
`zigzagGradedBimoduleUnitIso` to the single-degree complex. -/
def zigzagBraidUnitComplexHomotopyEquiv :
    HomotopyEquiv (zigzagBraidUnitComplex k G)
      (gradedBimoduleUnitComplex k (zigzagAlgebraInternalGrading k G)) :=
  HomotopyEquiv.ofIso
    ((HomologicalComplex.single (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
      c 0).mapIso (zigzagGradedBimoduleUnitIso k G).symm)

/-- The zigzag braid complexes satisfy the Khovanov-Seidel relations, with the inverse
complexes as prescribed inverses and the regular graded bimodule concentrated in cohomological
degree zero as the unit. -/
def zigzagBraidComplexRelations :
    KhovanovSeidelRelations k G (zigzagAlgebraInternalGrading k G)
      (zigzagBraidComplex k G) (zigzagBraidInverseComplex k G) where
  inverseForward i := (zigzagBraidComplexTensorInverseHomotopyEquiv k G i).trans
    (zigzagBraidUnitComplexHomotopyEquiv k G)
  inverseReverse i := (zigzagBraidInverseTensorComplexHomotopyEquiv k G i).trans
    (zigzagBraidUnitComplexHomotopyEquiv k G)
  commute := zigzagBraidComplexTensorCommHomotopyEquiv k G
  braid h := zigzagBraidComplexAdjacentHomotopyEquiv k G h

section ZigzagTransfer

variable {A : Type uA} [Ring A] [Algebra k A]
variable (Ξ : InternalGrading k A) [GradedAlgebra Ξ.piece]
variable (H : GradedBimoduleCat k (zigzagAlgebraInternalGrading k G) ⥤ GradedBimoduleCat k Ξ)
  [H.Additive]

/-- Transfer of the Khovanov-Seidel relations of the zigzag braid complexes to a family of
complexes in a second graded bimodule setting, the setting of the graded algebra `A` with
internal grading `Ξ`. The functor `H` is an additive functor from the setting of the zigzag
braid complexes to that second setting, `η` is its pointwise homotopy-monoidal datum, `ε`
compares the image of the unit complex of the zigzag setting with the unit complex of the
target setting, and `a` and `a'` identify the image of the zigzag braid complexes with the
target family. -/
def zigzagBraidRelationsTransfer
    (η : GradedBimoduleMonoidalDatum k (zigzagAlgebraInternalGrading k G) Ξ H)
    (ε : HomotopyEquiv
      ((H.mapHomologicalComplex c).obj
        (gradedBimoduleUnitComplex k (zigzagAlgebraInternalGrading k G)))
      (gradedBimoduleUnitComplex k Ξ))
    {C C' : V → HomologicalComplex (GradedBimoduleCat k Ξ) c}
    (a : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj (zigzagBraidComplex k G i))
      (C i))
    (a' : ∀ i, HomotopyEquiv ((H.mapHomologicalComplex c).obj
      (zigzagBraidInverseComplex k G i)) (C' i)) :
    KhovanovSeidelRelations k G Ξ C C' :=
  (zigzagBraidComplexRelations k G).transfer η ε a a'

/-- The complexes `H(zigzagBraidComplex i)` and their inverses
`H(zigzagBraidInverseComplex i)`, the images of the zigzag braid complexes under
`H.mapHomologicalComplex`, satisfy the Khovanov-Seidel relations in the target graded
bimodule setting: this is `zigzagBraidRelationsTransfer` with identity homotopy equivalences
for `a` and `a'`. -/
def zigzagBraidMapHomologicalComplexRelations
    (η : GradedBimoduleMonoidalDatum k (zigzagAlgebraInternalGrading k G) Ξ H)
    (ε : HomotopyEquiv
      ((H.mapHomologicalComplex c).obj
        (gradedBimoduleUnitComplex k (zigzagAlgebraInternalGrading k G)))
      (gradedBimoduleUnitComplex k Ξ)) :
    KhovanovSeidelRelations k G Ξ
      (fun i => (H.mapHomologicalComplex c).obj (zigzagBraidComplex k G i))
      (fun i => (H.mapHomologicalComplex c).obj (zigzagBraidInverseComplex k G i)) :=
  zigzagBraidRelationsTransfer k G Ξ H η ε (fun _ => HomotopyEquiv.refl _)
    (fun _ => HomotopyEquiv.refl _)

end ZigzagTransfer

end Zigzag

end TauCeti

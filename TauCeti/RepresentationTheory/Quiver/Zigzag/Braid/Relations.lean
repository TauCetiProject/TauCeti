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

/-!
# The zigzag braid complexes as a family of Khovanov-Seidel relations

The zigzag braid complexes satisfy the Khovanov-Seidel relations: the two one-sided inverse
products are homotopy equivalent to the regular graded bimodule concentrated in cohomological
degree zero, the nonadjacent factors commute up to chain homotopy, and the adjacent factors
satisfy the braid relation up to chain homotopy.

This file instantiates the abstract relations of
`TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.BraidRelations` for the zigzag
algebra. The unit complex of the graded bimodule setting of the zigzag algebra is the regular
graded zigzag bimodule in cohomological degree zero; the declarations
`zigzagBraidUnitComplex` and `zigzagBraidUnitComplexHomotopyEquiv` of
`TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Unit` spell it out and identify it with the
unit complex of that setting.

The four field values of the zigzag braid relations are the public declarations
`zigzagBraidComplexTensorInverseHomotopyEquiv`, `zigzagBraidInverseTensorComplexHomotopyEquiv`,
`zigzagBraidComplexTensorCommHomotopyEquiv` and `zigzagBraidComplexAdjacentHomotopyEquiv`, and
the four projection lemmas `zigzagBraidComplexRelations_inverseForward` and its three siblings
read those values off the relations.

The relations of the image complexes `H(zigzagBraidComplex i)` under the degreewise action of
an additive functor `H` of graded bimodule categories are the degreewise transfer
`KhovanovSeidelRelations.transferDegreewise` of the zigzag braid relations,
`(zigzagBraidComplexRelations k G).transferDegreewise η ε (fun _ => .refl _) (fun _ => .refl _)`,
applied with the identity homotopy equivalences for the source family and its inverse; the
projection lemmas `transferDegreewise_inverseForward` and its three siblings read its four
field values off.

## Scope

The relations `zigzagBraidComplexRelations` can be fed to `KhovanovSeidelRelations.transfer`
and `KhovanovSeidelRelations.transferDegreewise`, which transport them to a target graded
bimodule setting.

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

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V)

section Zigzag

variable [Finite V]

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

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

-- The four field values of `zigzagBraidComplexRelations` are read off by the four projection
-- lemmas below. Their proofs are written `(rfl)` and not `rfl`: a theorem whose proof is
-- syntactically `rfl` is tagged `@[defeq]`, and the module system refuses to export a
-- `@[defeq]` theorem whose proof needs the body of a definition that is not exposed.

/-- The forward inverse relation of the zigzag braid relations is the inverse-product homotopy
equivalence `zigzagBraidComplexTensorInverseHomotopyEquiv` followed by the unit-complex
homotopy equivalence `zigzagBraidUnitComplexHomotopyEquiv`. -/
@[simp] theorem zigzagBraidComplexRelations_inverseForward (i : V) :
    (zigzagBraidComplexRelations k G).inverseForward i
      = (zigzagBraidComplexTensorInverseHomotopyEquiv k G i).trans
        (zigzagBraidUnitComplexHomotopyEquiv k G) := (rfl)

/-- The reverse inverse relation of the zigzag braid relations is the inverse-product homotopy
equivalence `zigzagBraidInverseTensorComplexHomotopyEquiv` followed by the unit-complex
homotopy equivalence `zigzagBraidUnitComplexHomotopyEquiv`. -/
@[simp] theorem zigzagBraidComplexRelations_inverseReverse (i : V) :
    (zigzagBraidComplexRelations k G).inverseReverse i
      = (zigzagBraidInverseTensorComplexHomotopyEquiv k G i).trans
        (zigzagBraidUnitComplexHomotopyEquiv k G) := (rfl)

/-- The commutation relation of the zigzag braid relations is the commuting homotopy
equivalence `zigzagBraidComplexTensorCommHomotopyEquiv`. -/
@[simp] theorem zigzagBraidComplexRelations_commute
    (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    (zigzagBraidComplexRelations k G).commute i j hij hadj
      = zigzagBraidComplexTensorCommHomotopyEquiv k G i j hij hadj := (rfl)

/-- The braid relation of the zigzag braid relations is the adjacent homotopy equivalence
`zigzagBraidComplexAdjacentHomotopyEquiv`. -/
@[simp] theorem zigzagBraidComplexRelations_braid {i j : V} (h : G.Adj j i) :
    (zigzagBraidComplexRelations k G).braid h
      = zigzagBraidComplexAdjacentHomotopyEquiv k G h := (rfl)

end Zigzag

end TauCeti

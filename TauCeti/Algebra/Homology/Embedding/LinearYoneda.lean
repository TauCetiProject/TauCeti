/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.Ext
public import TauCeti.Algebra.Homology.Embedding.DownNatAdd
public import TauCeti.Algebra.Homology.Embedding.MapExtend

/-!
# Morphisms out of an extended chain complex

For a chain complex `X` in a `k`-linear abelian category and an object `Y`, the cochain complex
`Hom(X, Y)` (Mathlib's `ChainComplex.linearYonedaObj`) is computed degreewise. Extending `X` along
an embedding `e` of complex shapes (`HomologicalComplex.extend`) puts zero objects in the degrees
outside the image of `e`, and morphisms out of a zero object form the zero module. So
`Hom(X.extend e, Y)` is the extension of `Hom(X, Y)` along the opposite embedding
(`ChainComplex.linearYonedaObjExtendIso`).

In particular, placing a chain complex indexed by `ℕ` `n` degrees higher
(`ComplexShape.embeddingDownNatAdd n`) places its cochain complex of morphisms into `Y` `n`
degrees higher too, so that the cohomology of `Hom(X.extend e, Y)` in degree `q + n` is the
cohomology of `Hom(X, Y)` in degree `q` (`ChainComplex.linearYonedaObjExtendHomologyIso`). This is
how a chain-level identification of one complex with a shift of another, such as the cap product
of a Thom isomorphism, computes cohomology with values in any `Y`.

## Main definitions

* `ChainComplex.linearYonedaObjExtendIso`: the isomorphism
  `Hom(X.extend e, Y) ≅ Hom(X, Y).extend e.op`.
* `ChainComplex.linearYonedaObjExtendHomologyIso`: for the embedding `n ↦ n + k` of
  `ComplexShape.down ℕ`, the isomorphism `H^{q + n}(Hom(X.extend e, Y)) ≅ H^q(Hom(X, Y))`.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace ChainComplex

variable {C : Type*} [Category* C] [Abelian C] {k : Type*} [Ring k] [Linear k C] (Y : C)
  {α β : Type*} [AddRightCancelSemigroup α] [One α] [AddRightCancelSemigroup β] [One β]

/-- **Morphisms out of an extended chain complex.** For an embedding `e` of complex shapes, the
cochain complex of morphisms from the extension `X.extend e` into `Y` is the extension of the
cochain complex of morphisms from `X` into `Y` along the opposite embedding: both are zero outside
the image of `e`. -/
def linearYonedaObjExtendIso (X : ChainComplex C α)
    (e : (ComplexShape.down α).Embedding (ComplexShape.down β)) :
    ChainComplex.linearYonedaObj (X.extend e) k Y ≅ (X.linearYonedaObj k Y).extend e.op :=
  -- `Hom(-, Y)` is the image under the additive functor `Hom(-, Y)ᵒᵖ` followed by `unop`; the
  -- functor commutes with the extension, and so does `unop`, through Mathlib's `extendOpIso`
  (HomologicalComplex.unopFunctor _ _).mapIso
      (HomologicalComplex.mapExtendIso ((linearYoneda k C).obj Y).rightOp X e).symm.op ≪≫
    (HomologicalComplex.unopFunctor _ _).mapIso
      ((X.linearYonedaObj k Y).extendOpIso e.op).symm.op

/-- **Cohomology of morphisms out of a shifted chain complex.** If a chain complex `X` indexed by
`ℕ` is placed `n` degrees higher, the cohomology in degree `q + n` of the complex of morphisms
from it into `Y` is the cohomology in degree `q` of the complex of morphisms from `X` into `Y`. -/
def linearYonedaObjExtendHomologyIso (X : ChainComplex C ℕ) (n q : ℕ) :
    (ChainComplex.linearYonedaObj (X.extend (ComplexShape.embeddingDownNatAdd n)) k Y).homology
      (q + n) ≅
      (X.linearYonedaObj k Y).homology q :=
  (HomologicalComplex.homologyFunctor _ _ (q + n)).mapIso
      (linearYonedaObjExtendIso Y X (ComplexShape.embeddingDownNatAdd n)) ≪≫
    (X.linearYonedaObj k Y).extendHomologyIso (ComplexShape.embeddingDownNatAdd n).op
      (j := q) (ComplexShape.embeddingDownNatAdd_f n q)

end ChainComplex

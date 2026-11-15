/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import TauCeti.Topology.Category.TopCat.FunctorTensor

/-!
# The fat realization of a semi-simplicial space

A semi-simplicial space is a functor `X : SemiSimplexCategoryᵒᵖ ⥤ TopCat`: a space `Xₙ` for each
`n` with face maps along the order embeddings `⦋m⦌ₛ ⟶ ⦋n⦌ₛ`, but no degeneracies. Its fat
realization `‖X‖` (`TauCeti.fatRealization X`) is the functor tensor product
`TauCeti.functorTensor SemiSimplexCategory.toTop X`: the quotient of the disjoint union
`Σ n, Xₙ × Δⁿ` by the identifications `(X(f) x, t) ∼ (x, f_* t)` for every order embedding
`f : ⦋m⦌ₛ ⟶ ⦋n⦌ₛ`, where `f_*` is the induced face inclusion of topological simplices
(`SemiSimplexCategory.toTop`).

Characteristic maps (`TauCeti.functorTensor.ι`), universal property (`TauCeti.functorTensor.desc`,
`TauCeti.functorTensor.hom_ext`), functoriality (`TauCeti.fatRealizationFunctor`,
`TauCeti.functorTensor.map`), augmentations (`TauCeti.functorTensor.augment`), homotopies
(`TauCeti.functorTensor.homotopy`), and open/closed restrictions for saturated subfunctors
(`TauCeti.functorTensor.isOpenEmbedding_map`, `TauCeti.functorTensor.isClosedEmbedding_map`) are
inherited directly from `TauCeti.Topology.Category.TopCat.FunctorTensor`.

## References

* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* J. Ebert and O. Randal-Williams, *Semi-simplicial spaces*, Algebraic & Geometric Topology **19**
  (2019), 2099–2150, §1.2.
-/

public noncomputable section

open CategoryTheory

universe u

namespace SemiSimplexCategory

/-- The functor sending `⦋n⦌ₛ` to the topological `n`-simplex and an order embedding to the
induced face inclusion of topological simplices. -/
@[expose] def toTop : SemiSimplexCategory ⥤ TopCat.{u} :=
  toSimplexCategory ⋙ SimplexCategory.toTop

/-- The topological simplex of `⦋n⦌ₛ` is that of `⦋n⦌`. -/
theorem toTop_obj (n : SemiSimplexCategory) :
    toTop.{u}.obj n = SimplexCategory.toTop.obj (toSimplexCategory.obj n) :=
  (rfl)

/-- The face inclusion along an order embedding is the map of topological simplices induced by
the underlying morphism of the simplex category. -/
theorem toTop_map {m n : SemiSimplexCategory} (f : m ⟶ n) :
    toTop.{u}.map f = SimplexCategory.toTop.map (toSimplexCategory.map f) :=
  (rfl)

/-- Every topological simplex of `SemiSimplexCategory` is nonempty. -/
instance nonempty_toTop_obj (n : SemiSimplexCategory) : Nonempty (toTop.{u}.obj n) :=
  inferInstanceAs (Nonempty (SimplexCategory.toTop.{u}.obj (toSimplexCategory.obj n)))

end SemiSimplexCategory

namespace TauCeti

/-- The fat realization `‖X‖` of a semi-simplicial space `X`: the functor tensor product of
`SemiSimplexCategory.toTop` and `X`. -/
abbrev fatRealization (X : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}) : TopCat.{u} :=
  functorTensor SemiSimplexCategory.toTop X

/-- The fat realization as a functor from semi-simplicial spaces to spaces. -/
abbrev fatRealizationFunctor : (SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}) ⥤ TopCat.{u} :=
  functorTensorFunctor SemiSimplexCategory.toTop

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.TopologicalSimplex
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

Universal property, functoriality, quotient topology, augmentations, homotopies, and open/closed
restrictions for saturated subfunctors are provided directly by `TauCeti.functorTensor` in
`TauCeti.Topology.Category.TopCat.FunctorTensor` specialized to `SemiSimplexCategory.toTop`;
barycentric coordinates, boundaries, and carrier faces of `SemiSimplexCategory.toTop` live in
`TauCeti.AlgebraicTopology.TopologicalSimplex`; and skeletal filtrations and paracompactness live
in `TauCeti.AlgebraicTopology.FatRealization.Skeleton`.

## References

* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* J. Ebert and O. Randal-Williams, *Semi-simplicial spaces*, Algebraic & Geometric Topology **19**
  (2019), 2099–2150, §1.2.
-/

public noncomputable section

open CategoryTheory

universe u

namespace TauCeti

open SemiSimplexCategory (toTop)

/-- The fat realization `‖X‖` of a semi-simplicial space `X`: the functor tensor product of
`SemiSimplexCategory.toTop` and `X`. -/
abbrev fatRealization (X : SemiSimplexCategoryᵒᵖ ⥤ TopCat.{u}) : TopCat.{u} :=
  functorTensor toTop X

end TauCeti

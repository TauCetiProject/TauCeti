/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Subdivision.Subcomplex
public import TauCeti.Geometry.Manifold.SmoothSingular.Basic

/-!
# Barycentric subdivision of smooth singular chains

An affine map `A : Δᵏ → Δᵐ` of standard simplices, read on full-dimensional simplices, is the
restriction of a continuous affine map of the ambient Euclidean spaces
(`TauCeti.exists_continuousAffineMap_eq_affineMapMk`). So the composite `σ ∘ A` of a smooth singular
simplex `σ` of a manifold `M` with `A` is again smooth: the subcomplex of smooth singular simplices
is affinely stable (`SSet.Subcomplex.IsAffineStable`).

Barycentric subdivision and its prism operator therefore restrict to the smooth singular chains
`(smoothSingularSubcomplex I M : SSet).chainComplex R`. On these chains subdivision is a chain map
compatible with the inclusion into singular chains (`TauCeti.subcomplexSubdivisionChainMap_ι`),
chain homotopic to the identity through the prism operator
(`TauCeti.subcomplexSubdivisionHomotopy`), and it induces the identity on smooth singular homology
(`TauCeti.homologyMap_subcomplexSubdivisionChainMap`). Both operators commute with the maps
`TauCeti.smoothSingularSubcomplexMap` induced by smooth maps
(`TauCeti.subcomplexSubdivisionChainMap_naturality` and `TauCeti.subcomplexPrismX_naturality`,
with `TauCeti.smoothSingularSubcomplexMap_ι` as the compatibility hypothesis).

These operators are the input to the small-chain theorem for smooth chains, in which a smooth chain
is replaced by a fine subdivision of it without leaving the smooth chains: for an open cover of
`M`, the smooth singular simplices subordinate to the cover include into all smooth singular
chains by a chain homotopy equivalence (`TauCeti.subcomplexSmallChainHomotopyEquiv`, which applies
to every affinely stable subcomplex). That theorem is a step in comparing smooth with continuous
singular homology.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18, proof of Theorem 18.7.
* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.21.
-/

public section

noncomputable section

open CategoryTheory Convexity Set Simplicial
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- The smooth singular simplices form an affinely stable subcomplex: precomposing a smooth
singular simplex with an affine map of standard simplices gives a smooth singular simplex. Hence
barycentric subdivision and its prism operator restrict to smooth singular chains. -/
instance : (smoothSingularSubcomplex I M).IsAffineStable where
  comp_affineMapMk_mem {m k σ} hσ v := by
    obtain ⟨A, hA⟩ := exists_continuousAffineMap_eq_affineMapMk v
    have hst : MapsTo A (fullSimplex k) (fullSimplex m) := fun x hx ↦
      hA ⟨x, hx⟩ ▸ Subtype.prop _
    rw [mem_smoothSingularSubcomplex_iff] at hσ ⊢
    convert hσ.comp_contDiff A.contDiff hst using 1
    funext x
    have hx : hst.restrict A _ _ x = (fullSimplexEquivStdSimplex m).symm
        (StdSimplex.affineMapMk v (fullSimplexEquivStdSimplex k x)) :=
      Subtype.ext (hA x)
    simp [hx]

end TauCeti

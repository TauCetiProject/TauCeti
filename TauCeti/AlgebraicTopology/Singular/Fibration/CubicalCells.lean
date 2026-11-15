/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Excision
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Additivity
public import TauCeti.AlgebraicTopology.Singular.Fibration.CellFiber

/-!
# Relative cubical chains of the skeletal pairs of a Serre fibration

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex with skeleta
`Xⁿ = skeletonLT C (n + 1)`. For each `n`-cell `j`, let `(Pⱼ, ∂Pⱼ)` be the pullback of `p` along
the characteristic map of `j`, relative to its part over the boundary sphere
(`TauCeti.TopCat.cellDiskPullbackPair`). The projections `(Pⱼ, ∂Pⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))`
(`TauCeti.TopCat.cellDiskPullbackPairMap`) assemble into a chain map

`⨁ⱼ N(Pⱼ, ∂Pⱼ) ⟶ N(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))`

of relative normalized cubical chain complexes, over any ring `k`, and this map is a
quasi-isomorphism
(`TauCeti.TopCat.quasiIso_sigmaDesc_cubicalChainComplexMap_cellDiskPullbackPairMap`). It is the
excision step that cuts the relative chains of consecutive stages of the filtration
`Eₙ = p⁻¹(Xⁿ)` into the relative chains over the single cells. For the based path fibration of a
CW complex, the relative chains over a single cell are quasi-isomorphic to a free module over the
chains on the loop space, so this is the form in which Brown's semi-free model of the path chains
is compared, one skeleton at a time, with the skeletal filtration of the path chains.

The statement on homology is
`TauCeti.TopCat.isColimitCofanSingularHomologyPreimageSkeletonPair`, for singular chains. It
transfers to cubical chains along the comparison of relative cubical and singular homology, in two
steps:

* the projection from the pullback `(P, ∂P)` of `p` to the disks of all `n`-cells is a cubical
  quasi-isomorphism (`TauCeti.TopCat.quasiIso_cubicalChainComplexMap_cellPullbackPairMap`), the
  cubical form of `TauCeti.TopCat.isIso_singularHomologyMap_cellPullbackPairMap`;
* `(P, ∂P)` is the coproduct of the `(Pⱼ, ∂Pⱼ)` in `TopPair`
  (`TauCeti.TopCat.isColimitCofanCellDiskPullbackPairι`), and relative cubical chains are additive
  up to quasi-isomorphism (`TopPair.quasiIso_sigmaDesc_cubicalChainComplexMap`).

## Main results

* `TauCeti.TopCat.quasiIso_cubicalChainComplexMap_cellPullbackPairMap`: the projection
  `N(P, ∂P) ⟶ N(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` is a quasi-isomorphism.
* `TauCeti.TopCat.quasiIso_sigmaDesc_cubicalChainComplexMap_cellDiskPullbackPairMap`: the map
  `⨁ⱼ N(Pⱼ, ∂Pⱼ) ⟶ N(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` is a quasi-isomorphism.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe u

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]
  (hp : serreFibrations p) (k : Type u) [Ring k]

include hp

variable (C) in
/-- **The pullback to the disks of the cells computes the relative cubical chains of a skeletal
pair.** For a Serre fibration `p`, the projection `(P, ∂P) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` from the
pullback of `p` to the disks of the `n`-cells, relative to its part over their boundary spheres,
induces a quasi-isomorphism of relative normalized cubical chain complexes. -/
theorem quasiIso_cubicalChainComplexMap_cellPullbackPairMap (n : ℕ) :
    QuasiIso (TopPair.cubicalChainComplexMap k (cellPullbackPairMap p C n)) :=
  (quasiIso_iff _).2 fun q ↦ (quasiIsoAt_iff_isIso_homologyMap _ _).2
    (have := isIso_singularHomologyMap_cellPullbackPairMap C hp k n q
    TopPair.isIso_homologyMap_cubicalChainComplexMap_of_isIso _ q)

variable (C) in
/-- **The relative cubical chains of a skeletal pair of a Serre fibration are the sum of those over
the cells.** For a Serre fibration `p` over a relative CW complex, the chain map
`⨁ⱼ N(Pⱼ, ∂Pⱼ) ⟶ N(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))`, given on the summand of the `n`-cell `j` by the projection
from the pullback of `p` along its characteristic map, relative to the part over the boundary
sphere, is a quasi-isomorphism of relative normalized cubical chain complexes. -/
theorem quasiIso_sigmaDesc_cubicalChainComplexMap_cellDiskPullbackPairMap (n : ℕ) :
    QuasiIso (Sigma.desc fun j : cell C n ↦
      TopPair.cubicalChainComplexMap k (cellDiskPullbackPairMap p C n j)) := by
  have := TopPair.quasiIso_sigmaDesc_cubicalChainComplexMap k
    (isColimitCofanCellDiskPullbackPairι p C n)
  have := quasiIso_cubicalChainComplexMap_cellPullbackPairMap C hp k n
  -- Each projection factors through the inclusion of its cell into the pullback over all cells.
  rw [show (Sigma.desc fun j : cell C n ↦
      TopPair.cubicalChainComplexMap k (cellDiskPullbackPairMap p C n j)) =
        (Sigma.desc fun j ↦ TopPair.cubicalChainComplexMap k (cellDiskPullbackPairι p C n j)) ≫
          TopPair.cubicalChainComplexMap k (cellPullbackPairMap p C n) by
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    rw [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, cellDiskPullbackPairMap_def,
      TopPair.cubicalChainComplexMap_comp]]
  infer_instance

end TopCat

end TauCeti

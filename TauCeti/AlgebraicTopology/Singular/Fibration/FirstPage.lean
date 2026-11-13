/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.CellFiber
public import TauCeti.AlgebraicTopology.Singular.Fibration.Convergence

/-!
# The first page of the Serre spectral sequence

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex. The first page of the
Serre spectral sequence `TauCeti.TopCat.serreSpectralSequence C p R`, the spectral sequence of the
filtration of `E` by the preimages of the skeleta of `C`, is the direct sum, over the cells of `C`,
of the homology of the fibres over their centres. In the classical homological indexing,

`E¹_{k,q} ≅ ⨁ⱼ Hq(p⁻¹(χⱼ(0)); R)`,

the sum running over the `k`-cells `j` of `C`, with `χⱼ(0)` the centre of the cell `j`
(`TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoSigma`). On the summand of `j` the inverse is
induced by the pullback of `p` along the characteristic map of `j`
(`TauCeti.TopCat.ι_serreSpectralSequenceFirstPageXIsoSigma_inv`). For the identity fibration these
are the cellular chain groups.

The spectral sequence of a filtered space lives in cohomological indexing: the object at
`(a, b)` of its first page (numbered `2`) is `Hₙ(E_{b+1}, E_b; R)` with `a + b = -n`
(`TauCeti.filteredSpaceSpectralSequenceFirstPageXIso`). With `E_b = p⁻¹(C^(b))`, the classical
position `(k, q)` is `(a, b) = (1 - q - 2k, k - 1)`. The relative homology of consecutive preimages
of the skeleta is computed cell by cell in `TauCeti.AlgebraicTopology.Singular.Fibration.CellFiber`
(`TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma`); this file reads that computation
on the first page.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 5.1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 5.1, the proof of Theorem 5.15.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]
  (hp : serreFibrations p) (R : Type u) [Ring R]

include hp

variable (C) in
/-- **The first page of the Serre spectral sequence.** For a Serre fibration `p : E ⟶ B` and a
relative CW complex `C ⊆ B`, the object of the first page (numbered `2`) of the spectral sequence of
the filtration of `E` by the preimages of the skeleta at `pq = (a, b)`, with `b = k - 1` and
`a + b = -(q + k)`, is the direct sum `⨁ⱼ Hq(p⁻¹(χⱼ(0)); R)` over the `k`-cells `j` of `C`. In the
classical indexing this is `E¹_{k,q}`. -/
def serreSpectralSequenceFirstPageXIsoSigma (k q : ℕ) (pq : ℤ × ℤ) (hb : pq.2 = k - 1)
    (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    ((serreSpectralSequence C p R).page 2).X pq ≅
      ∐ fun j : cell C k ↦ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {map k j 0} : Set E)) :=
  filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R) (monotone_preimageSkeleton p) pq
      pq.2 (pq.2 + 1) rfl rfl _ rfl (q + k) ha ≪≫
    eqToIso (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) (q + k))
      (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair k pq.2 hb)) ≪≫
    preimageSkeletonPairSingularHomologyIsoSigma C hp R k q

/-- On the summand of the `k`-cell `j`, the inverse of
`TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoSigma` is induced by the pullback of `p` along the
characteristic map of `j`, `Hq(p⁻¹(χⱼ(0))) ≅ Hq+k(Pⱼ, ∂Pⱼ) ⟶ Hq+k(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹))`. -/
@[reassoc (attr := simp)]
lemma ι_serreSpectralSequenceFirstPageXIsoSigma_inv (k q : ℕ) (pq : ℤ × ℤ) (hb : pq.2 = k - 1)
    (ha : pq.1 + pq.2 = -(q + k : ℕ)) (j : cell C k) :
    Sigma.ι _ j ≫ (serreSpectralSequenceFirstPageXIsoSigma C hp R k q pq hb ha).inv =
      (cellDiskPullbackPairSingularHomologyIso hp R k q j).inv ≫
        (cellDiskPullbackPair p C k j).singularHomologyMap (cellDiskPullbackPairMap p C k j)
          (ModuleCat.of R R) (q + k) ≫
        eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) (q + k))
          (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair k pq.2 hb)).symm ≫
        (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R)
          (monotone_preimageSkeleton p) pq pq.2 (pq.2 + 1) rfl rfl (pq.1 + pq.2) rfl (q + k)
          ha).inv := by
  simp [serreSpectralSequenceFirstPageXIsoSigma]

end TopCat

end TauCeti

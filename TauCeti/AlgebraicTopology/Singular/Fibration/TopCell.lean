/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Skeleton
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Puncture

/-!
# Classes living over the fundamental class, read on the skeleton below the top cell

Let `p : E ⟶ B` be a Serre fibration over a relative CW complex `C ⊆ B` of dimension `n`, that is
`B = Xⁿ = skeletonLT C (n + 1)`, with a single `n`-cell `j`, whose centre is `b = map n j 0`.
Barraud–Damian–Humilière–Oancea read the shriek map of the inclusion of `b` through such a CW
structure (their Lemma 2.9): it is the map `Hₖ(E) ⟶ Hₖ(E, p⁻¹(Xⁿ⁻¹))` to the homology relative to
the part of `E` over the `(n-1)`-skeleton `Xⁿ⁻¹ = skeletonLT C n`, followed by the identification
of the relative group with `Hₖ₋ₙ(p⁻¹(b))`. In Tau Ceti a class lives over the fundamental class at
`b` when its image in the local homology `Hₖ(E, E ∖ p⁻¹(b))` along the fibre is nonzero
(`TauCeti.LivesOverFundamentalClass`). This file compares the two subspaces.

Since `b` does not lie in `Xⁿ⁻¹`, the identity of `E` is a map of pairs
`(E, p⁻¹(Xⁿ⁻¹)) ⟶ (E, E ∖ p⁻¹(b))`, and it induces isomorphisms on relative singular homology in
every degree and with every module of coefficients
(`TauCeti.TopCat.isIso_singularHomologyMap_ofSubsetMap_preimage_skeletonLT`). So a class lives over
the fundamental class at `b` exactly when its image in `Hₖ(E, p⁻¹(Xⁿ⁻¹))` is nonzero
(`TauCeti.livesOverFundamentalClass_iff_singularHomologyπ_preimage_skeletonLT_ne_zero`), that is,
by the long exact sequence of the pair, exactly when it does not come from the homology of the part
of `E` over `Xⁿ⁻¹` (`TauCeti.livesOverFundamentalClass_iff_notMem_range_preimage_skeletonLT`). This
is the equivalence of conditions (i) and (iii) in the source's Proposition 2.6.

The image of `Hₖ(p⁻¹(Xⁿ⁻¹))` in `Hₖ(E)` is the stage `n - 1` of the filtration of the abutment of
the Serre spectral sequence of `p` over `C`, so the last statement says that `α` has a nonzero image
in the rightmost column `E^∞_{n, k-n}`, the source's condition (ii). The identification of that
quotient with the objects of the spectral sequence is not made here.

## The comparison

By the long exact sequence of the triple `(E, E ∖ p⁻¹(b), p⁻¹(Xⁿ⁻¹))` it suffices that the pair
`(E ∖ p⁻¹(b), p⁻¹(Xⁿ⁻¹))` be acyclic
(`TauCeti.TopCat.isZero_singularHomology_preimage_skeletonDiffCenter`). It is filtered by the part
of `E` over the neighbourhood `N = TauCeti.skeletonNeighborhood C n` of `Xⁿ⁻¹`, and both steps are
acyclic because a Serre fibration pulls back a pair that deforms into its subspace relative to that
subspace to an acyclic pair (`TauCeti.TopCat.isZero_singularHomology_preimage_of_homotopyRel`):

* `Xⁿ ∖ {b}` deforms into `N` relative to `N`, by pushing the punctured inner half of the cell
  radially outwards (`TauCeti.skeletonDiffCenterHomotopyRel`; with a single `n`-cell the
  complement of the inner half of `j` is `N`, `TauCeti.skeletonDiffCore_eq_skeletonNeighborhood`);
* `N` deforms onto `Xⁿ⁻¹` relative to `Xⁿ⁻¹` (`TauCeti.skeletonNeighborhoodHomotopyRel`).

With several `n`-cells the relative group `Hₖ(E, p⁻¹(Xⁿ⁻¹))` is a sum over all of them, and only the
summand of the cell containing `b` is seen by the local homology at `b`; the single top cell is the
hypothesis of the source's Lemma 2.9.

## Main results

* `TauCeti.TopCat.isZero_singularHomology_preimage_skeletonDiffCenter`: the pair
  `(p⁻¹(Xⁿ ∖ {b}), p⁻¹(Xⁿ⁻¹))` is acyclic.
* `TauCeti.TopCat.isIso_singularHomologyMap_ofSubsetMap_preimage_skeletonLT`: the identity induces
  isomorphisms `Hₖ(E, p⁻¹(Xⁿ⁻¹)) ≅ Hₖ(E, E ∖ p⁻¹(b))`.
* `TauCeti.livesOverFundamentalClass_iff_singularHomologyπ_preimage_skeletonLT_ne_zero` and
  `TauCeti.livesOverFundamentalClass_iff_notMem_range_preimage_skeletonLT`: the source's
  Proposition 2.6, (i) ⇔ (iii).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4, Definition 2.3, Proposition 2.6 and
  Lemma 2.9.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
-/

public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]
  {n : ℕ} [Subsingleton (cell C n)] (j : cell C n) (hp : serreFibrations p)
  {R : Type*} [Ring R] (M : ModuleCat.{u} R)

include hp in
/-- **The part of a Serre fibration over the skeleton punctured at the centre of its only top cell
is acyclic modulo the part over the lower skeleton.** Let `p : E ⟶ B` be a Serre fibration and
`C ⊆ B` a relative CW complex with a single `n`-cell `j`. Then
`Hₘ(p⁻¹(Xⁿ ∖ {map n j 0}), p⁻¹(Xⁿ⁻¹); M) = 0` for every `m` and every module `M`. -/
theorem isZero_singularHomology_preimage_skeletonDiffCenter (m : ℕ) :
    IsZero ((TopPair.ofInclusion (X := E)
      (preimage_mono (f := p) (skeletonLT_subset_skeletonDiffCenter j))).singularHomology M m) := by
  have hNS : skeletonNeighborhood C n ⊆ skeletonDiffCenter j :=
    skeletonDiffCore_eq_skeletonNeighborhood j ▸ skeletonDiffCore_subset_skeletonDiffCenter j
  -- The part over `N` is acyclic modulo the part over `Xⁿ⁻¹`.
  have hinner := isZero_singularHomology_preimage_of_homotopyRel hp
    (skeletonLT_subset_skeletonNeighborhood (C := C) n) (skeletonNeighborhoodHomotopyRel C n)
    (fun x ↦ skeletonNeighborhoodEndpoint_mem _ x.2) M m
  -- The part over `Xⁿ ∖ {b}` is acyclic modulo the part over `N`.
  have houter := (TopPair.isZero_singularHomology_ofInclusion_congr M
    (preimage_mono (f := p) (skeletonDiffCore_subset_skeletonDiffCenter j))
    (preimage_mono (f := p) hNS) rfl
    (by rw [skeletonDiffCore_eq_skeletonNeighborhood j]) m).1
    (isZero_singularHomology_preimage_of_homotopyRel hp
      (skeletonDiffCore_subset_skeletonDiffCenter j) (skeletonDiffCenterHomotopyRel j)
      (skeletonDiffCenterEndpoint_mem j) M m)
  exact TopTriple.isZero_singularHomology_totalPair
    (TopTriple.ofInclusions (X := E)
      (preimage_mono (f := p) (skeletonLT_subset_skeletonNeighborhood (C := C) n))
      (preimage_mono (f := p) hNS)) M m hinner houter

variable {j}

omit [Subsingleton (cell C n)] in
/-- Over the `n`-skeleton, the complement of the fibre over the centre of the `n`-cell `j` is the
part over the punctured skeleton. -/
private lemma preimage_skeletonDiffCenter_eq
    (hB : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) = univ) :
    p ⁻¹' skeletonDiffCenter j = (p ⁻¹' {map n j 0})ᶜ := by
  ext x
  rw [mem_preimage, mem_skeletonDiffCenter, hB, mem_compl_iff, mem_preimage, mem_singleton_iff]
  exact and_iff_right (mem_univ _)

omit [Subsingleton (cell C n)] in
/-- The part of `E` over the `(n-1)`-skeleton misses the fibre over the centre of the
`n`-cell `j`. -/
private lemma preimage_skeletonLT_subset_compl :
    p ⁻¹' (skeletonLT C n : Set B) ⊆ (p ⁻¹' {map n j 0})ᶜ :=
  fun _ hx hb ↦ (mem_skeletonDiffCenter j).1 (skeletonLT_subset_skeletonDiffCenter j hx) |>.2 hb

omit [Subsingleton (cell C n)] in
/-- The part of `E` over the `(n-1)`-skeleton misses the fibre over the centre of the
`n`-cell `j`, so the identity of `E` maps it into the complement of that fibre. -/
lemma mapsTo_preimage_skeletonLT_compl_preimage_map_zero :
    MapsTo (𝟙 E) (p ⁻¹' (skeletonLT C n : Set B)) (p ⁻¹' {map n j 0})ᶜ :=
  fun _ hx ↦ preimage_skeletonLT_subset_compl hx

include hp in
/-- **The homology of a Serre fibration over a CW complex with a single top cell, relative to the
part over the lower skeleton, is the local homology along the fibre over the centre of the top
cell.** Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex whose `n`-skeleton
`Xⁿ = skeletonLT C (n + 1)` is all of `B` and which has a single `n`-cell `j`, with centre
`b = map n j 0`. The identity of `E`, as a map of pairs `(E, p⁻¹(Xⁿ⁻¹)) ⟶ (E, E ∖ p⁻¹(b))`,
induces isomorphisms on relative singular homology in every degree, with coefficients in every
module `M`. -/
theorem isIso_singularHomologyMap_ofSubsetMap_preimage_skeletonLT
    (hB : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) = univ) (m : ℕ) :
    IsIso (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 E)
      (mapsTo_preimage_skeletonLT_compl_preimage_map_zero (p := p) (j := j))) M m) := by
  have hz (k : ℕ) := (TopPair.isZero_singularHomology_ofInclusion_congr M
    (preimage_mono (f := p) (skeletonLT_subset_skeletonDiffCenter j))
    (preimage_skeletonLT_subset_compl (p := p) (j := j))
    (preimage_skeletonDiffCenter_eq hB) rfl k).1
    (isZero_singularHomology_preimage_skeletonDiffCenter j hp M k)
  have := TopTriple.isIso_singularHomologyMap_totalToOuter_of_isZero
    (TopTriple.ofSubset (X := E) (preimage_skeletonLT_subset_compl (p := p) (j := j))) M m
    (hz m) fun k _ ↦ hz k
  rw [TopTriple.totalToOuter_app_ofSubset] at this
  exact this

end TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]
  {n : ℕ} [Subsingleton (cell C n)] {j : cell C n} (hp : TopCat.serreFibrations p)
  (hB : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) = univ) {Λ : Type*} [Ring Λ]
  {M : ModuleCat.{u} Λ}

include hp hB in
/-- **Classes living over the fundamental class are detected on the skeleton below the top cell**
(Barraud–Damian–Humilière–Oancea, Proposition 2.6, (i) ⇔ (iii)). Let `p : E ⟶ B` be a Serre
fibration and `C ⊆ B` a relative CW complex whose `n`-skeleton is all of `B` and which has a single
`n`-cell `j`, with centre `b = map n j 0`. A class `α ∈ Hₖ(E; M)` lives over the fundamental class
at `b` exactly when its image in `Hₖ(E, p⁻¹(Xⁿ⁻¹); M)` is nonzero, where
`Xⁿ⁻¹ = skeletonLT C n`. -/
theorem livesOverFundamentalClass_iff_singularHomologyπ_preimage_skeletonLT_ne_zero {k : ℕ}
    (α : ((_root_.TopCat.toSSet.obj E).homology M k : ModuleCat.{u} Λ)) :
    LivesOverFundamentalClass M p (map n j 0) α ↔
      ((TopPair.ofSubset (p ⁻¹' (skeletonLT C n : Set B))).singularHomologyπ M k).hom α ≠ 0 := by
  have := TopCat.isIso_singularHomologyMap_ofSubsetMap_preimage_skeletonLT (j := j) hp M hB k
  -- The localization at the fibre factors through the isomorphism above.
  have h' : (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 E)
      (TopCat.mapsTo_preimage_skeletonLT_compl_preimage_map_zero (p := p) (j := j))) M k).hom
        (((TopPair.ofSubset (p ⁻¹' (skeletonLT C n : Set B))).singularHomologyπ M k).hom α) =
      (fiberLocalization M p (map n j 0) k).hom α :=
    congrArg (fun g ↦ g.hom α) (TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id M
      (TopCat.mapsTo_preimage_skeletonLT_compl_preimage_map_zero (p := p) (j := j)) k)
  rw [livesOverFundamentalClass_iff, ← h', not_iff_not]
  exact ((ModuleCat.mono_iff_injective _).1 inferInstance).eq_iff' (map_zero _)

include hp hB in
/-- **Classes living over the fundamental class are the classes not coming from the lower
skeleton.** Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex whose
`n`-skeleton is all of `B` and which has a single `n`-cell `j`, with centre `b = map n j 0`. A
class `α ∈ Hₖ(E; M)` lives over the fundamental class at `b` exactly when it is not the image of a
class of the part `p⁻¹(Xⁿ⁻¹)` of `E` over the `(n-1)`-skeleton `Xⁿ⁻¹ = skeletonLT C n`. -/
theorem livesOverFundamentalClass_iff_notMem_range_preimage_skeletonLT {k : ℕ}
    (α : ((_root_.TopCat.toSSet.obj E).homology M k : ModuleCat.{u} Λ)) :
    LivesOverFundamentalClass M p (map n j 0) α ↔
      α ∉ LinearMap.range (SSet.homologyMap (_root_.TopCat.toSSet.map
        (TopPair.ofSubset (p ⁻¹' (skeletonLT C n : Set B))).map) M k).hom := by
  rw [livesOverFundamentalClass_iff_singularHomologyπ_preimage_skeletonLT_ne_zero hp hB,
    not_iff_not, ((TopPair.ofSubset (p ⁻¹' (skeletonLT C n : Set B))).singularHomology_exact_space
      M k).moduleCat_range_eq_ker]
  exact LinearMap.mem_ker.symm

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.FilteredSpace
public import TauCeti.AlgebraicTopology.Singular.Fibration.FirstPage

/-!
# The Serre spectral sequence on cubical chains

Let `p : E ⟶ B` be a map and `C ⊆ B` a relative CW complex. Filtering the normalized cubical
chains of `E` by those of the preimages `p⁻¹(C^(i))` of the skeleta gives the **Serre spectral
sequence on cubical chains** (`TauCeti.TopCat.cubicalSerreSpectralSequence`), the form in which
Serre originally built it and in which it meets the chains on Moore loop spaces, which are cubical
because the cubical cross product is strictly associative. Its abutment in degree `-n` is the
cubical homology `Hₙ(E)` (`TauCeti.chainFiltrationAbutmentIso`).

The comparison of simplicial and cubical chains is an isomorphism from the simplicial Serre
spectral sequence `TauCeti.TopCat.serreSpectralSequence` onto the cubical one on every page `r ≥ 2`
(`TauCeti.isIso_singularToCubicalSpectralSequenceMap_hom_f`, an instance of the comparison for any
filtered space). Through it, the computations of the simplicial Serre spectral sequence of a Serre
fibration hold on cubical chains:

* **First quadrant.** The object at `(a, b)` on the first page (numbered `2`) vanishes when
  `0 ≤ a + 2b` (`TauCeti.TopCat.isZero_cubicalSerreSpectralSequence_page_two_X`).
* **First page.** The object at `(a, b)`, with `b = k - 1` and `a + b = -(q + k)`, is the direct
  sum `⨁ⱼ Hq(p⁻¹(χⱼ(0)); R)` over the `k`-cells `j` of `C` of the homology of the fibre over the
  centre of the cell (`TauCeti.TopCat.cubicalSerreSpectralSequenceFirstPageXIsoSigma`).

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

section Defs

variable {E B : _root_.TopCat.{u}} [T2Space B]

/-- **The Serre spectral sequence on cubical chains** of `p : E ⟶ B` over a relative CW complex
`C ⊆ B`, with coefficients in `R`: the spectral sequence
`TauCeti.cubicalFilteredSpaceSpectralSequence` of the filtration of the normalized cubical chains
of `E` by those of the preimages `p⁻¹(C^(i))` of the skeleta (`TauCeti.preimageSkeleton`). -/
abbrev cubicalSerreSpectralSequence (C : Set B) {D : Set B} [RelCWComplex C D] (p : E ⟶ B)
    (R : Type u) [Ring R] :=
  cubicalFilteredSpaceSpectralSequence R (monotone_preimageSkeleton (C := C) p)

end Defs

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]
  (R : Type u) [Ring R]

variable (hp : serreFibrations p)
include hp

variable (C) in
/-- **The Serre spectral sequence on cubical chains is a first-quadrant spectral sequence.** For a
Serre fibration `p`, the object at `pq = (a, b)` on the first page (numbered `2`) vanishes when
`0 ≤ a + 2b`. -/
theorem isZero_cubicalSerreSpectralSequence_page_two_X (pq : ℤ × ℤ)
    (h : 0 ≤ pq.1 + 2 * pq.2) :
    IsZero (((cubicalSerreSpectralSequence C p R).page 2).X pq) :=
  (isZero_serreSpectralSequence_page_two_X hp R C pq h).of_iso
    (singularCubicalSpectralSequencePageXIso R (monotone_preimageSkeleton (C := C) p) 2 le_rfl
      pq).symm

variable (C) in
/-- **The first page of the Serre spectral sequence on cubical chains.** For a Serre fibration
`p : E ⟶ B` and a relative CW complex `C ⊆ B`, the object of the first page (numbered `2`) at
`pq = (a, b)`, with `b = k - 1` and `a + b = -(q + k)`, is the direct sum `⨁ⱼ Hq(p⁻¹(χⱼ(0)); R)`
over the `k`-cells `j` of `C`. -/
def cubicalSerreSpectralSequenceFirstPageXIsoSigma (k q : ℕ) (pq : ℤ × ℤ) (hb : pq.2 = k - 1)
    (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    ((cubicalSerreSpectralSequence C p R).page 2).X pq ≅
      ∐ fun j : cell C k ↦ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {map k j 0} : Set E)) :=
  (singularCubicalSpectralSequencePageXIso R (monotone_preimageSkeleton (C := C) p) 2 le_rfl
      pq).symm ≪≫ serreSpectralSequenceFirstPageXIsoSigma C hp R k q pq hb ha

end TopCat

end TauCeti

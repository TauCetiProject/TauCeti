/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.FilteredSpace
public import TauCeti.AlgebraicTopology.Singular.Fibration.ArbitraryBase

/-!
# The Serre spectral sequence in cubical singular chains

The Serre spectral sequence of a map `p : E ⟶ B` over a relative CW complex `C ⊆ B`
(`TauCeti.TopCat.serreSpectralSequence`) is the spectral sequence of the filtration of the
simplicial singular chains of `E` by those of the preimages of the skeleta. Filtering the
normalized cubical singular chains of `E` in the same way gives the cubical Serre spectral object
(`TauCeti.TopCat.cubicalSerreSpectralObject`), and the comparison of simplicial and cubical
singular chains, as a morphism of filtered complexes, identifies the two spectral objects
(`TauCeti.TopCat.serreSpectralObjectIsoCubical`, from
`TauCeti.singularToCubicalFiltrationSpectralObjectIso`). So the Serre spectral sequence, its pages,
its abutment and the filtration of its abutment are all computed by cubical chains.

Over an arbitrary base, the Serre spectral sequence is that of the pullback to the CW
approximation (`TopCat.Hom.arbitraryBaseSerreSpectralSequence`), and the same holds
(`TauCeti.TopCat.arbitraryBaseSerreSpectralObjectIsoCubical`). For a Serre fibration, its abutment
and its first page are then read in normalized cubical singular homology of the total space and
of the fibres.

## Main definitions

* `TauCeti.TopCat.cubicalSerreSpectralObject`: the spectral object of the filtration of the
  normalized cubical chains of `E` by those of the preimages of the skeleta of `C`.
* `TauCeti.TopCat.serreSpectralObjectIsoCubical`,
  `TauCeti.TopCat.arbitraryBaseSerreSpectralObjectIsoCubical`: the Serre spectral object is
  isomorphic to its cubical version.
* `TauCeti.TopCat.cubicalArbitraryBaseSerreAbutmentIso`: for a Serre fibration, the abutment in
  degree `-n` is the normalized cubical singular homology `H^□ₙ(E; R)` of the total space.
* `TauCeti.TopCat.cubicalArbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma`: the object of the
  first page at the position of `E¹_{k,q}` is the sum, over the `k`-cells of the CW approximation of
  `B`, of the normalized cubical singular homology `H^□_q` of the fibre over the image of the centre
  of the cell.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* W. S. Massey, *Singular Homology Theory*, Graduate Texts in Mathematics 70, Springer, 1980,
  Chapter II.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

section SpectralObject

variable {E B : _root_.TopCat.{u}} [T2Space B]

/-- **The cubical Serre spectral object** of `p : E ⟶ B` over a relative CW complex `C ⊆ B`, with
coefficients in `R`: the spectral object of the filtration of the normalized cubical singular
chains of `E` by those of the preimages `p⁻¹(C^(i))` of the skeleta. -/
abbrev cubicalSerreSpectralObject (C : Set B) {D : Set B} [RelCWComplex C D] (p : E ⟶ B)
    (R : Type u) [Ring R] :=
  CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
    (monotone_cubicalChainFiltration R (monotone_preimageSkeleton (C := C) p)))

/-- **The Serre spectral sequence is computed by cubical chains.** The Serre spectral object of
`p : E ⟶ B` over a relative CW complex `C ⊆ B`, built from simplicial singular chains, is
isomorphic to the cubical Serre spectral object, through the comparison of simplicial and cubical
singular chains. -/
def serreSpectralObjectIsoCubical (C : Set B) {D : Set B} [RelCWComplex C D] (p : E ⟶ B)
    (R : Type u) [Ring R] :
    serreSpectralObject C p R ≅ cubicalSerreSpectralObject C p R :=
  singularToCubicalFiltrationSpectralObjectIso R (monotone_preimageSkeleton (C := C) p)

end SpectralObject

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p) (R : Type u) [Ring R]

/-- **The Serre spectral sequence over an arbitrary base is computed by cubical chains.** The
Serre spectral object of `p : E ⟶ B` over an arbitrary base is isomorphic to the cubical Serre
spectral object of the pullback of `p` to the CW approximation of `B`. -/
def arbitraryBaseSerreSpectralObjectIsoCubical :
    p.arbitraryBaseSerreSpectralObject R ≅
      cubicalSerreSpectralObject (univ : Set (sigmaCWApproximation B))
        (_root_.TopCat.pullbackFst (sigmaCWApproximationMap B) p) R :=
  serreSpectralObjectIsoCubical _ _ R

include hp

/-- **The abutment of the Serre spectral sequence in cubical singular homology.** For a Serre
fibration `p : E ⟶ B`, the abutment in degree `-n` of the Serre spectral sequence over an arbitrary
base is the normalized cubical singular homology `H^□ₙ(E; R)` of the total space: the isomorphism
`TauCeti.TopCat.arbitraryBaseSerreAbutmentIso` with simplicial singular homology, followed by the
comparison `TauCeti.singularCubicalHomologyIso`. -/
def cubicalArbitraryBaseSerreAbutmentIso (n : ℕ) :
    (p.arbitraryBaseSerreSpectralObject R).abutment (-n) ≅
      ((normalizedCubicalChainComplex R).obj E).homology n :=
  arbitraryBaseSerreAbutmentIso hp R n ≪≫ singularCubicalHomologyIso R E n

/-- The isomorphism `TauCeti.TopCat.cubicalArbitraryBaseSerreAbutmentIso` is the abutment
isomorphism with simplicial singular homology, followed by the map induced on homology by the
comparison `TauCeti.singularToCubical`. -/
lemma cubicalArbitraryBaseSerreAbutmentIso_hom (n : ℕ) :
    (cubicalArbitraryBaseSerreAbutmentIso hp R n).hom =
      (arbitraryBaseSerreAbutmentIso hp R n).hom ≫
        HomologicalComplex.homologyMap ((singularToCubical R).app E) n :=
  congrArg ((arbitraryBaseSerreAbutmentIso hp R n).hom ≫ ·)
    (singularCubicalHomologyIso_hom (k := R) E n)

/-- **The first page of the Serre spectral sequence in cubical singular homology.** For a Serre
fibration `p : E ⟶ B`, the object of the first page (numbered `2`) at `pq = (a, b)`, with
`b = k - 1` and `a + b = -(q + k)`, is the direct sum `⨁ⱼ H^□_q(p⁻¹(f(χⱼ(0))); R)` of the normalized
cubical singular homology of the fibres over the images of the centres of the `k`-cells `j` of the
CW approximation `f : ΓB ⟶ B`. In the classical indexing this is `E¹_{k,q}`. -/
def cubicalArbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma (k q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    ((p.arbitraryBaseSerreSpectralSequence R).page 2).X pq ≅
      ∐ fun j : cell (univ : Set (sigmaCWApproximation B)) k ↦
        ((normalizedCubicalChainComplex R).obj
          (p.fiber (sigmaCWApproximationMap B (map k j 0)))).homology q :=
  arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R k q pq hb ha ≪≫
    Sigma.mapIso fun _ ↦ singularCubicalHomologyIso R _ q

/-- The isomorphism `TauCeti.TopCat.cubicalArbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma` is
the first-page isomorphism with simplicial singular homology of the fibres, followed on each summand
by the map induced on homology by the comparison `TauCeti.singularToCubical`. -/
lemma cubicalArbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma_hom (k q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    (cubicalArbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R k q pq hb ha).hom =
      (arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R k q pq hb ha).hom ≫
        Limits.Sigma.map fun _ ↦ HomologicalComplex.homologyMap ((singularToCubical R).app _) q :=
  congrArg ((arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R k q pq hb ha).hom ≫ ·) <|
    Sigma.hom_ext _ _ fun j ↦ by
      refine (Sigma.ι_mapIso_hom (fun _ ↦ singularCubicalHomologyIso R _ q) j).trans ?_
      rw [singularCubicalHomologyIso_hom]
      exact (Sigma.ι_map (fun x ↦ HomologicalComplex.homologyMap
        ((singularToCubical R).app (p.fiber (sigmaCWApproximationMap B (map k x 0)))) q) j).symm

end TopCat

end TauCeti

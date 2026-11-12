/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic
public import TauCeti.AlgebraicTopology.Singular.Fibration.ArbitraryBase

/-!
# The Serre spectral sequence in cubical singular homology

The Serre spectral sequence of a Serre fibration `p : E ⟶ B` over an arbitrary base
(`TopCat.Hom.arbitraryBaseSerreSpectralSequence`) is built from simplicial singular chains. This
file reads its abutment and its first page in normalized cubical singular homology, through the
comparison `TauCeti.singularCubicalHomologyIso` of cubical and simplicial singular homology. The
spectral sequence itself is not rebuilt on cubical chains: every statement here is the simplicial
one followed by the comparison isomorphism.

## Main definitions

* `TauCeti.TopCat.cubicalSerreAbutmentIso`: the abutment in degree `-n` is the normalized cubical
  singular homology `H^□ₙ(E; R)` of the total space.
* `TauCeti.TopCat.cubicalSerreSpectralSequenceFirstPageXIsoSigma`: the object of the first page
  at the position of `E¹_{k,q}` is the sum, over the `k`-cells of the CW approximation of `B`, of
  the normalized cubical singular homology `H^□_q` of the fibre over the image of the centre of the
  cell.

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

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p) (R : Type u) [Ring R]

include hp

/-- **The abutment of the Serre spectral sequence in cubical singular homology.** For a Serre
fibration `p : E ⟶ B`, the abutment in degree `-n` of the Serre spectral sequence over an arbitrary
base is the normalized cubical singular homology `H^□ₙ(E; R)` of the total space: the isomorphism
`TauCeti.TopCat.arbitraryBaseSerreAbutmentIso` with simplicial singular homology, followed by the
comparison `TauCeti.singularCubicalHomologyIso`. -/
def cubicalSerreAbutmentIso (n : ℕ) :
    (p.arbitraryBaseSerreSpectralObject R).abutment (-n) ≅
      ((normalizedCubicalChainComplex R).obj E).homology n :=
  arbitraryBaseSerreAbutmentIso hp R n ≪≫ singularCubicalHomologyIso R E n

/-- The isomorphism `TauCeti.TopCat.cubicalSerreAbutmentIso` is the abutment isomorphism with
simplicial singular homology, followed by the map induced on homology by the comparison
`TauCeti.singularToCubical`. -/
lemma cubicalSerreAbutmentIso_hom (n : ℕ) :
    (cubicalSerreAbutmentIso hp R n).hom =
      (arbitraryBaseSerreAbutmentIso hp R n).hom ≫
        HomologicalComplex.homologyMap ((singularToCubical R).app E) n :=
  congrArg ((arbitraryBaseSerreAbutmentIso hp R n).hom ≫ ·)
    (singularCubicalHomologyIso_hom (k := R) E n)

/-- **The first page of the Serre spectral sequence in cubical singular homology.** For a Serre
fibration `p : E ⟶ B`, the object of the first page (numbered `2`) at `pq = (a, b)`, with
`b = k - 1` and `a + b = -(q + k)`, is the direct sum `⨁ⱼ H^□_q(p⁻¹(f(χⱼ(0))); R)` of the normalized
cubical singular homology of the fibres over the images of the centres of the `k`-cells `j` of the
CW approximation `f : ΓB ⟶ B`. In the classical indexing this is `E¹_{k,q}`. -/
def cubicalSerreSpectralSequenceFirstPageXIsoSigma (k q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    ((p.arbitraryBaseSerreSpectralSequence R).page 2).X pq ≅
      ∐ fun j : cell (univ : Set (sigmaCWApproximation B)) k ↦
        ((normalizedCubicalChainComplex R).obj
          (p.fiber (sigmaCWApproximationMap B (map k j 0)))).homology q :=
  arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R k q pq hb ha ≪≫
    Sigma.mapIso fun _ ↦ singularCubicalHomologyIso R _ q

end TopCat

end TauCeti

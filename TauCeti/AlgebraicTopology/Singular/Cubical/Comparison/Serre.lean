/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Comparison
public import TauCeti.AlgebraicTopology.Singular.Fibration.ArbitraryBase

/-!
# The Serre spectral sequence in cubical singular chains

The Serre spectral sequence of a map `p : E ⟶ B` over a relative CW complex `C ⊆ B`
(`TauCeti.TopCat.serreSpectralSequence`) is the spectral sequence of the filtration of the
simplicial singular chains of `E` by those of the preimages of the skeleta. Filtering the
normalized cubical singular chains of `E` in the same way gives the cubical Serre spectral object
(`TauCeti.TopCat.cubicalSerreSpectralObject`), and the comparison of simplicial and cubical
singular chains, as a morphism of filtered complexes, identifies the two spectral objects
(`TauCeti.TopCat.serreSpectralObjectIsoCubical`, an instance of
`TauCeti.chainFiltrationSpectralObjectIso`). So the Serre spectral sequence, its pages,
its abutment and the filtration of its abutment are all computed by cubical chains.

For a Serre fibration, the abutment and the first page of the Serre spectral sequence of a base
change along any `g : B' ⟶ B` are then read in normalized cubical singular homology of the total
space and of the fibres. Over an arbitrary base, the Serre spectral sequence is that of the pullback
to the CW approximation (`TopCat.Hom.arbitraryBaseSerreSpectralSequence`), so the same holds.

## Main definitions

* `TauCeti.TopCat.cubicalSerreSpectralObject`: the spectral object of the filtration of the
  normalized cubical chains of `E` by those of the preimages of the skeleta of `C`.
* `TauCeti.TopCat.serreSpectralObjectIsoCubical`: the Serre spectral object is isomorphic to its
  cubical version.
* `TauCeti.TopCat.serreSpectralObjectPullbackAbutmentIsoCubical`,
  `TauCeti.TopCat.serreSpectralSequencePullbackFirstPageXIsoSigmaCubical`: the abutment and the
  first page of the Serre spectral sequence of a base change, in cubical singular homology.
* `TauCeti.TopCat.arbitraryBaseSerreAbutmentIsoCubical`: for a Serre fibration, the abutment in
  degree `-n` is the normalized cubical singular homology `H^□ₙ(E; R)` of the total space.
* `TauCeti.TopCat.arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical`: the object of the
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
    (monotone_chainFiltration (normalizedCubicalChainComplex R)
      (monotone_preimageSkeleton (C := C) p)))

/-- **The Serre spectral sequence is computed by cubical chains.** The Serre spectral object of
`p : E ⟶ B` over a relative CW complex `C ⊆ B`, built from simplicial singular chains, is
isomorphic to the cubical Serre spectral object, through the comparison of simplicial and cubical
singular chains. -/
def serreSpectralObjectIsoCubical (C : Set B) {D : Set B} [RelCWComplex C D] (p : E ⟶ B)
    (R : Type u) [Ring R] :
    serreSpectralObject C p R ≅ cubicalSerreSpectralObject C p R :=
  chainFiltrationSpectralObjectIso (singularToCubical R) (monotone_preimageSkeleton (C := C) p)

/-- The isomorphism `TauCeti.TopCat.serreSpectralObjectIsoCubical` is the morphism of spectral
objects induced by the comparison `TauCeti.singularToCubical`, as a morphism of filtered
complexes. -/
@[simp]
lemma serreSpectralObjectIsoCubical_hom (C : Set B) {D : Set B} [RelCWComplex C D] (p : E ⟶ B)
    (R : Type u) [Ring R] :
    (serreSpectralObjectIsoCubical C p R).hom =
      CochainComplex.spectralObjectMap (chainFiltrationMap (singularToCubical R)
        (monotone_preimageSkeleton (C := C) p) (monotone_preimageSkeleton (C := C) p) (𝟙 E)
        fun _ _ hx ↦ hx) :=
  chainFiltrationSpectralObjectIso_hom _ _

end SpectralObject

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p) (R : Type u) [Ring R]

include hp

section Pullback

variable {B' : _root_.TopCat.{u}} [T2Space B'] {C D : Set B'} [RelCWComplex C D]

variable (C) in
/-- **The abutment of the Serre spectral sequence of a base change in cubical singular
homology.** Let `p : E ⟶ B` be a Serre fibration, `g : B' ⟶ B` a weak homotopy equivalence and
`C ⊆ B'` a relative CW complex. The abutment in degree `-n` of the Serre spectral sequence over `C`
of the base change `B' ×_B E ⟶ B'` is the normalized cubical singular homology `H^□ₙ(E; R)`: the
isomorphism `TauCeti.TopCat.serreSpectralObjectPullbackAbutmentIso` with simplicial singular
homology, followed by the comparison `TauCeti.singularCubicalHomologyIso`. -/
def serreSpectralObjectPullbackAbutmentIsoCubical {g : B' ⟶ B}
    (hg : g.hom.IsWeakHomotopyEquivalence) (n : ℕ) :
    (serreSpectralObject C (_root_.TopCat.pullbackFst g p) R).abutment (-n) ≅
      ((normalizedCubicalChainComplex R).obj E).homology n :=
  serreSpectralObjectPullbackAbutmentIso hp R C hg n ≪≫ singularCubicalHomologyIso R E n

/-- The isomorphism `TauCeti.TopCat.serreSpectralObjectPullbackAbutmentIsoCubical` is the abutment
isomorphism with simplicial singular homology, followed by the map induced on homology by the
comparison `TauCeti.singularToCubical`. -/
@[reassoc]
lemma serreSpectralObjectPullbackAbutmentIsoCubical_hom {g : B' ⟶ B}
    (hg : g.hom.IsWeakHomotopyEquivalence) (n : ℕ) :
    (serreSpectralObjectPullbackAbutmentIsoCubical hp R C hg n).hom =
      (serreSpectralObjectPullbackAbutmentIso hp R C hg n).hom ≫
        HomologicalComplex.homologyMap ((singularToCubical R).app E) n :=
  congrArg ((serreSpectralObjectPullbackAbutmentIso hp R C hg n).hom ≫ ·)
    (singularCubicalHomologyIso_hom (k := R) E n)

/-- The inverse of `TauCeti.TopCat.serreSpectralObjectPullbackAbutmentIsoCubical` is the map
induced on homology by the comparison `TauCeti.cubicalToSingular`, followed by the inverse of the
abutment isomorphism with simplicial singular homology. -/
@[reassoc]
lemma serreSpectralObjectPullbackAbutmentIsoCubical_inv {g : B' ⟶ B}
    (hg : g.hom.IsWeakHomotopyEquivalence) (n : ℕ) :
    (serreSpectralObjectPullbackAbutmentIsoCubical hp R C hg n).inv =
      HomologicalComplex.homologyMap ((cubicalToSingular R).app E) n ≫
        (serreSpectralObjectPullbackAbutmentIso hp R C hg n).inv :=
  congrArg (· ≫ (serreSpectralObjectPullbackAbutmentIso hp R C hg n).inv)
    (singularCubicalHomologyIso_inv (k := R) E n)

variable (C) in
/-- **The first page of the Serre spectral sequence of a base change in cubical singular
homology.** Let `p : E ⟶ B` be a Serre fibration, `g : B' ⟶ B` a map and `C ⊆ B'` a relative CW
complex. The object of the first page (numbered `2`) of the Serre spectral sequence over `C` of
the base change `B' ×_B E ⟶ B'` at `pq = (a, b)`, with `b = k - 1` and `a + b = -(q + k)`, is
`⨁ⱼ H^□_q(p⁻¹(g(χⱼ(0))); R)`, the sum of the normalized cubical singular homology of the fibres of
`p` over the images under `g` of the centres of the `k`-cells `j` of `C`. -/
def serreSpectralSequencePullbackFirstPageXIsoSigmaCubical (g : B' ⟶ B) (k q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    ((serreSpectralSequence C (_root_.TopCat.pullbackFst g p) R).page 2).X pq ≅
      ∐ fun j : cell C k ↦
        ((normalizedCubicalChainComplex R).obj (p.fiber (g (map k j 0)))).homology q :=
  serreSpectralSequencePullbackFirstPageXIsoSigma hp R C g k q pq hb ha ≪≫
    Sigma.mapIso fun _ ↦ singularCubicalHomologyIso R _ q

/-- The isomorphism `TauCeti.TopCat.serreSpectralSequencePullbackFirstPageXIsoSigmaCubical` is the
first-page isomorphism with simplicial singular homology of the fibres, followed on each summand
by the map induced on homology by the comparison `TauCeti.singularToCubical`. -/
@[reassoc]
lemma serreSpectralSequencePullbackFirstPageXIsoSigmaCubical_hom (g : B' ⟶ B) (k q : ℕ)
    (pq : ℤ × ℤ) (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    (serreSpectralSequencePullbackFirstPageXIsoSigmaCubical hp R C g k q pq hb ha).hom =
      (serreSpectralSequencePullbackFirstPageXIsoSigma hp R C g k q pq hb ha).hom ≫
        Limits.Sigma.map fun _ ↦ HomologicalComplex.homologyMap ((singularToCubical R).app _) q :=
  congrArg ((serreSpectralSequencePullbackFirstPageXIsoSigma hp R C g k q pq hb ha).hom ≫ ·)
    (sigmaMapIso_singularCubicalHomologyIso_hom R _ q)

/-- On the summand of the `k`-cell `j`, the inverse of
`TauCeti.TopCat.serreSpectralSequencePullbackFirstPageXIsoSigmaCubical` is the map induced on
homology by the comparison `TauCeti.cubicalToSingular`, followed by the inverse of the first-page
isomorphism with simplicial singular homology. -/
@[reassoc]
lemma ι_serreSpectralSequencePullbackFirstPageXIsoSigmaCubical_inv (g : B' ⟶ B) (k q : ℕ)
    (pq : ℤ × ℤ) (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) (j : cell C k) :
    Sigma.ι _ j ≫
        (serreSpectralSequencePullbackFirstPageXIsoSigmaCubical hp R C g k q pq hb ha).inv =
      HomologicalComplex.homologyMap ((cubicalToSingular R).app (p.fiber (g (map k j 0)))) q ≫
        Sigma.ι (fun j : cell C k ↦
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
            (ModuleCat.of R R)).obj (p.fiber (g (map k j 0)))) j ≫
        (serreSpectralSequencePullbackFirstPageXIsoSigma hp R C g k q pq hb ha).inv :=
  (congrArg (Sigma.ι _ j ≫ · ≫ _) (sigmaMapIso_singularCubicalHomologyIso_inv R _ q)).trans
    (Sigma.ι_map_assoc _ j _)

end Pullback

/-- **The abutment of the Serre spectral sequence in cubical singular homology.** For a Serre
fibration `p : E ⟶ B`, the abutment in degree `-n` of the Serre spectral sequence over an arbitrary
base is the normalized cubical singular homology `H^□ₙ(E; R)` of the total space: the isomorphism
`TauCeti.TopCat.arbitraryBaseSerreAbutmentIso` with simplicial singular homology, followed by the
comparison `TauCeti.singularCubicalHomologyIso`. -/
def arbitraryBaseSerreAbutmentIsoCubical (n : ℕ) :
    (p.arbitraryBaseSerreSpectralObject R).abutment (-n) ≅
      ((normalizedCubicalChainComplex R).obj E).homology n :=
  -- Not stated as the case of `serreSpectralObjectPullbackAbutmentIsoCubical`: the definition of
  -- `arbitraryBaseSerreAbutmentIso` as its pullback version is not exposed outside its file.
  arbitraryBaseSerreAbutmentIso hp R n ≪≫ singularCubicalHomologyIso R E n

/-- The isomorphism `TauCeti.TopCat.arbitraryBaseSerreAbutmentIsoCubical` is the abutment
isomorphism with simplicial singular homology, followed by the map induced on homology by the
comparison `TauCeti.singularToCubical`. -/
@[reassoc]
lemma arbitraryBaseSerreAbutmentIsoCubical_hom (n : ℕ) :
    (arbitraryBaseSerreAbutmentIsoCubical hp R n).hom =
      (arbitraryBaseSerreAbutmentIso hp R n).hom ≫
        HomologicalComplex.homologyMap ((singularToCubical R).app E) n :=
  congrArg ((arbitraryBaseSerreAbutmentIso hp R n).hom ≫ ·)
    (singularCubicalHomologyIso_hom (k := R) E n)

/-- The inverse of `TauCeti.TopCat.arbitraryBaseSerreAbutmentIsoCubical` is the map induced on
homology by the comparison `TauCeti.cubicalToSingular`, followed by the inverse of the abutment
isomorphism with simplicial singular homology. -/
@[reassoc]
lemma arbitraryBaseSerreAbutmentIsoCubical_inv (n : ℕ) :
    (arbitraryBaseSerreAbutmentIsoCubical hp R n).inv =
      HomologicalComplex.homologyMap ((cubicalToSingular R).app E) n ≫
        (arbitraryBaseSerreAbutmentIso hp R n).inv :=
  congrArg (· ≫ (arbitraryBaseSerreAbutmentIso hp R n).inv)
    (singularCubicalHomologyIso_inv (k := R) E n)

/-- **The first page of the Serre spectral sequence in cubical singular homology.** For a Serre
fibration `p : E ⟶ B`, the object of the first page (numbered `2`) at `pq = (a, b)`, with
`b = k - 1` and `a + b = -(q + k)`, is the direct sum `⨁ⱼ H^□_q(p⁻¹(f(χⱼ(0))); R)` of the normalized
cubical singular homology of the fibres over the images of the centres of the `k`-cells `j` of the
CW approximation `f : ΓB ⟶ B`. In the classical indexing this is `E¹_{k,q}`. -/
def arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical (k q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    ((p.arbitraryBaseSerreSpectralSequence R).page 2).X pq ≅
      ∐ fun j : cell (univ : Set (sigmaCWApproximation B)) k ↦
        ((normalizedCubicalChainComplex R).obj
          (p.fiber (sigmaCWApproximationMap B (map k j 0)))).homology q :=
  -- Built from `arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma`, whose definition as the
  -- pullback version is not exposed outside its file.
  arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R k q pq hb ha ≪≫
    Sigma.mapIso fun _ ↦ singularCubicalHomologyIso R _ q

/-- The isomorphism `TauCeti.TopCat.arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical` is
the first-page isomorphism with simplicial singular homology of the fibres, followed on each summand
by the map induced on homology by the comparison `TauCeti.singularToCubical`. -/
@[reassoc]
lemma arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical_hom (k q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    (arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical hp R k q pq hb ha).hom =
      (arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R k q pq hb ha).hom ≫
        Limits.Sigma.map fun _ ↦ HomologicalComplex.homologyMap ((singularToCubical R).app _) q :=
  congrArg ((arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R k q pq hb ha).hom ≫ ·)
    (sigmaMapIso_singularCubicalHomologyIso_hom R _ q)

/-- On the summand of the `k`-cell `j`, the inverse of
`TauCeti.TopCat.arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical` is the map induced on
homology by the comparison `TauCeti.cubicalToSingular`, followed by the inverse of the first-page
isomorphism with simplicial singular homology. -/
@[reassoc]
lemma ι_arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical_inv (k q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ))
    (j : cell (univ : Set (sigmaCWApproximation B)) k) :
    Sigma.ι _ j ≫
        (arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical hp R k q pq hb ha).inv =
      HomologicalComplex.homologyMap
          ((cubicalToSingular R).app (p.fiber (sigmaCWApproximationMap B (map k j 0)))) q ≫
        Sigma.ι (fun j : cell (univ : Set (sigmaCWApproximation B)) k ↦
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
            (ModuleCat.of R R)).obj (p.fiber (sigmaCWApproximationMap B (map k j 0)))) j ≫
        (arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R k q pq hb ha).inv :=
  (congrArg (Sigma.ι _ j ≫ · ≫ _) (sigmaMapIso_singularCubicalHomologyIso_inv R _ q)).trans
    (Sigma.ι_map_assoc _ j _)

end TopCat

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.FilteredSpace
public import TauCeti.AlgebraicTopology.Singular.Fibration.ArbitraryBase
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

The comparison identifies more than the pages: it is an isomorphism from the Serre spectral object
onto the cubical Serre spectral object (`TauCeti.TopCat.cubicalSerreSpectralObject`,
`TauCeti.TopCat.serreSpectralObjectIsoCubical`), so the abutment and its filtration are computed by
cubical chains too. For a Serre fibration, the abutment and the first page are then read in
normalized cubical singular homology of the total space and of the fibres. On the abutment, the
isomorphism of spectral objects is the comparison map in homology
(`TauCeti.TopCat.serreSpectralObjectIsoCubical_hom_app_chainFiltrationAbutmentIso_hom`). For the
base change along a map `g : B' ⟶ B`, the first page is read in cubical homology of the fibres for
every `g` (`TauCeti.TopCat.serreSpectralSequencePullbackFirstPageXIsoSigmaCubical`), and the
abutment in cubical homology of `E` when `g` is a weak homotopy equivalence
(`TauCeti.TopCat.serreSpectralObjectPullbackAbutmentIsoCubical`); the same holds over an arbitrary
base
through its CW approximation (`TauCeti.TopCat.arbitraryBaseSerreAbutmentIsoCubical`,
`TauCeti.TopCat.arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical`).

## Implementation notes

The simplicial isomorphisms composed here (for instance
`TauCeti.TopCat.serreSpectralObjectPullbackAbutmentIso`) land in
`((AlgebraicTopology.singularHomologyFunctor _ n).obj (ModuleCat.of R R)).obj E`, which is only
definitionally equal to the source `HomologicalComplex.homology ((singularChains R).obj E) n` of
`TauCeti.singularCubicalHomologyIso`. The composites `_ ≪≫ _` in the definitions therefore do
not match `Iso.trans_hom` or `Iso.trans_inv` syntactically, and `rw` fails on them. The `_hom`
and `_inv` lemmas are proved by terms that let Lean unfold the definitions instead.

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
  singularCubicalSpectralObjectIso R (monotone_preimageSkeleton (C := C) p)

/-- The isomorphism `TauCeti.TopCat.serreSpectralObjectIsoCubical` is the morphism of spectral
objects induced by the comparison `TauCeti.singularToCubical`, as a morphism of filtered
complexes. -/
lemma serreSpectralObjectIsoCubical_hom (C : Set B) {D : Set B} [RelCWComplex C D] (p : E ⟶ B)
    (R : Type u) [Ring R] :
    (serreSpectralObjectIsoCubical C p R).hom =
      CochainComplex.spectralObjectMap (chainFiltrationMap (singularToCubical R)
        (monotone_preimageSkeleton (C := C) p) (monotone_preimageSkeleton (C := C) p) (𝟙 E)
        fun _ _ hx ↦ hx) :=
  singularCubicalSpectralObjectIso_hom _ _

/-- **The Serre comparison on the abutment.** In degree `-n`, through the abutment isomorphisms
`TauCeti.chainFiltrationAbutmentIso` with simplicial and with normalized cubical homology of `E`,
`TauCeti.TopCat.serreSpectralObjectIsoCubical` is the map `Hₙ(E; R) ⟶ H^□ₙ(E; R)` induced by the
comparison `TauCeti.singularToCubical`. -/
@[reassoc (attr := simp)]
lemma serreSpectralObjectIsoCubical_hom_app_chainFiltrationAbutmentIso_hom (C : Set B)
    {D : Set B} [RelCWComplex C D] (p : E ⟶ B) (R : Type u) [Ring R] (n : ℕ) :
    ((serreSpectralObjectIsoCubical C p R).hom.hom (-n)).app
        (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫
        (chainFiltrationAbutmentIso (normalizedCubicalChainComplex R)
          (monotone_preimageSkeleton (C := C) p) n).hom =
      (chainFiltrationAbutmentIso (singularChains R) (monotone_preimageSkeleton (C := C) p) n).hom ≫
        HomologicalComplex.homologyMap ((singularToCubical R).app E) n :=
  singularCubicalSpectralObjectIso_hom_app_chainFiltrationAbutmentIso_hom _ _ n

end SpectralObject

section CubicalHomology

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
@[simp, reassoc]
lemma serreSpectralObjectPullbackAbutmentIsoCubical_hom {g : B' ⟶ B}
    (hg : g.hom.IsWeakHomotopyEquivalence) (n : ℕ) :
    (serreSpectralObjectPullbackAbutmentIsoCubical hp R C hg n).hom =
      (serreSpectralObjectPullbackAbutmentIso hp R C hg n).hom ≫
        HomologicalComplex.homologyMap ((singularToCubical R).app E) n :=
  -- Term proof by unfolding the definition; see the implementation notes.
  congrArg ((serreSpectralObjectPullbackAbutmentIso hp R C hg n).hom ≫ ·)
    (singularCubicalHomologyIso_hom (k := R) E n)

/-- The inverse of `TauCeti.TopCat.serreSpectralObjectPullbackAbutmentIsoCubical` is the map
induced on homology by the comparison `TauCeti.cubicalToSingular`, followed by the inverse of the
abutment isomorphism with simplicial singular homology. -/
@[simp, reassoc]
lemma serreSpectralObjectPullbackAbutmentIsoCubical_inv {g : B' ⟶ B}
    (hg : g.hom.IsWeakHomotopyEquivalence) (n : ℕ) :
    (serreSpectralObjectPullbackAbutmentIsoCubical hp R C hg n).inv =
      HomologicalComplex.homologyMap ((cubicalToSingular R).app E) n ≫
        (serreSpectralObjectPullbackAbutmentIso hp R C hg n).inv :=
  -- Term proof by unfolding the definition; see the implementation notes.
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
@[simp, reassoc]
lemma serreSpectralSequencePullbackFirstPageXIsoSigmaCubical_hom (g : B' ⟶ B) (k q : ℕ)
    (pq : ℤ × ℤ) (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    (serreSpectralSequencePullbackFirstPageXIsoSigmaCubical hp R C g k q pq hb ha).hom =
      (serreSpectralSequencePullbackFirstPageXIsoSigma hp R C g k q pq hb ha).hom ≫
        Limits.Sigma.map fun _ ↦ HomologicalComplex.homologyMap ((singularToCubical R).app _) q :=
  -- Term proof by unfolding the definition; see the implementation notes.
  congrArg ((serreSpectralSequencePullbackFirstPageXIsoSigma hp R C g k q pq hb ha).hom ≫ ·)
    (sigmaMapIso_singularCubicalHomologyIso_hom R _ q)

/-- On the summand of the `k`-cell `j`, the inverse of
`TauCeti.TopCat.serreSpectralSequencePullbackFirstPageXIsoSigmaCubical` is the map induced on
homology by the comparison `TauCeti.cubicalToSingular`, followed by the inverse of the first-page
isomorphism with simplicial singular homology. -/
@[reassoc (attr := simp)]
lemma ι_serreSpectralSequencePullbackFirstPageXIsoSigmaCubical_inv (g : B' ⟶ B) (k q : ℕ)
    (pq : ℤ × ℤ) (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) (j : cell C k) :
    Sigma.ι _ j ≫
        (serreSpectralSequencePullbackFirstPageXIsoSigmaCubical hp R C g k q pq hb ha).inv =
      HomologicalComplex.homologyMap ((cubicalToSingular R).app (p.fiber (g (map k j 0)))) q ≫
        Sigma.ι (fun j : cell C k ↦
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
            (ModuleCat.of R R)).obj (p.fiber (g (map k j 0)))) j ≫
        (serreSpectralSequencePullbackFirstPageXIsoSigma hp R C g k q pq hb ha).inv :=
  -- Term proof by unfolding the definition; see the implementation notes.
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
@[simp, reassoc]
lemma arbitraryBaseSerreAbutmentIsoCubical_hom (n : ℕ) :
    (arbitraryBaseSerreAbutmentIsoCubical hp R n).hom =
      (arbitraryBaseSerreAbutmentIso hp R n).hom ≫
        HomologicalComplex.homologyMap ((singularToCubical R).app E) n :=
  -- Term proof by unfolding the definition; see the implementation notes.
  congrArg ((arbitraryBaseSerreAbutmentIso hp R n).hom ≫ ·)
    (singularCubicalHomologyIso_hom (k := R) E n)

/-- The inverse of `TauCeti.TopCat.arbitraryBaseSerreAbutmentIsoCubical` is the map induced on
homology by the comparison `TauCeti.cubicalToSingular`, followed by the inverse of the abutment
isomorphism with simplicial singular homology. -/
@[simp, reassoc]
lemma arbitraryBaseSerreAbutmentIsoCubical_inv (n : ℕ) :
    (arbitraryBaseSerreAbutmentIsoCubical hp R n).inv =
      HomologicalComplex.homologyMap ((cubicalToSingular R).app E) n ≫
        (arbitraryBaseSerreAbutmentIso hp R n).inv :=
  -- Term proof by unfolding the definition; see the implementation notes.
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
      ∐ fun j : cell (Set.univ : Set (sigmaCWApproximation B)) k ↦
        ((normalizedCubicalChainComplex R).obj
          (p.fiber (sigmaCWApproximationMap B (map k j 0)))).homology q :=
  -- Built from `arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma`, whose definition as the
  -- pullback version is not exposed outside its file.
  arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R k q pq hb ha ≪≫
    Sigma.mapIso fun _ ↦ singularCubicalHomologyIso R _ q

/-- The isomorphism `TauCeti.TopCat.arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical` is
the first-page isomorphism with simplicial singular homology of the fibres, followed on each summand
by the map induced on homology by the comparison `TauCeti.singularToCubical`. -/
@[simp, reassoc]
lemma arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical_hom (k q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    (arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical hp R k q pq hb ha).hom =
      (arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R k q pq hb ha).hom ≫
        Limits.Sigma.map fun _ ↦ HomologicalComplex.homologyMap ((singularToCubical R).app _) q :=
  -- Term proof by unfolding the definition; see the implementation notes.
  congrArg ((arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R k q pq hb ha).hom ≫ ·)
    (sigmaMapIso_singularCubicalHomologyIso_hom R _ q)

/-- On the summand of the `k`-cell `j`, the inverse of
`TauCeti.TopCat.arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical` is the map induced on
homology by the comparison `TauCeti.cubicalToSingular`, followed by the inverse of the first-page
isomorphism with simplicial singular homology. -/
@[reassoc (attr := simp)]
lemma ι_arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical_inv (k q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ))
    (j : cell (Set.univ : Set (sigmaCWApproximation B)) k) :
    Sigma.ι _ j ≫
        (arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigmaCubical hp R k q pq hb ha).inv =
      HomologicalComplex.homologyMap
          ((cubicalToSingular R).app (p.fiber (sigmaCWApproximationMap B (map k j 0)))) q ≫
        Sigma.ι (fun j : cell (Set.univ : Set (sigmaCWApproximation B)) k ↦
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
            (ModuleCat.of R R)).obj (p.fiber (sigmaCWApproximationMap B (map k j 0)))) j ≫
        (arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R k q pq hb ha).inv :=
  -- Term proof by unfolding the definition; see the implementation notes.
  (congrArg (Sigma.ι _ j ≫ · ≫ _) (sigmaMapIso_singularCubicalHomologyIso_inv R _ q)).trans
    (Sigma.ι_map_assoc _ j _)

end CubicalHomology

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

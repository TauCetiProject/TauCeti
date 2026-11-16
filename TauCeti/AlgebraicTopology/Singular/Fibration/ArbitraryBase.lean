/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Sigma
public import TauCeti.AlgebraicTopology.Singular.Fibration.FirstPage
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.Topology.Category.TopCat.Pullback
public import TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence

/-!
# The Serre spectral sequence over an arbitrary base

Let `p : E ⟶ B` be a Serre fibration over an arbitrary space `B`, path-connected or not, with no
CW structure. Pull `p` back along the CW approximation `f : ΓB ⟶ B`
(`TauCeti.sigmaCWApproximationMap`) to the Serre fibration `p' : E' ⟶ ΓB`, where
`E' = ΓB ×_B E`. The Serre spectral sequence of `p` is the Serre spectral sequence of `p'` over the
CW complex `ΓB` (`TopCat.Hom.arbitraryBaseSerreSpectralSequence`), the spectral sequence of the
filtration of `E'` by the preimages of the skeleta of `ΓB`.

Since `f` is a weak homotopy equivalence, so is the projection `E' ⟶ E`
(`TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackSnd`), and it induces isomorphisms on singular
homology. So the spectral sequence converges to the homology of `E` itself:

* **Abutment.** The abutment in degree `-n` is `Hₙ(E; R)`
  (`TauCeti.TopCat.arbitraryBaseSerreAbutmentIso`), filtered by the images of the homology of the
  preimages in `E'` of the skeleta of `ΓB`.
* **First page.** The object at `(a, b)` of the first page (numbered `2`), with `b = k - 1` and
  `a + b = -(q + k)`, is `⨁ⱼ Hq(p⁻¹(f(χⱼ(0))); R)`, the sum over the `k`-cells `j` of `ΓB` of the
  homology of the fibre of `p` over the image of the centre of the cell
  (`TauCeti.TopCat.arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma`). It vanishes when
  `0 ≤ a + 2b`, that is in negative fibre degree
  (`TauCeti.TopCat.isZero_arbitraryBaseSerreSpectralSequence_page_two_X`).
* **Finite filtration.** In degree `n` the filtration of the abutment vanishes below `0` and is
  everything from `n` on
  (`TopCat.Hom.isZero_arbitraryBaseSerreSpectralObject_abutmentFiltration`,
  `TauCeti.TopCat.isIso_arbitraryBaseSerreSpectralObject_abutmentFiltrationι`), so it is finite,
  exhaustive and separated.
* **Strong convergence.** On every late enough page the object at `(a, b)` is the graded piece
  `F_{b+1} H / F_b H` of the filtration of `H_{-(a+b)}(E; R)`
  (`TauCeti.TopCat.arbitraryBaseSerreSpectralSequencePageXIsoGraded`).

The abutment and first-page identifications hold for the base change of `p` along any weak
homotopy equivalence `g : B' ⟶ B`, over any relative CW complex `C ⊆ B'`
(`TauCeti.TopCat.serreSpectralObjectPullbackAbutmentIso`; the first-page identification
`TauCeti.TopCat.serreSpectralSequencePullbackFirstPageXIsoSigma` needs no hypothesis on `g`). The
canonical spectral sequence instantiates them at the CW approximation.

No connectedness, finiteness or dimension hypothesis is imposed on `B` or on the fibres: the CW
approximation has one summand for each path component of `B`, so a disconnected base is covered
by the same construction.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 5.2 and Section 5.1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1 (CW approximation) and Section 5.1 (the Serre spectral sequence).
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TopCat.Hom

variable {E B : TopCat.{u}} (p : E ⟶ B) (R : Type u) [Ring R]

/-- **The Serre spectral sequence over an arbitrary base.** For `p : E ⟶ B`, the Serre spectral
sequence `TauCeti.TopCat.serreSpectralSequence` of the pullback `ΓB ×_B E ⟶ ΓB` of `p` to the CW
approximation `TauCeti.sigmaCWApproximation B` of `B`, with coefficients in `R`. -/
abbrev arbitraryBaseSerreSpectralSequence :=
  TauCeti.TopCat.serreSpectralSequence (univ : Set (TauCeti.sigmaCWApproximation B))
    (TopCat.pullbackFst (TauCeti.sigmaCWApproximationMap B) p) R

/-- **The spectral object of the Serre spectral sequence over an arbitrary base**: the spectral
object `TauCeti.TopCat.serreSpectralObject` of the pullback of `p` to the CW approximation of `B`.
Its spectral sequence is `TopCat.Hom.arbitraryBaseSerreSpectralSequence`, and its abutment in
degree `-n` is `Hₙ(E; R)` (`TauCeti.TopCat.arbitraryBaseSerreAbutmentIso`). -/
abbrev arbitraryBaseSerreSpectralObject :=
  TauCeti.TopCat.serreSpectralObject (univ : Set (TauCeti.sigmaCWApproximation B))
    (TopCat.pullbackFst (TauCeti.sigmaCWApproximationMap B) p) R

/-- **The filtration of the abutment of the Serre spectral sequence over an arbitrary base starts at
`0`**: its pieces `F_b Hₙ(E; R)` vanish for `b < 0`. -/
theorem isZero_arbitraryBaseSerreSpectralObject_abutmentFiltration {b : ℤ} (hb : b < 0)
    (n : ℤ) : IsZero ((p.arbitraryBaseSerreSpectralObject R).abutmentFiltration b n) :=
  TauCeti.TopCat.isZero_serreSpectralObject_abutmentFiltration _ R univ hb n

end TopCat.Hom

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p) (R : Type u) [Ring R]

include hp

section Pullback

variable {B' : _root_.TopCat.{u}} [T2Space B'] {C D : Set B'} [RelCWComplex C D]

variable (C) in
/-- **The abutment of the Serre spectral sequence of a base change along a weak homotopy
equivalence.** Let `p : E ⟶ B` be a Serre fibration, `g : B' ⟶ B` a weak homotopy equivalence and
`C ⊆ B'` a relative CW complex. The abutment in degree `-n` of the Serre spectral sequence over `C`
of the base change `B' ×_B E ⟶ B'` is `Hₙ(E; R)`: it is `Hₙ(B' ×_B E; R)`, followed by the
isomorphism induced by the projection `B' ×_B E ⟶ E`. -/
def serreSpectralObjectPullbackAbutmentIso {g : B' ⟶ B} (hg : g.hom.IsWeakHomotopyEquivalence)
    (n : ℕ) :
    (serreSpectralObject C (_root_.TopCat.pullbackFst g p) R).abutment (-n) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj E :=
  -- The projection `B' ×_B E ⟶ E` is a weak homotopy equivalence, since `g` is one.
  haveI := (isWeakHomotopyEquivalence_pullbackSnd hp hg).isIso_singularHomologyMap
    (ModuleCat.of R R) n
  filteredSpaceAbutmentIso (ModuleCat.of R R) (monotone_preimageSkeleton _) n ≪≫
    asIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).map (_root_.TopCat.pullbackSnd g p))

/-- The isomorphism `TauCeti.TopCat.serreSpectralObjectPullbackAbutmentIso` is the abutment
isomorphism of the spectral sequence of the base change, followed by the map induced by the
projection `B' ×_B E ⟶ E`. -/
@[simp]
lemma serreSpectralObjectPullbackAbutmentIso_hom {g : B' ⟶ B}
    (hg : g.hom.IsWeakHomotopyEquivalence) (n : ℕ) :
    (serreSpectralObjectPullbackAbutmentIso hp R C hg n).hom =
      (filteredSpaceAbutmentIso (ModuleCat.of R R) (monotone_preimageSkeleton _) n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map (_root_.TopCat.pullbackSnd g p) :=
  (rfl)

variable (C) in
/-- **The first page of the Serre spectral sequence of a base change.** Let `p : E ⟶ B` be a Serre
fibration, `g : B' ⟶ B` a map and `C ⊆ B'` a relative CW complex. The object of the first page
(numbered `2`) of the Serre spectral sequence over `C` of the base change `B' ×_B E ⟶ B'` at
`pq = (a, b)`, with `b = k - 1` and `a + b = -(q + k)`, is `⨁ⱼ Hq(p⁻¹(g(χⱼ(0))); R)`, the sum
running over the `k`-cells `j` of `C`. The terms are the homology of fibres of `p` itself, over the
images under `g` of the centres of the cells. -/
def serreSpectralSequencePullbackFirstPageXIsoSigma (g : B' ⟶ B) (k q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    ((serreSpectralSequence C (_root_.TopCat.pullbackFst g p) R).page 2).X pq ≅
      ∐ fun j : cell C k ↦
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).obj (p.fiber (g (map k j 0))) :=
  serreSpectralSequenceFirstPageXIsoSigma C (mem_serreFibrations_pullbackFst hp g) R k q pq hb
      ha ≪≫
    Sigma.mapIso fun j ↦ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).mapIso (p.fiberPullbackFstIso g (map k j 0))

/-- On the summand of the `k`-cell `j`, the inverse of
`TauCeti.TopCat.serreSpectralSequencePullbackFirstPageXIsoSigma` identifies the fibre of `p` over
`g(χⱼ(0))` with the fibre of the base change over `χⱼ(0)`, then includes it by the inverse of
`TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoSigma`. -/
@[reassoc (attr := simp)]
lemma ι_serreSpectralSequencePullbackFirstPageXIsoSigma_inv (g : B' ⟶ B) (k q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) (j : cell C k) :
    Sigma.ι _ j ≫ (serreSpectralSequencePullbackFirstPageXIsoSigma hp R C g k q pq hb ha).inv =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).map (p.fiberPullbackFstIso g (map k j 0)).inv ≫
        Sigma.ι (fun j : cell C k ↦
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
            (ModuleCat.of R R)).obj ((_root_.TopCat.pullbackFst g p).fiber (map k j 0))) j ≫
        (serreSpectralSequenceFirstPageXIsoSigma C (mem_serreFibrations_pullbackFst hp g) R k q
          pq hb ha).inv := by
  rw [serreSpectralSequencePullbackFirstPageXIsoSigma, Iso.trans_inv, Sigma.ι_mapIso_inv_assoc,
    Functor.mapIso_inv]

end Pullback

/-- **The abutment of the Serre spectral sequence over an arbitrary base** in degree `-n` is the
singular homology `Hₙ(E; R)` of the total space: the abutment `Hₙ(ΓB ×_B E; R)` of the spectral
sequence of the pullback to the CW approximation, followed by the isomorphism induced by the
projection `ΓB ×_B E ⟶ E`. -/
def arbitraryBaseSerreAbutmentIso (n : ℕ) :
    (p.arbitraryBaseSerreSpectralObject R).abutment (-n) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj E :=
  serreSpectralObjectPullbackAbutmentIso hp R univ
    (isWeakHomotopyEquivalence_sigmaCWApproximationMap B) n

/-- The isomorphism `TauCeti.TopCat.arbitraryBaseSerreAbutmentIso` is the abutment isomorphism of
the spectral sequence of the pullback, followed by the map induced by the projection
`ΓB ×_B E ⟶ E`. -/
@[simp]
lemma arbitraryBaseSerreAbutmentIso_hom (n : ℕ) :
    (arbitraryBaseSerreAbutmentIso hp R n).hom =
      (filteredSpaceAbutmentIso (ModuleCat.of R R) (monotone_preimageSkeleton _) n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map (_root_.TopCat.pullbackSnd (sigmaCWApproximationMap B) p) :=
  serreSpectralObjectPullbackAbutmentIso_hom ..

/-- **The first page of the Serre spectral sequence over an arbitrary base.** For a Serre fibration
`p : E ⟶ B`, the object of the first page (numbered `2`) at `pq = (a, b)`, with `b = k - 1` and
`a + b = -(q + k)`, is the direct sum `⨁ⱼ Hq(p⁻¹(f(χⱼ(0))); R)` over the `k`-cells `j` of the CW
approximation `ΓB`, where `f : ΓB ⟶ B` is the approximation map and `χⱼ(0)` the centre of the cell
`j`. In the classical indexing this is `E¹_{k,q}`. -/
def arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma (k q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    ((p.arbitraryBaseSerreSpectralSequence R).page 2).X pq ≅
      ∐ fun j : cell (univ : Set (sigmaCWApproximation B)) k ↦
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).obj (p.fiber (sigmaCWApproximationMap B (map k j 0))) :=
  serreSpectralSequencePullbackFirstPageXIsoSigma hp R univ (sigmaCWApproximationMap B) k q pq hb
    ha

/-- On the summand of the `k`-cell `j`, the inverse of
`TauCeti.TopCat.arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma` identifies the fibre of `p`
over `f(χⱼ(0))` with the fibre of the pullback over `χⱼ(0)`, then includes it by the inverse of
`TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoSigma`. -/
@[reassoc (attr := simp)]
lemma ι_arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma_inv (k q : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ))
    (j : cell (univ : Set (sigmaCWApproximation B)) k) :
    Sigma.ι _ j ≫ (arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R k q pq hb ha).inv =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
          (ModuleCat.of R R)).map
          (p.fiberPullbackFstIso (sigmaCWApproximationMap B) (map k j 0)).inv ≫
        Sigma.ι (fun j : cell (univ : Set (sigmaCWApproximation B)) k ↦
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
            (ModuleCat.of R R)).obj
            ((_root_.TopCat.pullbackFst (sigmaCWApproximationMap B) p).fiber (map k j 0))) j ≫
        (serreSpectralSequenceFirstPageXIsoSigma univ
          (mem_serreFibrations_pullbackFst hp (sigmaCWApproximationMap B)) R k q pq hb ha).inv :=
  ι_serreSpectralSequencePullbackFirstPageXIsoSigma_inv ..

/-- **The Serre spectral sequence over an arbitrary base is a first-quadrant spectral sequence.**
The object at `pq = (a, b)` of the first page (numbered `2`) vanishes when `0 ≤ a + 2b`, which is
`E¹_{k,q} = 0` for `q < 0` in the classical indexing. -/
theorem isZero_arbitraryBaseSerreSpectralSequence_page_two_X (pq : ℤ × ℤ)
    (h : 0 ≤ pq.1 + 2 * pq.2) :
    IsZero (((p.arbitraryBaseSerreSpectralSequence R).page 2).X pq) :=
  isZero_serreSpectralSequence_page_two_X
    (mem_serreFibrations_pullbackFst hp _) R univ pq h

/-- **The filtration of the abutment of the Serre spectral sequence over an arbitrary base reaches
everything in finitely many steps.** In degree `n`, every piece `F_b Hₙ(E; R)` with `n ≤ b` of the
filtration of the abutment is everything. -/
theorem isIso_arbitraryBaseSerreSpectralObject_abutmentFiltrationι (n : ℕ) {b : ℤ}
    (hb : n ≤ b) :
    IsIso ((p.arbitraryBaseSerreSpectralObject R).abutmentFiltrationι b (-n)) :=
  isIso_serreSpectralObject_abutmentFiltrationι
    (mem_serreFibrations_pullbackFst hp _) R univ (subset_univ _) n hb

/-- **Strong convergence of the Serre spectral sequence over an arbitrary base.** Let `p : E ⟶ B`
be a Serre fibration, with no hypothesis on `B`. On every page `r ≥ 2` with `b + 3 ≤ r` and
`2 - a - 2b ≤ r`, the object at `pq = (a, b)` is the graded piece `F_{b+1} H / F_b H` of the
filtration of the abutment in degree `a + b`, which is `H_{-(a+b)}(E; R)` by
`TauCeti.TopCat.arbitraryBaseSerreAbutmentIso`. -/
def arbitraryBaseSerreSpectralSequencePageXIsoGraded (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (hra : pq.2 + 3 ≤ r) (hrb : 2 - pq.1 - 2 * pq.2 ≤ r) :
    ((p.arbitraryBaseSerreSpectralSequence R).page r).X pq ≅
      cokernel ((p.arbitraryBaseSerreSpectralObject R).abutmentFiltrationMap pq.2
        (pq.1 + pq.2)) :=
  serreSpectralSequencePageXIsoGraded (mem_serreFibrations_pullbackFst hp _)
    R (subset_univ _) r hr pq hra hrb

end TopCat

end TauCeti

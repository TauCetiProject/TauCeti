/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Sigma
public import TauCeti.AlgebraicTopology.Singular.Fibration.FirstPage
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence

/-!
# The Serre spectral sequence over an arbitrary base

The Serre spectral sequence `TauCeti.TopCat.serreSpectralSequence` of a Serre fibration is built
from the skeletal filtration of a CW structure on the base. A Serre fibration `p : E ⟶ B` over an
arbitrary space `B` is first pulled back along a CW approximation `g : B' ⟶ B`, a weak homotopy
equivalence from a space with a CW structure. The base change `p' : B' ×_B E ⟶ B'` is a Serre
fibration over a CW complex, with the same fibres as `p`, and its total space is weakly equivalent
to `E` (`TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackSnd`). So the Serre spectral sequence of
`p'` is a spectral sequence for `p`:

* its abutment in degree `-n` is `Hₙ(E; R)`
  (`TauCeti.TopCat.serreSpectralObjectPullbackAbutmentIso`), through the homology isomorphism
  induced by the weak homotopy equivalence `B' ×_B E ⟶ E`;
* its first page is `E¹_{d,t} ≅ ⨁ⱼ H_t(p⁻¹(g(χⱼ(0))); R)`, the sum running over the `d`-cells `j`
  of `B'`, made of the homology of fibres of `p` itself
  (`TauCeti.TopCat.serreSpectralSequencePullbackFirstPageXIsoSigma`);
* it is a first-quadrant spectral sequence converging strongly to `H_*(E; R)`, with no finiteness,
  dimension or connectivity assumption on `B`, on `E` or on the fibres, by the convergence of the
  Serre spectral sequence over a CW complex (`TauCeti.TopCat.serreSpectralSequencePageXIsoGraded`).

For the CW approximation `TauCeti.sigmaCWApproximationMap B`, one summand for each path component
of `B`, this is the Serre spectral sequence over an arbitrary base,
`TauCeti.TopCat.arbitraryBaseSerreSpectralSequence p R`. For a disconnected base its cells are the
cells of the CW approximations of the path components (`Topology.CWComplex.sigmaUnivCellEquiv`).

## Main definitions

* `TauCeti.TopCat.arbitraryBaseSerreSpectralSequence`: the Serre spectral sequence of a Serre
  fibration over an arbitrary base.
* `TauCeti.TopCat.arbitraryBaseSerreSpectralObject`: its spectral object, which carries the
  filtration of the abutment.
* `TauCeti.TopCat.serreSpectralObjectPullbackAbutmentIso`,
  `TauCeti.TopCat.arbitraryBaseSerreAbutmentIso`: the abutment in degree `-n` is `Hₙ(E; R)`.
* `TauCeti.TopCat.serreSpectralSequencePullbackFirstPageXIsoSigma`,
  `TauCeti.TopCat.arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma`: the first page is the sum
  over the cells of the CW approximation of the homology of the fibres of `p`.
* `TauCeti.TopCat.arbitraryBaseSerreSpectralSequencePageXIsoGraded`: strong convergence.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 5.1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1 (CW approximation) and Section 5.1 (the Serre spectral sequence).
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p) (R : Type u) [Ring R]

section Pullback

variable {B' : _root_.TopCat.{u}} [T2Space B'] {C D : Set B'} [RelCWComplex C D]

include hp in
variable (C) in
/-- **The abutment of the Serre spectral sequence of a base change along a weak homotopy
equivalence.** Let `p : E ⟶ B` be a Serre fibration, `g : B' ⟶ B` a weak homotopy equivalence and
`C ⊆ B'` a relative CW complex. The abutment in degree `-n` of the Serre spectral sequence over `C`
of the base change `B' ×_B E ⟶ B'` is `Hₙ(E; R)`: it is `Hₙ(B' ×_B E; R)`, mapped isomorphically
to `Hₙ(E; R)` by the projection, a weak homotopy equivalence. -/
def serreSpectralObjectPullbackAbutmentIso {g : B' ⟶ B} (hg : g.hom.IsWeakHomotopyEquivalence)
    (n : ℕ) :
    (serreSpectralObject C (_root_.TopCat.pullbackFst g p) R).abutment (-n) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj E :=
  haveI := (isWeakHomotopyEquivalence_pullbackSnd hp hg).isIso_singularHomologyMap
    (ModuleCat.of R R) n
  filteredSpaceAbutmentIso (ModuleCat.of R R) (monotone_preimageSkeleton _) n ≪≫
    asIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R R)).map (_root_.TopCat.pullbackSnd g p))

@[simp]
lemma serreSpectralObjectPullbackAbutmentIso_hom {g : B' ⟶ B}
    (hg : g.hom.IsWeakHomotopyEquivalence) (n : ℕ) :
    (serreSpectralObjectPullbackAbutmentIso hp R C hg n).hom =
      (filteredSpaceAbutmentIso (ModuleCat.of R R) (monotone_preimageSkeleton _) n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map (_root_.TopCat.pullbackSnd g p) :=
  (rfl)

include hp in
variable (C) in
/-- **The first page of the Serre spectral sequence of a base change.** Let `p : E ⟶ B` be a Serre
fibration, `g : B' ⟶ B` a map and `C ⊆ B'` a relative CW complex. The object of the first page
(numbered `2`) of the Serre spectral sequence over `C` of the base change `B' ×_B E ⟶ B'` at
`pq = (a, b)` is `⨁ⱼ H_t(p⁻¹(g(χⱼ(0))); R)`, the sum running over the `d`-cells `j` of `C`, where
`d = b + 1` and `a + b = -(t + d)`. The terms are the homology of fibres of `p` itself, over the
images under `g` of the centres of the cells. -/
def serreSpectralSequencePullbackFirstPageXIsoSigma (g : B' ⟶ B) (pq : ℤ × ℤ) (d t : ℕ)
    (hd : pq.2 + 1 = d) (ht : pq.1 + pq.2 = -((t + d : ℕ) : ℤ)) :
    ((serreSpectralSequence C (_root_.TopCat.pullbackFst g p) R).page 2).X pq ≅
      ∐ fun j : cell C d ↦
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) t).obj
          (ModuleCat.of R R)).obj (p.fiber (g (map d j 0))) :=
  serreSpectralSequenceFirstPageXIsoSigma C (mem_serreFibrations_pullbackFst hp g) R pq d t hd
      ht ≪≫
    Sigma.mapIso fun j ↦ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) t).obj
      (ModuleCat.of R R)).mapIso (p.fiberPullbackFstIso g (map d j 0))

@[reassoc (attr := simp)]
lemma ι_serreSpectralSequencePullbackFirstPageXIsoSigma_inv (g : B' ⟶ B) (pq : ℤ × ℤ) (d t : ℕ)
    (hd : pq.2 + 1 = d) (ht : pq.1 + pq.2 = -((t + d : ℕ) : ℤ)) (j : cell C d) :
    Sigma.ι _ j ≫ (serreSpectralSequencePullbackFirstPageXIsoSigma hp R C g pq d t hd ht).inv =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) t).obj
          (ModuleCat.of R R)).map (p.fiberPullbackFstIso g (map d j 0)).inv ≫
        Sigma.ι (fun j : cell C d ↦
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) t).obj
            (ModuleCat.of R R)).obj ((_root_.TopCat.pullbackFst g p).fiber (map d j 0))) j ≫
        (serreSpectralSequenceFirstPageXIsoSigma C (mem_serreFibrations_pullbackFst hp g) R pq
          d t hd ht).inv := by
  rw [serreSpectralSequencePullbackFirstPageXIsoSigma, Iso.trans_inv, Sigma.ι_mapIso_inv_assoc]
  rfl

end Pullback

section Canonical

variable (p) in
/-- **The Serre spectral sequence of a map over an arbitrary base**, with coefficients in `R`: the
Serre spectral sequence of the base change of `p : E ⟶ B` along the CW approximation
`TauCeti.sigmaCWApproximationMap B`, over its CW structure. When `p` is a Serre fibration it is a
first-quadrant spectral sequence (`TauCeti.TopCat.isZero_serreSpectralSequence_page_two_X`) whose
first page is made of the homology of the fibres of `p`
(`TauCeti.TopCat.arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma`) and which converges
strongly to `H_*(E; R)` (`TauCeti.TopCat.arbitraryBaseSerreSpectralSequencePageXIsoGraded` and
`TauCeti.TopCat.arbitraryBaseSerreAbutmentIso`). -/
abbrev arbitraryBaseSerreSpectralSequence :=
  serreSpectralSequence (univ : Set (sigmaCWApproximation B))
    (_root_.TopCat.pullbackFst (sigmaCWApproximationMap B) p) R

variable (p) in
/-- **The spectral object of the Serre spectral sequence over an arbitrary base**: the spectral
object of the skeletal filtration of the base change of `p` along the CW approximation of `B`. Its
spectral sequence is `TauCeti.TopCat.arbitraryBaseSerreSpectralSequence p R`, and its abutment in
degree `-n`, filtered by the images of the homology of the preimages of the skeleta, is `Hₙ(E; R)`
when `p` is a Serre fibration (`TauCeti.TopCat.arbitraryBaseSerreAbutmentIso`). -/
abbrev arbitraryBaseSerreSpectralObject :=
  serreSpectralObject (univ : Set (sigmaCWApproximation B))
    (_root_.TopCat.pullbackFst (sigmaCWApproximationMap B) p) R

include hp in
/-- **The abutment of the Serre spectral sequence over an arbitrary base** in degree `-n` is
`Hₙ(E; R)`. -/
def arbitraryBaseSerreAbutmentIso (n : ℕ) :
    (arbitraryBaseSerreSpectralObject p R).abutment (-n) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj E :=
  serreSpectralObjectPullbackAbutmentIso hp R univ
    (isWeakHomotopyEquivalence_sigmaCWApproximationMap B) n

@[simp]
lemma arbitraryBaseSerreAbutmentIso_hom (n : ℕ) :
    (arbitraryBaseSerreAbutmentIso hp R n).hom =
      (filteredSpaceAbutmentIso (ModuleCat.of R R) (monotone_preimageSkeleton _) n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).obj
          (ModuleCat.of R R)).map (_root_.TopCat.pullbackSnd (sigmaCWApproximationMap B) p) :=
  serreSpectralObjectPullbackAbutmentIso_hom ..

include hp in
/-- **The first page of the Serre spectral sequence over an arbitrary base.** The object of the
first page (numbered `2`) of `TauCeti.TopCat.arbitraryBaseSerreSpectralSequence p R` at
`pq = (a, b)` is `⨁ⱼ H_t(p⁻¹(g(χⱼ(0))); R)`, the sum running over the `d`-cells `j` of the CW
approximation `g : ΓB ⟶ B` (`TauCeti.sigmaCWApproximationMap B`), where `d = b + 1` and
`a + b = -(t + d)`. -/
def arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma (pq : ℤ × ℤ) (d t : ℕ)
    (hd : pq.2 + 1 = d) (ht : pq.1 + pq.2 = -((t + d : ℕ) : ℤ)) :
    ((arbitraryBaseSerreSpectralSequence p R).page 2).X pq ≅
      ∐ fun j : cell (univ : Set (sigmaCWApproximation B)) d ↦
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) t).obj
          (ModuleCat.of R R)).obj (p.fiber (sigmaCWApproximationMap B (map d j 0))) :=
  serreSpectralSequencePullbackFirstPageXIsoSigma hp R univ (sigmaCWApproximationMap B) pq d t hd
    ht

@[reassoc (attr := simp)]
lemma ι_arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma_inv (pq : ℤ × ℤ) (d t : ℕ)
    (hd : pq.2 + 1 = d) (ht : pq.1 + pq.2 = -((t + d : ℕ) : ℤ))
    (j : cell (univ : Set (sigmaCWApproximation B)) d) :
    Sigma.ι _ j ≫ (arbitraryBaseSerreSpectralSequenceFirstPageXIsoSigma hp R pq d t hd ht).inv =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) t).obj
          (ModuleCat.of R R)).map
          (p.fiberPullbackFstIso (sigmaCWApproximationMap B) (map d j 0)).inv ≫
        Sigma.ι (fun j : cell (univ : Set (sigmaCWApproximation B)) d ↦
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) t).obj
            (ModuleCat.of R R)).obj
            ((_root_.TopCat.pullbackFst (sigmaCWApproximationMap B) p).fiber (map d j 0))) j ≫
        (serreSpectralSequenceFirstPageXIsoSigma univ
          (mem_serreFibrations_pullbackFst hp (sigmaCWApproximationMap B)) R pq d t hd ht).inv :=
  ι_serreSpectralSequencePullbackFirstPageXIsoSigma_inv ..

include hp in
/-- **The filtration of the abutment of the Serre spectral sequence over an arbitrary base reaches
everything in finitely many steps.** In degree `n`, every piece `F_b Hₙ(E; R)` with `n ≤ b` is
everything. Below `0` it vanishes (`TauCeti.TopCat.isZero_serreSpectralObject_abutmentFiltration`),
so in each degree the filtration is finite, exhaustive and separated. -/
theorem isIso_arbitraryBaseSerreSpectralObject_abutmentFiltrationι (n : ℕ) {b : ℤ} (hb : n ≤ b) :
    IsIso ((arbitraryBaseSerreSpectralObject p R).abutmentFiltrationι b (-n)) :=
  isIso_serreSpectralObject_abutmentFiltrationι (mem_serreFibrations_pullbackFst hp _) R univ
    (subset_univ _) n hb

include hp in
/-- **Strong convergence of the Serre spectral sequence over an arbitrary base.** Let
`p : E ⟶ B` be a Serre fibration over an arbitrary space `B`, with no finiteness, dimension or
connectivity assumption. On every page `r ≥ 2` with `b + 3 ≤ r` and `2 - a - 2b ≤ r`, the object at
`pq = (a, b)` of `TauCeti.TopCat.arbitraryBaseSerreSpectralSequence p R` is the graded piece
`F_{b+1} H / F_b H` of the filtration of the abutment in degree `a + b`, which is
`H_{-(a+b)}(E; R)` by `TauCeti.TopCat.arbitraryBaseSerreAbutmentIso`. -/
def arbitraryBaseSerreSpectralSequencePageXIsoGraded (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (hra : pq.2 + 3 ≤ r) (hrb : 2 - pq.1 - 2 * pq.2 ≤ r) :
    ((arbitraryBaseSerreSpectralSequence p R).page r).X pq ≅
      cokernel ((arbitraryBaseSerreSpectralObject p R).abutmentFiltrationMap pq.2
        (pq.1 + pq.2)) :=
  serreSpectralSequencePageXIsoGraded (mem_serreFibrations_pullbackFst hp _) R (subset_univ _) r hr
    pq hra hrb

end Canonical

end TopCat

end TauCeti

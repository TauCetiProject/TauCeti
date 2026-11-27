/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Fibration.CellFiber
public import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Sigma
public import TauCeti.Topology.Category.TopCat.Pullback
public import TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence

/-!
# The cohomological Serre spectral sequence over an arbitrary base

Let `p : E ⟶ B` be a Serre fibration over an arbitrary space `B`, path-connected or not, with no
CW structure, and let `M` be a module over a ring `R`. Pull `p` back along the CW approximation
`f : ΓB ⟶ B` (`TauCeti.sigmaCWApproximationMap`) to the Serre fibration `p' : E' ⟶ ΓB`, where
`E' = ΓB ×_B E`. The cohomological Serre spectral sequence of `p` is the cohomological Serre
spectral sequence of `p'` over the CW complex `ΓB`
(`TopCat.Hom.arbitraryBaseSerreCohomologySpectralSequence`), the spectral sequence of the
filtration of the singular cochains of `E'` by the cochains vanishing on the preimages of the
skeleta of `ΓB`.

Since `f` is a weak homotopy equivalence, so is the projection `E' ⟶ E`
(`TauCeti.TopCat.isWeakHomotopyEquivalence_pullbackSnd`), and it induces isomorphisms on singular
cohomology (`ContinuousMap.IsWeakHomotopyEquivalence.isIso_singularCohomologyMap`). So the
spectral sequence converges to the cohomology of `E` itself:

* **Abutment.** The abutment in degree `n` is `Hⁿ(E; M)`
  (`TauCeti.TopCat.arbitraryBaseSerreCohomologyAbutmentIso`), filtered by the images of the
  cohomology of `E'` relative to the preimages of the skeleta of `ΓB`.
* **First page.** The object at `(s, t)` of the first page, with `s = k` and `s + t = q + k`, is
  `∏ⱼ H^q(p⁻¹(f(χⱼ(0))); M)`, the product over the `k`-cells `j` of `ΓB` of the cohomology of the
  fibre of `p` over the image of the centre of the cell
  (`TauCeti.TopCat.arbitraryBaseSerreCohomologySpectralSequenceFirstPageXIsoPi`). It vanishes
  below the `s`-axis, that is in negative fibre degree
  (`TauCeti.TopCat.isZero_arbitraryBaseSerreCohomologySpectralSequence_page_one_X`).
* **Bounded filtration.** The piece `F^s Hⁿ(E; M)` of the filtration of the abutment vanishes for
  `n < s` (`TauCeti.TopCat.isZero_arbitraryBaseSerreCohomologySpectralObject_abutmentFiltration`).
* **Strong convergence.** On every late enough page the object at `(s, t)` is the graded piece
  `F^s H^{s+t} / F^{s+1} H^{s+t}` of the filtration of `H^{s+t}(E; M)`
  (`TauCeti.TopCat.arbitraryBaseSerreCohomologySpectralSequencePageXIsoGraded`).

The abutment and first-page identifications hold for the base change of `p` along any weak
homotopy equivalence `g : B' ⟶ B`, over any relative CW complex `C ⊆ B'`
(`TauCeti.TopCat.serreCohomologySpectralObjectPullbackAbutmentIso`; the first-page identification
`TauCeti.TopCat.serreCohomologySpectralSequencePullbackFirstPageXIsoPi` needs no hypothesis on
`g`). The canonical spectral sequence instantiates them at the CW approximation.

No connectedness, finiteness or dimension hypothesis is imposed on `B` or on the fibres: the CW
approximation has one summand for each path component of `B`, so a disconnected base is covered
by the same construction. This is the cohomological counterpart of
`TopCat.Hom.arbitraryBaseSerreSpectralSequence`, built in the same way.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 5.2 and Section 5.1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1 (CW approximation).
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1, Section 1.2 (the cohomology spectral sequence).
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TopCat.Hom

variable {E B : TopCat.{u}} (p : E ⟶ B) (R : Type u) [Ring R] (k : Type*) [Ring k]
  [Linear k (ModuleCat.{u} R)] (M : ModuleCat.{u} R)

/-- **The cohomological Serre spectral sequence over an arbitrary base.** For `p : E ⟶ B`, the
cohomological Serre spectral sequence `TauCeti.TopCat.serreCohomologySpectralSequence` of the
pullback `ΓB ×_B E ⟶ ΓB` of `p` to the CW approximation `TauCeti.sigmaCWApproximation B` of `B`,
with coefficients in the `R`-module `M`. -/
abbrev arbitraryBaseSerreCohomologySpectralSequence :=
  TauCeti.TopCat.serreCohomologySpectralSequence (univ : Set (TauCeti.sigmaCWApproximation B))
    (TopCat.pullbackFst (TauCeti.sigmaCWApproximationMap B) p) R k M

/-- **The spectral object of the cohomological Serre spectral sequence over an arbitrary base**:
the spectral object `TauCeti.TopCat.serreCohomologySpectralObject` of the pullback of `p` to the CW
approximation of `B`. Its spectral sequence is
`TopCat.Hom.arbitraryBaseSerreCohomologySpectralSequence`, and its abutment in degree `n` is
`Hⁿ(E; M)` (`TauCeti.TopCat.arbitraryBaseSerreCohomologyAbutmentIso`). -/
abbrev arbitraryBaseSerreCohomologySpectralObject :=
  TauCeti.TopCat.serreCohomologySpectralObject (univ : Set (TauCeti.sigmaCWApproximation B))
    (TopCat.pullbackFst (TauCeti.sigmaCWApproximationMap B) p) R k M

end TopCat.Hom

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} (hp : serreFibrations p) (R : Type u) [Ring R]
  (k : Type*) [Ring k] [Linear k (ModuleCat.{u} R)] (M : ModuleCat.{u} R)

section Pullback

variable {B' : _root_.TopCat.{u}} [T2Space B'] {C D : Set B'} [RelCWComplex C D]

include hp in
variable (C) in
/-- **The abutment of the cohomological Serre spectral sequence of a base change along a weak
homotopy equivalence.** Let `p : E ⟶ B` be a Serre fibration, `g : B' ⟶ B` a weak homotopy
equivalence and `C ⊆ B'` a relative CW complex. The abutment in degree `n` of the cohomological
Serre spectral sequence over `C` of the base change `B' ×_B E ⟶ B'` is `Hⁿ(E; M)`: it is
`Hⁿ(B' ×_B E; M)`, followed by the inverse of the isomorphism induced by the projection
`B' ×_B E ⟶ E`. -/
def serreCohomologySpectralObjectPullbackAbutmentIso {g : B' ⟶ B}
    (hg : g.hom.IsWeakHomotopyEquivalence) (n : ℕ) :
    (serreCohomologySpectralObject C (_root_.TopCat.pullbackFst g p) R k M).abutment n ≅
      E.singularCohomology (ModuleCat.of R R) k M n :=
  -- The projection `B' ×_B E ⟶ E` is a weak homotopy equivalence, since `g` is one.
  haveI := (isWeakHomotopyEquivalence_pullbackSnd hp hg).isIso_singularCohomologyMap
    (ModuleCat.of R R) k M n
  filteredSpaceCohomologyAbutmentIso (ModuleCat.of R R) k M (monotone_preimageSkeleton _) n ≪≫
    (asIso (_root_.TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M)
      (_root_.TopCat.pullbackSnd g p) n)).symm

/-- The inverse of `TauCeti.TopCat.serreCohomologySpectralObjectPullbackAbutmentIso` is the map
induced by the projection `B' ×_B E ⟶ E`, followed by the inverse of the abutment isomorphism of
the spectral sequence of the base change. -/
@[simp]
lemma serreCohomologySpectralObjectPullbackAbutmentIso_inv {g : B' ⟶ B}
    (hg : g.hom.IsWeakHomotopyEquivalence) (n : ℕ) :
    (serreCohomologySpectralObjectPullbackAbutmentIso hp R k M C hg n).inv =
      _root_.TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M)
          (_root_.TopCat.pullbackSnd g p) n ≫
        (filteredSpaceCohomologyAbutmentIso (ModuleCat.of R R) k M
          (monotone_preimageSkeleton _) n).inv :=
  (rfl)

variable (C) in
/-- **The first page of the cohomological Serre spectral sequence of a base change.** Let
`p : E ⟶ B` be a Serre fibration, `g : B' ⟶ B` a map and `C ⊆ B'` a relative CW complex. The
object at `(s, t)` of the first page of the cohomological Serre spectral sequence over `C` of the
base change `B' ×_B E ⟶ B'`, with `s = n` and `s + t = q + n`, is `∏ⱼ H^q(p⁻¹(g(χⱼ(0))); M)`, the
product running over the `n`-cells `j` of `C`. The factors are the cohomology of fibres of `p`
itself, over the images under `g` of the centres of the cells. -/
def serreCohomologySpectralSequencePullbackFirstPageXIsoPi (g : B' ⟶ B) (n q : ℕ) (s t : ℤ)
    (hs : s = n) (hst : s + t = (q + n : ℕ)) :
    ((serreCohomologySpectralSequence C (_root_.TopCat.pullbackFst g p) R k M).page 1).X
        (s, t) ≅
      ∏ᶜ fun j : cell C n ↦ (p.fiber (g (map n j 0))).singularCohomology (ModuleCat.of R R) k M q :=
  serreCohomologySpectralSequenceFirstPageXIsoPi C (mem_serreFibrations_pullbackFst hp g) R k M n
      q s t hs hst ≪≫
    Pi.mapIso fun j ↦ (singularCohomologyFunctor (ModuleCat.of R R) k M q).mapIso
      (p.fiberPullbackFstIso g (map n j 0)).symm.op

/-- On the factor of the `n`-cell `j`,
`TauCeti.TopCat.serreCohomologySpectralSequencePullbackFirstPageXIsoPi` is the factor of
`TauCeti.TopCat.serreCohomologySpectralSequenceFirstPageXIsoPi` for the base change, followed by
the map induced by the identification of the fibre of `p` over `g(χⱼ(0))` with the fibre of the
base change over `χⱼ(0)`. -/
@[reassoc (attr := simp)]
lemma serreCohomologySpectralSequencePullbackFirstPageXIsoPi_hom_π (g : B' ⟶ B) (n q : ℕ)
    (s t : ℤ) (hs : s = n) (hst : s + t = (q + n : ℕ)) (j : cell C n) :
    (serreCohomologySpectralSequencePullbackFirstPageXIsoPi hp R k M C g n q s t hs hst).hom ≫
        Pi.π _ j =
      (serreCohomologySpectralSequenceFirstPageXIsoPi C (mem_serreFibrations_pullbackFst hp g) R k
          M n q s t hs hst).hom ≫
        Pi.π (fun j : cell C n ↦ ((_root_.TopCat.pullbackFst g p).fiber
          (map n j 0)).singularCohomology (ModuleCat.of R R) k M q) j ≫
        _root_.TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M)
          (p.fiberPullbackFstIso g (map n j 0)).inv q := by
  rw [serreCohomologySpectralSequencePullbackFirstPageXIsoPi, Iso.trans_hom, Category.assoc]
  -- `rw [Pi.mapIso_hom_π]` fails: the factors of `Pi.mapIso` are objects of
  -- `TauCeti.singularCohomologyFunctor`, which match the product only up to unfolding, so the
  -- target is not type-correct at instance transparency. Unification by `exact` sees through this.
  exact congrArg (_ ≫ ·) ((Pi.mapIso_hom_π _ j).trans (congrArg (_ ≫ ·)
    ((Functor.mapIso_hom _ _).trans (singularCohomologyFunctor_map _ _ _ _ _))))

end Pullback

/-- **The abutment of the cohomological Serre spectral sequence over an arbitrary base** in degree
`n` is the singular cohomology `Hⁿ(E; M)` of the total space: the abutment `Hⁿ(ΓB ×_B E; M)` of
the spectral sequence of the pullback to the CW approximation, followed by the inverse of the
isomorphism induced by the projection `ΓB ×_B E ⟶ E`. -/
def arbitraryBaseSerreCohomologyAbutmentIso (n : ℕ) :
    (p.arbitraryBaseSerreCohomologySpectralObject R k M).abutment n ≅
      E.singularCohomology (ModuleCat.of R R) k M n :=
  serreCohomologySpectralObjectPullbackAbutmentIso hp R k M univ
    (isWeakHomotopyEquivalence_sigmaCWApproximationMap B) n

/-- The inverse of `TauCeti.TopCat.arbitraryBaseSerreCohomologyAbutmentIso` is the map induced by
the projection `ΓB ×_B E ⟶ E`, followed by the inverse of the abutment isomorphism of the
spectral sequence of the pullback. -/
@[simp]
lemma arbitraryBaseSerreCohomologyAbutmentIso_inv (n : ℕ) :
    (arbitraryBaseSerreCohomologyAbutmentIso hp R k M n).inv =
      _root_.TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M)
          (_root_.TopCat.pullbackSnd (sigmaCWApproximationMap B) p) n ≫
        (filteredSpaceCohomologyAbutmentIso (ModuleCat.of R R) k M
          (monotone_preimageSkeleton _) n).inv :=
  serreCohomologySpectralObjectPullbackAbutmentIso_inv ..

/-- **The first page of the cohomological Serre spectral sequence over an arbitrary base.** For a
Serre fibration `p : E ⟶ B`, the object at `(s, t)` of the first page, with `s = n` and
`s + t = q + n`, is the product `∏ⱼ H^q(p⁻¹(f(χⱼ(0))); M)` over the `n`-cells `j` of the CW
approximation `ΓB`, where `f : ΓB ⟶ B` is the approximation map and `χⱼ(0)` the centre of the cell
`j`. In the classical indexing this is `E₁^{n,q}`. -/
def arbitraryBaseSerreCohomologySpectralSequenceFirstPageXIsoPi (n q : ℕ) (s t : ℤ) (hs : s = n)
    (hst : s + t = (q + n : ℕ)) :
    ((p.arbitraryBaseSerreCohomologySpectralSequence R k M).page 1).X (s, t) ≅
      ∏ᶜ fun j : cell (univ : Set (sigmaCWApproximation B)) n ↦
        (p.fiber (sigmaCWApproximationMap B (map n j 0))).singularCohomology (ModuleCat.of R R) k
          M q :=
  serreCohomologySpectralSequencePullbackFirstPageXIsoPi hp R k M univ (sigmaCWApproximationMap B)
    n q s t hs hst

/-- On the factor of the `n`-cell `j`,
`TauCeti.TopCat.arbitraryBaseSerreCohomologySpectralSequenceFirstPageXIsoPi` is the factor of
`TauCeti.TopCat.serreCohomologySpectralSequenceFirstPageXIsoPi` for the pullback, followed by the
map induced by the identification of the fibre of `p` over `f(χⱼ(0))` with the fibre of the
pullback over `χⱼ(0)`. -/
@[reassoc (attr := simp)]
lemma arbitraryBaseSerreCohomologySpectralSequenceFirstPageXIsoPi_hom_π (n q : ℕ) (s t : ℤ)
    (hs : s = n) (hst : s + t = (q + n : ℕ)) (j : cell (univ : Set (sigmaCWApproximation B)) n) :
    (arbitraryBaseSerreCohomologySpectralSequenceFirstPageXIsoPi hp R k M n q s t hs hst).hom ≫
        Pi.π _ j =
      (serreCohomologySpectralSequenceFirstPageXIsoPi univ
          (mem_serreFibrations_pullbackFst hp (sigmaCWApproximationMap B)) R k M n q s t hs
          hst).hom ≫
        Pi.π (fun j : cell (univ : Set (sigmaCWApproximation B)) n ↦
          ((_root_.TopCat.pullbackFst (sigmaCWApproximationMap B) p).fiber
            (map n j 0)).singularCohomology (ModuleCat.of R R) k M q) j ≫
        _root_.TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k) (M := M)
          (p.fiberPullbackFstIso (sigmaCWApproximationMap B) (map n j 0)).inv q :=
  serreCohomologySpectralSequencePullbackFirstPageXIsoPi_hom_π ..

include hp in
/-- **The first page of the cohomological Serre spectral sequence over an arbitrary base vanishes
below the `s`-axis.** The object at `(s, t)` of the first page vanishes when `t < 0`, which is
`E₁^{s,t} = 0` in negative fibre degree. -/
theorem isZero_arbitraryBaseSerreCohomologySpectralSequence_page_one_X (s t : ℤ) (ht : t < 0) :
    IsZero (((p.arbitraryBaseSerreCohomologySpectralSequence R k M).page 1).X (s, t)) :=
  isZero_serreCohomologySpectralSequence_page_one_X (mem_serreFibrations_pullbackFst hp _) R k M
    univ s t ht

include hp in
/-- **The filtration of the abutment of the cohomological Serre spectral sequence over an
arbitrary base vanishes above the degree.** The piece `F^s Hⁿ(E; M)` of the filtration of the
abutment, which sits at index `-s`, vanishes for `n < s`. -/
theorem isZero_arbitraryBaseSerreCohomologySpectralObject_abutmentFiltration {s n : ℤ}
    (hn : n < s) :
    IsZero ((p.arbitraryBaseSerreCohomologySpectralObject R k M).abutmentFiltration (-s) n) :=
  isZero_serreCohomologySpectralObject_abutmentFiltration (mem_serreFibrations_pullbackFst hp _)
    R k M univ (subset_univ _) hn

/-- **Strong convergence of the cohomological Serre spectral sequence over an arbitrary base.**
Let `p : E ⟶ B` be a Serre fibration, with no hypothesis on `B`. On every page `r ≥ 1` with
`s < r` and `t + 1 < r`, the object at `(s, t)` is the graded piece
`F^s H^{s+t} / F^{s+1} H^{s+t}` of the filtration of the abutment in degree `s + t`, which is
`H^{s+t}(E; M)` by `TauCeti.TopCat.arbitraryBaseSerreCohomologyAbutmentIso`. -/
def arbitraryBaseSerreCohomologySpectralSequencePageXIsoGraded (r : ℤ) (hr : 1 ≤ r) (s t : ℤ)
    (hs : s < r) (ht : t + 1 < r) :
    ((p.arbitraryBaseSerreCohomologySpectralSequence R k M).page r).X (s, t) ≅
      cokernel ((p.arbitraryBaseSerreCohomologySpectralObject R k M).abutmentFiltrationMap
        (-s - 1) (s + t)) :=
  serreCohomologySpectralSequencePageXIsoGraded (mem_serreFibrations_pullbackFst hp _) R k M
    (subset_univ _) r hr s t hs ht

end TopCat

end TauCeti

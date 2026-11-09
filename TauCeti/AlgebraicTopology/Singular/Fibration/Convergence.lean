/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Skeleton
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Skeleton

/-!
# Convergence of the Serre spectral sequence over a CW complex

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex. Filtering `E` by the
preimages `E_i = p⁻¹(C^(i))` of the skeleta (`TauCeti.preimageSkeleton`) gives the spectral
sequence `TauCeti.filteredSpaceSpectralSequence` of a filtered space, the Serre spectral sequence
of `p`. This file proves that it is a first-quadrant spectral sequence and that, over a CW complex,
it converges strongly to the homology of `E`.

Everything rests on the vanishing `Hₙ(E_{i+1}, E_i; R) = 0` for `n ≤ i`
(`TauCeti.TopCat.isZero_singularHomology_preimageSkeleton_succ`). It is the vanishing
`TauCeti.TopCat.isZero_singularHomology_preimage_skeletonLT` for the skeletal filtration of a Serre
fibration, read in the indexing of `TauCeti.preimageSkeleton`: a Serre fibration pulls the
`i`-connected pair of consecutive skeleta back to an `i`-connected pair.

* **First quadrant.** The object at `(a, b)` on the first page (numbered `2`) is
  `Hₙ(E_{b+1}, E_b; R)` with `a + b = -n`, so it vanishes when `0 ≤ a + 2b`
  (`TauCeti.TopCat.isZero_serreSpectralSequence_page_two_X`). In the classical homological indexing
  `E¹_{d,t} = H_{d+t}(E_d, E_{d-1}; R)` with `d = b + 1`, this is the vanishing for `t < 0`.
* **Finite filtration of the abutment.** Over a CW complex `K` containing the image of `p`, with no
  finiteness or dimension bound, the induced filtration `F_b Hₙ(E; R)` of the abutment is
  everything from `b = n` on (`TauCeti.TopCat.isIso_serreAbutmentFiltrationι`, which holds over
  relative CW complexes as well). For an absolute CW complex it vanishes below `0` because `E_{-1}`
  is empty (`CochainComplex.isZero_filtrationAbutmentFiltration`), so in each degree it is finite,
  exhaustive and separated.
* **Strong convergence.** On every late enough page the object at `(a, b)` is the graded piece
  `F_{b+1} H / F_b H` of the filtration of `H_{-(a+b)}(E; R)`
  (`TauCeti.TopCat.serreSpectralSequencePageXIsoGraded`).

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 2.6 and Section 5.1.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 5.1 (the Serre spectral sequence).
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] (hp : serreFibrations p)
  (R : Type u) [Ring R]

section Relative

variable {C D : Set B} [RelCWComplex C D]

include hp in
/-- **The skeletal filtration of a Serre fibration has no homology below the cell dimension**:
for the preimages `E_i = p⁻¹(C^(i))` of the skeleta, `Hₙ(E_{i+1}, E_i; R) = 0` whenever `n ≤ i`.
This is `TauCeti.TopCat.isZero_singularHomology_preimage_skeletonLT` read in the indexing
`TauCeti.preimageSkeleton` of the filtration. -/
theorem isZero_singularHomology_preimageSkeleton_succ (i : ℤ) (n : ℕ) (hn : n ≤ i) :
    IsZero ((TopPair.ofInclusion (monotone_preimageSkeleton (C := C) p (Int.le_add_one le_rfl) :
      preimageSkeleton C p i ⊆ preimageSkeleton C p (i + 1))).singularHomology
        (ModuleCat.of R R) n) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by lia : 0 ≤ i)
  refine (TopPair.isZero_singularHomology_ofInclusion_congr _ _
    (preimage_mono (f := p) (skeletonLT_mono (C := C) (by norm_cast; lia :
      ((m + 1 : ℕ) : ℕ∞) ≤ ((m + 2 : ℕ) : ℕ∞)))) ?_ ?_ n).2
    (isZero_singularHomology_preimage_skeletonLT hp R (i := m) (by norm_cast; lia) (by lia))
  all_goals
    rw [preimageSkeleton_def]
    congr 3

include hp in
variable (C) in
/-- **The Serre spectral sequence is a first-quadrant spectral sequence.** The object at
`pq = (a, b)` on the first page (numbered `2`) of the spectral sequence of the filtration of `E` by
the preimages of the skeleta vanishes when `0 ≤ a + 2b`. In the classical homological indexing
`E¹_{d,t} = H_{d+t}(E_d, E_{d-1}; R)`, with `d = b + 1` and `d + t = -(a + b)`, this is the
vanishing of `E¹_{d,t}` for `t < 0`. -/
theorem isZero_serreSpectralSequence_page_two_X (pq : ℤ × ℤ) (h : 0 ≤ pq.1 + 2 * pq.2) :
    IsZero (((filteredSpaceSpectralSequence (ModuleCat.of R R)
      (monotone_preimageSkeleton (C := C) p)).page 2).X pq) := by
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hneg
  · exact isZero_filteredSpaceSpectralSequence_page_two_X _ _ pq hpos
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by lia : 0 ≤ -(pq.1 + pq.2))
    exact (isZero_singularHomology_preimageSkeleton_succ hp R pq.2 n (by lia)).of_iso
      (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R)
        (monotone_preimageSkeleton p) pq pq.2 (pq.2 + 1) rfl rfl _ rfl n (by lia))

include hp in
variable (C) in
/-- **The filtration of the abutment of the Serre spectral sequence reaches everything in finitely
many steps.** Let `p : E ⟶ B` be a Serre fibration with values in a relative CW complex `C ⊆ B`,
with no finiteness or dimension bound on `C`. In degree `n`, the `n`th piece `F_n Hₙ(E; R)` of the
filtration of the abutment, the image of the homology of the preimage of the `n`-skeleton, is
everything. -/
theorem isIso_serreAbutmentFiltrationι (hpC : range p ⊆ C) (n : ℕ) :
    IsIso ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
      (monotone_singularChainFiltration (ModuleCat.of R R)
        (monotone_preimageSkeleton (C := C) p)))).abutmentFiltrationι n (-n)) :=
  isIso_filteredSpaceAbutmentFiltrationι_of_exhaustive (ModuleCat.of R R)
    (monotone_preimageSkeleton p)
    (fun _ hS ↦ exists_subset_preimageSkeleton_of_isCompact p.hom.continuous hpC hS) n
    fun i hi ↦ isZero_singularHomology_preimageSkeleton_succ hp R i n hi

end Relative

section Absolute

variable {K : Set B} [CWComplex K]

/-- **Strong convergence of the Serre spectral sequence over a CW complex.** Let `p : E ⟶ B` be a
Serre fibration with values in a CW complex `K ⊆ B`, with no finiteness or dimension bound on `K`.
On every page `r ≥ 2` with `b + 3 ≤ r` and `2 - a - 2b ≤ r`, the object at `pq = (a, b)` of the
spectral sequence of the filtration of `E` by the preimages of the skeleta is the graded piece
`F_{b+1} H / F_b H` of the induced filtration of the abutment in degree `a + b`, which is
`H_{-(a+b)}(E; R)` by `TauCeti.filteredSpaceAbutmentIso`. -/
def serreSpectralSequencePageXIsoGraded (hpK : range p ⊆ K) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (hra : pq.2 + 3 ≤ r) (hrb : 2 - pq.1 - 2 * pq.2 ≤ r) :
    ((filteredSpaceSpectralSequence (ModuleCat.of R R)
        (monotone_preimageSkeleton (C := K) p)).page r).X pq ≅
      cokernel (Abelian.SpectralObject.abutmentFiltrationMap
        (CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
          (monotone_singularChainFiltration (ModuleCat.of R R)
            (monotone_preimageSkeleton (C := K) p))))
        pq.2 (pq.1 + pq.2)) :=
  preimageSkeletonSpectralSequencePageXIsoGraded (ModuleCat.of R R) p.hom.continuous hpK
    (fun i n hn ↦ isZero_singularHomology_preimageSkeleton_succ hp R i n hn) r hr pq hra hrb

end Absolute

end TopCat

end TauCeti

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
`TauCeti.TopCat.serreSpectralSequence` of `p`. It is the spectral sequence of the spectral object
`TauCeti.TopCat.serreSpectralObject`, whose abutment carries the induced filtration of the homology
of `E`. This file proves that it is a first-quadrant spectral sequence and that, over a CW complex,
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
  everything from `b = n` on
  (`TauCeti.TopCat.isIso_serreSpectralObject_abutmentFiltrationι`, which holds over relative CW
  complexes as well). For an absolute CW complex it vanishes below `0` because `E_{-1}`
  is empty (`TauCeti.TopCat.isZero_serreSpectralObject_abutmentFiltration`), so in each degree it
  is finite, exhaustive and separated.
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

section Defs

variable {E B : _root_.TopCat.{u}} [T2Space B]

/-- **The Serre spectral sequence** of `p : E ⟶ B` over a relative CW complex `C ⊆ B`, with
coefficients in `R`: the spectral sequence `TauCeti.filteredSpaceSpectralSequence` of the
filtration of `E` by the preimages `p⁻¹(C^(i))` of the skeleta (`TauCeti.preimageSkeleton`). -/
abbrev serreSpectralSequence (C : Set B) {D : Set B} [RelCWComplex C D] (p : E ⟶ B)
    (R : Type u) [Ring R] :=
  filteredSpaceSpectralSequence (ModuleCat.of R R) (monotone_preimageSkeleton (C := C) p)

/-- **The spectral object of the Serre spectral sequence** of `p : E ⟶ B` over a relative CW
complex `C ⊆ B`, with coefficients in `R`: the spectral object of the filtration of the singular
chains of `E` by the singular chains of the preimages of the skeleta. Its spectral sequence is
`TauCeti.TopCat.serreSpectralSequence`, and its abutment in degree `-n` is `Hₙ(E; R)`
(`TauCeti.filteredSpaceAbutmentIso`), filtered by the images of the homology of the preimages of
the skeleta. -/
abbrev serreSpectralObject (C : Set B) {D : Set B} [RelCWComplex C D] (p : E ⟶ B)
    (R : Type u) [Ring R] :=
  CochainComplex.spectralObject (CochainComplex.filtrationFunctor _
    (monotone_singularChainFiltration (ModuleCat.of R R) (monotone_preimageSkeleton (C := C) p)))

end Defs

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
  · rw [preimageSkeleton_def, show ((m : ℤ) + 1 + 1).toNat = m + 2 by lia]
  · rw [preimageSkeleton_def, show ((m : ℤ) + 1).toNat = m + 1 by lia]

include hp in
variable (C) in
/-- **The Serre spectral sequence is a first-quadrant spectral sequence.** The object at
`pq = (a, b)` on the first page (numbered `2`) of the spectral sequence of the filtration of `E` by
the preimages of the skeleta vanishes when `0 ≤ a + 2b`. In the classical homological indexing
`E¹_{d,t} = H_{d+t}(E_d, E_{d-1}; R)`, with `d = b + 1` and `d + t = -(a + b)`, this is the
vanishing of `E¹_{d,t}` for `t < 0`. -/
theorem isZero_serreSpectralSequence_page_two_X (pq : ℤ × ℤ) (h : 0 ≤ pq.1 + 2 * pq.2) :
    IsZero (((serreSpectralSequence C p R).page 2).X pq) := by
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
with no finiteness or dimension bound on `C`. In degree `n`, every piece `F_b Hₙ(E; R)` with
`n ≤ b` of the filtration of the abutment, the image of the homology of the preimage of the
`b`-skeleton, is everything. -/
theorem isIso_serreSpectralObject_abutmentFiltrationι (hpC : range p ⊆ C) (n : ℕ) {b : ℤ}
    (hb : n ≤ b) :
    IsIso ((serreSpectralObject C p R).abutmentFiltrationι b (-n)) :=
  isIso_filteredSpaceAbutmentFiltrationι_of_exhaustive (ModuleCat.of R R)
    (monotone_preimageSkeleton p)
    (fun _ hS ↦ exists_subset_preimageSkeleton_of_isCompact p.hom.continuous hpC hS) n
    fun i hi ↦ isZero_singularHomology_preimageSkeleton_succ hp R i n (hb.trans hi)

end Relative

section Absolute

variable {K : Set B} [CWComplex K]

omit hp in
variable (K p) in
/-- **The filtration of the abutment of the Serre spectral sequence starts at `0`.** Over a CW
complex `K ⊆ B`, the piece `F_b Hₙ(E; R)` of the filtration of the abutment vanishes for `b < 0`,
since the preimage of the `b`-skeleton is empty. -/
theorem isZero_serreSpectralObject_abutmentFiltration {b : ℤ} (hb : b < 0) (n : ℤ) :
    IsZero ((serreSpectralObject K p R).abutmentFiltration b n) :=
  CochainComplex.isZero_filtrationAbutmentFiltration _ _
    (singularChainFiltration_eq_bot (ModuleCat.of R R) (preimageSkeleton_eq_empty p hb)) n

/-- **Strong convergence of the Serre spectral sequence over a CW complex.** Let `p : E ⟶ B` be a
Serre fibration with values in a CW complex `K ⊆ B`, with no finiteness or dimension bound on `K`.
On every page `r ≥ 2` with `b + 3 ≤ r` and `2 - a - 2b ≤ r`, the object at `pq = (a, b)` of the
spectral sequence of the filtration of `E` by the preimages of the skeleta is the graded piece
`F_{b+1} H / F_b H` of the induced filtration of the abutment in degree `a + b`, which is
`H_{-(a+b)}(E; R)` by `TauCeti.filteredSpaceAbutmentIso`. -/
def serreSpectralSequencePageXIsoGraded (hpK : range p ⊆ K) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (hra : pq.2 + 3 ≤ r) (hrb : 2 - pq.1 - 2 * pq.2 ≤ r) :
    ((serreSpectralSequence K p R).page r).X pq ≅
      cokernel ((serreSpectralObject K p R).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) :=
  preimageSkeletonSpectralSequencePageXIsoGraded (ModuleCat.of R R) p.hom.continuous hpK
    (fun i n hn ↦ isZero_singularHomology_preimageSkeleton_succ hp R i n hn) r hr pq hra hrb

end Absolute

end TopCat

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.FilteredSpace
public import TauCeti.AlgebraicTopology.Singular.Fibration.Convergence
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# The cohomological Serre spectral sequence over a CW complex

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex. Filtering `E` by the
preimages `E_j = p⁻¹(C^(j))` of the skeleta (`TauCeti.preimageSkeleton`) gives the cohomological
spectral sequence of a filtered space `TauCeti.filteredSpaceCohomologySpectralSequence`, the
decreasing filtration of the singular cochains of `E` with coefficients in a module `M` over a
commutative ring `k` by the cochains vanishing on `E_{j-1}`. This is the cohomological Serre
spectral sequence `TauCeti.TopCat.serreCohomologySpectralSequence` of `p`, in the classical
indexing: `E₁^{j,q} = H^{j+q}(E_j, E_{j-1}; M)` and `d_r : E_r^{j,q} ⟶ E_r^{j+r,q-r+1}`.

Everything rests on the vanishing of `Hⁿ(E_j, E_{j-1}; M)` for `n < j`
(`TauCeti.TopCat.isZero_singularCohomology_preimageSkeleton`): a Serre fibration pulls the
`(j - 1)`-connected pair of consecutive skeleta back to a pair whose relative homology with
coefficients in `k` vanishes up to degree `j - 1`
(`TauCeti.TopCat.isZero_singularHomology_preimageSkeleton_succ`), and the relative singular chains
are free, so relative cohomology vanishes in the same range.

* **First quadrant.** The first page vanishes below the horizontal axis: `E₁^{j,q} = 0` for `q < 0`
  (`TauCeti.TopCat.isZero_serreCohomologySpectralSequence_page_one_X`).
* **Finite filtration of the abutment.** Over a CW complex `K` containing the image of `p`, with no
  finiteness or dimension bound, the piece `F^j Hⁿ(E; M)` of the filtration of the abutment, the
  image of the cohomology of the cochains vanishing on `E_{j-1}`, vanishes for `n < j`
  (`TauCeti.TopCat.isZero_serreCohomologySpectralObject_abutmentFiltration`).
* **Strong convergence.** On every late enough page the object at `(j, q)` is the graded piece
  `F^j H^{j+q} / F^{j+1} H^{j+q}` of the filtration of `H^{j+q}(E; M)`
  (`TauCeti.TopCat.serreCohomologySpectralSequencePageXIsoGraded`). The cochain filtration does not
  vanish in any degree over an infinite-dimensional base; convergence comes from its completeness
  (`TauCeti.isCompleteFiltration_vanishingSingularCochains`).

The identification of the second page with `H^j(B; H^q(F; M))` and the multiplicative structure are
not treated here.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 5.2.
* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Theorem 5.5.10.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

section Defs

variable {E B : _root_.TopCat.{u}} [T2Space B]

/-- **The cohomological Serre spectral sequence** of `p : E ⟶ B` over a relative CW complex
`C ⊆ B`, with coefficients in a module `M` over a commutative ring `k`: the cohomological spectral
sequence `TauCeti.filteredSpaceCohomologySpectralSequence` of the filtration of `E` by the
preimages `p⁻¹(C^(j))` of the skeleta (`TauCeti.preimageSkeleton`). Its first page is
`E₁^{j,q} = H^{j+q}(E_j, E_{j-1}; M)`
(`TauCeti.filteredSpaceCohomologySpectralSequenceFirstPageXIso`). -/
abbrev serreCohomologySpectralSequence (C : Set B) {D : Set B} [RelCWComplex C D] (p : E ⟶ B)
    (k : Type u) [CommRing k] (M : ModuleCat.{u} k) :=
  filteredSpaceCohomologySpectralSequence (ModuleCat.of k k) k M
    (monotone_preimageSkeleton (C := C) p)

/-- **The spectral object of the cohomological Serre spectral sequence** of `p : E ⟶ B` over a
relative CW complex `C ⊆ B`, with coefficients in a module `M` over a commutative ring `k`. Its
abutment in degree `n` is `Hⁿ(E; M)` (`TauCeti.filteredSpaceCohomologyAbutmentIso`), filtered by
the images of the cohomology of the cochains vanishing on the preimages of the skeleta. -/
abbrev serreCohomologySpectralObject (C : Set B) {D : Set B} [RelCWComplex C D] (p : E ⟶ B)
    (k : Type u) [CommRing k] (M : ModuleCat.{u} k) :=
  filteredSpaceCohomologySpectralObject (ModuleCat.of k k) k M
    (monotone_preimageSkeleton (C := C) p)

end Defs

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] (hp : serreFibrations p)
  (k : Type u) [CommRing k] (M : ModuleCat.{u} k)

section Relative

variable {C D : Set B} [RelCWComplex C D]

include hp in
/-- **The skeletal filtration of a Serre fibration has no cohomology below the cell dimension**:
for the preimages `E_j = p⁻¹(C^(j))` of the skeleta, `Hⁿ(E_j, E_{j-1}; M) = 0` whenever `n < j`.
The relative homology with coefficients in `k` vanishes in degrees `≤ j - 1`
(`TauCeti.TopCat.isZero_singularHomology_preimageSkeleton_succ`), and the relative singular
chains with coefficients in `k` are free. -/
theorem isZero_singularCohomology_preimageSkeleton (j : ℤ) (n : ℕ) (hn : n < j) :
    IsZero ((TopPair.ofInclusion (monotone_preimageSkeleton (C := C) p (sub_le_self j zero_le_one) :
      preimageSkeleton C p (j - 1) ⊆ preimageSkeleton C p j)).singularCohomology
        (ModuleCat.of k k) k M n) :=
  have : Projective (ModuleCat.of k k) :=
    ModuleCat.projective_of_free (Module.Basis.singleton Unit k)
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of k k) M n
    fun j' hj' ↦ (TopPair.isZero_singularHomology_ofInclusion_congr _ _ _
      (congrArg (preimageSkeleton C p) (by lia)) rfl j').1
        (isZero_singularHomology_preimageSkeleton_succ hp k (j - 1) j' (by lia))

include hp in
variable (C) in
/-- **The cohomological Serre spectral sequence is a first-quadrant spectral sequence.** The object
at `(j, q)` on the first page vanishes when `q < 0`: it is `H^{j+q}(E_j, E_{j-1}; M)`, which
vanishes in negative total degree and below the cell dimension `j`. -/
theorem isZero_serreCohomologySpectralSequence_page_one_X (j q : ℤ) (hq : q < 0) :
    IsZero (((serreCohomologySpectralSequence C p k M).page 1).X (j, q)) := by
  rcases lt_or_ge (j + q) 0 with hneg | hpos
  · exact isZero_filteredSpaceCohomologySpectralSequence_page_one_X _ _ _ _ j q hneg
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hpos
    exact (isZero_singularCohomology_preimageSkeleton hp k M j n (by lia)).of_iso
      (filteredSpaceCohomologySpectralSequenceFirstPageXIso (ModuleCat.of k k) k M
        (monotone_preimageSkeleton p) j q (j - 1) j rfl rfl n hn)

end Relative

section Absolute

variable {K : Set B} [CWComplex K]

include hp in
/-- **The filtration of the abutment of the cohomological Serre spectral sequence is finite.** Let
`p : E ⟶ B` be a Serre fibration with values in a CW complex `K ⊆ B`, with no finiteness or
dimension bound on `K`. In degree `n`, the piece `F^j Hⁿ(E; M)` of the filtration of the abutment,
indexed by `-j` in the spectral object, vanishes for `n < j`. -/
theorem isZero_serreCohomologySpectralObject_abutmentFiltration (hpK : range p ⊆ K) {j n : ℤ}
    (hn : n < j) :
    IsZero ((serreCohomologySpectralObject K p k M).abutmentFiltration (-j) n) :=
  isZero_filteredSpaceCohomologySpectralObject_abutmentFiltration _
    (fun _ hS ↦ exists_subset_preimageSkeleton_of_isCompact p.hom.continuous hpK hS)
    (preimageSkeleton_eq_empty p (by lia)) (fun j n hn ↦
      isZero_singularCohomology_preimageSkeleton hp k M j n hn) hn

/-- **Strong convergence of the cohomological Serre spectral sequence over a CW complex.** Let
`p : E ⟶ B` be a Serre fibration with values in a CW complex `K ⊆ B`, with no finiteness or
dimension bound on `K`. On every page `r ≥ 1` with `j < r` and `q + 1 < r`, the object at `(j, q)`
is the graded piece `F^j H^{j+q} / F^{j+1} H^{j+q}` of the induced filtration of the abutment,
which is `H^{j+q}(E; M)` by `TauCeti.filteredSpaceCohomologyAbutmentIso`. -/
def serreCohomologySpectralSequencePageXIsoGraded (hpK : range p ⊆ K) (r : ℤ) (hr : 1 ≤ r)
    (j q : ℤ) (hj : j < r) (hq : q + 1 < r) :
    ((serreCohomologySpectralSequence K p k M).page r).X (j, q) ≅
      cokernel ((serreCohomologySpectralObject K p k M).abutmentFiltrationMap (-j - 1) (j + q)) :=
  filteredSpaceCohomologySpectralSequencePageXIsoGraded _
    (fun _ hS ↦ exists_subset_preimageSkeleton_of_isCompact p.hom.continuous hpK hS)
    (preimageSkeleton_eq_empty p (by lia)) (fun j n hn ↦
      isZero_singularCohomology_preimageSkeleton hp k M j n hn) r hr j q hj hq

end Absolute

end TopCat

end TauCeti

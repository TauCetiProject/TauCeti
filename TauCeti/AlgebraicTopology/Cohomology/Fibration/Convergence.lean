/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.FilteredSpace.Complete
public import TauCeti.AlgebraicTopology.Singular.Fibration.Convergence
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Convergence of the cohomology Serre spectral sequence over a CW complex

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex. Filtering the singular
cochains of `E` by the cochains vanishing on the preimages `E_s = p⁻¹(C^(s))` of the skeleta
(`TauCeti.preimageSkeleton`) gives the cohomology Serre spectral sequence
`TauCeti.TopCat.serreCohomologySpectralSequence`, with first page
`E₁^{s,t} = H^{s+t}(E_s, E_{s-1}; M)`
(`TauCeti.filteredSpaceCohomologySpectralSequenceFirstPageXIso`) and abutment `H^{s+t}(E; M)`
(`TauCeti.filteredSpaceCohomologyAbutmentIso`). The chains have coefficients in a ring `R` and
the cochains take values in an `R`-module `M`.

Everything rests on the vanishing `Hⁿ(E_j, E_{j-1}; M) = 0` for `n < j`
(`TauCeti.TopCat.isZero_singularCohomology_preimageSkeleton`). It follows from the vanishing of
the relative homology `H_i(E_j, E_{j-1}; R)` for `i < j`
(`TauCeti.TopCat.isZero_singularHomology_preimageSkeleton_succ`), since the relative singular
chains are projective.

* **Nonnegative fibre degrees.** `E₁^{s,t} = 0` for `t < 0`
  (`TauCeti.TopCat.isZero_serreCohomologySpectralSequence_page_one_X`).
* **Finite filtration of the abutment.** Over a CW complex `K` containing the image of `p`, with no
  finiteness or dimension bound, the piece `F^s Hⁿ(E; M)` of the induced filtration vanishes for
  `n < s` (`TauCeti.TopCat.isZero_serreCohomologySpectralObject_abutmentFiltration`).
* **Strong convergence.** On every page `r` with `s < r` and `t + 1 < r`, the object at `(s, t)` is
  the graded piece `F^s H / F^{s+1} H` of `H^{s+t}(E; M)`
  (`TauCeti.TopCat.serreCohomologySpectralSequencePageXIsoGraded`).

Over an infinite-dimensional base no preimage of a skeleton is all of `E`, and the filtration of
the cochains is not finite in any degree. The convergence comes from its completeness
(`TauCeti.isCompleteFiltration_singularCochainFiltration`): a cochain is determined by its values
on singular simplices, each of which lies over a finite skeleton.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 5.1.
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

/-- **The cohomology Serre spectral sequence** of `p : E ⟶ B` over a relative CW complex
`C ⊆ B`, for singular chains with coefficients in `R` and cochains with values in `M`: the
cohomology spectral sequence `TauCeti.filteredSpaceCohomologySpectralSequence` of the filtration of
`E` by the preimages `p⁻¹(C^(i))` of the skeleta (`TauCeti.preimageSkeleton`). Its first page is
`E₁^{s,t} = H^{s+t}(p⁻¹(C^(s)), p⁻¹(C^(s-1)); M)`. -/
abbrev serreCohomologySpectralSequence (C : Set B) {D : Set B} [RelCWComplex C D] (p : E ⟶ B)
    (R : Type u) [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) :=
  filteredSpaceCohomologySpectralSequence (ModuleCat.of R R) k M
    (monotone_preimageSkeleton (C := C) p)

/-- **The spectral object of the cohomology Serre spectral sequence** of `p : E ⟶ B` over a
relative CW complex `C ⊆ B`: the spectral object of the filtration of the singular cochains of `E`
by the cochains vanishing on the preimages of the skeleta. Its abutment in degree `n` is
`Hⁿ(E; M)` (`TauCeti.filteredSpaceCohomologyAbutmentIso`), and the piece at `-s` of the induced
filtration of the abutment is the image of the cohomology of `E` relative to `p⁻¹(C^(s-1))`. -/
abbrev serreCohomologySpectralObject (C : Set B) {D : Set B} [RelCWComplex C D] (p : E ⟶ B)
    (R : Type u) [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) :=
  filteredSpaceCohomologySpectralObject (ModuleCat.of R R) k M
    (monotone_preimageSkeleton (C := C) p)

end Defs

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] (hp : serreFibrations p)
  (R : Type u) [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{u} R)] (M : ModuleCat.{u} R)

section Relative

variable {C D : Set B} [RelCWComplex C D]

include hp in
/-- **The skeletal filtration of a Serre fibration has no cohomology below the cell dimension**:
for the preimages `E_j = p⁻¹(C^(j))` of the skeleta, `Hⁿ(E_j, E_{j-1}; M) = 0` whenever `n < j`.
The relative homology `H_i(E_j, E_{j-1}; R)` vanishes for `i < j`
(`TauCeti.TopCat.isZero_singularHomology_preimageSkeleton_succ`), and the relative singular chains
are projective. -/
theorem isZero_singularCohomology_preimageSkeleton (j : ℤ) (n : ℕ) (hn : n < j) :
    IsZero ((TopPair.ofInclusion (monotone_preimageSkeleton (C := C) p (by lia : j - 1 ≤ j) :
      preimageSkeleton C p (j - 1) ⊆ preimageSkeleton C p j)).singularCohomology
        (ModuleCat.of R R) k M n) :=
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of R R) M n
    fun i hi ↦ (TopPair.isZero_singularHomology_ofInclusion_congr _ _ _
      (by rw [sub_add_cancel]) rfl i).1
        (isZero_singularHomology_preimageSkeleton_succ hp R (j - 1) i (by lia))

include hp in
variable (C) in
/-- **The cohomology Serre spectral sequence is concentrated in nonnegative fibre degrees.** The
object `E₁^{s,t} = H^{s+t}(E_s, E_{s-1}; M)` on the first page vanishes for `t < 0`. -/
theorem isZero_serreCohomologySpectralSequence_page_one_X (s t : ℤ) (ht : t < 0) :
    IsZero (((serreCohomologySpectralSequence C p R k M).page 1).X (s, t)) := by
  rcases lt_or_ge (s + t) 0 with hneg | hnonneg
  · exact isZero_filteredSpaceCohomologySpectralSequence_page_one_X _ _ _ _ s t hneg
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnonneg
    exact (isZero_singularCohomology_preimageSkeleton hp R k M s n (by lia)).of_iso
      (filteredSpaceCohomologySpectralSequenceFirstPageXIso (ModuleCat.of R R) k M
        (monotone_preimageSkeleton p) s t (s - 1) s rfl rfl n hn)

end Relative

section Absolute

variable {K : Set B} [CWComplex K]

include hp in
variable (K) in
/-- **The filtration of the abutment of the cohomology Serre spectral sequence is finite.** Let
`p : E ⟶ B` be a Serre fibration with values in a CW complex `K ⊆ B`, with no finiteness or
dimension bound on `K`. In degree `n`, the piece `F^s Hⁿ(E; M)` of the filtration of the abutment,
the image of the cohomology of `E` relative to the preimage of the `(s - 1)`-skeleton, vanishes for
`n < s`. -/
theorem isZero_serreCohomologySpectralObject_abutmentFiltration (hpK : range p ⊆ K) {s n : ℤ}
    (hn : n < s) :
    IsZero ((serreCohomologySpectralObject K p R k M).abutmentFiltration (-s) n) :=
  isZero_filteredSpaceCohomologySpectralObject_abutmentFiltration _ _ _
    (monotone_preimageSkeleton p)
    (fun _ hS ↦ exists_subset_preimageSkeleton_of_isCompact p.hom.continuous hpK hS)
    (preimageSkeleton_eq_empty p (by lia : (-1 : ℤ) < 0))
    (fun j n hn ↦ isZero_singularCohomology_preimageSkeleton hp R k M j n hn) hn

include hp in
variable (K) in
/-- **Strong convergence of the cohomology Serre spectral sequence over a CW complex.** Let
`p : E ⟶ B` be a Serre fibration with values in a CW complex `K ⊆ B`, with no finiteness or
dimension bound on `K`. On every page `r ≥ 1` with `s < r` and `t + 1 < r`, the object at `(s, t)`
of the cohomology spectral sequence of the filtration of `E` by the preimages of the skeleta is the
graded piece `F^s H / F^{s+1} H` of the induced filtration of the abutment in degree `s + t`, which
is `H^{s+t}(E; M)` by `TauCeti.filteredSpaceCohomologyAbutmentIso`. -/
def serreCohomologySpectralSequencePageXIsoGraded (hpK : range p ⊆ K) (r : ℤ) (hr : 1 ≤ r)
    (s t : ℤ) (hs : s < r) (ht : t + 1 < r) :
    ((serreCohomologySpectralSequence K p R k M).page r).X (s, t) ≅
      cokernel ((serreCohomologySpectralObject K p R k M).abutmentFiltrationMap (-s - 1)
        (s + t)) :=
  filteredSpaceCohomologySpectralSequencePageXIsoGradedOfExhaustive _ _ _
    (monotone_preimageSkeleton p)
    (fun _ hS ↦ exists_subset_preimageSkeleton_of_isCompact p.hom.continuous hpK hS)
    (preimageSkeleton_eq_empty p (by lia : (-1 : ℤ) < 0))
    (fun j n hn ↦ isZero_singularCohomology_preimageSkeleton hp R k M j n hn) r hr s t hs ht

end Absolute

end TopCat

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.AlgebraicTopology.Cohomology.FilteredSpace
public import TauCeti.AlgebraicTopology.Singular.Fibration.Convergence

/-!
# The cohomological Serre spectral sequence over a CW complex

Let `f : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex, and let `M` be a module
over a ring `R`. Filtering the singular cochains of `E` with coefficients in `M` by
the cochains vanishing on the preimages `E_{s-1} = f⁻¹(C^(s-1))` of the skeleta
(`TauCeti.preimageSkeleton`) gives the cohomological spectral sequence of a filtered space
`TauCeti.filteredSpaceCohomologySpectralSequence`, the cohomological Serre spectral sequence
`TauCeti.TopCat.serreCohomologySpectralSequence` of `f`. Its first page is
`E₁^{s,t} = H^{s+t}(E_s, E_{s-1}; M)`
(`TauCeti.filteredSpaceCohomologySpectralSequenceFirstPageXIso`), and its abutment is
`H^{s+t}(E; M)` (`TauCeti.filteredSpaceCohomologyAbutmentIso`).

As for the homological Serre spectral sequence, everything rests on the vanishing of the relative
homology `Hₙ(E_s, E_{s-1}; R)` for `n < s`
(`TauCeti.TopCat.isZero_singularHomology_preimageSkeleton_succ`): a Serre fibration pulls the
`(s - 1)`-connected pair of consecutive skeleta back to an `(s - 1)`-connected pair. The relative
singular chains with coefficients in `R` are projective, so the relative cohomology vanishes in
the same range (`TauCeti.TopCat.isZero_singularCohomology_preimageSkeleton`).

* **Vanishing below the `s`-axis.** The object at `(s, t)` on the first page vanishes when `t < 0`
  (`TauCeti.TopCat.isZero_serreCohomologySpectralSequence_page_one_X`).
* **Strong convergence.** When `C` contains the image of `f`, with no finiteness or dimension
  bound on `C`, the filtration of the cochains is complete and separated in each degree, since
  every singular simplex of `E` lies over a finite skeleton. The induced filtration
  `F^s Hⁿ(E; M)` of the abutment vanishes for `n < s`
  (`TauCeti.TopCat.isZero_serreCohomologySpectralObject_abutmentFiltration`). Over a CW complex
  `K` containing the image of `f`, on every page `r ≥ 1` with `s < r` and `t + 1 < r` the object
  at `(s, t)` is the graded piece `F^s H^{s+t} / F^{s+1} H^{s+t}`
  (`TauCeti.TopCat.serreCohomologySpectralSequencePageXIsoGraded`).
  Unlike the filtration of the singular chains, the stages of the filtration of the cochains
  need not vanish in any degree when `K` is infinite-dimensional, so the convergence uses the
  completeness of the filtration.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 5.2 and Section 5.1.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1, Section 1.2 (the cohomology spectral sequence).
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

section Defs

variable {E B : _root_.TopCat.{u}} [T2Space B]

/-- **The cohomological Serre spectral sequence** of `f : E ⟶ B` over a relative CW complex
`C ⊆ B`, with coefficients in an `R`-module `M`: the spectral sequence
`TauCeti.filteredSpaceCohomologySpectralSequence` of the filtration of the singular cochains of
`E` by the cochains vanishing on the preimages `f⁻¹(C^(s-1))` of the skeleta
(`TauCeti.preimageSkeleton`). -/
abbrev serreCohomologySpectralSequence (C : Set B) {D : Set B} [RelCWComplex C D] (f : E ⟶ B)
    (R : Type u) [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) :=
  filteredSpaceCohomologySpectralSequence (ModuleCat.of R R) k M
    (monotone_preimageSkeleton (C := C) f)

/-- **The spectral object of the cohomological Serre spectral sequence** of `f : E ⟶ B` over a
relative CW complex `C ⊆ B`, with coefficients in an `R`-module `M`. Its abutment in degree `n` is
`Hⁿ(E; M)` (`TauCeti.filteredSpaceCohomologyAbutmentIso`), filtered by the images of the relative
cohomology of the pairs `(E, f⁻¹(C^(s-1)))`; the piece `F^s` sits at index `-s`. -/
abbrev serreCohomologySpectralObject (C : Set B) {D : Set B} [RelCWComplex C D] (f : E ⟶ B)
    (R : Type u) [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) :=
  filteredSpaceCohomologySpectralObject (ModuleCat.of R R) k M
    (monotone_preimageSkeleton (C := C) f)

end Defs

variable {E B : _root_.TopCat.{u}} {f : E ⟶ B} [T2Space B] (hf : serreFibrations f)
  (R : Type u) [Ring R] (k : Type*) [Ring k] [Linear k (ModuleCat.{u} R)] (M : ModuleCat.{u} R)

section Relative

variable {C D : Set B} [RelCWComplex C D]

include hf in
variable (C) in
/-- **The skeletal filtration of a Serre fibration has no cohomology below the cell dimension**:
for the preimages `E_s = f⁻¹(C^(s))` of the skeleta, `Hⁿ(E_s, E_{s-1}; M) = 0` whenever `n < s`.
It follows from the vanishing of the relative homology with coefficients in `R`
(`TauCeti.TopCat.isZero_singularHomology_preimageSkeleton_succ`), since the relative singular
chains with coefficients in `R` are projective. -/
theorem isZero_singularCohomology_preimageSkeleton (s : ℤ) (n : ℕ) (hn : n < s) :
    IsZero ((TopPair.ofInclusion (monotone_preimageSkeleton (C := C) f (by lia : s - 1 ≤ s))
      ).singularCohomology (ModuleCat.of R R) k M n) :=
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of R R) M n
    fun m hm ↦ (TopPair.isZero_singularHomology_ofInclusion_congr _ _ _
      (by rw [sub_add_cancel]) rfl m).1
        (isZero_singularHomology_preimageSkeleton_succ hf R (s - 1) m (by lia))

include hf in
variable (C) in
/-- **The first page of the cohomological Serre spectral sequence vanishes below the `s`-axis.**
The object at `(s, t)` on the first page, `H^{s+t}(E_s, E_{s-1}; M)`, vanishes when `t < 0`. -/
theorem isZero_serreCohomologySpectralSequence_page_one_X (s t : ℤ) (ht : t < 0) :
    IsZero (((serreCohomologySpectralSequence C f R k M).page 1).X (s, t)) := by
  rcases lt_or_ge (s + t) 0 with hneg | hpos
  · exact isZero_filteredSpaceCohomologySpectralSequence_page_one_X _ _ _ _ s t hneg
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hpos
    exact (isZero_singularCohomology_preimageSkeleton hf R k M C s n (by lia)).of_iso
      (filteredSpaceCohomologySpectralSequenceFirstPageXIso _ _ _ _ s t (s - 1) s rfl rfl n hn)

include hf in
variable (C) in
/-- **The filtration of the abutment of the cohomological Serre spectral sequence vanishes above
the degree.** Let `f : E ⟶ B` be a Serre fibration with values in a relative CW complex `C ⊆ B`,
with no finiteness or dimension bound on `C`. The piece `F^s Hⁿ(E; M)` of the filtration of the
abutment, the image of `Hⁿ(E, E_{s-1}; M)`, vanishes for `n < s`. -/
theorem isZero_serreCohomologySpectralObject_abutmentFiltration (hfC : range f ⊆ C) {s n : ℤ}
    (hn : n < s) :
    IsZero ((serreCohomologySpectralObject C f R k M).abutmentFiltration (-s) n) :=
  isZero_filteredSpaceCohomologySpectralObject_abutmentFiltration (monotone_preimageSkeleton f)
    (fun _ hS ↦ exists_subset_preimageSkeleton_of_isCompact f.hom.continuous hfC hS)
    (fun s n hn ↦ isZero_singularCohomology_preimageSkeleton hf R k M C s n hn) hn

end Relative

section Absolute

variable {K : Set B} [CWComplex K]

include hf in
/-- **Strong convergence of the cohomological Serre spectral sequence over a CW complex.** Let
`f : E ⟶ B` be a Serre fibration with values in a CW complex `K ⊆ B`, with no finiteness or
dimension bound on `K`. On every page `r ≥ 1` with `s < r` and `t + 1 < r`, the object at `(s, t)`
is the graded piece `F^s H^{s+t} / F^{s+1} H^{s+t}` of the induced filtration of the abutment,
which is `H^{s+t}(E; M)` by `TauCeti.filteredSpaceCohomologyAbutmentIso`. -/
def serreCohomologySpectralSequencePageXIsoGraded (hfK : range f ⊆ K) (r : ℤ) (hr : 1 ≤ r)
    (s t : ℤ) (hs : s < r) (ht : t + 1 < r) :
    ((serreCohomologySpectralSequence K f R k M).page r).X (s, t) ≅
      cokernel ((serreCohomologySpectralObject K f R k M).abutmentFiltrationMap (-s - 1)
        (s + t)) :=
  filteredSpaceCohomologySpectralSequencePageXIsoGradedOfFirstQuadrant
    (monotone_preimageSkeleton f)
    (fun _ hS ↦ exists_subset_preimageSkeleton_of_isCompact f.hom.continuous hfK hS)
    (preimageSkeleton_eq_empty f (by lia))
    (fun s n hn ↦ isZero_singularCohomology_preimageSkeleton hf R k M K s n hn) r hr s t hs ht

end Absolute

end TopCat

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Convergence
public import TauCeti.AlgebraicTopology.Singular.Fibration.Sphere.Basic
public import TauCeti.Algebra.Homology.SpectralSequence.Degeneration

/-!
# The Serre spectral sequence of a fibration over a sphere

Let `p : E ⟶ Sⁿ` be a map to the unit sphere of `EuclideanSpace ℝ ι`, and give `Sⁿ` its CW
structure with one `0`-cell, the pole `x₀`, and one `n`-cell with centre `x₁`
(`TauCeti.TopCat.sphereRelCWComplex`). The filtration of `E` by the preimages of the skeleta has
only the two stages `p⁻¹(x₀) ⊆ E`, so its spectral sequence, the Serre spectral sequence
`TauCeti.TopCat.sphereSerreSpectralSequence` of `p`, has two columns. In the classical homological
indexing `E^r_{k,q}`, with `E¹_{k,q} = Hq+k(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹); R)`:

* the first page vanishes outside the columns `k = 0` and `k = n`
  (`TauCeti.TopCat.isZero_sphereSerreSpectralSequence_page_two_X`), and
  `E¹_{0,q} ≅ Hq(p⁻¹(x₀); R)` (`TauCeti.TopCat.sphereSerreSpectralSequenceFirstPageXIsoPole`) while,
  for a Serre fibration, `E¹_{n,q} ≅ Hq(p⁻¹(x₁); R)`
  (`TauCeti.TopCat.sphereSerreSpectralSequenceFirstPageXIsoTopCell`);
* a differential `d^r` moves `r` columns to the left
  (`TauCeti.TopCat.isZero_sphereSerreSpectralSequence_page_two_X_of_rel`), so the two columns
  survive unchanged up to `Eⁿ` (`TauCeti.TopCat.sphereSerreSpectralSequencePageXIsoFirstPageX`); in
  particular `E² = E¹` when `n ≥ 2`;
* the only differential that can be nonzero from then on is the transgression
  `dⁿ : Eⁿ_{n,q} ⟶ Eⁿ_{0,q+n-1}`, after which the spectral sequence stops: `Eⁿ⁺¹ = E^∞` is made of
  graded pieces of `H*(E; R)`, and vanishes in total degree `m` when `Hₘ(E; R) = 0`
  (`TauCeti.TopCat.isZero_sphereSerreSpectralSequence_page_X_of_isZero`);
* so `dⁿ` is injective when `Hq+n(E; R) = 0`
  (`TauCeti.TopCat.mono_sphereSerreSpectralSequence_page_d`) and surjective when
  `Hq+n-1(E; R) = 0` (`TauCeti.TopCat.epi_sphereSerreSpectralSequence_page_d`).

These are the statements of the Wang sequence of a fibration over a sphere read on the spectral
sequence. Only the identification of the column `n` uses that `p` is a Serre fibration: the shape
of the spectral sequence comes from the filtration alone.

## Indexing

The spectral sequence of a filtered space lives in Mathlib's cohomological indexing: its first page
is numbered `2`, the page numbered `r` is the classical `E^{r-1}`, and the classical position
`(k, q)` is `(a, b) = (1 - q - 2k, k - 1)`. So the columns `0` and `n` are `b = -1` and `b = n - 1`,
and the transgression `dⁿ` is the differential of the page numbered `n + 1`, from `(a, n - 1)` to
`(a + n + 1, -1)`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1 (the Serre spectral sequence and the Wang sequence of a fibration over a sphere).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 5.1.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex Metric

namespace TauCeti

namespace TopCat

variable {ι : Type u} [Fintype ι] {n : ℕ} (h : Fintype.card ι = n + 1)

variable {E : _root_.TopCat.{u}} (p : E ⟶ _root_.TopCat.of (sphere (0 : EuclideanSpace ℝ ι) 1))
  (R : Type u) [Ring R]

/-- **The Serre spectral sequence of a map to a sphere**, for the CW structure on `Sⁿ` with one
`0`-cell, the pole, and one `n`-cell (`TauCeti.TopCat.sphereRelCWComplex`). -/
abbrev sphereSerreSpectralSequence :=
  letI := sphereRelCWComplex h
  serreSpectralSequence (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) p R

/-- **The first page of the Serre spectral sequence of a map to `Sⁿ` has two columns.** The object
at `pq = (a, b)` of the first page (numbered `2`) vanishes unless `b = -1` or `b = n - 1`, the
columns `0` and `n` of the classical indexing `E¹_{k,q}` with `k = b + 1`. -/
theorem isZero_sphereSerreSpectralSequence_page_two_X (pq : ℤ × ℤ) (h₀ : pq.2 ≠ -1)
    (h₁ : pq.2 ≠ n - 1) : IsZero (((sphereSerreSpectralSequence h p R).page 2).X pq) := by
  let _ := sphereRelCWComplex h
  rcases le_or_gt pq.2 (-2) with hb | hb
  · exact isZero_serreSpectralSequence_page_two_X_of_snd_le_neg_two R _ pq hb
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hle
  · exact isZero_filteredSpaceSpectralSequence_page_two_X _ (monotone_preimageSkeleton p) pq hpos
  obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat hle
  refine IsZero.of_iso ?_ (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R)
    (monotone_preimageSkeleton p) pq pq.2 (pq.2 + 1) rfl rfl _ rfl m hm)
  -- The two stages `E_b ⊆ E_{b+1}` coincide: both are the fibre over the pole, or both are `E`.
  have heq : preimageSkeleton (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) p (pq.2 + 1) =
      preimageSkeleton (univ : Set (sphere (0 : EuclideanSpace ℝ ι) 1)) p pq.2 := by
    rcases lt_or_ge pq.2 n with hbn | hbn
    · rw [preimageSkeleton_sphereRelCWComplex_of_lt h p (by lia) (by lia),
        preimageSkeleton_sphereRelCWComplex_of_lt h p (by lia) hbn]
    · rw [preimageSkeleton_sphereRelCWComplex_of_le h p (by lia),
        preimageSkeleton_sphereRelCWComplex_of_le h p hbn]
  exact (TopPair.isZero_singularHomology_ofInclusion_congr _ _ subset_rfl heq rfl m).2
    (TopPair.isZero_singularHomology_ofInclusion_self _ _ m)

/-- **The column `0` of the first page of the Serre spectral sequence of a map to `Sⁿ`** is the
homology of the fibre over the pole: `E¹_{0,q} = Hq(p⁻¹(x₀), ∅; R) ≅ Hq(p⁻¹(x₀); R)`. -/
@[expose, simps! hom]
def sphereSerreSpectralSequenceFirstPageXIsoPole (hn : 1 ≤ n) (q : ℕ) (pq : ℤ × ℤ) (hb : pq.2 = -1)
    (ha : pq.1 + pq.2 = -(q : ℕ)) :
    ((sphereSerreSpectralSequence h p R).page 2).X pq ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {spherePolePoint h} : Set E)) :=
  letI := sphereRelCWComplex h
  haveI : IsEmpty (TopPair.ofInclusion (monotone_preimageSkeleton (C := univ) p
      (by lia : (-1 : ℤ) ≤ 0))).snd :=
    isEmpty_coe_sort.2 (preimageSkeleton_sphereRelCWComplex_of_neg h p (by lia))
  filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R) (monotone_preimageSkeleton p) pq
      (-1) 0 hb.symm (by lia) _ rfl q ha ≪≫
    (asIso ((TopPair.ofInclusion (monotone_preimageSkeleton (C := univ) p
      (by lia : (-1 : ℤ) ≤ 0))).singularHomologyπ (ModuleCat.of R R) q)).symm ≪≫
    eqToIso (singularHomologyFunctor_obj_obj_eq_toSSet_homology _ _ _).symm ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).mapIso (_root_.TopCat.isoOfHomeo (Homeomorph.setCongr
        (preimageSkeleton_sphereRelCWComplex_of_lt h p le_rfl (by lia))))

variable {p} in
/-- **The column `n` of the first page of the Serre spectral sequence of a map to `Sⁿ`** is the
homology of the fibre over the centre `x₁` of the top cell, shifted by `n`:
`E¹_{n,q} = Hq+n(E, p⁻¹(x₀); R) ≅ Hq(p⁻¹(x₁); R)`. -/
@[expose, simps! hom]
def sphereSerreSpectralSequenceFirstPageXIsoTopCell (hp : serreFibrations p) (hn : 1 ≤ n) (q : ℕ)
    (pq : ℤ × ℤ) (hb : pq.2 = n - 1) (ha : pq.1 + pq.2 = -(q + n : ℕ)) :
    ((sphereSerreSpectralSequence h p R).page 2).X pq ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {sphereTopCellCenter h} : Set E)) :=
  letI := sphereRelCWComplex h
  filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R) (monotone_preimageSkeleton p) pq
      pq.2 (pq.2 + 1) rfl rfl _ rfl (q + n) ha ≪≫
    eqToIso (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) (q + n))
      (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair (p := p) (C := univ) n pq.2 hb)) ≪≫
    TopPair.singularHomologyMapIso (ModuleCat.of R R) (spherePreimageSkeletonPairIso h hn)
      (q + n) ≪≫
    sphereFibrationSingularHomologyIso h hp R hn q

/-- Before the page `n + 1`, every position joined to a position `pq` in the column `0` or `n` by
a differential of the Serre spectral sequence of a map to `Sⁿ` lies in an empty column of the first
page. -/
theorem isZero_sphereSerreSpectralSequence_page_two_X_of_rel (r : ℤ) (hrn : r ≤ n + 1)
    (pq : ℤ × ℤ) (hb : pq.2 = -1 ∨ pq.2 = n - 1) (s : ℤ) (hs : 2 ≤ s) (hsr : s < r) (pq' : ℤ × ℤ)
    (hpq' : (ComplexShape.up' ((s, 1 - s) : ℤ × ℤ)).Rel pq pq' ∨
      (ComplexShape.up' ((s, 1 - s) : ℤ × ℤ)).Rel pq' pq) :
    IsZero (((sphereSerreSpectralSequence h p R).page 2).X pq') := by
  have := ComplexShape.snd_eq_of_up'_rel hpq'
  exact isZero_sphereSerreSpectralSequence_page_two_X h p R pq' (by lia) (by lia)

/-- **The objects of the two columns survive to the page `n + 1`.** For `2 ≤ r ≤ n + 1`, the
object at a position `pq` in the column `0` or `n` of the page `r` of the Serre spectral sequence of
a map to `Sⁿ` is the object of the first page: the differentials of the pages before `n + 1` join
the two columns to the empty columns strictly between them or outside them. -/
def sphereSerreSpectralSequencePageXIsoFirstPageX (r : ℤ) (hr : 2 ≤ r)
    (hrn : r ≤ n + 1) (pq : ℤ × ℤ) (hb : pq.2 = -1 ∨ pq.2 = n - 1) :
    ((sphereSerreSpectralSequence h p R).page r).X pq ≅
      ((sphereSerreSpectralSequence h p R).page 2).X pq :=
  (sphereSerreSpectralSequence h p R).pageXIsoOfLEOfIsZeroOfLT le_rfl r hr
    (isZero_sphereSerreSpectralSequence_page_two_X_of_rel h p R r hrn pq hb)

/-- `TauCeti.TopCat.sphereSerreSpectralSequencePageXIsoFirstPageX` is the survival isomorphism
`CategoryTheory.SpectralSequence.pageXIsoOfLEOfIsZeroOfLT` from the first page. -/
@[simp]
theorem sphereSerreSpectralSequencePageXIsoFirstPageX_hom (r : ℤ) (hr : 2 ≤ r)
    (hrn : r ≤ n + 1) (pq : ℤ × ℤ) (hb : pq.2 = -1 ∨ pq.2 = n - 1) :
    (sphereSerreSpectralSequencePageXIsoFirstPageX h p R r hr hrn pq hb).hom =
      ((sphereSerreSpectralSequence h p R).pageXIsoOfLEOfIsZeroOfLT le_rfl r hr
        (isZero_sphereSerreSpectralSequence_page_two_X_of_rel h p R r hrn pq hb)).hom :=
  (rfl)

/-- **The page `n + 2` of the Serre spectral sequence of a map to `Sⁿ` is its last.** From the page
`n + 2` on, every differential at a position `pq` in the column `0` or `n` joins it to an empty
column, so the object at `pq` is the same on every later page. In particular it is the graded piece
of the abutment, and it vanishes when the homology `Hₘ(E; R)` of its total degree does. -/
theorem isZero_sphereSerreSpectralSequence_page_X_of_isZero (pq : ℤ × ℤ)
    (hb : pq.2 = -1 ∨ pq.2 = n - 1) {m : ℕ} (hm : pq.1 + pq.2 = -m)
    (hE : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
      (ModuleCat.of R R)).obj E)) :
    IsZero (((sphereSerreSpectralSequence h p R).page (n + 2)).X pq) := by
  let _ := sphereRelCWComplex h
  let S := sphereSerreSpectralSequence h p R
  -- From the page `n + 2` on, the object at `pq` survives unchanged to the page `n + 3 + m`.
  have hsurvive := S.pageXIsoOfLEOfIsZero (r := n + 2) (by lia) (pq := pq) (fun s hs pq' hpq' ↦ by
    have := ComplexShape.snd_eq_of_up'_rel hpq'
    exact S.isZero_page_X_of_le le_rfl
      (isZero_sphereSerreSpectralSequence_page_two_X h p R pq' (by lia) (by lia)) _ (by lia))
    (n + 3 + m) (by lia)
  refine IsZero.of_iso ?_ hsurvive.symm
  have hpq : 0 ≤ pq.2 + 1 := by rcases hb with hb | hb <;> lia
  -- On that page it is a graded piece of the filtration of `Hₘ(E; R)`, which vanishes.
  have e := filteredSpaceSpectralSequencePageXIsoGradedOfExhaustive
    (ModuleCat.of R R) (monotone_preimageSkeleton (C := univ) p)
    (fun _ hK ↦ exists_subset_preimageSkeleton_of_isCompact p.hom.continuous (subset_univ _) hK)
    (preimageSkeleton_sphereRelCWComplex_of_neg h p (by lia : (-1 : ℤ) < 0)) (n + 3 + m) (by lia)
    pq (by lia) fun i hi k _ ↦ by
      -- The stages `E_i ⊆ E_{i+1}` of the filtration are both `E` for `i ≥ n`.
      rw [TopPair.isZero_singularHomology_ofInclusion_congr _ _ subset_rfl
        (preimageSkeleton_sphereRelCWComplex_of_le h p (by lia))
        (preimageSkeleton_sphereRelCWComplex_of_le h p (by lia)) k]
      exact TopPair.isZero_singularHomology_ofInclusion_self _ _ k
  refine IsZero.of_iso (IsZero.of_epi (cokernel.π _) (IsZero.of_mono
    ((filteredSpaceSpectralObject (ModuleCat.of R R)
      (monotone_preimageSkeleton (C := univ) p)).abutmentFiltrationι _ _) ?_)) e
  rw [hm]
  exact hE.of_iso (chainFiltrationAbutmentIso _ (monotone_preimageSkeleton (C := univ) p) m)

/-- On the page `n + 1` of the Serre spectral sequence of a map to `Sⁿ`, the homology at a
position `j` in the column `0` or `n` vanishes when the homology `Hₘ(E; R)` of its total degree
does, since it is the object at `j` of the page `n + 2`. -/
private lemma exact_sphereSerreSpectralSequence_page_sc' (hn : 1 ≤ n) (i j k : ℤ × ℤ)
    (hij : i + ((n + 1 : ℤ), -(n : ℤ)) = j) (hjk : j + ((n + 1 : ℤ), -(n : ℤ)) = k)
    (hb : j.2 = -1 ∨ j.2 = n - 1) {m : ℕ} (hm : j.1 + j.2 = -m)
    (hE : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
      (ModuleCat.of R R)).obj E)) :
    (((sphereSerreSpectralSequence h p R).page (n + 1) (by lia)).sc' i j k).Exact := by
  let S := sphereSerreSpectralSequence h p R
  have hij' : (ComplexShape.up' (((n + 1 : ℤ), 1 - (n + 1 : ℤ)) : ℤ × ℤ)).Rel i j := by
    rw [← hij]; ext <;> simp
  have hjk' : (ComplexShape.up' (((n + 1 : ℤ), 1 - (n + 1 : ℤ)) : ℤ × ℤ)).Rel j k := by
    rw [← hjk]; ext <;> simp
  exact ((S.page (n + 1) (by lia)).exactAt_iff' i j k (ComplexShape.prev_eq' _ hij')
    (ComplexShape.next_eq' _ hjk')).1
      (((S.page (n + 1) (by lia)).exactAt_iff_isZero_homology j).2
      ((isZero_sphereSerreSpectralSequence_page_X_of_isZero h p R j hb hm hE).of_iso
        (S.iso (n + 1) (n + 2) j (by lia) (by lia))))

/-- **The transgression `dⁿ` of a fibration over `Sⁿ` is injective when the total space has no
homology in its degree.** The only differential of the Serre spectral sequence of a map to `Sⁿ`
that can be nonzero goes from the column `n` to the column `0` on the page `n + 1` (classically
`dⁿ : Eⁿ_{n,q} ⟶ Eⁿ_{0,q+n-1}`). Its kernel is the object at its source on the page `n + 2`, a
graded piece of `Hq+n(E; R)`, so it is a monomorphism when `Hq+n(E; R) = 0`. -/
theorem mono_sphereSerreSpectralSequence_page_d (hn : 1 ≤ n) (r : ℤ) (hr : r = n + 1)
    (pq pq' : ℤ × ℤ) (hb : pq.2 = n - 1)
    (hpq' : pq + ((n + 1 : ℤ), -(n : ℤ)) = pq') {m : ℕ} (hm : pq.1 + pq.2 = -m)
    (hE : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
      (ModuleCat.of R R)).obj E)) :
    Mono (((sphereSerreSpectralSequence h p R).page r (by lia)).d pq pq') := by
  subst hr
  -- The incoming differential starts in the empty column `2n`.
  refine (exact_sphereSerreSpectralSequence_page_sc' h p R hn _ pq pq' (sub_add_cancel _ _) hpq'
    (Or.inr hb) hm hE).mono_g (((sphereSerreSpectralSequence h p R).isZero_page_X_of_le le_rfl
      (isZero_sphereSerreSpectralSequence_page_two_X h p R _ ?_ ?_) (n + 1) (by lia)).eq_of_src _ _)
  · simp only [Prod.snd_sub]; lia
  · simp only [Prod.snd_sub]; lia

/-- **The transgression `dⁿ` of a fibration over `Sⁿ` is surjective when the total space has no
homology in the degree of its target.** The differential `dⁿ : Eⁿ_{n,q} ⟶ Eⁿ_{0,q+n-1}` of the page
`n + 1` of the Serre spectral sequence of a map to `Sⁿ` has as cokernel the object at its target on
the page `n + 2`, a graded piece of `Hq+n-1(E; R)`, so it is an epimorphism when
`Hq+n-1(E; R) = 0`. -/
theorem epi_sphereSerreSpectralSequence_page_d (hn : 1 ≤ n) (r : ℤ) (hr : r = n + 1)
    (pq pq' : ℤ × ℤ) (hb : pq.2 = n - 1)
    (hpq' : pq + ((n + 1 : ℤ), -(n : ℤ)) = pq') {m : ℕ} (hm : pq'.1 + pq'.2 = -m)
    (hE : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) m).obj
      (ModuleCat.of R R)).obj E)) :
    Epi (((sphereSerreSpectralSequence h p R).page r (by lia)).d pq pq') := by
  subst hr
  let _ := sphereRelCWComplex h
  have hb' : pq'.2 = -1 := by rw [← hpq', Prod.snd_add]; lia
  -- The outgoing differential ends below the column `0`.
  refine (exact_sphereSerreSpectralSequence_page_sc' h p R hn pq pq' _ hpq' rfl (Or.inl hb') hm
    hE).epi_f (((sphereSerreSpectralSequence h p R).isZero_page_X_of_le le_rfl
      (isZero_serreSpectralSequence_page_two_X_of_snd_le_neg_two R _ _ ?_) (n + 1)
        (by lia)).eq_of_tgt _ _)
  rw [Prod.snd_add]
  lia

end TopCat

end TauCeti

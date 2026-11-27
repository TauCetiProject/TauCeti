/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Comparison
public import TauCeti.Algebra.Homology.SpectralSequence.Degeneration
public import TauCeti.AlgebraicTopology.Cohomology.Fibration.Naturality
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.AlgebraicTopology.Singular.Fibration.Cohomology

/-!
# The base row of the second page of the cohomological Serre spectral sequence

Let `p : E ⟶ B` be a Serre fibration over a CW complex `B` whose fibres are path connected, and let
`M` be a module over a ring `R`. In the classical cohomological indexing, the cohomological Serre
spectral sequence of `p` has `E₂^{s,t} = H^s(B; H^t(F; M))`. This file proves the row `t = 0`,
where the coefficients `H⁰(F; M) = M` are constant: `E₂^{s,0} ≅ H^s(B; M)`
(`TauCeti.TopCat.serreCohomologySpectralSequenceSecondPageXIsoSingularCohomology`).

The projection `p` maps the preimages `p⁻¹(Xˢ)` of the skeleta of `B` to the skeleta themselves, so
pulling back cochains along it induces a morphism from the cohomological Serre spectral sequence of
the identity of `B`, the spectral sequence of the skeletal filtration of `B`, to that of `p`
(`TauCeti.TopCat.serreCohomologySpectralSequenceProj`, the morphism
`TauCeti.TopCat.serreCohomologySpectralSequenceMapOver` of `p` as a map over `B`).

* On the row `t = 0` of the first page this morphism is the map
  `H^s(Xˢ, Xˢ⁻¹; M) ⟶ H^s(p⁻¹(Xˢ), p⁻¹(Xˢ⁻¹); M)`. Cell by cell it is the map `H⁰(pt; M) ⟶ H⁰(F; M)`
  of the fibres over the centres of the `s`-cells, an isomorphism since the fibres are path
  connected (`TauCeti.TopCat.isIso_serreCohomologySpectralSequenceProj_hom_one_f`).
* The differentials of the first page preserve the row, so the morphism is an isomorphism on the
  row `t = 0` of the second page as well
  (`TauCeti.TopCat.isIso_serreCohomologySpectralSequenceProj_hom_two_f`).
* The first page of the spectral sequence of the skeletal filtration of `B` is concentrated on the
  row `t = 0`, because the fibres of the identity are points
  (`TauCeti.TopCat.isZero_serreCohomologySpectralSequence_id_page_one_X`). It therefore
  degenerates, and its row `t = 0` is the cohomology of `B`
  (`TauCeti.TopCat.serreCohomologySpectralSequenceIdSecondPageXIsoSingularCohomology`): in degree
  `s` the filtration of `H^s(B; M)` jumps only at `s`.

The identification on the second page of `p` is therefore the inverse of the projection, followed
by that of the identity of `B`
(`TauCeti.TopCat.serreCohomologySpectralSequenceSecondPageXIsoSingularCohomology_inv`): its inverse
is the edge map `H^s(B; M) ⟶ E₂^{s,0}` that pulls classes of the base back along `p`.

The degree-zero input is that a map of path-connected spaces induces an isomorphism on `H⁰` with
any coefficients (`TopCat.isIso_singularCohomologyMap_zero_of_pathConnectedSpace`).

This is the cohomological counterpart of
`TauCeti.TopCat.serreSpectralSequenceSecondPageXIsoSingularHomology`
(`TauCeti.AlgebraicTopology.Singular.Fibration.BaseRow`). The spectral sequences are indexed as in
`TauCeti.filteredSpaceCohomologySpectralSequence`: the first page is the page numbered `1`, and the
classical position `(s, t)` is the position `(s, t)`.

## Main definitions

* `TauCeti.TopCat.serreCohomologySpectralSequenceProj`: the morphism from the cohomological Serre
  spectral sequence of the identity of the base to that of `p`.
* `TauCeti.TopCat.serreCohomologySpectralSequenceIdSecondPageXIsoSingularCohomology`:
  `E₂^{s,0} ≅ H^s(B; M)` for the skeletal filtration of a CW complex `B`.
* `TauCeti.TopCat.serreCohomologySpectralSequenceSecondPageXIsoSingularCohomology`:
  `E₂^{s,0} ≅ H^s(B; M)` for a Serre fibration with path-connected fibres over a CW complex.

## Main results

* `TauCeti.TopCat.isIso_serreCohomologySpectralSequenceProj_hom_two_f`: the projection is an
  isomorphism on the row `t = 0` of the second page.
* `TauCeti.TopCat.isZero_serreCohomologySpectralSequence_id_page_one_X`: the first page of the
  skeletal filtration is concentrated on the row `t = 0`.

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

variable {E B : _root_.TopCat.{u}} (p : E ⟶ B) [T2Space B] (R : Type u) [Ring R] (k : Type*)
  [Ring k] [Linear k (ModuleCat.{u} R)] (M : ModuleCat.{u} R)

section Proj

variable (C : Set B) {D : Set B} [RelCWComplex C D]

/-- **The projection of the cohomological Serre spectral sequence onto the base.** The morphism
from the cohomological Serre spectral sequence of the identity of `B` over a relative CW complex
`C`, the spectral sequence of the skeletal filtration of `C`, to that of `p`, induced by pulling
back cochains along `p`: the morphism `TauCeti.TopCat.serreCohomologySpectralSequenceMapOver` of
the map `p` over `B` into the identity of `B`. -/
def serreCohomologySpectralSequenceProj :
    serreCohomologySpectralSequence C (𝟙 B) R k M ⟶ serreCohomologySpectralSequence C p R k M :=
  serreCohomologySpectralSequenceMapOver C R k M (Category.comp_id p)

/-- The projection of the cohomological Serre spectral sequence onto the base is the morphism
induced by `p` as a map over `B`. -/
lemma serreCohomologySpectralSequenceProj_def :
    serreCohomologySpectralSequenceProj p R k M C =
      serreCohomologySpectralSequenceMapOver C R k M (Category.comp_id p) :=
  (rfl)

end Proj

/-- The fibre of the identity of `B` over a point is a point. -/
private abbrev uniqueFiberId (b : B) : Unique ((𝟙 B : B ⟶ B).fiber b) :=
  ⟨⟨⟨b, rfl⟩⟩, fun x ↦ Subtype.ext x.property⟩

/-! ### The row `t = 0` of the first and second pages -/

section Row

variable {C D : Set B} [RelCWComplex C D] {p}

/-- On the row `t = 0` of the first page, the projection of the cohomological Serre spectral
sequence of a fibration with path-connected fibres onto the base is an isomorphism: the map
`H^s(Xˢ, Xˢ⁻¹; M) ⟶ H^s(p⁻¹(Xˢ), p⁻¹(Xˢ⁻¹); M)` is, cell by cell, the map `H⁰(pt; M) ⟶ H⁰(F; M)`
of the fibres over the centres of the `s`-cells. -/
theorem isIso_serreCohomologySpectralSequenceProj_hom_one_f (hp : serreFibrations p)
    (hconn : ∀ b ∈ C, PathConnectedSpace (p.fiber b)) (st : ℤ × ℤ) (ht : st.2 = 0) :
    IsIso (((serreCohomologySpectralSequenceProj p R k M C).hom 1 le_rfl).f st) := by
  obtain ⟨s, t⟩ := st
  obtain rfl : t = 0 := ht
  rcases lt_or_ge s 0 with hs | hs
  · exact (isZero_filteredSpaceCohomologySpectralSequence_page_one_X _ _ _ _ s 0 (by lia)).isIso
      (isZero_filteredSpaceCohomologySpectralSequence_page_one_X _ _ _ _ s 0 (by lia)) _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n := ⟨s.toNat, by lia⟩
  -- Through the identifications with the products over the cells, the projection is the product
  -- of the maps induced on `H⁰` by the maps of fibres over the centres of the cells.
  have e := serreCohomologySpectralSequenceFirstPageXIsoPi_hom_naturality (C := C) hp
    (MorphismProperty.id_mem _ B) R k M (Category.comp_id p) n 0 n 0 rfl (by push_cast; ring)
  rw [← Iso.eq_comp_inv] at e
  rw [serreCohomologySpectralSequenceProj_def, e]
  have (j : cell C n) : IsIso (TopCat.singularCohomologyMap (R := ModuleCat.of R R) (k := k)
      (M := M) (p.preimageMap (Category.comp_id p) {map n j 0}) 0) :=
    have := hconn _ (closedCell_subset_complex n j ⟨0, Metric.mem_closedBall_self zero_le_one,
      rfl⟩)
    have := uniqueFiberId (map n j 0)
    TopCat.isIso_singularCohomologyMap_zero_of_pathConnectedSpace _ k
  infer_instance

/-- **The projection is an isomorphism on the row `t = 0` of the second page.** For a Serre
fibration with path-connected fibres, the morphism from the cohomological Serre spectral sequence
of the identity of the base to that of the fibration is an isomorphism on `E₂^{s,0}`: on the first
page it is one on the row `t = 0`, which the differentials of that page preserve. -/
theorem isIso_serreCohomologySpectralSequenceProj_hom_two_f (hp : serreFibrations p)
    (hconn : ∀ b ∈ C, PathConnectedSpace (p.fiber b)) (st : ℤ × ℤ) (ht : st.2 = 0) :
    IsIso (((serreCohomologySpectralSequenceProj p R k M C).hom 2).f st) :=
  (serreCohomologySpectralSequenceProj p R k M C).isIso_hom_f_add_one 1 le_rfl st fun st' hst' ↦
    isIso_serreCohomologySpectralSequenceProj_hom_one_f R k M hp hconn st' (by
      rcases hst' with rfl | h
      · exact ht
      · rcases ComplexShape.snd_eq_of_up'_rel h with h | h <;> lia)

end Row

/-! ### The spectral sequence of the skeletal filtration of the base -/

section Base

/-- **The first page of the skeletal filtration is concentrated on the row `t = 0`.** For a
relative CW complex `C ⊆ B`, the object at `(s, t)` of the first page of the cohomological Serre
spectral sequence of the identity of `B` vanishes unless `t = 0`: it is the product, over the
`s`-cells, of the cohomology `H^t(pt; M)` of the fibres of the identity. -/
theorem isZero_serreCohomologySpectralSequence_id_page_one_X {C D : Set B} [RelCWComplex C D]
    (st : ℤ × ℤ) (ht : st.2 ≠ 0) :
    IsZero (((serreCohomologySpectralSequence C (𝟙 B) R k M).page 1).X st) := by
  obtain ⟨s, t⟩ := st
  rcases lt_or_gt_of_ne ht with ht | ht
  · exact isZero_serreCohomologySpectralSequence_page_one_X (MorphismProperty.id_mem _ B) R k M C
      s t ht
  rcases lt_or_ge (s + t) 0 with hst | hst
  · exact isZero_filteredSpaceCohomologySpectralSequence_page_one_X _ _ _ _ s t hst
  rcases lt_or_ge s 0 with hs | hs
  · -- Below the base both stages of the filtration are `D`, so the pair has no cohomology.
    refine IsZero.of_iso ?_ (filteredSpaceCohomologySpectralSequenceFirstPageXIso _ _ _
      (monotone_preimageSkeleton (C := C) (𝟙 B)) s t (s - 1) s rfl rfl (s + t).toNat (by lia))
    exact TopPair.isZero_singularCohomology_of_surjective_map _ _ _ _ (fun y ↦ by
      refine ⟨⟨y.val, ?_⟩, rfl⟩
      rw [preimageSkeleton_of_neg (C := C) (𝟙 B) (by lia : s - 1 < 0),
        ← preimageSkeleton_of_neg (C := C) (𝟙 B) hs]
      exact y.property) _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n := ⟨s.toNat, by lia⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, t = q := ⟨t.toNat, by lia⟩
  refine IsZero.of_iso ?_ (serreCohomologySpectralSequenceFirstPageXIsoPi C
    (MorphismProperty.id_mem _ B) R k M n q n q rfl (by push_cast; ring))
  refine (IsZero.iff_id_eq_zero _).2 (Pi.hom_ext _ _ fun j ↦ ?_)
  have := uniqueFiberId (map n j 0)
  exact (isZero_singularCohomology_point _ k M _ (by lia)).eq_of_tgt _ _

/-- From the second page on, the differentials at a position on the row `t = 0` of the spectral
sequence of the skeletal filtration leave that row, so their other ends vanish already on the
second page. -/
lemma isZero_serreCohomologySpectralSequence_id_page_two_X_of_rel {C D : Set B}
    [RelCWComplex C D] {st : ℤ × ℤ} (ht : st.2 = 0) (r : ℤ) (hr : 2 ≤ r) (st' : ℤ × ℤ)
    (hst' : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel st st' ∨
      (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel st' st) :
    IsZero (((serreCohomologySpectralSequence C (𝟙 B) R k M).page 2).X st') :=
  (serreCohomologySpectralSequence C (𝟙 B) R k M).isZero_page_X_of_le (r := 1) le_rfl
    (isZero_serreCohomologySpectralSequence_id_page_one_X R k M st' (by
      rcases ComplexShape.snd_eq_of_up'_rel hst' with h | h <;> lia)) 2 (by norm_num)

variable [CWComplex (univ : Set B)]

/-- **The filtration of `H^s(B; M)` by the skeleta starts at `s`.** Over a CW complex `B`, every
piece `F^j H^s(B; M)` of the filtration of the abutment of the spectral sequence of the skeletal
filtration with `j ≤ s`, the image of the cohomology of `B` relative to its `(j - 1)`-skeleton, is
all of `H^s(B; M)`; the piece `F^j` sits at the index `a = -j`. Its graded pieces above `s` are the
objects of the limit page on rows `t > 0`, which vanish. -/
private lemma isIso_serreCohomologySpectralObject_id_abutmentFiltrationι (s : ℕ) {a : ℤ}
    (ha : -(s : ℤ) ≤ a) :
    IsIso ((serreCohomologySpectralObject univ (𝟙 B) R k M).abutmentFiltrationι a s) := by
  -- The pieces `F^j` with `j ≤ 0` are everything: the cochains vanishing on the empty set.
  have htop (b : ℤ) (hb : 0 ≤ b) :
      IsIso ((serreCohomologySpectralObject univ (𝟙 B) R k M).abutmentFiltrationι b s) :=
    CochainComplex.isIso_filtrationAbutmentFiltrationι _ _ (b := b) (by
      exact singularCochainFiltration_eq_top _ _ _
        (preimageSkeleton_eq_empty (C := (univ : Set B)) (𝟙 B) (by lia : -b - 1 < 0))) _
  rcases le_or_gt 0 a with h | h
  · exact htop a h
  refine (serreCohomologySpectralObject univ (𝟙 B) R k M).isIso_abutmentFiltrationι_of_isZero_EInfty
    h.le (htop 0 le_rfl) fun j hj₁ hj₂ ↦ ?_
  -- The graded piece `F^i / F^{i+1}` with `j = -i - 1` is the object at `(i, s - i)` of a late
  -- page, on the row `t = s - i > 0`, where already the first page vanishes.
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, j = -(i : ℤ) - 1 := ⟨(-j - 1).toNat, by lia⟩
  have e := serreCohomologySpectralSequencePageXIsoGraded (MorphismProperty.id_mem _ B) R k M
    (K := univ) (subset_univ _) (s + 3) (by lia) i (s - i) (by lia) (by lia)
  rw [show (i : ℤ) + ((s : ℤ) - i) = s by ring] at e
  exact ((serreCohomologySpectralSequence univ (𝟙 B) R k M).isZero_page_X_of_le le_rfl
    (isZero_serreCohomologySpectralSequence_id_page_one_X R k M _ (by dsimp; lia)) (s + 3)
      (by lia)).of_iso e.symm |>.of_iso
    ((serreCohomologySpectralObject univ (𝟙 B) R k M).EInftyIsoCokernel _ _)

/-- The graded piece `F^s H^s / F^{s+1} H^s` of the filtration of `H^s(B; M)` by the skeleta is all
of `H^s(B; M)`. The piece `F^s` sits at the index `-s` and `F^{s+1}` at `a = -s - 1`. -/
def cokernelSerreCohomologySpectralObjectIdAbutmentFiltrationMapIso (s : ℕ) (a n : ℤ)
    (ha : a = -s - 1) (hn : n = s) :
    cokernel ((serreCohomologySpectralObject univ (𝟙 B) R k M).abutmentFiltrationMap a n) ≅
      B.singularCohomology (ModuleCat.of R R) k M s := by
  subst ha hn
  -- The piece `F^{s+1} H^s` vanishes, since the filtration vanishes above the degree.
  have hz : IsZero ((serreCohomologySpectralObject univ (𝟙 B) R k M).abutmentFiltration
      (-(s : ℤ) - 1) s) := by
    simpa only [neg_add'] using isZero_serreCohomologySpectralObject_abutmentFiltration
      (MorphismProperty.id_mem _ B) R k M (univ : Set B) (subset_univ _) (s := (s : ℤ) + 1)
      (n := s) (by lia)
  have := cokernel.π_of_zero (hz.eq_of_src
    ((serreCohomologySpectralObject univ (𝟙 B) R k M).abutmentFiltrationMap (-(s : ℤ) - 1) s) 0)
  have := isIso_serreCohomologySpectralObject_id_abutmentFiltrationι (B := B) R k M s
    (a := -(s : ℤ) - 1 + 1) (by lia)
  exact (asIso (cokernel.π _)).symm ≪≫
    asIso ((serreCohomologySpectralObject univ (𝟙 B) R k M).abutmentFiltrationι _ _) ≪≫
    filteredSpaceCohomologyAbutmentIso (ModuleCat.of R R) k M (monotone_preimageSkeleton (𝟙 B)) s

/-- The identification of the graded piece `F^s H^s / F^{s+1} H^s` with `H^s(B; M)` is induced by
the inclusion of `F^s H^s` into the abutment, followed by the identification of the abutment with
`H^s(B; M)`. -/
@[reassoc (attr := simp)]
lemma π_cokernelSerreCohomologySpectralObjectIdAbutmentFiltrationMapIso_hom (s : ℕ) (a n : ℤ)
    (ha : a = -s - 1) (hn : n = s) :
    cokernel.π _ ≫
        (cokernelSerreCohomologySpectralObjectIdAbutmentFiltrationMapIso R k M s a n ha hn).hom =
      (serreCohomologySpectralObject univ (𝟙 B) R k M).abutmentFiltrationι (a + 1) n ≫
        eqToHom (congrArg (serreCohomologySpectralObject univ (𝟙 B) R k M).abutment hn) ≫
        (filteredSpaceCohomologyAbutmentIso (ModuleCat.of R R) k M
          (monotone_preimageSkeleton (𝟙 B)) s).hom := by
  subst ha hn
  simp only [cokernelSerreCohomologySpectralObjectIdAbutmentFiltrationMapIso, Iso.trans_hom,
    Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc, eqToHom_refl, Category.id_comp]
  rfl

/-- **The row `t = 0` of the second page of the skeletal filtration.** For a CW complex `B`, the
object `E₂^{s,0}` of the cohomological Serre spectral sequence of the identity of `B` is
`H^s(B; M)`. The first page is concentrated on the row `t = 0`, so this object survives to the
limit page, where it is the graded piece `F^s H^s / F^{s+1} H^s = H^s(B; M)` of the filtration of
the abutment. -/
def serreCohomologySpectralSequenceIdSecondPageXIsoSingularCohomology (s : ℕ) (st : ℤ × ℤ)
    (hs : st.1 = s) (ht : st.2 = 0) :
    ((serreCohomologySpectralSequence univ (𝟙 B) R k M).page 2).X st ≅
      B.singularCohomology (ModuleCat.of R R) k M s :=
  ((serreCohomologySpectralSequence univ (𝟙 B) R k M).pageXIsoOfLEOfIsZero (r := 2) (by norm_num)
      (isZero_serreCohomologySpectralSequence_id_page_two_X_of_rel R k M ht) (s + 3)
        (by lia)).symm ≪≫
    serreCohomologySpectralSequencePageXIsoGraded (MorphismProperty.id_mem _ B) R k M (K := univ)
      (subset_univ _) (s + 3) (by lia) st.1 st.2 (by lia) (by lia) ≪≫
    cokernelSerreCohomologySpectralObjectIdAbutmentFiltrationMapIso R k M s _ _ (by lia) (by lia)

/-- The identification of the row `t = 0` of the second page of the skeletal filtration with
`H^s(B; M)` is the passage to a late page, where the object is the graded piece
`F^s H^s / F^{s+1} H^s` of the filtration of the abutment, followed by the identification of that
graded piece with `H^s(B; M)`
(`TauCeti.TopCat.π_cokernelSerreCohomologySpectralObjectIdAbutmentFiltrationMapIso_hom`). -/
lemma serreCohomologySpectralSequenceIdSecondPageXIsoSingularCohomology_hom (s : ℕ) (st : ℤ × ℤ)
    (hs : st.1 = s) (ht : st.2 = 0) :
    (serreCohomologySpectralSequenceIdSecondPageXIsoSingularCohomology R k M s st hs ht).hom =
      ((serreCohomologySpectralSequence univ (𝟙 B) R k M).pageXIsoOfLEOfIsZero (r := 2)
          (by norm_num) (isZero_serreCohomologySpectralSequence_id_page_two_X_of_rel R k M ht)
          (s + 3) (by lia)).inv ≫
        (serreCohomologySpectralSequencePageXIsoGraded (MorphismProperty.id_mem _ B) R k M
          (K := univ) (subset_univ _) (s + 3) (by lia) st.1 st.2 (by lia) (by lia)).hom ≫
        (cokernelSerreCohomologySpectralObjectIdAbutmentFiltrationMapIso R k M s _ _ (by lia)
          (by lia)).hom :=
  (rfl)

end Base

/-! ### The row `t = 0` of the second page -/

variable [CWComplex (univ : Set B)] {p}

/-- **The row `t = 0` of the second page of the cohomological Serre spectral sequence.** Let
`p : E ⟶ B` be a Serre fibration with path-connected fibres over a CW complex `B`, and `M` a module
over `R`. Then `E₂^{s,0} ≅ H^s(B; M)`: the object at `(s, 0)` of the second page of the
cohomological Serre spectral sequence of `p` is the singular cohomology of the base. It is the
inverse of the projection from the spectral sequence of the skeletal filtration of `B`
(`TauCeti.TopCat.isIso_serreCohomologySpectralSequenceProj_hom_two_f`), followed by the
identification of the latter's row `t = 0`
(`TauCeti.TopCat.serreCohomologySpectralSequenceIdSecondPageXIsoSingularCohomology`). -/
def serreCohomologySpectralSequenceSecondPageXIsoSingularCohomology (hp : serreFibrations p)
    (hconn : ∀ b, PathConnectedSpace (p.fiber b)) (s : ℕ) (st : ℤ × ℤ) (hs : st.1 = s)
    (ht : st.2 = 0) :
    ((serreCohomologySpectralSequence univ p R k M).page 2).X st ≅
      B.singularCohomology (ModuleCat.of R R) k M s :=
  have : IsIso (((serreCohomologySpectralSequenceProj p R k M univ).hom 2).f st) :=
    isIso_serreCohomologySpectralSequenceProj_hom_two_f R k M hp (fun b _ ↦ hconn b) st ht
  (@asIso _ _ _ _ _ this).symm ≪≫
    serreCohomologySpectralSequenceIdSecondPageXIsoSingularCohomology R k M s st hs ht

/-- The inverse of the identification `E₂^{s,0} ≅ H^s(B; M)` is the edge map: the identification
of `H^s(B; M)` with the row `t = 0` of the second page of the skeletal filtration of `B`, followed
by the projection, which pulls back along `p`. -/
lemma serreCohomologySpectralSequenceSecondPageXIsoSingularCohomology_inv
    (hp : serreFibrations p) (hconn : ∀ b, PathConnectedSpace (p.fiber b)) (s : ℕ) (st : ℤ × ℤ)
    (hs : st.1 = s) (ht : st.2 = 0) :
    (serreCohomologySpectralSequenceSecondPageXIsoSingularCohomology R k M hp hconn s st hs
        ht).inv =
      (serreCohomologySpectralSequenceIdSecondPageXIsoSingularCohomology R k M s st hs ht).inv ≫
        ((serreCohomologySpectralSequenceProj p R k M univ).hom 2).f st :=
  (rfl)

end TopCat

end TauCeti

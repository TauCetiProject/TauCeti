/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Comparison
public import TauCeti.Algebra.Homology.SpectralSequence.Degeneration
public import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
public import TauCeti.AlgebraicTopology.Singular.Fibration.FirstPage
import TauCeti.AlgebraicTopology.Singular.Reduced
import TauCeti.CategoryTheory.ObjectProperty.ColimitsOfShape

/-!
# The base row of the second page of the Serre spectral sequence

Let `p : E ⟶ B` be a Serre fibration over a CW complex `B` whose fibres are path connected. In the
classical homological indexing, the Serre spectral sequence of `p` has `E²_{k,q} = H_k(B; H_q(F))`.
This file proves the row `q = 0`, where the coefficients `H₀(F; R) = R` are constant:
`E²_{k,0} ≅ H_k(B; R)` (`TauCeti.TopCat.serreSpectralSequenceSecondPageXIsoSingularHomology`).

The projection `p` maps the preimages `p⁻¹(Xᵏ)` of the skeleta of `B` to the skeleta themselves, so
it induces a morphism from the Serre spectral sequence of `p` to that of the identity of `B`, the
spectral sequence of the skeletal filtration of `B`
(`TauCeti.TopCat.serreSpectralSequenceProj`).

* On the row `q = 0` of the first page this morphism is the map
  `H_k(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹)) ⟶ H_k(Xᵏ, Xᵏ⁻¹)`. Cell by cell it is the map `H₀(F) ⟶ H₀(pt)` of the
  fibres over the centres of the `k`-cells, an isomorphism since the fibres are path connected
  (`TauCeti.TopCat.isIso_serreSpectralSequenceProj_hom_two_f`).
* The differentials of the first page preserve the row, so the morphism is an isomorphism on the
  row `q = 0` of the second page as well
  (`TauCeti.TopCat.isIso_serreSpectralSequenceProj_hom_three_f`).
* The first page of the spectral sequence of the skeletal filtration of `B` is concentrated on the
  row `q = 0`, because `H_n(Xᵏ, Xᵏ⁻¹) = 0` for `n ≠ k`
  (`TauCeti.TopCat.isZero_serreSpectralSequence_id_page_two_X`). It therefore degenerates, and
  its row `q = 0` is the homology of `B`
  (`TauCeti.TopCat.serreSpectralSequenceIdSecondPageXIsoSingularHomology`): in degree `k` the
  filtration of `H_k(B; R)` jumps only at `k`.

The spectral sequences are indexed as in `TauCeti.filteredSpaceSpectralSequence`: the second page
is the page numbered `3`, and the classical position `(k, q)` is `(a, b) = (1 - q - 2k, k - 1)`.
So the row `q = 0` is the set of positions with `a + 2b = -1`.

## Main definitions

* `TauCeti.TopCat.serreSpectralSequenceProj`: the morphism from the Serre spectral sequence of
  `p` to that of the identity of the base.
* `TauCeti.TopCat.serreSpectralSequenceSecondPageXIsoSingularHomology`: `E²_{k,0} ≅ H_k(B; R)`
  for a Serre fibration with path-connected fibres over a CW complex.

## Main results

* `TauCeti.TopCat.isIso_serreSpectralSequenceProj_hom_three_f`: the projection is an isomorphism
  on the row `q = 0` of the second page.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 5.1.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1, Section 1.1 (the homology spectral sequence).
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} (p : E ⟶ B) [T2Space B] (R : Type u) [Ring R]

section Proj

variable (C : Set B) {D : Set B} [RelCWComplex C D]

/-- **The projection of the Serre spectral sequence onto the base.** The morphism from the Serre
spectral sequence of `p` over a relative CW complex `C` to that of the identity of `B`, the
spectral sequence of the skeletal filtration of `C`, induced by `p`. -/
def serreSpectralSequenceProj : serreSpectralSequence C p R ⟶ serreSpectralSequence C (𝟙 B) R :=
  filteredSpaceSpectralSequenceMap (ModuleCat.of R R) (monotone_preimageSkeleton p)
    (monotone_preimageSkeleton (𝟙 B)) p (mapsTo_preimageSkeleton (C := C) p fun _ ↦ rfl)

/-- The projection of the Serre spectral sequence onto the base is the morphism of spectral
sequences of filtered spaces induced by `p`. -/
lemma serreSpectralSequenceProj_def :
    serreSpectralSequenceProj p R C = filteredSpaceSpectralSequenceMap (ModuleCat.of R R)
      (monotone_preimageSkeleton p) (monotone_preimageSkeleton (𝟙 B)) p
      (mapsTo_preimageSkeleton (C := C) p fun _ ↦ rfl) :=
  (rfl)

end Proj

/-! ### The row `q = 0` of the first and second pages -/

section Row

variable {C D : Set B} [RelCWComplex C D]

variable {p}

/-- On the row `q = 0` of the first page, the projection of the Serre spectral sequence of a
fibration with path-connected fibres onto the base is an isomorphism: the map
`H_k(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹); R) ⟶ H_k(Xᵏ, Xᵏ⁻¹; R)` is, cell by cell, the map `H₀(F) ⟶ H₀(pt)` of the
fibres over the centres of the `k`-cells. -/
theorem isIso_serreSpectralSequenceProj_hom_two_f (hp : serreFibrations p)
    (hconn : ∀ b ∈ C, PathConnectedSpace (p.fiber b)) (pq : ℤ × ℤ) (hpq : pq.1 + 2 * pq.2 = -1) :
    IsIso (((serreSpectralSequenceProj p R C).hom 2 le_rfl).f pq) := by
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hle
  · exact (isZero_filteredSpaceSpectralSequence_page_two_X _ _ pq hpos).isIso
      (isZero_filteredSpaceSpectralSequence_page_two_X _ _ pq hpos) _
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hle
  have e := filteredSpaceSpectralSequenceFirstPageXIso_hom_naturality (ModuleCat.of R R)
    (monotone_preimageSkeleton p) (monotone_preimageSkeleton (𝟙 B)) p
    (mapsTo_preimageSkeleton (C := C) p fun _ ↦ rfl) pq pq.2 (pq.2 + 1) rfl rfl _ rfl n hn
  rw [← Iso.eq_comp_inv] at e
  rw [serreSpectralSequenceProj_def, e]
  suffices IsIso (TopPair.singularHomologyMap (filteredSpaceStepMap (monotone_preimageSkeleton p)
      (monotone_preimageSkeleton (𝟙 B)) p (mapsTo_preimageSkeleton (C := C) p fun _ ↦ rfl)
      (by lia : pq.2 ≤ pq.2 + 1)) (ModuleCat.of R R) n) from inferInstance
  -- The step is the map of the pairs of preimages of the `n`-skeleton and the `(n - 1)`-skeleton,
  -- which the comparison of Serre fibrations computes cell by cell.
  let sq : CommSq p p (𝟙 B) (𝟙 B) := ⟨rfl⟩
  -- This is the case of the Serre class of zero modules.
  have key := (ObjectProperty.isoModSerre_isZero_iff _).1 <|
    isoModSerre_singularHomologyMap_preimagePairMap hp (MorphismProperty.id_mem _ B) R IsZero IsZero
      le_rfl sq n n fun j q hq ↦ by
      obtain rfl : q = 0 := by lia
      have := hconn _ (closedCell_subset_complex n j ⟨0, Metric.mem_closedBall_self zero_le_one,
        rfl⟩)
      -- The fibre of the identity is a point, so the map of fibres is one between path-connected
      -- spaces, an isomorphism on `H₀` since both augmentations are.
      have : Unique ((𝟙 B : B ⟶ B).fiber ((𝟙 B) (map n j 0))) :=
        ⟨⟨⟨map n j 0, rfl⟩⟩, fun x ↦ Subtype.ext x.property⟩
      exact (ObjectProperty.isoModSerre_isZero_iff _).2 (IsIso.of_isIso_fac_right
        (singularHomologyMap_singularHomology₀ε (ModuleCat.of R R) _))
  have hb : (pq.2 + 1).toNat = n := by lia
  have hb' : (pq.2 + 1 + 1).toNat = n + 1 := by lia
  refine (TopPair.isIso_singularHomologyMap_ofInclusion_congr (ModuleCat.of R R) p ?_ ?_ ?_ ?_ _ _
    (filteredSpaceStepMap_fst_apply _ _ _ _ _) (fun x ↦ by
      rw [TopCat.Hom.preimagePairMap_fst]
      exact p.coe_preimageMap_apply _ _ x) n).2 key
  all_goals rw [preimageSkeleton_def]; simp only [hb, hb']

/-- **The projection is an isomorphism on the row `q = 0` of the second page.** For a Serre
fibration with path-connected fibres, the morphism from its Serre spectral sequence to that of the
identity of the base is an isomorphism on `E²_{k,0}`: on the first page it is one on the row
`q = 0`, which the differentials of that page preserve. -/
theorem isIso_serreSpectralSequenceProj_hom_three_f (hp : serreFibrations p)
    (hconn : ∀ b ∈ C, PathConnectedSpace (p.fiber b)) (pq : ℤ × ℤ) (hpq : pq.1 + 2 * pq.2 = -1) :
    IsIso (((serreSpectralSequenceProj p R C).hom 3).f pq) :=
  (serreSpectralSequenceProj p R C).isIso_hom_f_add_one 2 le_rfl pq fun pq' hpq' ↦
    isIso_serreSpectralSequenceProj_hom_two_f R hp hconn pq' (by
      rcases hpq' with rfl | hpq'
      · exact hpq
      · rcases ComplexShape.add_two_mul_eq_of_up'_rel hpq' with h | h <;> lia)

end Row

/-! ### The spectral sequence of the skeletal filtration of the base -/

section Base

/-- **The first page of the spectral sequence of the skeletal filtration is concentrated on the
row `q = 0`.** For a relative CW complex `C ⊆ B`, the object at `pq = (a, b)` of the first page of
the Serre spectral sequence of the identity of `B` vanishes unless `a + 2b = -1`: it is
`H_n(Xᵏ, Xᵏ⁻¹; R)` with `k = b + 1` and `n = -(a + b)`, which vanishes for `n ≠ k`. -/
theorem isZero_serreSpectralSequence_id_page_two_X {C D : Set B} [RelCWComplex C D]
    (pq : ℤ × ℤ) (hpq : pq.1 + 2 * pq.2 ≠ -1) :
    IsZero (((serreSpectralSequence C (𝟙 B) R).page 2).X pq) := by
  rcases le_or_gt 0 (pq.1 + 2 * pq.2) with hq | hq
  · exact isZero_serreSpectralSequence_page_two_X (MorphismProperty.id_mem _ B) R C pq hq
  rcases lt_or_ge 0 (pq.1 + pq.2) with hpos | hle
  · exact isZero_filteredSpaceSpectralSequence_page_two_X _ _ pq hpos
  obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hle
  refine IsZero.of_iso ?_ (filteredSpaceSpectralSequenceFirstPageXIso (ModuleCat.of R R)
    (monotone_preimageSkeleton (C := C) (𝟙 B)) pq pq.2 (pq.2 + 1) rfl rfl _ rfl n hn)
  rcases lt_or_ge pq.2 (-1) with hb | hb
  · -- Below the skeleton `X⁻¹`, both stages of the filtration are the preimage of the base.
    have h₁ : preimageSkeleton C (𝟙 B) (pq.2 + 1) = preimageSkeleton C (𝟙 B) pq.2 := by
      rw [preimageSkeleton_def, preimageSkeleton_def, show (pq.2 + 1).toNat = 0 by lia,
        show (pq.2 + 1 + 1).toNat = 0 by lia]
    exact (TopPair.isZero_singularHomology_ofInclusion_congr _ _ subset_rfl h₁ rfl n).2
      (TopPair.isZero_singularHomology_ofInclusion_self _ _ n)
  · -- Otherwise the stages are the skeleta `Xᵏ⁻¹ ⊆ Xᵏ` with `k = b + 1 ≠ n`.
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by lia : 0 ≤ pq.2 + 1)
    have h₁ : preimageSkeleton C (𝟙 B) pq.2 = (skeletonLT C k : Set B) := by
      rw [preimageSkeleton_def, hk, Int.toNat_natCast, _root_.TopCat.coe_id, preimage_id]
    have h₂ : preimageSkeleton C (𝟙 B) (pq.2 + 1) = (skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set B) := by
      rw [preimageSkeleton_def, show pq.2 + 1 + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; lia,
        Int.toNat_natCast, _root_.TopCat.coe_id, preimage_id]
    exact (TopPair.isZero_singularHomology_ofInclusion_congr _ _
      (skeletonLT_subset_skeletonLT_succ C k) h₂ h₁ n).2
      (isZero_singularHomology_skeletonPair_of_ne C (ModuleCat.of R R) (by lia))

/-- From the second page on, numbered `3`, the differentials at a position on the row `q = 0` of
the spectral sequence of the skeletal filtration leave that row, so their other ends vanish
already on the second page. -/
lemma isZero_serreSpectralSequence_id_page_three_X_of_rel {C D : Set B}
    [RelCWComplex C D] {pq : ℤ × ℤ} (hpq : pq.1 + 2 * pq.2 = -1) (s : ℤ) (hs : 3 ≤ s)
    (pq' : ℤ × ℤ) (hpq' : (ComplexShape.up' ((s, 1 - s) : ℤ × ℤ)).Rel pq pq' ∨
      (ComplexShape.up' ((s, 1 - s) : ℤ × ℤ)).Rel pq' pq) :
    IsZero (((serreSpectralSequence C (𝟙 B) R).page 3).X pq') :=
  (serreSpectralSequence C (𝟙 B) R).isZero_page_X_of_le (r := 2) le_rfl
    (isZero_serreSpectralSequence_id_page_two_X R pq' (by
      rcases ComplexShape.add_two_mul_eq_of_up'_rel hpq' with h | h <;> lia)) 3 (by norm_num)

variable [CWComplex (univ : Set B)]

/-- The filtration of `H_k(B; R)` by the images of the homology of the skeleta vanishes below the
`k`-skeleton: the piece `F_{j-1} H_k(B; R)` vanishes for `j ≤ k`. Its graded pieces below `k` are
the objects of the limit page on rows `q > 0`, which vanish. -/
private lemma isZero_serreSpectralObject_id_abutmentFiltration (k j : ℕ) (hj : j ≤ k) :
    IsZero ((serreSpectralObject univ (𝟙 B) R).abutmentFiltration ((j : ℤ) - 1) (-k)) := by
  induction j with
  | zero => exact isZero_serreSpectralObject_abutmentFiltration (𝟙 B) R univ (by lia) _
  | succ j ih =>
    rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) - 1 + 1 by push_cast; ring]
    have hF := ih (by lia)
    -- The graded piece `F_j / F_{j-1}` is the object at `(-k - (j - 1), j - 1)` of a late page,
    -- on the row `q = k - j > 0`, where already the first page vanishes.
    have e := serreSpectralSequencePageXIsoGraded (MorphismProperty.id_mem _ B) R (K := univ)
      (subset_univ _) (k + 3) (by lia) (-(k : ℤ) - ((j : ℤ) - 1), (j : ℤ) - 1) (by dsimp; lia)
      (by dsimp; lia)
    dsimp only at e
    rw [sub_add_cancel (-(k : ℤ)) ((j : ℤ) - 1)] at e
    have hcok := ((serreSpectralSequence univ (𝟙 B) R).isZero_page_X_of_le le_rfl
      (isZero_serreSpectralSequence_id_page_two_X R _ (by dsimp; lia)) (k + 3) (by lia)).of_iso
        e.symm
    have := cokernel.π_of_zero (hF.eq_of_src
      ((serreSpectralObject univ (𝟙 B) R).abutmentFiltrationMap ((j : ℤ) - 1) (-k)) 0)
    exact hcok.of_iso (asIso (cokernel.π _))

/-- The graded piece `F_k H_k / F_{k-1} H_k` of the filtration of `H_k(B; R)` by the images of the
homology of the skeleta is all of `H_k(B; R)`. -/
def cokernelSerreSpectralObjectIdAbutmentFiltrationMapIso (k : ℕ) (b m : ℤ)
    (hb : b = k - 1) (hm : m = -k) :
    cokernel ((serreSpectralObject univ (𝟙 B) R).abutmentFiltrationMap b m) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
        (ModuleCat.of R R)).obj B := by
  subst hb hm
  have := cokernel.π_of_zero ((isZero_serreSpectralObject_id_abutmentFiltration R k k
    le_rfl).eq_of_src
      ((serreSpectralObject univ (𝟙 B) R).abutmentFiltrationMap ((k : ℤ) - 1) (-k)) 0)
  have := isIso_serreSpectralObject_abutmentFiltrationι (MorphismProperty.id_mem _ B) R univ
    (subset_univ _) k (b := (k : ℤ) - 1 + 1) (by lia)
  exact (asIso (cokernel.π _)).symm ≪≫
    asIso ((serreSpectralObject univ (𝟙 B) R).abutmentFiltrationι _ _) ≪≫
    chainFiltrationAbutmentIso (singularChains R) (monotone_preimageSkeleton (𝟙 B)) k

/-- The identification of the graded piece `F_k H_k / F_{k-1} H_k` with `H_k(B; R)` is induced by
the inclusion of `F_k H_k` into the abutment, followed by the identification of the abutment with
`H_k(B; R)`. -/
@[reassoc (attr := simp)]
lemma π_cokernelSerreSpectralObjectIdAbutmentFiltrationMapIso_hom (k : ℕ) (b m : ℤ)
    (hb : b = k - 1) (hm : m = -k) :
    cokernel.π _ ≫ (cokernelSerreSpectralObjectIdAbutmentFiltrationMapIso R k b m hb hm).hom =
      (serreSpectralObject univ (𝟙 B) R).abutmentFiltrationι (b + 1) m ≫
        eqToHom (congrArg (serreSpectralObject univ (𝟙 B) R).abutment hm) ≫
        (chainFiltrationAbutmentIso (singularChains R) (monotone_preimageSkeleton (𝟙 B))
          k).hom := by
  subst hb hm
  simp only [cokernelSerreSpectralObjectIdAbutmentFiltrationMapIso, Iso.trans_hom, Iso.symm_hom,
    asIso_inv, IsIso.hom_inv_id_assoc, eqToHom_refl, Category.id_comp]
  rfl

/-- **The row `q = 0` of the second page of the spectral sequence of the skeletal filtration.** For
a CW complex `B`, the object `E²_{k,0}` of the Serre spectral sequence of the identity of `B`, at
the position `pq = (1 - 2k, k - 1)` of the page numbered `3`, is `H_k(B; R)`. The first page is
concentrated on the row `q = 0`, so this object survives to the limit page, where it is the graded
piece `F_k H_k / F_{k-1} H_k = H_k(B; R)` of the filtration of the abutment. -/
def serreSpectralSequenceIdSecondPageXIsoSingularHomology (k : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -k) :
    ((serreSpectralSequence univ (𝟙 B) R).page 3).X pq ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
        (ModuleCat.of R R)).obj B :=
  ((serreSpectralSequence univ (𝟙 B) R).pageXIsoOfLEOfIsZero (r := 3) (by norm_num)
      (isZero_serreSpectralSequence_id_page_three_X_of_rel R (by lia)) (k + 3) (by lia)).symm ≪≫
    serreSpectralSequencePageXIsoGraded (MorphismProperty.id_mem _ B) R (K := univ)
      (subset_univ _) (k + 3) (by lia) pq (by lia) (by lia) ≪≫
    cokernelSerreSpectralObjectIdAbutmentFiltrationMapIso R k _ _ hb ha

/-- The identification of the row `q = 0` of the second page of the spectral sequence of the
skeletal filtration with `H_k(B; R)` is the passage to a late page, where the object is the graded
piece `F_k H_k / F_{k-1} H_k` of the filtration of the abutment, followed by the identification of
that graded piece with `H_k(B; R)`
(`TauCeti.TopCat.π_cokernelSerreSpectralObjectIdAbutmentFiltrationMapIso_hom`). -/
lemma serreSpectralSequenceIdSecondPageXIsoSingularHomology_hom (k : ℕ) (pq : ℤ × ℤ)
    (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -k) :
    (serreSpectralSequenceIdSecondPageXIsoSingularHomology R k pq hb ha).hom =
      ((serreSpectralSequence univ (𝟙 B) R).pageXIsoOfLEOfIsZero (r := 3) (by norm_num)
        (isZero_serreSpectralSequence_id_page_three_X_of_rel R (by lia)) (k + 3) (by lia)).inv ≫
      (serreSpectralSequencePageXIsoGraded (MorphismProperty.id_mem _ B) R (K := univ)
        (subset_univ _) (k + 3) (by lia) pq (by lia) (by lia)).hom ≫
      (cokernelSerreSpectralObjectIdAbutmentFiltrationMapIso R k _ _ hb ha).hom :=
  (rfl)

end Base

/-! ### The row `q = 0` of the second page -/

variable [CWComplex (univ : Set B)] {p}

/-- **The row `q = 0` of the second page of the Serre spectral sequence.** Let `p : E ⟶ B` be a
Serre fibration with path-connected fibres over a CW complex `B`. Then `E²_{k,0} ≅ H_k(B; R)`: the
object at `pq = (1 - 2k, k - 1)` of the page numbered `3` of the Serre spectral sequence of `p` is
the singular homology of the base. It is the projection onto the spectral sequence of the skeletal
filtration of `B` (`TauCeti.TopCat.isIso_serreSpectralSequenceProj_hom_three_f`), followed by the
identification of the latter's row `q = 0`
(`TauCeti.TopCat.serreSpectralSequenceIdSecondPageXIsoSingularHomology`). -/
def serreSpectralSequenceSecondPageXIsoSingularHomology (hp : serreFibrations p)
    (hconn : ∀ b, PathConnectedSpace (p.fiber b)) (k : ℕ) (pq : ℤ × ℤ) (hb : pq.2 = k - 1)
    (ha : pq.1 + pq.2 = -k) :
    ((serreSpectralSequence univ p R).page 3).X pq ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) k).obj
        (ModuleCat.of R R)).obj B :=
  have : IsIso (((serreSpectralSequenceProj p R univ).hom 3).f pq) :=
    isIso_serreSpectralSequenceProj_hom_three_f R hp (fun b _ ↦ hconn b) pq (by lia)
  @asIso _ _ _ _ _ this ≪≫ serreSpectralSequenceIdSecondPageXIsoSingularHomology R k pq hb ha

/-- The identification `E²_{k,0} ≅ H_k(B; R)` is the projection onto the spectral sequence of the
skeletal filtration of the base, followed by the identification of its row `q = 0`. -/
lemma serreSpectralSequenceSecondPageXIsoSingularHomology_hom (hp : serreFibrations p)
    (hconn : ∀ b, PathConnectedSpace (p.fiber b)) (k : ℕ) (pq : ℤ × ℤ) (hb : pq.2 = k - 1)
    (ha : pq.1 + pq.2 = -k) :
    (serreSpectralSequenceSecondPageXIsoSingularHomology R hp hconn k pq hb ha).hom =
      ((serreSpectralSequenceProj p R univ).hom 3).f pq ≫
        (serreSpectralSequenceIdSecondPageXIsoSingularHomology R k pq hb ha).hom :=
  (rfl)

end TopCat

end TauCeti

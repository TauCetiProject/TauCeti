/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.Basic
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Edge
public import TauCeti.Algebra.Homology.SpectralObject.PageHomology

/-!
# The edge map of the spectral sequence of a first-quadrant bicomplex

Let `K` be a first-quadrant bicomplex in an abelian category, with the spectral sequence
`HomologicalComplex₂.rowFiltrationSpectralSequence` of the filtration of its total complex by its
rows. The row `0` contributes to the total homology in degree `k` through the object at `(-k, 0)`
of each page `r ≥ 2`: since the filtration starts with the row `0`, this object maps onto the
limit object, which is the bottom piece of the filtration of `H_k(Tot K)`, the image of the
homology of the row `0`. This is the **edge map**
`HomologicalComplex₂.rowFiltrationEdge r hr pq k hpq : E_r^{-k,0} ⟶ H_k(Tot K)`.

On the first page, whose object at `(-k, 0)` is the homology of the row `0` in degree `k`, the edge
map is the map induced on homology by the inclusion of the row `0` into the total complex
(`HomologicalComplex₂.rowFiltrationSpectralSequenceFirstPageXIso_inv_rowFiltrationEdge`), and the
edge maps of consecutive pages are compatible with the passage from a page to its homology
(`HomologicalComplex₂.homologyπ_iso_hom_rowFiltrationEdge`).

For the column filtration, `HomologicalComplex₂.columnFiltrationEdge` is the edge map of the row
filtration of `K.flip`, followed by the comparison of the total complexes of `K.flip` and `K`. Its
object at `(-k, 0)` on the first page is the homology of the column `K.X 0`, and for an
augmentation `ε : K.X 0 ⟶ E` of the column `0`, the edge map followed by the map induced by the
augmentation of the total complex is the map induced by `ε`
(`HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso_inv_columnFiltrationEdge`).

**Collapse.** The differentials of the page `r` change the row by `r - 1`. If a page `r ≥ 3`
vanishes in the rows `≥ 2`, no differential from the page `r` on reaches or leaves the rows `0`
and `1`, so their objects on the page `r` are the limit objects
(`HomologicalComplex₂.isIso_rowFiltrationSpectralSequencePageXToEInfty_of_isZero`), and the limit
objects vanish in the rows `≥ 2`, so the rows `< 2` give the whole homology of the total complex.
The main application is to the second page, numbered `r = 3`.

* If a page `r ≥ 2` vanishes in the rows `≥ 1`, the edge map from the page `r` is an isomorphism
  (`HomologicalComplex₂.isIso_rowFiltrationEdge_of_isZero`).
* If a page `r ≥ 3` vanishes in the rows `≥ 2`, the homology of the total complex in degree `k` is
  an extension of the object `E_r^{-k-1,1}` of the row `1` by the object `E_r^{-k,0}` of the row
  `0`: with the map `HomologicalComplex₂.rowFiltrationToRowOne` onto the row `1`, characterized by
  `HomologicalComplex₂.rowFiltrationToRowOne_comp_spectralSequencePageXToEInfty`, the sequence
  `0 ⟶ E_r^{-k,0} ⟶ H_k(Tot K) ⟶ E_r^{-k-1,1} ⟶ 0` is short exact
  (`HomologicalComplex₂.rowFiltrationEdge_shortExact`).

The same holds for the column filtration
(`HomologicalComplex₂.isIso_columnFiltrationEdge_of_isZero`,
`HomologicalComplex₂.columnFiltrationEdge_shortExact`).

## Main definitions and results

* `HomologicalComplex₂.rowFiltrationEdge`, `HomologicalComplex₂.columnFiltrationEdge`: the edge
  maps of the spectral sequences of the row and column filtrations.
* `HomologicalComplex₂.rowFiltrationSpectralSequenceFirstPageXIso_inv_rowFiltrationEdge`,
  `HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso_inv_columnFiltrationEdge`:
  the edge maps on the first page.
* `HomologicalComplex₂.homologyπ_iso_hom_rowFiltrationEdge`,
  `HomologicalComplex₂.homologyπ_iso_hom_columnFiltrationEdge`: compatibility of the edge maps of
  consecutive pages.
* `HomologicalComplex₂.isIso_rowFiltrationEdge_of_isZero`,
  `HomologicalComplex₂.isIso_columnFiltrationEdge_of_isZero`: collapse onto the row or column `0`.
* `HomologicalComplex₂.rowFiltrationToRowOne`, `HomologicalComplex₂.columnFiltrationToColumnOne`,
  `HomologicalComplex₂.rowFiltrationEdge_shortExact`,
  `HomologicalComplex₂.columnFiltrationEdge_shortExact`: the short exact sequence when only the rows
  or columns `0` and `1` are nonzero on a page `r ≥ 3`.
-/

public section

noncomputable section

open CategoryTheory Limits ComplexShape

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Abelian C] (K : HomologicalComplex₂ C (down ℕ) (down ℕ))

/-- **The edge map of the spectral sequence of the row filtration.** The object at
`pq = (-k, 0)` on the page `r ≥ 2` maps onto the limit object `E^{-k}(⊥ ≤ 0 ≤ 1 ≤ ⊤)`, which is the
bottom piece of the filtration of the abutment since the rows `< 0` vanish; this piece embeds in the
abutment, the homology of the total complex in degree `k`. -/
def rowFiltrationEdge (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (k : ℕ) (hpq : pq = (-(k : ℤ), 0)) :
    (K.rowFiltrationSpectralSequence.page r).X pq ⟶ (K.total (down ℕ)).homology k :=
  K.rowFiltrationSpectralObject.spectralSequencePageXToEInfty r hr pq (pq.1 + pq.2) rfl
      (K.isZero_rowFiltrationSpectralObject_H_bot _ _ (by subst hpq; dsimp; omega)) ≫
    K.rowFiltrationSpectralObject.EInftyToAbutment pq.2 (pq.1 + pq.2)
      (K.isZero_rowFiltration_abutmentFiltration _ (by subst hpq; simp) _) ≫
    (CochainComplex.filtrationAbutmentIso _ K.monotone_rowFiltration (pq.1 + pq.2)).hom ≫
    ((K.total (down ℕ)).extendHomologyIso embeddingDownNat (by subst hpq; simp)).hom

/-- The edge map `HomologicalComplex₂.rowFiltrationEdge` is the map onto the limit object, followed
by its embedding in the abutment and the identification of the abutment with the homology of the
total complex. -/
lemma rowFiltrationEdge_def (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (k : ℕ)
    (hpq : pq = (-(k : ℤ), 0)) :
    K.rowFiltrationEdge r hr pq k hpq =
      K.rowFiltrationSpectralObject.spectralSequencePageXToEInfty r hr pq (pq.1 + pq.2) rfl
          (K.isZero_rowFiltrationSpectralObject_H_bot _ _ (by subst hpq; dsimp; omega)) ≫
        K.rowFiltrationSpectralObject.EInftyToAbutment pq.2 (pq.1 + pq.2)
          (K.isZero_rowFiltration_abutmentFiltration _ (by subst hpq; simp) _) ≫
        (CochainComplex.filtrationAbutmentIso _ K.monotone_rowFiltration (pq.1 + pq.2)).hom ≫
        ((K.total (down ℕ)).extendHomologyIso embeddingDownNat (by subst hpq; simp)).hom :=
  (rfl)

/-- **The edge map of the row filtration on the first page.** On the first page, whose object at
`(-k, 0)` is the homology of the row `0` in degree `k`, the edge map is the map induced on homology
by the inclusion `HomologicalComplex₂.rowZeroι` of the row `0` into the total complex. -/
theorem rowFiltrationSpectralSequenceFirstPageXIso_inv_rowFiltrationEdge (p : ℤ) (k : ℕ)
    (hp : p + 2 * ((0 : ℕ) : ℤ) + k = 0) :
    (K.rowFiltrationSpectralSequenceFirstPageXIso p 0 k hp).inv ≫
      K.rowFiltrationEdge 2 le_rfl (p, ((0 : ℕ) : ℤ)) k (Prod.ext (by simp; omega) (by simp)) =
    HomologicalComplex.homologyMap K.rowZeroι k := by
  have hF := CochainComplex.homologyMap_comp_spectralSequencePageXToEInfty_EInftyToAbutment
    K.rowFiltration K.monotone_rowFiltration (p, ((0 : ℕ) : ℤ)) _ rfl
    (Subobject.isZero_homology_of_eq_bot _ (K.rowFiltration_eq_bot _ (by simp)) _)
    (K.isZero_rowFiltration_abutmentFiltration _ (by simp) _)
  -- reduce the projections of the pair `(p, 0)`
  dsimp only at hF
  have hG := K.π_rowFiltrationGradedIso_hom_totalRowι 0
  rw [toTotalRowsGE_zero, HomologicalComplex.extendMap_id, Category.comp_id] at hG
  -- the row `0` of the filtration is the bottom piece, so the projection onto the graded piece is
  -- an isomorphism
  have hz : IsZero ((CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration).obj
      (((0 : ℕ) : ℤ) : EInt)) := by
    rw [CochainComplex.filtrationFunctor_obj_coe, K.rowFiltration_eq_bot _ (by simp)]
    exact IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero
  have := cokernel.π_of_zero (hz.eq_of_src
    ((CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration).map
      (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : (((0 : ℕ) : ℤ)) = _) rfl))) 0)
  -- on the homology of the row `0`, placed in the degrees of the total complex, the edge map is
  -- induced by the inclusion of the row `0`
  have key : HomologicalComplex.homologyMap (K.rowFiltrationGradedIso 0).inv (p + (0 : ℕ)) ≫
      (CochainComplex.spectralSequenceFirstPageXIsoCokernel _ (p, (0 : ℕ)) (0 : ℕ) ((0 : ℕ) + 1)
        rfl rfl (p + (0 : ℕ)) rfl).inv ≫
      K.rowFiltrationSpectralObject.spectralSequencePageXToEInfty 2 le_rfl (p, (0 : ℕ))
        (p + (0 : ℕ)) rfl (K.isZero_rowFiltrationSpectralObject_H_bot _ _ (by simp)) ≫
      K.rowFiltrationSpectralObject.EInftyToAbutment ((0 : ℕ) : ℤ) (p + (0 : ℕ))
        (K.isZero_rowFiltration_abutmentFiltration _ (by simp) _) ≫
      (CochainComplex.filtrationAbutmentIso _ K.monotone_rowFiltration (p + (0 : ℕ))).hom =
      HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap (K.totalRowι 0) embeddingDownNat) (p + (0 : ℕ)) := by
    rw [← cancel_epi (HomologicalComplex.homologyMap (eqToHom
      (CochainComplex.filtrationFunctor_obj_coe K.rowFiltration K.monotone_rowFiltration
        (((0 : ℕ) : ℤ) + 1)).symm ≫ cokernel.π _ ≫ (K.rowFiltrationGradedIso 0).hom)
        (p + (0 : ℕ))),
      ← HomologicalComplex.homologyMap_comp_assoc, Category.assoc, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, hF, ← HomologicalComplex.homologyMap_comp,
      Category.assoc, Category.assoc, hG]
    -- `filtrationFunctorArrow` is by definition the identification of the object of the
    -- functor of the filtration with the subcomplex, followed by its inclusion
    exact congrArg (HomologicalComplex.homologyMap · (p + (0 : ℕ)))
      (CochainComplex.eqToHom_comp_filtrationFunctorArrow K.rowFiltration K.monotone_rowFiltration
        (((0 : ℕ) : ℤ) + 1)).symm
  simp only [rowFiltrationSpectralSequenceFirstPageXIso_eq,
    rowFiltrationSpectralSequenceFirstPageXIsoTotalRow_eq, Iso.trans_inv, totalRowHomologyIso_zero,
    Iso.refl_inv, HomologicalComplex.homologyMapIso_inv, Category.assoc, rowFiltrationEdge_def]
  rw [reassoc_of% key, HomologicalComplex.extendHomologyIso_hom_naturality,
    Iso.inv_hom_id_assoc, totalRowι_zero]
  -- `k + 0` is `k` by definition
  exact Category.id_comp _

/-- **The edge maps of consecutive pages.** On the cycles of the page `r`, the projection onto the
homology of the page `r`, followed by its identification with the page `r + 1` and the edge map of
the page `r + 1`, is the edge map of the page `r`. -/
@[reassoc]
lemma homologyπ_iso_hom_rowFiltrationEdge (r r' : ℤ) (hrr' : r + 1 = r') (hr : 2 ≤ r)
    (pq : ℤ × ℤ) (k : ℕ) (hpq : pq = (-(k : ℤ), 0)) :
    (K.rowFiltrationSpectralSequence.page r).homologyπ pq ≫
        (K.rowFiltrationSpectralSequence.iso r r' pq hrr' hr).hom ≫
        K.rowFiltrationEdge r' (by omega) pq k hpq =
      (K.rowFiltrationSpectralSequence.page r).iCycles pq ≫ K.rowFiltrationEdge r hr pq k hpq := by
  rw [← Abelian.SpectralObject.iCycles_spectralSequencePageXToPageX_assoc _ r r' hrr' hr pq
      (pq.1 + pq.2) rfl
      (K.isZero_rowFiltrationSpectralObject_H_bot _ _ (by subst hpq; dsimp; omega))
      (K.isZero_rowFiltrationSpectralObject_H_bot _ _ (by subst hpq; dsimp; omega)),
    rowFiltrationEdge_def, rowFiltrationEdge_def,
    Abelian.SpectralObject.spectralSequencePageXToPageX_spectralSequencePageXToEInfty_assoc]

/-! ### Collapse -/

/-- An object of the page `r ≥ 2` of the spectral sequence of the row filtration which vanishes
has vanishing limit object: the limit object is a subquotient of it. -/
lemma isZero_rowFiltrationSpectralObject_EInfty (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (h : IsZero ((K.rowFiltrationSpectralSequence.page r).X pq)) :
    IsZero (K.rowFiltrationSpectralObject.EInfty pq.2 (pq.1 + pq.2)) :=
  (K.rowFiltrationSpectralSequence.isZero_page_X_of_le hr h
    (r + 1 + pq.1.natAbs + 2 * pq.2.natAbs) (by omega)).of_iso
    (K.rowFiltrationSpectralSequencePageXIsoEInfty _ (by omega) pq _ rfl (by omega)
      (by omega)).symm

/-- **Degeneration in the rows `0` and `1`.** If the page `r ≥ 3` of the spectral sequence of the
row filtration vanishes in the rows `≥ 2`, then no differential from the page `r` on reaches or
leaves the rows `0` and `1`, so their objects on the page `r` are the limit objects: the map
`spectralSequencePageXToEInfty` from the page `r` is an isomorphism. -/
lemma isIso_rowFiltrationSpectralSequencePageXToEInfty_of_isZero (r : ℤ) (hr : 3 ≤ r)
    (pq : ℤ × ℤ) (n : ℤ) (hn : n = pq.1 + pq.2) (hpq₀ : 0 ≤ pq.2) (hpq₁ : pq.2 ≤ 1)
    (h : ∀ pq' : ℤ × ℤ, 2 ≤ pq'.2 → IsZero ((K.rowFiltrationSpectralSequence.page r).X pq')) :
    IsIso (K.rowFiltrationSpectralObject.spectralSequencePageXToEInfty r (by omega) pq n hn
      (K.isZero_rowFiltrationSpectralObject_H_bot _ _ (by omega))) :=
  K.rowFiltrationSpectralObject.isIso_spectralSequencePageXToEInfty_of_isZero
    (r + pq.1.natAbs + 2 * pq.2.natAbs) pq n hn r (by omega) (by omega)
    (fun r' _ _ ↦ K.isZero_rowFiltrationSpectralObject_H_bot _ _ (by omega))
    (CochainComplex.isZero_spectralObject_H_top _ _ _ _
      (K.isZero_homology_cokernel_rowFiltration_arrow _ _ (by omega)))
    (fun r' hr' _ ↦ ⟨h _ (by dsimp; omega),
      K.isZero_rowFiltrationSpectralSequence_page_X r (by omega) _ _ (Or.inl (by omega))⟩)

/-- If the page `r ≥ 2` of the spectral sequence of the row filtration vanishes in the rows `≥ s`,
`s ≥ 0`, then the piece `F_s H_k` of the filtration of the homology of the total complex coming
from the rows `< s` is everything. -/
lemma isIso_rowFiltration_abutmentFiltrationι_of_isZero (r : ℤ) (hr : 2 ≤ r) (s : ℤ) (hs : 0 ≤ s)
    (n : ℤ)
    (h : ∀ pq' : ℤ × ℤ, s ≤ pq'.2 → IsZero ((K.rowFiltrationSpectralSequence.page r).X pq')) :
    IsIso (K.rowFiltrationSpectralObject.abutmentFiltrationι s n) :=
  K.rowFiltrationSpectralObject.isIso_abutmentFiltrationι_of_isZero_EInfty
    (b := s + n.natAbs + 1) (by omega)
    (K.isIso_rowFiltration_abutmentFiltrationι _ _ (by omega))
    (fun s' h₁ _ ↦ by
      simpa using
        K.isZero_rowFiltrationSpectralObject_EInfty r hr (n - s', s') (h _ (by simpa using h₁)))

/-- **Collapse onto the row `0`.** If the page `r ≥ 2` of the spectral sequence of the row
filtration vanishes in the rows `≥ 1`, the edge map from the page `r` is an isomorphism: the
homology of the total complex is the object of the row `0` of the page `r`. -/
theorem isIso_rowFiltrationEdge_of_isZero (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (k : ℕ)
    (hpq : pq = (-(k : ℤ), 0))
    (h : ∀ pq' : ℤ × ℤ, 1 ≤ pq'.2 → IsZero ((K.rowFiltrationSpectralSequence.page r).X pq')) :
    IsIso (K.rowFiltrationEdge r hr pq k hpq) := by
  -- no differential from the page `r` on reaches or leaves the row `0`
  have := K.rowFiltrationSpectralObject.isIso_spectralSequencePageXToEInfty_of_isZero
    (r + 1 + pq.1.natAbs + 2 * pq.2.natAbs) pq _ rfl r hr (by omega)
    (fun r' _ _ ↦ K.isZero_rowFiltrationSpectralObject_H_bot _ _ (by subst hpq; dsimp; omega))
    (CochainComplex.isZero_spectralObject_H_top _ _ _ _
      (K.isZero_homology_cokernel_rowFiltration_arrow _ _ (by subst hpq; dsimp; omega)))
    (fun r' hr' _ ↦ ⟨h _ (by subst hpq; dsimp; omega),
      K.isZero_rowFiltrationSpectralSequence_page_X r hr _ _
        (Or.inl (by subst hpq; dsimp; omega))⟩)
  have := K.isIso_rowFiltration_abutmentFiltrationι_of_isZero r hr (pq.2 + 1)
    (by subst hpq; simp) (pq.1 + pq.2) (fun pq' h' ↦ h pq' (by subst hpq; simp at h'; omega))
  have := K.rowFiltrationSpectralObject.isIso_EInftyToAbutment pq.2 (pq.1 + pq.2)
    (K.isZero_rowFiltration_abutmentFiltration _ (by subst hpq; simp) _)
  rw [rowFiltrationEdge_def]
  infer_instance

/-- **The map onto the row `1`.** If the page `r ≥ 3` of the spectral sequence of the row
filtration vanishes in the rows `≥ 2`, the homology of the total complex in degree `k` maps onto
the object at `(-k - 1, 1)` of the page `r`: it is the projection onto the graded piece
`F_2 H_k / F_1 H_k`, identified with the limit object of the row `1`, which is the object of the
page `r`. -/
def rowFiltrationToRowOne (r : ℤ) (hr : 3 ≤ r) (pq : ℤ × ℤ) (k : ℕ) (hpq : pq = (-(k : ℤ), 0))
    (h : ∀ pq' : ℤ × ℤ, 2 ≤ pq'.2 → IsZero ((K.rowFiltrationSpectralSequence.page r).X pq')) :
    (K.total (down ℕ)).homology k ⟶
      (K.rowFiltrationSpectralSequence.page r).X (pq.1 - 1, pq.2 + 1) :=
  have := K.isIso_rowFiltration_abutmentFiltrationι_of_isZero r (by omega) (pq.2 + 1 + 1)
    (by subst hpq; simp) (pq.1 + pq.2) (fun pq' h' ↦ h pq' (by subst hpq; simp at h'; omega))
  have hiso := K.isIso_rowFiltrationSpectralSequencePageXToEInfty_of_isZero r hr
    (pq.1 - 1, pq.2 + 1) (pq.1 + pq.2) (by dsimp; omega) (by subst hpq; simp) (by subst hpq; simp) h
  ((K.total (down ℕ)).extendHomologyIso embeddingDownNat (by subst hpq; simp)).inv ≫
    (CochainComplex.filtrationAbutmentIso _ K.monotone_rowFiltration (pq.1 + pq.2)).inv ≫
    K.rowFiltrationSpectralObject.abutmentToEInfty pq.2 (pq.1 + pq.2) ≫
    -- the limit object of the row `(pq.1 - 1, pq.2 + 1).2` is by definition that of the row
    -- `pq.2 + 1`
    @inv _ _ _ _ _ hiso

/-- The map `HomologicalComplex₂.rowFiltrationToRowOne`, followed by the isomorphism
`spectralSequencePageXToEInfty` from the object of the row `1` to its limit object, is the
identification of the homology of the total complex with the abutment, followed by the
projection `abutmentToEInfty` onto the graded piece of the row `1`. -/
@[reassoc]
lemma rowFiltrationToRowOne_comp_spectralSequencePageXToEInfty (r : ℤ) (hr : 3 ≤ r)
    (pq : ℤ × ℤ) (k : ℕ) (hpq : pq = (-(k : ℤ), 0))
    (h : ∀ pq' : ℤ × ℤ, 2 ≤ pq'.2 → IsZero ((K.rowFiltrationSpectralSequence.page r).X pq')) :
    haveI := K.isIso_rowFiltration_abutmentFiltrationι_of_isZero r (by omega) (pq.2 + 1 + 1)
      (by subst hpq; simp) (pq.1 + pq.2) (fun pq' h' ↦ h pq' (by subst hpq; simp at h'; omega))
    K.rowFiltrationToRowOne r hr pq k hpq h ≫
        K.rowFiltrationSpectralObject.spectralSequencePageXToEInfty r (by omega)
          (pq.1 - 1, pq.2 + 1) (pq.1 + pq.2) (by dsimp; omega)
          (K.isZero_rowFiltrationSpectralObject_H_bot _ _ (by subst hpq; dsimp; omega)) =
      ((K.total (down ℕ)).extendHomologyIso embeddingDownNat (by subst hpq; simp)).inv ≫
        (CochainComplex.filtrationAbutmentIso _ K.monotone_rowFiltration (pq.1 + pq.2)).inv ≫
        K.rowFiltrationSpectralObject.abutmentToEInfty pq.2 (pq.1 + pq.2) := by
  simp only [rowFiltrationToRowOne, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The edge map followed by the map onto the row `1` vanishes. -/
@[reassoc (attr := simp)]
lemma rowFiltrationEdge_rowFiltrationToRowOne (r : ℤ) (hr : 3 ≤ r) (pq : ℤ × ℤ) (k : ℕ)
    (hpq : pq = (-(k : ℤ), 0))
    (h : ∀ pq' : ℤ × ℤ, 2 ≤ pq'.2 → IsZero ((K.rowFiltrationSpectralSequence.page r).X pq')) :
    K.rowFiltrationEdge r (by omega) pq k hpq ≫ K.rowFiltrationToRowOne r hr pq k hpq h = 0 := by
  have := K.isIso_rowFiltrationSpectralSequencePageXToEInfty_of_isZero r hr (pq.1 - 1, pq.2 + 1)
    (pq.1 + pq.2) (by dsimp; omega) (by subst hpq; simp) (by subst hpq; simp) h
  rw [← cancel_mono (K.rowFiltrationSpectralObject.spectralSequencePageXToEInfty r (by omega)
      (pq.1 - 1, pq.2 + 1) (pq.1 + pq.2) (by dsimp; omega)
      (K.isZero_rowFiltrationSpectralObject_H_bot _ _ (by subst hpq; dsimp; omega))),
    Category.assoc, rowFiltrationToRowOne_comp_spectralSequencePageXToEInfty, zero_comp]
  simp [rowFiltrationEdge_def]

/-- **The two-row short exact sequence.** If the page `r ≥ 3` of the spectral sequence of the row
filtration vanishes in the rows `≥ 2`, the sequence `0 ⟶ E^{-k,0} ⟶ H_k(Tot K) ⟶ E^{-k-1,1} ⟶ 0`
of the edge map and of the map onto the row `1` is short exact. -/
theorem rowFiltrationEdge_shortExact (r : ℤ) (hr : 3 ≤ r) (pq : ℤ × ℤ) (k : ℕ)
    (hpq : pq = (-(k : ℤ), 0))
    (h : ∀ pq' : ℤ × ℤ, 2 ≤ pq'.2 → IsZero ((K.rowFiltrationSpectralSequence.page r).X pq')) :
    (ShortComplex.mk _ _
      (K.rowFiltrationEdge_rowFiltrationToRowOne r hr pq k hpq h)).ShortExact := by
  have := K.isIso_rowFiltration_abutmentFiltrationι_of_isZero r (by omega) (pq.2 + 1 + 1)
    (by subst hpq; simp) (pq.1 + pq.2) (fun pq' h' ↦ h pq' (by subst hpq; simp at h'; omega))
  have h₀ := K.isIso_rowFiltrationSpectralSequencePageXToEInfty_of_isZero r hr pq _ rfl
    (by subst hpq; simp) (by subst hpq; simp) h
  have h₁ := K.isIso_rowFiltrationSpectralSequencePageXToEInfty_of_isZero r hr (pq.1 - 1, pq.2 + 1)
    (pq.1 + pq.2) (by dsimp; omega) (by subst hpq; simp) (by subst hpq; simp) h
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk (@asIso _ _ _ _ _ h₀).symm
    (CochainComplex.filtrationAbutmentIso _ K.monotone_rowFiltration (pq.1 + pq.2) ≪≫
      (K.total (down ℕ)).extendHomologyIso embeddingDownNat (by subst hpq; simp))
    (@asIso _ _ _ _ _ h₁).symm ?_ ?_)
    (K.rowFiltrationSpectralObject.EInftyToAbutment_shortExact pq.2 (pq.1 + pq.2)
      (K.isZero_rowFiltration_abutmentFiltration _ (by subst hpq; simp) _))
  · simp [rowFiltrationEdge_def]
  · rw [← cancel_mono (K.rowFiltrationSpectralObject.spectralSequencePageXToEInfty r (by omega)
      (pq.1 - 1, pq.2 + 1) (pq.1 + pq.2) (by dsimp; omega)
      (K.isZero_rowFiltrationSpectralObject_H_bot _ _ (by subst hpq; dsimp; omega)))]
    simp [rowFiltrationToRowOne_comp_spectralSequencePageXToEInfty]

/-! ### The column filtration -/

/-- **The edge map of the spectral sequence of the column filtration**: the edge map
`HomologicalComplex₂.rowFiltrationEdge` of the flipped bicomplex, followed by the signed
isomorphism `HomologicalComplex₂.totalFlipIso` between the total complexes of `K.flip` and `K`. -/
def columnFiltrationEdge (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (k : ℕ) (hpq : pq = (-(k : ℤ), 0)) :
    (K.columnFiltrationSpectralSequence.page r).X pq ⟶ (K.total (down ℕ)).homology k :=
  K.flip.rowFiltrationEdge r hr pq k hpq ≫
    HomologicalComplex.homologyMap (K.totalFlipIso (down ℕ)).hom k

/-- The edge map `HomologicalComplex₂.columnFiltrationEdge` is the edge map of the row filtration
of `K.flip`, followed by the map induced by `HomologicalComplex₂.totalFlipIso`. -/
lemma columnFiltrationEdge_def (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (k : ℕ)
    (hpq : pq = (-(k : ℤ), 0)) :
    K.columnFiltrationEdge r hr pq k hpq = K.flip.rowFiltrationEdge r hr pq k hpq ≫
      HomologicalComplex.homologyMap (K.totalFlipIso (down ℕ)).hom k :=
  (rfl)

/-- **The edge maps of consecutive pages of the column filtration** are compatible with the
passage from a page to its homology. -/
@[reassoc]
lemma homologyπ_iso_hom_columnFiltrationEdge (r r' : ℤ) (hrr' : r + 1 = r') (hr : 2 ≤ r)
    (pq : ℤ × ℤ) (k : ℕ) (hpq : pq = (-(k : ℤ), 0)) :
    (K.columnFiltrationSpectralSequence.page r).homologyπ pq ≫
        (K.columnFiltrationSpectralSequence.iso r r' pq hrr' hr).hom ≫
        K.columnFiltrationEdge r' (by omega) pq k hpq =
      (K.columnFiltrationSpectralSequence.page r).iCycles pq ≫
        K.columnFiltrationEdge r hr pq k hpq := by
  simp only [columnFiltrationEdge_def,
    K.flip.homologyπ_iso_hom_rowFiltrationEdge_assoc r r' hrr' hr]

/-- **The edge map of the column filtration on the first page.** Let `ε : K.X 0 ⟶ E` be an
augmentation of the column `0` with `K.d 1 0 ≫ ε = 0`. On the first page, whose object at
`(-k, 0)` is the homology of the column `K.X 0` in degree `k`, the edge map followed by the map
induced by the augmentation `HomologicalComplex₂.totalAugmentation` of the total complex is the
map induced by `ε`. -/
theorem columnFiltrationSpectralSequenceFirstPageXIso_inv_columnFiltrationEdge
    {E : ChainComplex C ℕ} (ε : K.X 0 ⟶ E) (hε : K.d 1 0 ≫ ε = 0) (k : ℕ) :
    (K.columnFiltrationSpectralSequenceFirstPageXIso 0 k).inv ≫
      K.columnFiltrationEdge 2 le_rfl (-(k : ℤ) - 2 * ((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)) k
        (Prod.ext (by simp) (by simp)) ≫
      HomologicalComplex.homologyMap (K.totalAugmentation ε hε) k =
    HomologicalComplex.homologyMap ε k := by
  have h : (K.flipRowIso 0).inv ≫ K.flip.rowZeroι ≫ (K.totalFlipIso (down ℕ)).hom ≫
      K.totalAugmentation ε hε = ε := by
    ext n
    simp [ιTotal_totalFlipIso_f_hom_assoc]
  rw [columnFiltrationSpectralSequenceFirstPageXIso_eq, Iso.trans_inv,
    HomologicalComplex.homologyMapIso_inv, Category.assoc, columnFiltrationEdge_def,
    Category.assoc,
    reassoc_of% (K.flip.rowFiltrationSpectralSequenceFirstPageXIso_inv_rowFiltrationEdge _ k _)]
  simp only [← HomologicalComplex.homologyMap_comp, h]

/-- **Collapse onto the column `0`.** If the page `r ≥ 2` of the spectral sequence of the column
filtration vanishes in the columns `≥ 1`, the edge map from the page `r` is an isomorphism. -/
theorem isIso_columnFiltrationEdge_of_isZero (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (k : ℕ)
    (hpq : pq = (-(k : ℤ), 0))
    (h : ∀ pq' : ℤ × ℤ, 1 ≤ pq'.2 → IsZero ((K.columnFiltrationSpectralSequence.page r).X pq')) :
    IsIso (K.columnFiltrationEdge r hr pq k hpq) := by
  have := K.flip.isIso_rowFiltrationEdge_of_isZero r hr pq k hpq h
  rw [columnFiltrationEdge_def]
  infer_instance

/-- **The map onto the column `1`.** If the page `r ≥ 3` of the spectral sequence of the column
filtration vanishes in the columns `≥ 2`, the homology of the total complex in degree `k` maps
onto the object at `(-k - 1, 1)` of the page `r`: it is the map
`HomologicalComplex₂.rowFiltrationToRowOne` of the flipped bicomplex, after the comparison of the
total complexes of `K` and `K.flip`. -/
def columnFiltrationToColumnOne (r : ℤ) (hr : 3 ≤ r) (pq : ℤ × ℤ) (k : ℕ)
    (hpq : pq = (-(k : ℤ), 0))
    (h : ∀ pq' : ℤ × ℤ, 2 ≤ pq'.2 → IsZero ((K.columnFiltrationSpectralSequence.page r).X pq')) :
    (K.total (down ℕ)).homology k ⟶
      (K.columnFiltrationSpectralSequence.page r).X (pq.1 - 1, pq.2 + 1) :=
  HomologicalComplex.homologyMap (K.totalFlipIso (down ℕ)).inv k ≫
    K.flip.rowFiltrationToRowOne r hr pq k hpq h

/-- The map `HomologicalComplex₂.columnFiltrationToColumnOne` is the map induced on homology by the
inverse of `HomologicalComplex₂.totalFlipIso`, followed by the map onto the row `1` of the row
filtration of `K.flip`. -/
lemma columnFiltrationToColumnOne_def (r : ℤ) (hr : 3 ≤ r) (pq : ℤ × ℤ) (k : ℕ)
    (hpq : pq = (-(k : ℤ), 0))
    (h : ∀ pq' : ℤ × ℤ, 2 ≤ pq'.2 → IsZero ((K.columnFiltrationSpectralSequence.page r).X pq')) :
    K.columnFiltrationToColumnOne r hr pq k hpq h =
      HomologicalComplex.homologyMap (K.totalFlipIso (down ℕ)).inv k ≫
        K.flip.rowFiltrationToRowOne r hr pq k hpq h :=
  (rfl)

/-- The edge map of the column filtration followed by the map onto the column `1` vanishes. -/
@[reassoc (attr := simp)]
lemma columnFiltrationEdge_columnFiltrationToColumnOne (r : ℤ) (hr : 3 ≤ r) (pq : ℤ × ℤ) (k : ℕ)
    (hpq : pq = (-(k : ℤ), 0))
    (h : ∀ pq' : ℤ × ℤ, 2 ≤ pq'.2 → IsZero ((K.columnFiltrationSpectralSequence.page r).X pq')) :
    K.columnFiltrationEdge r (by omega) pq k hpq ≫ K.columnFiltrationToColumnOne r hr pq k hpq h =
      0 := by
  rw [columnFiltrationEdge_def, columnFiltrationToColumnOne_def, Category.assoc,
    ← HomologicalComplex.homologyMap_comp_assoc, Iso.hom_inv_id, HomologicalComplex.homologyMap_id,
    Category.id_comp, rowFiltrationEdge_rowFiltrationToRowOne]

/-- **The two-column short exact sequence.** If the page `r ≥ 3` of the spectral sequence of the
column filtration vanishes in the columns `≥ 2`, the sequence
`0 ⟶ E^{-k,0} ⟶ H_k(Tot K) ⟶ E^{-k-1,1} ⟶ 0` of the edge map and of the map onto the column `1`
is short exact. -/
theorem columnFiltrationEdge_shortExact (r : ℤ) (hr : 3 ≤ r) (pq : ℤ × ℤ) (k : ℕ)
    (hpq : pq = (-(k : ℤ), 0))
    (h : ∀ pq' : ℤ × ℤ, 2 ≤ pq'.2 → IsZero ((K.columnFiltrationSpectralSequence.page r).X pq')) :
    (ShortComplex.mk _ _
      (K.columnFiltrationEdge_columnFiltrationToColumnOne r hr pq k hpq h)).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ (K.flip.rowFiltrationEdge_shortExact r hr pq k hpq h)
  refine ShortComplex.isoMk (Iso.refl _)
    (HomologicalComplex.homologyMapIso (K.totalFlipIso (down ℕ)) k) (Iso.refl _) ?_ ?_
  · simp [columnFiltrationEdge_def]
  · simp [columnFiltrationToColumnOne_def, ← HomologicalComplex.homologyMap_comp_assoc]

end HomologicalComplex₂

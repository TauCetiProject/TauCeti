/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The second page of a spectral sequence from a model of its first page

Let `E` be a cohomological spectral sequence whose first page is numbered `2`, as are those of
filtered complexes and bicomplexes in Mathlib's conventions. Its differentials on the page `2` go
from `(a, b)` to `(a + 2, b - 1)`, so they preserve the lines `a + 2b = -k`. Suppose that along
such a line, parametrised by `p : ℕ` as `(-k - 2p, p)`, the objects of the page `2` are identified
with the terms of a chain complex `H` indexed by `ℕ`, so that the differentials correspond up to a
fixed sign `ε : ℤˣ`, and that the object of the line at `p = -1`, the point `(-k + 2, -1)` which
is the target of the differential leaving `(-k, 0)`, vanishes. Then the object at `(-k - 2p, p)`
of the next page (numbered `3`), which is the homology of the page `2`, is the homology of `H` in
degree `p`
(`CategoryTheory.SpectralSequence.pageThreeXIsoHomology`). On classes of cycles of the page `2`,
the identification is the class of the corresponding cycle of `H`
(`CategoryTheory.SpectralSequence.homologyπ_pageThreeXIsoHomology_hom`).

This is the form in which the classical `E₂` term of a first-quadrant spectral sequence is
computed: the first page is a family of complexes of homology objects whose differentials are
induced by the data, and the second page is their homology. For the spectral sequence of the
column filtration of a first-quadrant bicomplex, see
`TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.SecondPage`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Definition 5.2.1 (the page `E^{r+1}` is the homology of the page `E^r`).
-/

public section

noncomputable section

namespace CategoryTheory.SpectralSequence

open Limits

variable {C : Type*} [Category* C] [Abelian C] (E : E₂CohomologicalSpectralSequence C)
  (H : ChainComplex C ℕ) (k : ℕ) (ε : ℤˣ)
  (e : ∀ p : ℕ, (E.page 2 le_rfl).X (-(k : ℤ) - 2 * p, p) ≅ H.X p)
  (he : ∀ p : ℕ, (e (p + 1)).inv ≫
    (E.page 2 le_rfl).d (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ))
      (-(k : ℤ) - 2 * p, p) ≫ (e p).hom = ε • H.d (p + 1) p)
  (h₀ : IsZero ((E.page 2 le_rfl).X (-(k : ℤ) + 2, -1)))

/-- The comparison of the target `(-k - 2p + 2, p - 1)` of the differential leaving `(-k - 2p, p)`
on the page `2` with the term of `H` in degree `p - 1`: zero for `p = 0`, where the source vanishes
by `h₀`, and otherwise `ε⁻¹` times the identification `e (p - 1)`. -/
private def pageTwoXToChainComplexX : (p : ℕ) →
    ((E.page 2 le_rfl).X (-(k : ℤ) - 2 * p + 2, (p : ℤ) - 1) ⟶ H.X (p - 1))
  | 0 => 0
  | s + 1 => (ε⁻¹ • ((E.page 2 le_rfl).XIsoOfEq (Prod.ext (by omega) (by omega)) ≪≫ e s ≪≫
      H.XIsoOfEq (by omega))).hom

include h₀ in
/-- The comparison `pageTwoXToChainComplexX` is a monomorphism: its source is zero for `p = 0`, and
it is an isomorphism otherwise. -/
private lemma mono_pageTwoXToChainComplexX (p : ℕ) :
    Mono (pageTwoXToChainComplexX E H k ε e p) := by
  cases p with
  | zero => exact ⟨fun _ _ _ ↦ (h₀.of_iso ((E.page 2 le_rfl).XIsoOfEq
      (Prod.ext (by simp) (by simp)))).eq_of_tgt _ _⟩
  | succ s => exact inferInstanceAs (Mono ((ε⁻¹ • _ : _ ≅ _).hom))

include he in
/-- The differential leaving `(-k - 2p, p)`, followed by `pageTwoXToChainComplexX`, is the
differential of `H` leaving degree `p`, transported along `e p`. -/
private lemma d_pageTwoXToChainComplexX (p : ℕ) :
    (E.page 2 le_rfl).d (-(k : ℤ) - 2 * p, p) (-(k : ℤ) - 2 * p + 2, (p : ℤ) - 1) ≫
        pageTwoXToChainComplexX E H k ε e p = (e p).hom ≫ H.d p (p - 1) := by
  cases p with
  | zero =>
    rw [H.shape _ _ (by simp), comp_zero]
    simp only [pageTwoXToChainComplexX, comp_zero]
  | succ s =>
    have h := he s
    rw [Iso.inv_comp_eq] at h
    -- `h` is stated with the casts `((s + 1 : ℕ) : ℤ)` that `simp` would split, so it is used by
    -- `rw` before the signs `ε⁻¹ * ε` are cancelled
    simp only [pageTwoXToChainComplexX, Preadditive.smul_iso_hom, Units.smul_def,
      Iso.trans_hom, Preadditive.comp_zsmul, HomologicalComplex.d_comp_XIsoOfEq_hom_assoc]
    rw [reassoc_of% h]
    simp [Units.smul_def, Preadditive.comp_zsmul, smul_smul, ← Units.val_mul]

/-- The morphism from the short complex of the page `2` around `(-k - 2p, p)` to the short complex
of `H` around degree `p`. Its first two components are isomorphisms, and its third is a
monomorphism (`mono_pageTwoXToChainComplexX`). -/
private def pageTwoShortComplexHom (p : ℕ) :
    (E.page 2 le_rfl).sc' (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(k : ℤ) - 2 * p, p)
        (-(k : ℤ) - 2 * p + 2, (p : ℤ) - 1) ⟶ H.sc' (p + 1) p (p - 1) where
  τ₁ := (ε • e (p + 1)).hom
  τ₂ := (e p).hom
  τ₃ := pageTwoXToChainComplexX E H k ε e p
  comm₁₂ := by
    dsimp only [HomologicalComplex.shortComplexFunctor'_obj_f]
    have h := he p
    rw [Iso.inv_comp_eq] at h
    rw [h]
    simp [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  comm₂₃ := (d_pageTwoXToChainComplexX E H k ε e he p).symm

include h₀ in
/-- The short complex morphism `pageTwoShortComplexHom` induces an isomorphism in homology. -/
private lemma isIso_homologyMap_pageTwoShortComplexHom (p : ℕ) :
    IsIso (ShortComplex.homologyMap (pageTwoShortComplexHom E H k ε e he p)) :=
  have := mono_pageTwoXToChainComplexX E H k ε e h₀ p
  ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' _
    (inferInstanceAs (Epi (ε • e (p + 1)).hom)) (inferInstanceAs (IsIso (e p).hom))
    (inferInstanceAs (Mono (pageTwoXToChainComplexX E H k ε e p)))

/-- **The second page from a model of the first page.** If, along the line `(-k - 2p, p)`, the
objects of the page `2` of `E` are the terms of a chain complex `H`, compatibly with the
differentials up to a sign `ε`, and the object of the line at `p = -1`, the point `(-k + 2, -1)`
which is the target of the differential leaving `(-k, 0)`, vanishes, then the object at
`(-k - 2p, p)` of the page `3` is the homology of `H` in degree `p`. -/
def pageThreeXIsoHomology (p : ℕ) : (E.page 3).X (-(k : ℤ) - 2 * p, p) ≅ H.homology p :=
  have := isIso_homologyMap_pageTwoShortComplexHom E H k ε e he h₀ p
  (E.iso 2 3 (-(k : ℤ) - 2 * p, p)).symm ≪≫
    (E.page 2 le_rfl).homologyIsoSc' (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ))
      (-(k : ℤ) - 2 * p, p) (-(k : ℤ) - 2 * p + 2, (p : ℤ) - 1)
      ((ComplexShape.up' _).prev_eq' (Prod.ext (by dsimp; omega) (by dsimp; omega)))
      ((ComplexShape.up' _).next_eq' (Prod.ext (by dsimp) (by dsimp; omega))) ≪≫
    asIso (ShortComplex.homologyMap (pageTwoShortComplexHom E H k ε e he p)) ≪≫
    (H.homologyIsoSc' (p + 1) p (p - 1) (by simp) (by cases p <;> simp)).symm

include he in
/-- A cycle of the page `2` at `(-k - 2p, p)` is sent by the identification `e p` to a cycle of
`H` in degree `p`. -/
@[reassoc]
lemma iCycles_pageTwo_comp_hom_d (p : ℕ) :
    (E.page 2 le_rfl).iCycles (-(k : ℤ) - 2 * p, p) ≫ (e p).hom ≫ H.d p (p - 1) = 0 := by
  rw [← d_pageTwoXToChainComplexX E H k ε e he p, HomologicalComplex.iCycles_d_assoc, zero_comp]

/-- **The second-page identification on classes of cycles.** The class on the page `3` of a cycle
`z` of the page `2` at `(-k - 2p, p)` is sent by
`CategoryTheory.SpectralSequence.pageThreeXIsoHomology` to the class in the homology of `H` of the
cycle `(e p).hom z`. -/
@[reassoc]
lemma homologyπ_pageThreeXIsoHomology_hom (p : ℕ) :
    (E.page 2 le_rfl).homologyπ (-(k : ℤ) - 2 * p, p) ≫ (E.iso 2 3 (-(k : ℤ) - 2 * p, p)).hom ≫
        (pageThreeXIsoHomology E H k ε e he h₀ p).hom =
      H.liftCycles ((E.page 2 le_rfl).iCycles (-(k : ℤ) - 2 * p, p) ≫ (e p).hom) (p - 1)
          (by cases p <;> simp)
          (by rw [Category.assoc, iCycles_pageTwo_comp_hom_d E H k ε e he]) ≫
        H.homologyπ p := by
  have := isIso_homologyMap_pageTwoShortComplexHom E H k ε e he h₀ p
  simp only [pageThreeXIsoHomology, Iso.trans_hom, Iso.symm_hom, asIso_hom, Iso.hom_inv_id_assoc,
    HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.homologyπ_naturality_assoc,
    HomologicalComplex.π_homologyIsoSc'_inv]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono (H.iCycles p)]
  simp [pageTwoShortComplexHom]

/-- **Naturality of the second-page identification.** Let `F : E ⟶ E'` be a morphism of spectral
sequences whose component on the page `2` at `(-k - 2p, p)` corresponds, under the identifications
`e p` and `e' p`, to the component in degree `p` of a chain map `T : H ⟶ H'`. Then its component on
the page `3` corresponds, under `CategoryTheory.SpectralSequence.pageThreeXIsoHomology`, to the map
induced by `T` on homology in degree `p`. -/
lemma pageThreeXIsoHomology_hom_naturality {E' : E₂CohomologicalSpectralSequence C}
    {H' : ChainComplex C ℕ} {ε' : ℤˣ}
    {e' : ∀ p : ℕ, (E'.page 2 le_rfl).X (-(k : ℤ) - 2 * p, p) ≅ H'.X p}
    {he' : ∀ p : ℕ, (e' (p + 1)).inv ≫
      (E'.page 2 le_rfl).d (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ))
        (-(k : ℤ) - 2 * p, p) ≫ (e' p).hom = ε' • H'.d (p + 1) p}
    {h₀' : IsZero ((E'.page 2 le_rfl).X (-(k : ℤ) + 2, -1))} (F : E ⟶ E') (T : H ⟶ H') (p : ℕ)
    (hF : (F.hom 2).f (-(k : ℤ) - 2 * p, p) ≫ (e' p).hom = (e p).hom ≫ T.f p) :
    (F.hom 3).f (-(k : ℤ) - 2 * p, p) ≫ (pageThreeXIsoHomology E' H' k ε' e' he' h₀' p).hom =
      (pageThreeXIsoHomology E H k ε e he h₀ p).hom ≫ HomologicalComplex.homologyMap T p := by
  rw [← cancel_epi ((E.page 2 le_rfl).homologyπ (-(k : ℤ) - 2 * p, p) ≫
    (E.iso 2 3 (-(k : ℤ) - 2 * p, p)).hom), Category.assoc, Category.assoc, ← F.comm_assoc 2 3]
  simp only [homologyπ_pageThreeXIsoHomology_hom_assoc, HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.homologyπ_naturality_assoc, homologyπ_pageThreeXIsoHomology_hom]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono (H'.iCycles p)]
  simp [hF]

end CategoryTheory.SpectralSequence

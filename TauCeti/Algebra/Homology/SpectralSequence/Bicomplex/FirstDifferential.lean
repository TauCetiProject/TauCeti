/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.Basic
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.FirstPage

/-!
# The first differential of the spectral sequences of a bicomplex

Let `K` be a first-quadrant bicomplex, with homological differentials, in an abelian category.
The first page (numbered `2` in Mathlib's indexing) of the spectral sequence of the filtration of
its total complex by rows (`HomologicalComplex₂.rowFiltrationSpectralSequence`) is the homology of
the rows (`HomologicalComplex₂.rowFiltrationSpectralSequenceFirstPageXIso`): its object at
`(p, s)` with `p + 2s + k = 0` is the homology in degree `k` of the row `s`. This file shows that
the differential of this page, from the row `s + 1` to the row `s`, is induced by the vertical
differentials, up to the sign `(-1)^k`
(`HomologicalComplex₂.rowFiltrationSpectralSequence_page_two_d`). The rows of `K` are the columns
`K.flip.X s` of the flipped bicomplex, and the map they induce is the differential
`K.flip.d (s + 1) s`; the statement conjugates its homology map by the identifications
`HomologicalComplex₂.flipRowIso` of `K.flip`, which are identities.

The sign comes from the convention `d₁ + (-1)^p d₂` for the differential of the total complex on
the summand `(K.X p).X q`. The differential is the connecting map of the short exact sequence
`row s ⟶ Tot (rows ≥ s) ⟶ Tot (rows ≥ s + 1)`
(`HomologicalComplex₂.totalRowHomologyIso_inv_homologyMap_totalRowι_δ`): a cycle `x` of the row
`s + 1` in horizontal degree `k` lifts to itself in `Tot (rows ≥ s)`, whose differential is
`(-1)^k` times its vertical differential, in the row `s`.

Applied to the flipped bicomplex `K.flip`, whose rows are the columns `K.X p` of `K`, this says
that the first differential of `HomologicalComplex₂.columnFiltrationSpectralSequence`, from the
column `p + 1` to the column `p`, is `(-1)^k` times the map induced on homology in degree `k` by
the horizontal differential `K.d (p + 1) p`
(`HomologicalComplex₂.columnFiltrationSpectralSequence_page_two_d`). Here `k` is the vertical
degree, which is the horizontal degree of `K.flip`.

## Main results

* `HomologicalComplex₂.totalRowHomologyIso_inv_homologyMap_totalRowι_δ`: the connecting map of
  `row s ⟶ Tot (rows ≥ s) ⟶ Tot (rows ≥ s + 1)`, restricted to the row `s + 1`, is induced by the
  vertical differentials, with the sign `(-1)^k`.
* `HomologicalComplex₂.rowFiltrationSpectralSequence_page_two_d`: the first differential of the
  spectral sequence of the row filtration.
* `HomologicalComplex₂.columnFiltrationSpectralSequence_page_two_d`: the first differential of
  the spectral sequence of the column filtration.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Section 5.6.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 2.15.
-/

public section

noncomputable section

open CategoryTheory Limits ComplexShape

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Abelian C] (K : HomologicalComplex₂ C (down ℕ) (down ℕ))

/-! ### The connecting map of a row and the rows above it -/

/-- The horizontal part of the differential of the total complex vanishes on the cycles of a
row. -/
lemma iCycles_d₁ (s k n : ℕ) :
    (((HomologicalComplex.eval C (down ℕ) s).mapHomologicalComplex (down ℕ)).obj K).iCycles k ≫
      K.d₁ (down ℕ) k s n = 0 := by
  rcases k with _ | k
  · rw [d₁_eq_zero _ _ _ _ _ (by simp), comp_zero]
  · have := (((HomologicalComplex.eval C (down ℕ) s).mapHomologicalComplex
      (down ℕ)).obj K).iCycles_d (k + 1) k
    rw [d₁_eq' K _ (ComplexShape.down_mk _ _ rfl), Linear.comp_units_smul]
    simp only [Functor.mapHomologicalComplex_obj_d, HomologicalComplex.eval_map] at this
    rw [reassoc_of% this, zero_comp, smul_zero]

/-- On a cycle of the row `s + 1` in horizontal degree `k`, the differential of the total complex
of the rows `≥ s` is `(-1)^k` times the vertical differential, which lands in the row `s`. -/
lemma iCycles_ιTotalRowsGE_d (s k : ℕ) :
    (((HomologicalComplex.eval C (down ℕ) (s + 1)).mapHomologicalComplex (down ℕ)).obj
        K).iCycles k ≫
      K.ιTotalRowsGE s k (s + 1) (k + (s + 1)) (by omega) rfl ≫
      (K.totalRowsGE s).d (k + (s + 1)) (k + s) =
    ((-1 : ℤ) ^ k) • ((((HomologicalComplex.eval C (down ℕ) (s + 1)).mapHomologicalComplex
        (down ℕ)).obj K).iCycles k ≫
      (K.X k).d (s + 1) s ≫ K.ιTotalRowsGE s k s (k + s) le_rfl rfl) := by
  -- Write the summand inclusions through the total complex, whose projection is a chain map.
  rw [← K.ιTotal_toTotalRowsGE_f s k (s + 1) _ (by omega) rfl,
    ← K.ιTotal_toTotalRowsGE_f s k s _ le_rfl rfl, Category.assoc, (K.toTotalRowsGE s).comm]
  simp only [total_d, Preadditive.add_comp, Preadditive.comp_add, ι_D₁_assoc, ι_D₂_assoc,
    reassoc_of% K.iCycles_d₁, zero_comp, zero_add]
  -- The vertical part sends the row `s + 1` to the row `s`, with the sign `ε₂ = (-1)^k`.
  rw [d₂_eq K _ _ (ComplexShape.down_mk _ _ rfl) _ (by simp)]
  simp [ComplexShape.ε_down_ℕ, Units.smul_def]

/-- The connecting map of `row s ⟶ Tot (rows ≥ s) ⟶ Tot (rows ≥ s + 1)`, restricted to the row
`s + 1`, for any chain map `φ` from the row `s + 1` to the row `s` with the vertical differentials
as components. -/
private lemma totalRowHomologyIso_inv_homologyMap_totalRowι_δ_of_f (s k : ℕ)
    (φ : ((HomologicalComplex.eval C (down ℕ) (s + 1)).mapHomologicalComplex (down ℕ)).obj K ⟶
      ((HomologicalComplex.eval C (down ℕ) s).mapHomologicalComplex (down ℕ)).obj K)
    (hφ : ∀ p, φ.f p = (K.X p).d (s + 1) s) :
    (K.totalRowHomologyIso (s + 1) k).inv ≫
      HomologicalComplex.homologyMap (K.totalRowι (s + 1)) (k + (s + 1)) ≫
      (K.totalRowShortComplex_shortExact s).δ (k + (s + 1)) (k + s) (by simp; omega) ≫
      (K.totalRowHomologyIso s k).hom =
    ((-1 : ℤ) ^ k) • HomologicalComplex.homologyMap φ k := by
  let x₃ := (K.totalRow (s + 1)).iCycles (k + (s + 1)) ≫ (K.totalRowι (s + 1)).f (k + (s + 1))
  let x₂ := (K.totalRowCyclesIso (s + 1) k).hom ≫ (((HomologicalComplex.eval C (down ℕ)
    (s + 1)).mapHomologicalComplex (down ℕ)).obj K).iCycles k ≫
    K.ιTotalRowsGE s k (s + 1) (k + (s + 1)) (by omega) rfl
  let x₁ := ((-1 : ℤ) ^ k) • ((K.totalRowCyclesIso (s + 1) k).hom ≫
    (((HomologicalComplex.eval C (down ℕ) (s + 1)).mapHomologicalComplex (down ℕ)).obj
      K).iCycles k ≫ (K.X k).d (s + 1) s ≫ (K.totalRowXIso s k).inv)
  have hx₃ : x₃ ≫ (K.totalRowsGE (s + 1)).d (k + (s + 1)) (k + s) = 0 := by simp [x₃]
  have hx₁ : x₁ ≫ (K.totalRowι s).f (k + s) =
      x₂ ≫ (K.totalRowsGE s).d (k + (s + 1)) (k + s) := by
    simp only [x₁, x₂, Category.assoc, iCycles_ιTotalRowsGE_d, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, totalRowXIso_inv_totalRowι_f]
  have hδ := (K.totalRowShortComplex_shortExact s).δ_eq (k + (s + 1)) (k + s)
    (by simp; omega) x₃ hx₃ x₂ (by simp [x₂, x₃, ← totalRowXIso_inv_totalRowι_f]) x₁ hx₁ _ rfl
  have hc : HomologicalComplex.cyclesMap (K.totalRowι (s + 1)) (k + (s + 1)) =
      (K.totalRowsGE (s + 1)).liftCycles x₃ (k + s) ((down ℕ).next_eq' (by simp; omega))
        hx₃ := by
    rw [← cancel_mono ((K.totalRowsGE (s + 1)).iCycles (k + (s + 1)))]
    simp [x₃]
  have hl : ∀ h, (K.totalRow s).liftCycles x₁ _ rfl h ≫ (K.totalRowCyclesIso s k).hom =
      ((-1 : ℤ) ^ k) • ((K.totalRowCyclesIso (s + 1) k).hom ≫
        HomologicalComplex.cyclesMap φ k) := fun _ ↦ by
    simp [← cancel_mono ((((HomologicalComplex.eval C (down ℕ) s).mapHomologicalComplex
      (down ℕ)).obj K).iCycles k), x₁, hφ]
  -- Compute on the cycles: lift through `Tot (rows ≥ s)` and apply the connecting map.
  rw [Iso.inv_comp_eq, ← cancel_epi ((K.totalRow (s + 1)).homologyπ (k + (s + 1))),
    HomologicalComplex.homologyπ_naturality_assoc, hc, reassoc_of% hδ,
    homologyπ_totalRowHomologyIso_hom, reassoc_of% (hl _)]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  rw [homologyπ_totalRowHomologyIso_hom_assoc, HomologicalComplex.homologyπ_naturality]

/-- The rows of `K` are the columns `K.flip.X s` of the flipped bicomplex, and the chain map
between them induced by the vertical differentials is `K.flip.d (s + 1) s`. -/
private lemma flipRowIso_hom_d_flipRowIso_inv_f (s p : ℕ) :
    ((K.flip.flipRowIso (s + 1)).hom ≫ K.flip.d (s + 1) s ≫ (K.flip.flipRowIso s).inv).f p =
      (K.X p).d (s + 1) s := by
  simp only [HomologicalComplex.comp_f, flipRowIso_hom_f, flipRowIso_inv_f, flip_d_f]
  -- The identities are those of `(K.X p).X (s + 1)` and `(K.X p).X s`, up to unfolding `flip`.
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- **The connecting map of a row and the rows above it.** For the short exact sequence
`row s ⟶ Tot (rows ≥ s) ⟶ Tot (rows ≥ s + 1)`, the connecting map restricted to the row `s + 1`
is, in horizontal degree `k`, `(-1)^k` times the map induced on homology by the vertical
differentials, that is by the differential `K.flip.d (s + 1) s` of the flipped bicomplex, whose
columns `K.flip.X s` are the rows of `K` (`HomologicalComplex₂.flipRowIso` applied to `K.flip`). -/
theorem totalRowHomologyIso_inv_homologyMap_totalRowι_δ (s k : ℕ) :
    (K.totalRowHomologyIso (s + 1) k).inv ≫
      HomologicalComplex.homologyMap (K.totalRowι (s + 1)) (k + (s + 1)) ≫
      (K.totalRowShortComplex_shortExact s).δ (k + (s + 1)) (k + s) (by simp; omega) ≫
      (K.totalRowHomologyIso s k).hom =
    ((-1 : ℤ) ^ k) • ((HomologicalComplex.homologyMapIso (K.flip.flipRowIso (s + 1)) k).hom ≫
      HomologicalComplex.homologyMap (K.flip.d (s + 1) s) k ≫
      (HomologicalComplex.homologyMapIso (K.flip.flipRowIso s) k).inv) :=
  -- The rows of `K.flip.flip` are those of `K` by definition.
  (K.totalRowHomologyIso_inv_homologyMap_totalRowι_δ_of_f s k _
    (K.flipRowIso_hom_d_flipRowIso_inv_f s)).trans (congrArg _
      ((HomologicalComplex.homologyMap_comp _ _ _).trans
        (congrArg _ (HomologicalComplex.homologyMap_comp _ _ _))))

/-! ### Comparison with the graded pieces of the row filtration -/

/-- The rows `< s` of the total complex are killed by the projection onto the total complex of
the rows `≥ s`. -/
lemma filtrationFunctorArrow_extendMap_toTotalRowsGE (s : ℕ) :
    CochainComplex.filtrationFunctorArrow K.rowFiltration K.monotone_rowFiltration
        ((s : ℤ) : EInt) ≫
      HomologicalComplex.extendMap (K.toTotalRowsGE s) embeddingDownNat = 0 := by
  rw [← cancel_epi (eqToHom (CochainComplex.filtrationFunctor_obj_coe _ _ (s : ℤ)).symm),
    comp_zero, ← Category.assoc, CochainComplex.eqToHom_comp_filtrationFunctorArrow,
    rowFiltration_natCast]
  exact kernelSubobject_arrow_comp _

/-- The map `F_{s+1}/F_s ⟶ row s`, the index `s + 1` of the filtration being written
`((s + 1 : ℕ) : ℤ)`, induced by `HomologicalComplex₂.rowFiltrationGradedIso`. -/
private def rowFiltrationGradedToTotalRow (s : ℕ) :
    cokernel ((CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration).map
      (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : (s : ℤ) = s)
        (Nat.cast_succ s)))) ⟶ (K.totalRow s).extend embeddingDownNat :=
  cokernel.map _ _ (𝟙 _)
    ((CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration).map
      (homOfLE (by simp)))
    (by rw [Category.id_comp, ← Functor.map_comp]; exact congrArg _ (Subsingleton.elim _ _)) ≫
    (K.rowFiltrationGradedIso s).hom

/-- The map `F_{s+2}/F_s ⟶ Tot (rows ≥ s)` induced by the projection of the total complex. -/
private def rowFiltrationCokernelToTotalRowsGE (s : ℕ) :
    cokernel ((CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration).map
      (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : (s : ℤ) = s)
        (Nat.cast_succ s))) ≫
      (CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one
          (rfl : ((s + 1 : ℕ) : ℤ) = (s + 1 : ℕ)) rfl))) ⟶
      (K.totalRowsGE s).extend embeddingDownNat :=
  cokernel.desc _ (CochainComplex.filtrationFunctorArrow K.rowFiltration
      K.monotone_rowFiltration (((s + 1 : ℕ) : ℤ) + 1 : ℤ) ≫
    HomologicalComplex.extendMap (K.toTotalRowsGE s) embeddingDownNat) (by
      simpa using K.filtrationFunctorArrow_extendMap_toTotalRowsGE s)

@[reassoc]
private lemma π_rowFiltrationGradedToTotalRow (s : ℕ) :
    cokernel.π _ ≫ K.rowFiltrationGradedToTotalRow s ≫
      HomologicalComplex.extendMap (K.totalRowι s) embeddingDownNat =
    CochainComplex.filtrationFunctorArrow K.rowFiltration K.monotone_rowFiltration
        ((s + 1 : ℕ) : ℤ) ≫
      HomologicalComplex.extendMap (K.toTotalRowsGE s) embeddingDownNat := by
  rw [rowFiltrationGradedToTotalRow, Category.assoc, cokernel.π_desc_assoc, Category.assoc,
    π_rowFiltrationGradedIso_hom_totalRowι]
  simp

private lemma rowFiltrationGradedToTotalRow_comp_extendMap_totalRowι (s : ℕ) :
    K.rowFiltrationGradedToTotalRow s ≫
      HomologicalComplex.extendMap (K.totalRowι s) embeddingDownNat =
    cokernel.map _ _ (𝟙 _)
      ((CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one
          (rfl : ((s + 1 : ℕ) : ℤ) = (s + 1 : ℕ)) rfl))) (by simp) ≫
      K.rowFiltrationCokernelToTotalRowsGE s := by
  rw [← cancel_epi (cokernel.π _), π_rowFiltrationGradedToTotalRow, cokernel.π_desc_assoc]
  simp [rowFiltrationCokernelToTotalRowsGE]

private lemma rowFiltrationCokernelToTotalRowsGE_comp_extendMap_totalRowsGEMap (s : ℕ) :
    K.rowFiltrationCokernelToTotalRowsGE s ≫
      HomologicalComplex.extendMap (K.totalRowsGEMap s) embeddingDownNat =
    cokernel.map _ _
      ((CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : (s : ℤ) = s)
          (Nat.cast_succ s)))) (𝟙 _) (by simp) ≫
      (K.rowFiltrationGradedIso (s + 1)).hom ≫
      HomologicalComplex.extendMap (K.totalRowι (s + 1)) embeddingDownNat := by
  rw [← cancel_epi (cokernel.π _), cokernel.π_desc_assoc]
  simp [rowFiltrationCokernelToTotalRowsGE, ← HomologicalComplex.extendMap_comp]

/-- The morphism from the short exact sequence `F_{s+1}/F_s ⟶ F_{s+2}/F_s ⟶ F_{s+2}/F_{s+1}` of
graded pieces of the row filtration to `row s ⟶ Tot (rows ≥ s) ⟶ Tot (rows ≥ s + 1)`. -/
private def rowFiltrationShortComplexHom (s : ℕ) :
    TauCeti.cokernelCompSequence
      ((CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : (s : ℤ) = s)
          (Nat.cast_succ s))))
      ((CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one
          (rfl : ((s + 1 : ℕ) : ℤ) = (s + 1 : ℕ)) rfl))) ⟶
      (K.totalRowShortComplex s).map (embeddingDownNat.extendFunctor C) :=
  ShortComplex.homMk (K.rowFiltrationGradedToTotalRow s) (K.rowFiltrationCokernelToTotalRowsGE s)
    ((K.rowFiltrationGradedIso (s + 1)).hom ≫
      HomologicalComplex.extendMap (K.totalRowι (s + 1)) embeddingDownNat)
    (K.rowFiltrationGradedToTotalRow_comp_extendMap_totalRowι s)
    (K.rowFiltrationCokernelToTotalRowsGE_comp_extendMap_totalRowsGEMap s)

private lemma rowFiltrationShortComplexHom_τ₁ (s : ℕ) :
    (K.rowFiltrationShortComplexHom s).τ₁ = K.rowFiltrationGradedToTotalRow s :=
  (rfl)

private lemma rowFiltrationShortComplexHom_τ₃ (s : ℕ) :
    (K.rowFiltrationShortComplexHom s).τ₃ = (K.rowFiltrationGradedIso (s + 1)).hom ≫
      HomologicalComplex.extendMap (K.totalRowι (s + 1)) embeddingDownNat :=
  (rfl)

/-- Under the identifications
`HomologicalComplex₂.rowFiltrationSpectralSequenceFirstPageXIsoTotalRow` of the first page with
the homology of the rows placed in the degrees of the total complex, the first differential from
the row `s + 1` to the row `s` is the connecting map of the short exact sequence
`row s ⟶ Tot (rows ≥ s) ⟶ Tot (rows ≥ s + 1)`, restricted to the row `s + 1`. -/
lemma rowFiltrationSpectralSequence_page_two_d_totalRow (p : ℤ) (s : ℕ) :
    (K.rowFiltrationSpectralSequenceFirstPageXIsoTotalRow p (s + 1)).inv ≫
      (K.rowFiltrationSpectralSequence.page 2).d (p, (s + 1 : ℕ)) (p + 2, s) ≫
      (K.rowFiltrationSpectralSequenceFirstPageXIsoTotalRow (p + 2) s).hom =
    HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap (K.totalRowι (s + 1)) embeddingDownNat)
        (p + (s + 1 : ℕ)) ≫
      ((K.totalRowShortComplex_shortExact s).extend embeddingDownNat).δ (p + (s + 1 : ℕ))
        (p + 2 + s) (by simp; omega) := by
  have h := CochainComplex.spectralSequence_first_page_d_eq_cokernelMap
    (CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration) p (p + 2) s
    (s + 1 : ℕ) (s + 1) ((s + 1 : ℕ) + 1) (p + (s + 1 : ℕ)) (p + 2 + s) rfl
    (Nat.cast_succ s).symm rfl (Nat.cast_succ s) rfl (by push_cast; ring)
  have hφ := HomologicalComplex.HomologySequence.δ_naturality (K.rowFiltrationShortComplexHom s)
    (TauCeti.cokernelCompSequence_shortExact _ _)
    ((K.totalRowShortComplex_shortExact s).extend embeddingDownNat) (p + (s + 1 : ℕ))
    (p + 2 + s) (by simp; omega)
  rw [rowFiltrationSpectralSequenceFirstPageXIsoTotalRow_eq,
    rowFiltrationSpectralSequenceFirstPageXIsoTotalRow_eq]
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc,
    HomologicalComplex.homologyMapIso_inv, HomologicalComplex.homologyMapIso_hom]
  rw [reassoc_of% h]
  -- The first component of `HomologicalComplex₂.rowFiltrationShortComplexHom` is the composite
  -- of the comparison of cokernels with `HomologicalComplex₂.rowFiltrationGradedIso s`, and its
  -- third component is `HomologicalComplex₂.rowFiltrationGradedIso (s + 1)` followed by the
  -- inclusion of the row `s + 1`.
  have hτ₃ : HomologicalComplex.homologyMap (K.rowFiltrationGradedIso (s + 1)).inv _ ≫
      HomologicalComplex.homologyMap (K.rowFiltrationShortComplexHom s).τ₃ (p + (s + 1 : ℕ)) =
      HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap (K.totalRowι (s + 1)) embeddingDownNat) _ := by
    rw [rowFiltrationShortComplexHom_τ₃]
    exact (HomologicalComplex.homologyMap_comp _ _ _).symm.trans
      (congrArg (HomologicalComplex.homologyMap · _) (Iso.inv_hom_id_assoc _ _))
  rw [← hτ₃, Category.assoc, ← hφ, rowFiltrationShortComplexHom_τ₁, rowFiltrationGradedToTotalRow,
    ← HomologicalComplex.homologyMap_comp]

/-- The form of `HomologicalComplex₂.rowFiltrationSpectralSequence_page_two_d_totalRow` in which
the homology of the rows placed in the degrees of the total complex, regarded as cochain
complexes, is identified with that of the chain complexes. -/
lemma rowFiltrationSpectralSequence_page_two_d_totalRow_extendHomologyIso (p : ℤ) (s k : ℕ)
    (hp : p + 2 * ((s + 1 : ℕ) : ℤ) + k = 0) :
    (K.rowFiltrationSpectralSequenceFirstPageXIsoTotalRow p (s + 1)).inv ≫
      (K.rowFiltrationSpectralSequence.page 2).d (p, (s + 1 : ℕ)) (p + 2, s) ≫
      (K.rowFiltrationSpectralSequenceFirstPageXIsoTotalRow (p + 2) s).hom ≫
      ((K.totalRow s).extendHomologyIso embeddingDownNat (j := k + s) (by simp; omega)).hom =
    ((K.totalRow (s + 1)).extendHomologyIso embeddingDownNat (j := k + (s + 1))
        (by simp; omega)).hom ≫
      HomologicalComplex.homologyMap (K.totalRowι (s + 1)) (k + (s + 1)) ≫
      (K.totalRowShortComplex_shortExact s).δ (k + (s + 1)) (k + s) (by simp; omega) := by
  -- The connecting maps and the homology maps commute with the extension along
  -- `embeddingDownNat`.
  have hi : embeddingDownNat.f (k + (s + 1)) = p + (s + 1 : ℕ) := by simp; omega
  have hδ := ShortComplex.ShortExact.extend_δ_comp_extendHomologyIso_hom
    (K.totalRowShortComplex_shortExact s) embeddingDownNat
    (show (down ℕ).Rel (k + (s + 1)) (k + s) by simp; omega) hi
    (show embeddingDownNat.f (k + s) = p + 2 + s by simp; omega) (by simp; omega)
  have hι := HomologicalComplex.extendHomologyIso_hom_naturality (K.totalRowι (s + 1))
    embeddingDownNat hi
  rw [reassoc_of% (K.rowFiltrationSpectralSequence_page_two_d_totalRow p s)]
  -- The objects of the extended sequence are only definitionally the extended complexes, so the
  -- steps are given as terms: `hδ` for the connecting maps, then `hι` for the homology maps.
  calc _ = HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap (K.totalRowι (s + 1)) embeddingDownNat) _ ≫ _ ≫
          (K.totalRowShortComplex_shortExact s).δ (k + (s + 1)) (k + s) _ :=
        congrArg _ hδ
    _ = _ := (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) hι).trans (Category.assoc _ _ _))

/-! ### The first differentials -/

/-- The first differential of the spectral sequence of the row filtration, for any chain map `φ`
from the row `s + 1` to the row `s` with the vertical differentials as components. -/
private lemma rowFiltrationSpectralSequence_page_two_d_of_f (p p' : ℤ) (s k : ℕ)
    (hp : p + 2 * ((s + 1 : ℕ) : ℤ) + k = 0) (hp' : p' + 2 * (s : ℤ) + k = 0)
    (φ : ((HomologicalComplex.eval C (down ℕ) (s + 1)).mapHomologicalComplex (down ℕ)).obj K ⟶
      ((HomologicalComplex.eval C (down ℕ) s).mapHomologicalComplex (down ℕ)).obj K)
    (hφ : ∀ p, φ.f p = (K.X p).d (s + 1) s) :
    (K.rowFiltrationSpectralSequenceFirstPageXIso p (s + 1) k hp).inv ≫
      (K.rowFiltrationSpectralSequence.page 2).d (p, (s + 1 : ℕ)) (p', s) ≫
      (K.rowFiltrationSpectralSequenceFirstPageXIso p' s k hp').hom =
    ((-1 : ℤ) ^ k) • HomologicalComplex.homologyMap φ k := by
  obtain rfl : p' = p + 2 := by omega
  rw [rowFiltrationSpectralSequenceFirstPageXIso_eq,
    rowFiltrationSpectralSequenceFirstPageXIso_eq]
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
  rw [reassoc_of%
      (K.rowFiltrationSpectralSequence_page_two_d_totalRow_extendHomologyIso p s k hp),
    Iso.inv_hom_id_assoc]
  exact K.totalRowHomologyIso_inv_homologyMap_totalRowι_δ_of_f s k φ hφ

/-- **The first differential of the spectral sequence of the row filtration.** On the first page
(numbered `2`), the differential from `(p, s + 1)` to `(p', s)`, where `p + 2(s + 1) + k = 0` and
`p' + 2s + k = 0`, is, under the identifications
`HomologicalComplex₂.rowFiltrationSpectralSequenceFirstPageXIso` with the homology of the rows in
degree `k`, the map induced by the vertical differentials `(K.X p).d (s + 1) s`, multiplied by
`(-1)^k`. This map is the differential `K.flip.d (s + 1) s` of the flipped bicomplex, whose columns
`K.flip.X s` are the rows of `K` (`HomologicalComplex₂.flipRowIso` applied to `K.flip`). -/
theorem rowFiltrationSpectralSequence_page_two_d (p p' : ℤ) (s k : ℕ)
    (hp : p + 2 * ((s + 1 : ℕ) : ℤ) + k = 0) (hp' : p' + 2 * (s : ℤ) + k = 0) :
    (K.rowFiltrationSpectralSequenceFirstPageXIso p (s + 1) k hp).inv ≫
      (K.rowFiltrationSpectralSequence.page 2).d (p, (s + 1 : ℕ)) (p', s) ≫
      (K.rowFiltrationSpectralSequenceFirstPageXIso p' s k hp').hom =
    ((-1 : ℤ) ^ k) • ((HomologicalComplex.homologyMapIso (K.flip.flipRowIso (s + 1)) k).hom ≫
      HomologicalComplex.homologyMap (K.flip.d (s + 1) s) k ≫
      (HomologicalComplex.homologyMapIso (K.flip.flipRowIso s) k).inv) :=
  -- The rows of `K.flip.flip` are those of `K` by definition.
  (K.rowFiltrationSpectralSequence_page_two_d_of_f p p' s k hp hp' _
    (K.flipRowIso_hom_d_flipRowIso_inv_f s)).trans (congrArg _
      ((HomologicalComplex.homologyMap_comp _ _ _).trans
        (congrArg _ (HomologicalComplex.homologyMap_comp _ _ _))))

/-- **The first differential of the spectral sequence of the column filtration.** On the first
page (numbered `2`), the differential from `(-k - 2(p + 1), p + 1)` to `(-k - 2p, p)` is, under
the identifications `HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso` with the
vertical homology of the columns in degree `k`, the map induced by the horizontal differential
`K.d (p + 1) p : K.X (p + 1) ⟶ K.X p`, multiplied by `(-1)^k`. -/
theorem columnFiltrationSpectralSequence_page_two_d (p k : ℕ) :
    (K.columnFiltrationSpectralSequenceFirstPageXIso (p + 1) k).inv ≫
      (K.columnFiltrationSpectralSequence.page 2).d
        (-(k : ℤ) - 2 * ((p + 1 : ℕ) : ℤ), (p + 1 : ℕ)) (-(k : ℤ) - 2 * p, p) ≫
      (K.columnFiltrationSpectralSequenceFirstPageXIso p k).hom =
    ((-1 : ℤ) ^ k) • HomologicalComplex.homologyMap (K.d (p + 1) p) k := by
  rw [columnFiltrationSpectralSequenceFirstPageXIso_eq,
    columnFiltrationSpectralSequenceFirstPageXIso_eq]
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc,
    HomologicalComplex.homologyMapIso_inv, HomologicalComplex.homologyMapIso_hom]
  rw [reassoc_of% (K.flip.rowFiltrationSpectralSequence_page_two_d_of_f _ _ p k (by omega)
      (by omega) ((K.flipRowIso (p + 1)).hom ≫ K.d (p + 1) p ≫ (K.flipRowIso p).inv)
      -- The identities are those of `(K.X (p + 1)).X q` and `(K.X p).X q`, up to unfolding
      -- `flip`.
      (fun q ↦ by
        simp only [HomologicalComplex.comp_f, flipRowIso_hom_f, flipRowIso_inv_f, flip_X_d]
        exact (Category.id_comp _).trans (Category.comp_id _))),
    Preadditive.zsmul_comp, Preadditive.comp_zsmul, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]
  simp

end HomologicalComplex₂

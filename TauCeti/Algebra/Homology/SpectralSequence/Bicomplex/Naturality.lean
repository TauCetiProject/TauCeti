/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.Basic
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality

/-!
# Naturality of the spectral sequences of a first-quadrant bicomplex

A morphism `φ : K ⟶ L` of first-quadrant bicomplexes induces a morphism of total complexes which
sends the rows `< q` of `K` into the rows `< q` of `L` (`HomologicalComplex₂.rowFiltration_factors`,
through `HomologicalComplex₂.mapTotalRowsGE`). It therefore induces a morphism of the filtration
functors of the row filtrations (`HomologicalComplex₂.rowFiltrationFunctorMap`), of
their spectral objects (`HomologicalComplex₂.rowFiltrationSpectralObjectMap`) and of their spectral
sequences (`HomologicalComplex₂.rowFiltrationSpectralSequenceMap`), compatibly with identities and
composition. On the abutment, identified with the homology of the total complex by
`HomologicalComplex₂.rowFiltrationAbutmentIso`, the morphism of spectral objects is the map induced
on homology by the morphism of total complexes
(`HomologicalComplex₂.rowFiltrationSpectralObjectMap_abutment_naturality`).

Applied to the flipped morphism, this gives the same for the column filtrations; on the abutment,
identified by `HomologicalComplex₂.columnFiltrationAbutmentIso`, it is again the map induced on
the homology of the original total complexes
(`HomologicalComplex₂.columnFiltrationSpectralObjectMap_abutment_naturality`).

On the first page, identified with the homology of the rows, the morphism of spectral sequences is
the map induced in homology by the morphisms of rows
(`HomologicalComplex₂.rowFiltrationSpectralSequenceFirstPageXIso_hom_naturality`). This comes from
the naturality of the identification of the graded pieces of the row filtration with the rows
(`HomologicalComplex₂.rowFiltrationGradedIso_hom_naturality`). For the column filtrations, it is
the map induced in homology by the components `φ.f p` on the columns
(`HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso_hom_naturality`).

## Main definitions and results

* `HomologicalComplex₂.rowFiltrationFunctorMap`,
  `HomologicalComplex₂.rowFiltrationSpectralObjectMap`,
  `HomologicalComplex₂.rowFiltrationSpectralSequenceMap`: the induced morphisms, compatible
  with identities and composition, and their column versions
  `HomologicalComplex₂.columnFiltrationSpectralObjectMap`,
  `HomologicalComplex₂.columnFiltrationSpectralSequenceMap`, the latter described by
  `HomologicalComplex₂.columnFiltrationSpectralSequenceMap_eq`.
* `HomologicalComplex₂.rowFiltrationSpectralObjectMap_abutment_naturality`,
  `HomologicalComplex₂.columnFiltrationSpectralObjectMap_abutment_naturality`: the induced
  morphisms on the abutments.
* `HomologicalComplex₂.rowFiltrationSpectralSequenceFirstPageXIsoTotalRow_hom_naturality`,
  `HomologicalComplex₂.rowFiltrationSpectralSequenceFirstPageXIso_hom_naturality`,
  `HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso_hom_naturality`: the induced
  morphisms on the first pages.
-/

public section

noncomputable section

open CategoryTheory Limits ComplexShape ComposableArrows

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Abelian C]

variable {K L M : HomologicalComplex₂ C (down ℕ) (down ℕ)} (φ : K ⟶ L) (ψ : L ⟶ M)

/-- A morphism of bicomplexes sends the rows `< q` of the total complex into the rows `< q`. -/
lemma rowFiltration_factors (q : ℤ) :
    (L.rowFiltration q).Factors ((K.rowFiltration q).arrow ≫
      HomologicalComplex.extendMap (total.map φ (down ℕ)) embeddingDownNat) := by
  rw [rowFiltration_toNat L, rowFiltration_natCast]
  refine (kernelSubobject_factors_iff _ _).2 ?_
  rw [Category.assoc, ← HomologicalComplex.extendMap_comp, ← toTotalRowsGE_naturality,
    HomologicalComplex.extendMap_comp, rowFiltration_toNat K, rowFiltration_natCast,
    kernelSubobject_arrow_comp_assoc, zero_comp]

/-- The morphism of the filtration functors of the row filtrations induced by a morphism of
bicomplexes. -/
def rowFiltrationFunctorMap :
    CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration ⟶
      CochainComplex.filtrationFunctor L.rowFiltration L.monotone_rowFiltration :=
  CochainComplex.filtrationFunctorMap _ _ _ (rowFiltration_factors φ)

/-- On each stage, the morphism of filtration functors is the restriction of the morphism of
total complexes. -/
@[reassoc (attr := simp)]
lemma rowFiltrationFunctorMap_app_comp (a : EInt) :
    (rowFiltrationFunctorMap φ).app a ≫
        (CochainComplex.filtrationFunctorObjIso L.rowFiltration L.monotone_rowFiltration a).hom ≫
        (CochainComplex.filtrationEInt L.rowFiltration a).arrow =
      (CochainComplex.filtrationFunctorObjIso K.rowFiltration K.monotone_rowFiltration a).hom ≫
        (CochainComplex.filtrationEInt K.rowFiltration a).arrow ≫
        HomologicalComplex.extendMap (total.map φ (down ℕ)) embeddingDownNat :=
  CochainComplex.filtrationFunctorMap_app_comp _ _ a

/-- The morphism `HomologicalComplex₂.rowFiltrationFunctorMap φ` is the morphism of filtration
functors induced by the morphism of total complexes. -/
lemma rowFiltrationFunctorMap_def :
    rowFiltrationFunctorMap φ =
      CochainComplex.filtrationFunctorMap _ _ _ (rowFiltration_factors φ) :=
  (rfl)

/-- The morphism of the spectral objects of the row filtrations induced by a morphism of
bicomplexes. -/
abbrev rowFiltrationSpectralObjectMap :
    K.rowFiltrationSpectralObject ⟶ L.rowFiltrationSpectralObject :=
  CochainComplex.spectralObjectMap (rowFiltrationFunctorMap φ)

/-- The morphism of the spectral sequences of the row filtrations induced by a morphism of
bicomplexes. -/
abbrev rowFiltrationSpectralSequenceMap :
    K.rowFiltrationSpectralSequence ⟶ L.rowFiltrationSpectralSequence :=
  Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
    (rowFiltrationSpectralObjectMap φ)

@[simp]
lemma rowFiltrationFunctorMap_id : rowFiltrationFunctorMap (𝟙 K) = 𝟙 _ := by
  rw [rowFiltrationFunctorMap, CochainComplex.filtrationFunctorMap_congr (f' := 𝟙 _) (by simp)]
  exact CochainComplex.filtrationFunctorMap_id _

@[simp]
lemma rowFiltrationFunctorMap_comp :
    rowFiltrationFunctorMap (φ ≫ ψ) = rowFiltrationFunctorMap φ ≫ rowFiltrationFunctorMap ψ := by
  rw [rowFiltrationFunctorMap, CochainComplex.filtrationFunctorMap_congr
    (f' := HomologicalComplex.extendMap (total.map φ (down ℕ)) embeddingDownNat ≫
      HomologicalComplex.extendMap (total.map ψ (down ℕ)) embeddingDownNat)
    (by simp [HomologicalComplex.extendMap_comp])]
  exact CochainComplex.filtrationFunctorMap_comp _ _ _ _ _

@[simp]
lemma rowFiltrationSpectralObjectMap_id : rowFiltrationSpectralObjectMap (𝟙 K) = 𝟙 _ := by
  simp [rowFiltrationSpectralObjectMap]

@[simp]
lemma rowFiltrationSpectralObjectMap_comp :
    rowFiltrationSpectralObjectMap (φ ≫ ψ) =
      rowFiltrationSpectralObjectMap φ ≫ rowFiltrationSpectralObjectMap ψ := by
  simp [rowFiltrationSpectralObjectMap, CochainComplex.spectralObjectMap_comp]

@[simp]
lemma rowFiltrationSpectralSequenceMap_id : rowFiltrationSpectralSequenceMap (𝟙 K) = 𝟙 _ := by
  simp [rowFiltrationSpectralSequenceMap, Abelian.SpectralObject.spectralSequenceMap_id]

@[simp]
lemma rowFiltrationSpectralSequenceMap_comp :
    rowFiltrationSpectralSequenceMap (φ ≫ ψ) =
      rowFiltrationSpectralSequenceMap φ ≫ rowFiltrationSpectralSequenceMap ψ := by
  simp [rowFiltrationSpectralSequenceMap, rowFiltrationSpectralObjectMap_comp,
    Abelian.SpectralObject.spectralSequenceMap_comp]

/-- The morphism of the spectral objects of the column filtrations induced by a morphism of
bicomplexes: that of the row filtrations of the flipped bicomplexes. -/
abbrev columnFiltrationSpectralObjectMap :
    K.flip.rowFiltrationSpectralObject ⟶ L.flip.rowFiltrationSpectralObject :=
  rowFiltrationSpectralObjectMap ((flipFunctor C _ _).map φ)

/-- The morphism of the spectral sequences of the column filtrations induced by a morphism of
bicomplexes: that of the row filtrations of the flipped bicomplexes. -/
abbrev columnFiltrationSpectralSequenceMap :
    K.columnFiltrationSpectralSequence ⟶ L.columnFiltrationSpectralSequence :=
  rowFiltrationSpectralSequenceMap ((flipFunctor C _ _).map φ)

/-- The morphism of the spectral sequences of the column filtrations is that of the row
filtrations along the morphism `K.flip ⟶ L.flip` of flipped bicomplexes induced by `φ`. -/
lemma columnFiltrationSpectralSequenceMap_eq :
    columnFiltrationSpectralSequenceMap φ =
      rowFiltrationSpectralSequenceMap (K := K.flip) (L := L.flip) ((flipFunctor C _ _).map φ) :=
  -- `(flipFunctor C _ _).obj K` is `K.flip` by definition
  (rfl)

-- The identity of `(flipFunctor C _ _).obj K` is that of `K.flip` only after unfolding
-- `flipFunctor`, so the lemmas on the flipped bicomplexes are applied up to that unfolding.
@[simp]
lemma columnFiltrationSpectralObjectMap_id : columnFiltrationSpectralObjectMap (𝟙 K) = 𝟙 _ := by
  rw [columnFiltrationSpectralObjectMap, CategoryTheory.Functor.map_id]
  exact rowFiltrationSpectralObjectMap_id

@[simp]
lemma columnFiltrationSpectralObjectMap_comp :
    columnFiltrationSpectralObjectMap (φ ≫ ψ) =
      columnFiltrationSpectralObjectMap φ ≫ columnFiltrationSpectralObjectMap ψ := by
  rw [columnFiltrationSpectralObjectMap, CategoryTheory.Functor.map_comp,
    rowFiltrationSpectralObjectMap_comp]

@[simp]
lemma columnFiltrationSpectralSequenceMap_id :
    columnFiltrationSpectralSequenceMap (𝟙 K) = 𝟙 _ := by
  rw [columnFiltrationSpectralSequenceMap, CategoryTheory.Functor.map_id]
  exact rowFiltrationSpectralSequenceMap_id

@[simp]
lemma columnFiltrationSpectralSequenceMap_comp :
    columnFiltrationSpectralSequenceMap (φ ≫ ψ) =
      columnFiltrationSpectralSequenceMap φ ≫ columnFiltrationSpectralSequenceMap ψ := by
  rw [columnFiltrationSpectralSequenceMap, CategoryTheory.Functor.map_comp,
    rowFiltrationSpectralSequenceMap_comp]

open CochainComplex in
/-- **Naturality on the abutment.** Through `HomologicalComplex₂.rowFiltrationAbutmentIso`, the
morphism of spectral objects induced by `φ` is, on the abutment in degree `-n`, the map induced on
the homology of the total complexes in degree `n`. -/
@[reassoc]
lemma rowFiltrationSpectralObjectMap_abutment_naturality (n : ℕ) :
    ((rowFiltrationSpectralObjectMap φ).hom (-n)).app
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫ (L.rowFiltrationAbutmentIso n).hom =
      (K.rowFiltrationAbutmentIso n).hom ≫
        HomologicalComplex.homologyMap (total.map φ (down ℕ)) n := by
  rw [rowFiltrationAbutmentIso_hom, rowFiltrationAbutmentIso_hom, rowFiltrationSpectralObjectMap,
    rowFiltrationFunctorMap,
    spectralObjectMap_filtrationFunctorMap_hom_app_comp_filtrationAbutmentIso_hom_assoc,
    Category.assoc, HomologicalComplex.extendHomologyIso_hom_naturality]

/-- **Naturality on the abutment of the column filtration.** Through
`HomologicalComplex₂.columnFiltrationAbutmentIso`, the morphism of spectral objects of the column
filtrations induced by `φ` is, on the abutment in degree `-n`, the map induced on the homology of
the total complexes in degree `n`. -/
@[reassoc]
lemma columnFiltrationSpectralObjectMap_abutment_naturality (n : ℕ) :
    ((columnFiltrationSpectralObjectMap φ).hom (-n)).app
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫ (L.columnFiltrationAbutmentIso n).hom =
      (K.columnFiltrationAbutmentIso n).hom ≫
        HomologicalComplex.homologyMap (total.map φ (down ℕ)) n := by
  rw [columnFiltrationAbutmentIso_hom, columnFiltrationAbutmentIso_hom]
  -- `(flipFunctor C _ _).map φ` is a morphism `K.flip ⟶ L.flip` only after unfolding
  -- `flipFunctor`, so the naturality on the flipped bicomplexes is applied up to that unfolding
  refine (rowFiltrationSpectralObjectMap_abutment_naturality_assoc
    ((flipFunctor C _ _).map φ) n _).trans ?_
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]
  rw [total_map_flip_totalFlipIso_hom φ (down ℕ)]
  -- `(flipFunctor C _ _).obj K` is `K.flip` by definition
  rfl

/-! ### The first page -/

/-- The identification `HomologicalComplex₂.rowFiltrationGradedIso` of the graded pieces of the row
filtration with the rows is natural: the morphism of graded pieces induced by
`HomologicalComplex₂.rowFiltrationFunctorMap φ` is the morphism of rows `mapTotalRow s φ`. -/
@[reassoc]
lemma rowFiltrationGradedIso_hom_naturality (s : ℕ) :
    cokernel.map
        ((CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration).map
          (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : (s : ℤ) = s) rfl)))
        ((CochainComplex.filtrationFunctor L.rowFiltration L.monotone_rowFiltration).map
          (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : (s : ℤ) = s) rfl)))
        ((rowFiltrationFunctorMap φ).app _) ((rowFiltrationFunctorMap φ).app _)
        ((rowFiltrationFunctorMap φ).naturality _).symm ≫ (L.rowFiltrationGradedIso s).hom =
      (K.rowFiltrationGradedIso s).hom ≫
        HomologicalComplex.extendMap (mapTotalRow s φ) embeddingDownNat := by
  have : Mono (HomologicalComplex.extendMap (L.totalRowι s) embeddingDownNat) :=
    ((L.totalRowShortComplex_shortExact s).extend embeddingDownNat).mono_f
  rw [← cancel_epi (cokernel.π _),
    ← cancel_mono (HomologicalComplex.extendMap (L.totalRowι s) embeddingDownNat)]
  simp only [Category.assoc, cokernel.π_desc_assoc, π_rowFiltrationGradedIso_hom_totalRowι,
    rowFiltrationFunctorMap_app_comp_assoc]
  rw [← HomologicalComplex.extendMap_comp (mapTotalRow s φ), ← totalRowι_naturality,
    HomologicalComplex.extendMap_comp, π_rowFiltrationGradedIso_hom_totalRowι_assoc,
    ← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    toTotalRowsGE_naturality]

/-- **The morphism of spectral sequences of the row filtrations on the first page**, through the
identifications `HomologicalComplex₂.rowFiltrationSpectralSequenceFirstPageXIsoTotalRow`: it is the
map induced in homology by the morphism of rows `HomologicalComplex₂.mapTotalRow s φ`. -/
@[reassoc]
lemma rowFiltrationSpectralSequenceFirstPageXIsoTotalRow_hom_naturality (p : ℤ) (s : ℕ) :
    ((rowFiltrationSpectralSequenceMap φ).hom 2).f (p, s) ≫
        (L.rowFiltrationSpectralSequenceFirstPageXIsoTotalRow p s).hom =
      (K.rowFiltrationSpectralSequenceFirstPageXIsoTotalRow p s).hom ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap (mapTotalRow s φ) embeddingDownNat) (p + s) := by
  rw [rowFiltrationSpectralSequenceFirstPageXIsoTotalRow_eq,
    rowFiltrationSpectralSequenceFirstPageXIsoTotalRow_eq, Iso.trans_hom, Iso.trans_hom,
    CochainComplex.spectralSequenceFirstPageXIsoCokernel_hom_naturality_assoc,
    HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_hom,
    ← HomologicalComplex.homologyMap_comp, rowFiltrationGradedIso_hom_naturality,
    HomologicalComplex.homologyMap_comp, Category.assoc]

/-- **The morphism of spectral sequences of the row filtrations on the first page**: through the
identifications `HomologicalComplex₂.rowFiltrationSpectralSequenceFirstPageXIso` of the first pages
with the homology of the rows, it is the map induced in homology by the morphism of rows `s`. -/
@[reassoc]
lemma rowFiltrationSpectralSequenceFirstPageXIso_hom_naturality (p : ℤ) (s k : ℕ)
    (hp : p + 2 * s + k = 0) :
    ((rowFiltrationSpectralSequenceMap φ).hom 2).f (p, s) ≫
        (L.rowFiltrationSpectralSequenceFirstPageXIso p s k hp).hom =
      (K.rowFiltrationSpectralSequenceFirstPageXIso p s k hp).hom ≫
        HomologicalComplex.homologyMap
          (((HomologicalComplex.eval C (down ℕ) s).mapHomologicalComplex (down ℕ)).map φ) k := by
  simp only [rowFiltrationSpectralSequenceFirstPageXIso_eq, Iso.trans_hom,
    rowFiltrationSpectralSequenceFirstPageXIsoTotalRow_hom_naturality_assoc,
    HomologicalComplex.extendHomologyIso_hom_naturality_assoc,
    totalRowHomologyIso_hom_naturality, Category.assoc]

/-- **The morphism of spectral sequences of the column filtrations on the first page**: through
the identifications `HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso` of the
first pages with the homology of the columns, it is the map induced in homology by the component
`φ.f p` of `φ` on the columns `p`. -/
@[reassoc]
lemma columnFiltrationSpectralSequenceFirstPageXIso_hom_naturality (p k : ℕ) :
    ((columnFiltrationSpectralSequenceMap φ).hom 2).f (-(k : ℤ) - 2 * p, p) ≫
        (L.columnFiltrationSpectralSequenceFirstPageXIso p k).hom =
      (K.columnFiltrationSpectralSequenceFirstPageXIso p k).hom ≫
        HomologicalComplex.homologyMap (φ.f p) k := by
  rw [columnFiltrationSpectralSequenceFirstPageXIso_eq,
    columnFiltrationSpectralSequenceFirstPageXIso_eq, Iso.trans_hom, Iso.trans_hom,
    HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_hom,
    columnFiltrationSpectralSequenceMap_eq,
    rowFiltrationSpectralSequenceFirstPageXIso_hom_naturality_assoc, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 2
  ext q
  simp

end HomologicalComplex₂

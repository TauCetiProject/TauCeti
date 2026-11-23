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
sends the rows `< q` of `K` into the rows `< q` of `L`. It therefore induces a morphism of the
filtration functors of the row filtrations (`HomologicalComplex₂.rowFiltrationFunctorMap`), of
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

## Main definitions and results

* `HomologicalComplex₂.mapTotalRowsGE`: the morphism of the total complexes of the rows `≥ s`,
  compatible with the projections from the total complexes and between the rows
  (`HomologicalComplex₂.toTotalRowsGE_naturality`, `HomologicalComplex₂.totalRowsGEMap_naturality`).
* `HomologicalComplex₂.rowFiltrationFunctorMap`,
  `HomologicalComplex₂.rowFiltrationSpectralObjectMap`,
  `HomologicalComplex₂.rowFiltrationSpectralSequenceMap`: the induced morphisms, compatible
  with identities and composition.
* `HomologicalComplex₂.rowFiltrationSpectralObjectMap_abutment_naturality`,
  `HomologicalComplex₂.columnFiltrationSpectralObjectMap_abutment_naturality`: the induced
  morphisms on the abutments.
-/

public section

noncomputable section

open CategoryTheory Limits ComplexShape ComposableArrows

namespace HomologicalComplex₂

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteCoproducts C] [HasZeroObject C]

/-- The morphism of the total complexes of the rows `≥ s` induced by a morphism of bicomplexes. -/
def mapTotalRowsGE : (s : ℕ) → {K L : HomologicalComplex₂ C (down ℕ) (down ℕ)} → (K ⟶ L) →
    (K.totalRowsGE s ⟶ L.totalRowsGE s)
  | 0, _, _, φ => total.map φ (down ℕ)
  | s + 1, _, _, φ =>
    HomologicalComplex.extendMap (mapTotalRowsGE s (rowsSuccMap φ)) (embeddingDownNatAdd 1)

variable {K L M : HomologicalComplex₂ C (down ℕ) (down ℕ)} (φ : K ⟶ L) (ψ : L ⟶ M)

/-- On the rows `≥ 0`, the morphism of total complexes is that of the whole total complexes. -/
@[simp]
lemma mapTotalRowsGE_zero : mapTotalRowsGE 0 φ = total.map φ (down ℕ) := (rfl)

/-- On the rows `≥ s + 1`, the morphism of total complexes is that of the rows `≥ s` of the
bicomplexes of rows `≥ 1`, placed one degree higher. -/
lemma mapTotalRowsGE_succ (s : ℕ) :
    mapTotalRowsGE (s + 1) φ =
      HomologicalComplex.extendMap (mapTotalRowsGE s (rowsSuccMap φ)) (embeddingDownNatAdd 1) :=
  (rfl)

@[simp]
lemma mapTotalRowsGE_id (s : ℕ) : mapTotalRowsGE s (𝟙 K) = 𝟙 _ := by
  induction s generalizing K with
  | zero => simp
  | succ s ih => rw [mapTotalRowsGE_succ, rowsSuccMap_id, ih, HomologicalComplex.extendMap_id]

@[simp]
lemma mapTotalRowsGE_comp (s : ℕ) :
    mapTotalRowsGE s (φ ≫ ψ) = mapTotalRowsGE s φ ≫ mapTotalRowsGE s ψ := by
  induction s generalizing K L M with
  | zero => simp [total.map_comp]
  | succ s ih =>
    rw [mapTotalRowsGE_succ, mapTotalRowsGE_succ, mapTotalRowsGE_succ, rowsSuccMap_comp, ih,
      HomologicalComplex.extendMap_comp]

/-- The projections onto the total complexes of the rows `≥ s` are natural. -/
@[reassoc]
lemma toTotalRowsGE_naturality (s : ℕ) :
    K.toTotalRowsGE s ≫ mapTotalRowsGE s φ = total.map φ (down ℕ) ≫ L.toTotalRowsGE s := by
  induction s generalizing K L with
  | zero => simp
  | succ s ih =>
    rw [toTotalRowsGE_succ, toTotalRowsGE_succ, mapTotalRowsGE_succ, Category.assoc,
      ← HomologicalComplex.extendMap_comp, ih, HomologicalComplex.extendMap_comp,
      dropRowZero_naturality_assoc]

/-- The projections of the total complexes of the rows `≥ s` onto the rows `≥ s + 1` are
natural. -/
@[reassoc]
lemma totalRowsGEMap_naturality (s : ℕ) :
    mapTotalRowsGE s φ ≫ L.totalRowsGEMap s = K.totalRowsGEMap s ≫ mapTotalRowsGE (s + 1) φ := by
  induction s generalizing K L with
  | zero =>
    rw [mapTotalRowsGE_zero, totalRowsGEMap_zero, totalRowsGEMap_zero, mapTotalRowsGE_succ,
      mapTotalRowsGE_zero, dropRowZero_naturality]
  | succ s ih =>
    rw [mapTotalRowsGE_succ, totalRowsGEMap_succ, totalRowsGEMap_succ,
      mapTotalRowsGE_succ _ (s + 1), ← HomologicalComplex.extendMap_comp, ih,
      HomologicalComplex.extendMap_comp]

/-- On the summand `(K.X p).X q`, `s ≤ q`, the morphism of the total complexes of the rows `≥ s`
is the component `(φ.f p).f q`. -/
@[reassoc (attr := simp)]
lemma ιTotalRowsGE_mapTotalRowsGE_f (s p q n : ℕ) (hs : s ≤ q) (h : p + q = n) :
    K.ιTotalRowsGE s p q n hs h ≫ (mapTotalRowsGE s φ).f n =
      (φ.f p).f q ≫ L.ιTotalRowsGE s p q n hs h := by
  rw [← ιTotal_toTotalRowsGE_f, ← ιTotal_toTotalRowsGE_f, Category.assoc,
    ← HomologicalComplex.comp_f, toTotalRowsGE_naturality, HomologicalComplex.comp_f,
    ιTotal_map_assoc]

end Preadditive

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
    ((rowFiltrationSpectralObjectMap ((flipFunctor C _ _).map φ)).hom (-n)).app
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
  congr 2
  refine HomologicalComplex.hom_ext _ _ fun m ↦ total.hom_ext _ fun p q h ↦ ?_
  simp [ιTotal_totalFlipIso_f_hom_assoc]

end HomologicalComplex₂

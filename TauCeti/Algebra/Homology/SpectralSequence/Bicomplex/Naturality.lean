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
  compatible with the projections from the total complexes
  (`HomologicalComplex₂.toTotalRowsGE_naturality`).
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

variable {C : Type*} [Category* C] [Abelian C]

/-- The morphism of the bicomplexes of rows `≥ 1` induced by a morphism of bicomplexes. -/
@[expose, simps]
def rowsSuccMap {K L : HomologicalComplex₂ C (down ℕ) (down ℕ)} (φ : K ⟶ L) :
    K.rowsSucc ⟶ L.rowsSucc where
  f p := { f q := (φ.f p).f (q + 1) }

/-- The projection killing row `0` is natural. -/
@[reassoc]
lemma dropRowZero_naturality {K L : HomologicalComplex₂ C (down ℕ) (down ℕ)} (φ : K ⟶ L) :
    total.map φ (down ℕ) ≫ L.dropRowZero =
      K.dropRowZero ≫
        HomologicalComplex.extendMap (total.map (rowsSuccMap φ) (down ℕ))
          (embeddingDownNatAdd 1) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rcases n with _ | n
  · exact (HomologicalComplex.isZero_extend_X _ _ 0 fun _ ↦ by simp).eq_of_tgt _ _
  · refine total.hom_ext _ fun p q h ↦ ?_
    rcases q with _ | q
    · simp
    · simp [HomologicalComplex.extendMap_f _ (embeddingDownNatAdd 1) (embeddingDownNatAdd_f 1 n)]

/-- The morphism of the total complexes of the rows `≥ s` induced by a morphism of bicomplexes. -/
def mapTotalRowsGE : (s : ℕ) → {K L : HomologicalComplex₂ C (down ℕ) (down ℕ)} → (K ⟶ L) →
    (K.totalRowsGE s ⟶ L.totalRowsGE s)
  | 0, _, _, φ => total.map φ (down ℕ)
  | s + 1, _, _, φ =>
    HomologicalComplex.extendMap (mapTotalRowsGE s (rowsSuccMap φ)) (embeddingDownNatAdd 1)

/-- The projections onto the total complexes of the rows `≥ s` are natural. -/
@[reassoc]
lemma toTotalRowsGE_naturality (s : ℕ) {K L : HomologicalComplex₂ C (down ℕ) (down ℕ)}
    (φ : K ⟶ L) :
    K.toTotalRowsGE s ≫ mapTotalRowsGE s φ = total.map φ (down ℕ) ≫ L.toTotalRowsGE s := by
  induction s generalizing K L with
  | zero => simp [mapTotalRowsGE]
  | succ s ih =>
    rw [toTotalRowsGE_succ, toTotalRowsGE_succ, mapTotalRowsGE, Category.assoc,
      ← HomologicalComplex.extendMap_comp, ih, HomologicalComplex.extendMap_comp,
      dropRowZero_naturality_assoc]

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

lemma rowFiltrationSpectralObjectMap_comp :
    rowFiltrationSpectralObjectMap (φ ≫ ψ) =
      rowFiltrationSpectralObjectMap φ ≫ rowFiltrationSpectralObjectMap ψ := by
  simp [rowFiltrationSpectralObjectMap, CochainComplex.spectralObjectMap_comp]

@[simp]
lemma rowFiltrationSpectralSequenceMap_id : rowFiltrationSpectralSequenceMap (𝟙 K) = 𝟙 _ := by
  simp [rowFiltrationSpectralSequenceMap, Abelian.SpectralObject.spectralSequenceMap_id]

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

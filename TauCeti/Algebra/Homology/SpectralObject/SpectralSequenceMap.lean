/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.Map
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
public import TauCeti.Algebra.Homology.HomologicalComplex
public import TauCeti.Algebra.Homology.ShortComplex.LeftHomology
-- The statement of `SpectralObject.spectralSequence_iso` refers to private auxiliary proofs of
-- this file, so that it may only be used with access to its private declarations.
import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# The morphism of spectral sequences induced by a morphism of spectral objects

Let `φ : X ⟶ Y` be a morphism of spectral objects indexed by a preorder `ι`, and `data` a recipe
for spectral sequences such that `X.HasSpectralSequence data` and `Y.HasSpectralSequence data`.
On each page, `φ` induces a morphism of homological complexes
`CategoryTheory.Abelian.SpectralObject.spectralSequencePageMap data φ r`, given on the object at
`pq` by `EMap` through Mathlib's identifications `spectralSequencePageXIso`, and these morphisms
are compatible with the isomorphisms between the homology of a page and the next page. They form
the morphism of spectral sequences `CategoryTheory.Abelian.SpectralObject.spectralSequenceMap`,
which is functorial in `φ`.

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.spectralSequencePageMap data φ r`: the morphism of pages.
* `CategoryTheory.Abelian.SpectralObject.spectralSequenceMap data φ`: the morphism of spectral
  sequences.

## Main results

* `CategoryTheory.Abelian.SpectralObject.homologyMap_spectralSequencePageMap_comp_iso_hom`: the
  morphisms of pages are compatible with the identification of the homology of a page with the
  next page.
* `CategoryTheory.Abelian.SpectralObject.spectralSequenceMap_id`,
  `CategoryTheory.Abelian.SpectralObject.spectralSequenceMap_comp`: functoriality.

## Implementation notes

The explicit description `SpectralObject.spectralSequence_iso` of the isomorphisms between the
homology of a page and the next page refers to private auxiliary proofs of its file, so that this
file imports all of `Mathlib.Algebra.Homology.SpectralObject.SpectralSequence`. The comparison
with `spectralSequenceHomologyData` uses `unseal spectralSequence`, like the proofs of Mathlib's
`spectralSequenceHomologyData_left_i` and `_left_π`.
-/

public section

namespace CategoryTheory.Abelian.SpectralObject

open ComposableArrows Limits

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι] {c : ℤ → ComplexShape κ}
  {r₀ : ℤ} (data : SpectralSequenceDataCore ι c r₀)
  {X Y Z : SpectralObject C ι} (φ : X ⟶ Y) (ψ : Y ⟶ Z)
  [X.HasSpectralSequence data] [Y.HasSpectralSequence data] [Z.HasSpectralSequence data]

/-- The morphism between the objects at `pq` on the `r`th pages of the spectral sequences of `X`
and `Y`, through Mathlib's identifications of these objects with objects `E`. -/
noncomputable def spectralSequencePageXMap (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    ((X.spectralSequence data).page r).X pq ⟶ ((Y.spectralSequence data).page r).X pq :=
  (X.spectralSequencePageXIso data r hr pq _ _ _ _ rfl rfl rfl rfl (data.deg pq - 1) _
      (data.deg pq + 1) rfl (by lia) rfl).hom ≫
    EMap φ _ _ _ (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (sub_add_cancel _ _) rfl ≫
      (Y.spectralSequencePageXIso data r hr pq _ _ _ _ rfl rfl rfl rfl (data.deg pq - 1) _
        (data.deg pq + 1) rfl (by lia) rfl).inv

/-- The morphism `spectralSequencePageXMap` may be computed through any choice of indices
equal to those of the recipe `data`. -/
lemma spectralSequencePageXMap_eq (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq)
    (h₃ : i₃ = data.i₃ r pq) (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    spectralSequencePageXMap data φ r hr pq =
      (X.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom ≫
        EMap φ _ _ _ n₀ n₁ n₂ hn₁ hn₂ ≫
          (Y.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁
            hn₂).inv := by
  subst h₀ h₁ h₂ h₃ h
  obtain rfl : n₀ = data.deg pq - 1 := by lia
  obtain rfl := hn₂
  rfl

section

variable (r : ℤ) (hr : r₀ ≤ r) (pq : κ) (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq)
  (h₁ : i₁ = data.i₁ pq) (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq) (n₀ n₁ n₂ : ℤ)
  (h : n₁ = data.deg pq) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)

@[reassoc]
lemma spectralSequencePageXIso_hom_comp_EMap :
    (X.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).hom ≫
        EMap φ _ _ _ n₀ n₁ n₂ hn₁ hn₂ =
      spectralSequencePageXMap data φ r hr pq ≫
        (Y.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁
          hn₂).hom := by
  rw [spectralSequencePageXMap_eq data φ r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂]
  simp

@[reassoc]
lemma EMap_comp_spectralSequencePageXIso_inv :
    EMap φ _ _ _ n₀ n₁ n₂ hn₁ hn₂ ≫
        (Y.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).inv =
      (X.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
        spectralSequencePageXMap data φ r hr pq := by
  rw [spectralSequencePageXMap_eq data φ r hr pq i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ h hn₁ hn₂]
  simp

end

/-- The morphisms `spectralSequencePageXMap` commute with the differentials of the pages. -/
@[reassoc]
lemma spectralSequence_page_d_comp_spectralSequencePageXMap (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ)
    (hpq : (c r).Rel pq pq') :
    ((X.spectralSequence data).page r).d pq pq' ≫ spectralSequencePageXMap data φ r hr pq' =
      spectralSequencePageXMap data φ r hr pq ≫ ((Y.spectralSequence data).page r).d pq pq' := by
  have h₀₂ := data.hc₀₂ r pq pq' hpq
  have h₁₃ := data.hc₁₃ r pq pq' hpq
  have hdeg := data.hc r pq pq' hpq
  have h₁₂ : data.i₁ pq' ≤ data.i₀ r pq := h₀₂ ▸ data.le₁₂ pq'
  rw [X.spectralSequence_page_d_eq data r hr pq pq' hpq (homOfLE (data.le₀₁ r pq'))
      (homOfLE h₁₂) (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq))
      (homOfLE (data.le₂₃ r pq)) rfl rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq)
      (data.deg pq + 1) (data.deg pq + 2) rfl (by lia) rfl (by lia),
    Y.spectralSequence_page_d_eq data r hr pq pq' hpq (homOfLE (data.le₀₁ r pq'))
      (homOfLE h₁₂) (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq))
      (homOfLE (data.le₂₃ r pq)) rfl rfl rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq)
      (data.deg pq + 1) (data.deg pq + 2) rfl (by lia) rfl (by lia),
    spectralSequencePageXMap_eq data φ r hr pq' _ _ (data.i₀ r pq) (data.i₁ pq) rfl rfl
      h₀₂ h₁₃ (data.deg pq) (data.deg pq + 1) (data.deg pq + 2) (by lia) rfl (by lia)]
  simp only [spectralSequencePageXMap, Category.assoc, Iso.inv_hom_id_assoc]
  rw [d_EMap_assoc]

/-- The morphism between the `r`th pages of the spectral sequences of `X` and `Y` induced by a
morphism `φ : X ⟶ Y` of spectral objects. -/
noncomputable def spectralSequencePageMap (r : ℤ) (hr : r₀ ≤ r) :
    (X.spectralSequence data).page r ⟶ (Y.spectralSequence data).page r where
  f := spectralSequencePageXMap data φ r hr
  comm' pq pq' hpq :=
    (spectralSequence_page_d_comp_spectralSequencePageXMap data φ r hr pq pq' hpq).symm

@[simp]
lemma spectralSequencePageMap_f (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    (spectralSequencePageMap data φ r hr).f pq = spectralSequencePageXMap data φ r hr pq := by
  rw [spectralSequencePageMap]

unseal spectralSequence in
/-- The left homology map data, between the homology data `spectralSequenceHomologyData` of the
`r`th pages of the spectral sequences of `X` and `Y`, given by the maps `EMap φ`. Its
compatibilities with `i` and `π` are instances of `map_EMap`; they are stated with the composites
`mapFourδ₁Toδ₀' ≫ inv` and `mapFourδ₄Toδ₃'`, which are `left.i` and `left.π` by `rfl` after
`unseal spectralSequence` (rewriting with `spectralSequenceHomologyData_left_i` fails, as the
objects `left.K` and `X.E …` agree only up to unfolding). Its type mentions private proofs of
Mathlib's `SpectralSequence.lean`, hence it is private. -/
private noncomputable abbrev spectralSequenceHomologyDataLeftHomologyMapData (r r' : ℤ)
    (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq : κ) :
    ShortComplex.LeftHomologyMapData ((HomologicalComplex.shortComplexFunctor' C (c r) _ pq
      _).map (spectralSequencePageMap data φ r hr))
      (X.spectralSequenceHomologyData data r r' hrr' hr _ pq _ rfl rfl _ _ _ _ _ _ rfl rfl
        rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl).left
      (Y.spectralSequenceHomologyData data r r' hrr' hr _ pq _ rfl rfl _ _ _ _ _ _ rfl rfl
        rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl).left :=
  have hi : EMap φ _ _ _ (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)
      (sub_add_cancel _ _) rfl ≫
      Y.mapFourδ₁Toδ₀' _ _ _ _ _ (data.i₀_le' hrr' hr pq rfl rfl) (data.le₀₁ r pq)
        (data.le₁₂ pq) (data.le₂₃ r pq) (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) ≫
        (Y.spectralSequencePageXIso data r hr pq _ _ _ _ rfl rfl rfl rfl (data.deg pq - 1)
          (data.deg pq) (data.deg pq + 1) rfl (by lia) rfl).inv =
      (X.mapFourδ₁Toδ₀' _ _ _ _ _ (data.i₀_le' hrr' hr pq rfl rfl) (data.le₀₁ r pq)
        (data.le₁₂ pq) (data.le₂₃ r pq) (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) ≫
        (X.spectralSequencePageXIso data r hr pq _ _ _ _ rfl rfl rfl rfl (data.deg pq - 1)
          (data.deg pq) (data.deg pq + 1) rfl (by lia) rfl).inv) ≫
        spectralSequencePageXMap data φ r hr pq := by
    rw [Category.assoc, ← EMap_comp_spectralSequencePageXIso_inv data φ r hr pq _ _ _ _ rfl rfl
      rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl, map_EMap_assoc]
  have hπ : X.mapFourδ₄Toδ₃' _ _ _ _ _ ((data.i₀_le' hrr' hr pq rfl rfl).trans (data.le₀₁ r pq))
        (data.le₁₂ pq) (data.le₂₃ r pq) (data.le₃₃' hrr' hr pq rfl rfl) (data.deg pq - 1)
        (data.deg pq) (data.deg pq + 1) ≫
        EMap φ _ _ _ (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (sub_add_cancel _ _) rfl =
      EMap φ _ _ _ (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (sub_add_cancel _ _) rfl ≫
        Y.mapFourδ₄Toδ₃' _ _ _ _ _ ((data.i₀_le' hrr' hr pq rfl rfl).trans (data.le₀₁ r pq))
          (data.le₁₂ pq) (data.le₂₃ r pq) (data.le₃₃' hrr' hr pq rfl rfl) (data.deg pq - 1)
          (data.deg pq) (data.deg pq + 1) :=
    map_EMap ..
  { φK := EMap φ _ _ _ (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (sub_add_cancel _ _) rfl
    φH := EMap φ _ _ _ (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (sub_add_cancel _ _) rfl
    commi := hi
    commf' := ShortComplex.LeftHomologyMapData.commf'_of_commi _
      (X.spectralSequenceHomologyData data r r' hrr' hr _ pq _ rfl rfl _ _ _ _ _ _ rfl rfl
        rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl).left
      (Y.spectralSequenceHomologyData data r r' hrr' hr _ pq _ rfl rfl _ _ _ _ _ _ rfl rfl
        rfl rfl rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl).left _ hi
    commπ := hπ }

/-- The morphisms of pages `spectralSequencePageMap` are compatible with the isomorphisms between
the homology of a page and the next page. -/
@[reassoc]
lemma homologyMap_spectralSequencePageMap_comp_iso_hom (r r' : ℤ) (hrr' : r + 1 = r')
    (hr : r₀ ≤ r) (hr' : r₀ ≤ r') (pq : κ) :
    HomologicalComplex.homologyMap (spectralSequencePageMap data φ r hr) pq ≫
        ((Y.spectralSequence data).iso r r' pq hrr' hr).hom =
      ((X.spectralSequence data).iso r r' pq hrr' hr).hom ≫
        (spectralSequencePageMap data φ r' hr').f pq := by
  have hX := X.spectralSequence_iso data r r' hrr' hr _ pq _ rfl rfl _ _ _ _ _ _ rfl rfl rfl rfl
    rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl (by lia) (by lia)
  have hY := Y.spectralSequence_iso data r r' hrr' hr _ pq _ rfl rfl _ _ _ _ _ _ rfl rfl rfl rfl
    rfl rfl (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl (by lia) (by lia)
  simp only [hX, hY, Iso.trans_hom, Category.assoc]
  -- Plan: after Mathlib's description `spectralSequence_iso` of the isomorphisms and the
  -- naturality of `homologyIsoSc'`, compare the homology of the `r`th pages through the left
  -- homology map data `spectralSequenceHomologyDataLeftHomologyMapData`.
  rw [HomologicalComplex.homologyMap_comp_homologyIsoSc'_hom_assoc]
  congr 1
  let γ := spectralSequenceHomologyDataLeftHomologyMapData data φ r r' hrr' hr pq
  have hg : (X.spectralSequencePageXIso data r' hr' pq _ _ _ _ rfl rfl rfl rfl (data.deg pq - 1)
      (data.deg pq) (data.deg pq + 1) rfl (by lia) rfl).hom ≫
        EMap φ _ _ _ (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (sub_add_cancel _ _) rfl =
      spectralSequencePageXMap data φ r' hr' pq ≫
        (Y.spectralSequencePageXIso data r' hr' pq _ _ _ _ rfl rfl rfl rfl (data.deg pq - 1)
          (data.deg pq) (data.deg pq + 1) rfl (by lia) rfl).hom :=
    spectralSequencePageXIso_hom_comp_EMap data φ r' hr' pq _ _ _ _ rfl rfl rfl rfl
      (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) rfl _ _
  exact γ.homologyMap_comp_homologyIso_trans_hom _ _ _ hg

/-- The morphism of spectral sequences induced by a morphism of spectral objects. -/
noncomputable def spectralSequenceMap : X.spectralSequence data ⟶ Y.spectralSequence data where
  hom r hr := spectralSequencePageMap data φ r hr
  comm r r' pq hrr' hr := homologyMap_spectralSequencePageMap_comp_iso_hom data φ r r' hrr' hr
    (hrr' ▸ Int.le_add_one hr) pq

@[simp]
lemma spectralSequenceMap_hom (r : ℤ) (hr : r₀ ≤ r) :
    (spectralSequenceMap data φ).hom r hr = spectralSequencePageMap data φ r hr := by
  rw [spectralSequenceMap]

@[simp]
lemma spectralSequencePageXMap_id (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    spectralSequencePageXMap data (𝟙 X) r hr pq = 𝟙 _ := by
  simp [spectralSequencePageXMap]

@[reassoc, simp]
lemma spectralSequencePageXMap_comp (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    spectralSequencePageXMap data (φ ≫ ψ) r hr pq =
      spectralSequencePageXMap data φ r hr pq ≫ spectralSequencePageXMap data ψ r hr pq := by
  simp [spectralSequencePageXMap]

@[simp]
lemma spectralSequencePageMap_id (r : ℤ) (hr : r₀ ≤ r) :
    spectralSequencePageMap data (𝟙 X) r hr = 𝟙 _ := by
  ext pq
  simp

@[reassoc, simp]
lemma spectralSequencePageMap_comp (r : ℤ) (hr : r₀ ≤ r) :
    spectralSequencePageMap data (φ ≫ ψ) r hr =
      spectralSequencePageMap data φ r hr ≫ spectralSequencePageMap data ψ r hr := by
  ext pq
  simp

@[simp]
lemma spectralSequenceMap_id : spectralSequenceMap data (𝟙 X) = 𝟙 _ := by
  ext r hr : 2
  simp

@[reassoc, simp]
lemma spectralSequenceMap_comp :
    spectralSequenceMap data (φ ≫ ψ) = spectralSequenceMap data φ ≫ spectralSequenceMap data ψ := by
  ext r hr : 2
  simp

end CategoryTheory.Abelian.SpectralObject

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.SpectralSequence
public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.Naturality

/-!
# Naturality of the Künneth spectral sequence

A chain map `f : K ⟶ K'` of complexes of modules over a commutative ring induces a morphism of
Künneth spectral sequences (`HomologicalComplex.kunnethSpectralSequenceMapLeft`): the morphism of
the spectral sequences of the column filtrations
(`HomologicalComplex₂.columnFiltrationSpectralSequenceMap`) induced by the morphism of Künneth
bicomplexes `HomologicalComplex.kunnethBicomplexMapLeft f L`, `f ▷ Q.X p` on column `p` for the
Cartan–Eilenberg resolution `Q` of `L`. On the first page, identified with
`⨁_{i + j = k} Hᵢ(K) ⊗ Hⱼ(Q.X p)`, it is the map induced by the maps `Hᵢ(f)`
(`HomologicalComplex.kunnethSpectralSequenceFirstPageXIso_hom_naturality`), and on the second page,
identified with `⨁_{i + j = q} Torₚ(Hᵢ(K), Hⱼ(L))`, it is the map induced by the maps
`Torₚ(Hᵢ(f), Hⱼ(L))` (`HomologicalComplex.kunnethSpectralSequenceSecondPageXIso_hom_naturality`).

The Künneth bicomplex is built from the Cartan–Eilenberg resolution of the second variable, so a
chain map `g : L₁ ⟶ L₂` induces a morphism of Künneth spectral sequences
(`HomologicalComplex.kunnethSpectralSequenceMapRight`) through a lift of `g` to the
Cartan–Eilenberg resolutions (`ChainComplex.cartanEilenbergResolutionMap`). That lift depends on
choices, so no functoriality is stated for it.

## Main definitions and results

* `HomologicalComplex.kunnethSpectralSequenceMapLeft`: the morphism of Künneth spectral sequences
  in the first variable, with `HomologicalComplex.kunnethSpectralSequenceMapLeft_id` and
  `HomologicalComplex.kunnethSpectralSequenceMapLeft_comp`.
* `HomologicalComplex.kunnethSpectralSequenceFirstPageXIso_hom_naturality`,
  `HomologicalComplex.kunnethFirstPageXIsoTorSum_hom_naturality`: the morphism in the first
  variable on the first page.
* `HomologicalComplex.kunnethSpectralSequenceSecondPageXIso_hom_naturality`: the morphism in the
  first variable on the second page.
* `HomologicalComplex.kunnethSpectralSequenceMapRight`: a morphism of Künneth spectral sequences
  in the second variable, through a lift to the Cartan–Eilenberg resolutions.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Limits

universe u

namespace HomologicalComplex

variable {R : Type u} [CommRing R] {K K' K'' : ChainComplex (ModuleCat.{u} R) ℕ}
  (f : K ⟶ K') (f' : K' ⟶ K'') (L : ChainComplex (ModuleCat.{u} R) ℕ)

/-- **Naturality of the Künneth spectral sequence in the first variable**: the morphism of
Künneth spectral sequences induced by a chain map `f : K ⟶ K'`, that of the spectral sequences of
the column filtrations induced by `HomologicalComplex.kunnethBicomplexMapLeft f L`. -/
abbrev kunnethSpectralSequenceMapLeft :
    kunnethSpectralSequence K L ⟶ kunnethSpectralSequence K' L :=
  HomologicalComplex₂.columnFiltrationSpectralSequenceMap (kunnethBicomplexMapLeft f L)

@[simp]
lemma kunnethSpectralSequenceMapLeft_id : kunnethSpectralSequenceMapLeft (𝟙 K) L = 𝟙 _ := by
  simp [kunnethSpectralSequenceMapLeft]

@[simp]
lemma kunnethSpectralSequenceMapLeft_comp :
    kunnethSpectralSequenceMapLeft (f ≫ f') L =
      kunnethSpectralSequenceMapLeft f L ≫ kunnethSpectralSequenceMapLeft f' L := by
  simp [kunnethSpectralSequenceMapLeft]

/-- **The morphism of Künneth spectral sequences in the first variable on the first page.** Under
the identifications `HomologicalComplex.kunnethSpectralSequenceFirstPageXIso` of the first pages at
column `p`, degree `k` with `⨁_{i + j = k} Hᵢ(K) ⊗ Hⱼ(Q.X p)`, the morphism induced by `f` is the
map induced by the maps `Hᵢ(f)`. -/
@[reassoc]
theorem kunnethSpectralSequenceFirstPageXIso_hom_naturality (p k : ℕ) :
    ((kunnethSpectralSequenceMapLeft f L).hom 2).f (-(k : ℤ) - 2 * p, p) ≫
        (kunnethSpectralSequenceFirstPageXIso K' L p k).hom =
      (kunnethSpectralSequenceFirstPageXIso K L p k).hom ≫
        GradedObject.Monoidal.whiskerRight (fun i ↦ homologyMap f i)
          (fun j ↦ ((ChainComplex.cartanEilenbergResolution L).X p).homology j) k := by
  simp only [kunnethSpectralSequenceFirstPageXIso_eq, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [HomologicalComplex₂.columnFiltrationSpectralSequenceFirstPageXIso_hom_naturality_assoc,
    Category.assoc]
  congr 1
  rw [IsIso.eq_inv_comp, ← kunnethColumnHomologyKunneth_naturality_left_assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- The morphism of Künneth spectral sequences in the first variable on the first page, under the
identifications `HomologicalComplex.kunnethFirstPageXIsoTorSum` with the terms of the complexes
`HomologicalComplex.kunnethTorSumComplex`: it is the morphism of complexes
`HomologicalComplex.kunnethTorSumComplexMap` induced by the maps `Hᵢ(f)`. -/
@[reassoc]
theorem kunnethFirstPageXIsoTorSum_hom_naturality (p q : ℕ) :
    ((kunnethSpectralSequenceMapLeft f L).hom 2).f (-(q : ℤ) - 2 * p, p) ≫
        (kunnethFirstPageXIsoTorSum K' L p q).hom =
      (kunnethFirstPageXIsoTorSum K L p q).hom ≫
        (kunnethTorSumComplexMap L (fun i ↦ homologyMap f i) q).f p := by
  rw [kunnethFirstPageXIsoTorSum_eq, kunnethFirstPageXIsoTorSum_eq, Iso.trans_hom, Iso.trans_hom,
    kunnethSpectralSequenceFirstPageXIso_hom_naturality_assoc,
    tensorObjIsoKunnethTorSumComplexX_hom_naturality, Category.assoc]

/-- **The morphism of Künneth spectral sequences in the first variable on the second page.** Under
the identifications `HomologicalComplex.kunnethSpectralSequenceSecondPageXIso` of the second pages
at column `p`, degree `q` with `⨁_{i + j = q} Torₚ(Hᵢ(K), Hⱼ(L))`, the morphism induced by `f` is
the map induced by the maps `Torₚ(Hᵢ(f), Hⱼ(L))`. -/
@[reassoc]
theorem kunnethSpectralSequenceSecondPageXIso_hom_naturality (p q : ℕ) :
    ((kunnethSpectralSequenceMapLeft f L).hom 3).f (-(q : ℤ) - 2 * p, p) ≫
        (kunnethSpectralSequenceSecondPageXIso K' L p q).hom =
      (kunnethSpectralSequenceSecondPageXIso K L p q).hom ≫
        GradedObject.mapBifunctorMapMap (Tor (ModuleCat.{u} R) p) (fun x ↦ x.1 + x.2)
          (fun i ↦ homologyMap f i) (𝟙 fun j ↦ L.homology j) q := by
  -- the square of cycles: the first-page morphism, on cycles, followed by the lift to the cycles
  -- of `kunnethTorSumComplex K' L q`, is the lift to the cycles of `kunnethTorSumComplex K L q`
  -- followed by the map induced by `kunnethTorSumComplexMap`
  have hcycles : cyclesMap ((kunnethSpectralSequenceMapLeft f L).hom 2) (-(q : ℤ) - 2 * p, p) ≫
      (kunnethTorSumComplex K' L q).liftCycles
        (((kunnethSpectralSequence K' L).page 2).iCycles (-(q : ℤ) - 2 * p, p) ≫
          (kunnethFirstPageXIsoTorSum K' L p q).hom) (p - 1) (by cases p <;> simp)
        (by rw [Category.assoc, iCycles_kunnethFirstPageXIsoTorSum_hom_d]) =
      (kunnethTorSumComplex K L q).liftCycles
        (((kunnethSpectralSequence K L).page 2).iCycles (-(q : ℤ) - 2 * p, p) ≫
          (kunnethFirstPageXIsoTorSum K L p q).hom) (p - 1) (by cases p <;> simp)
        (by rw [Category.assoc, iCycles_kunnethFirstPageXIsoTorSum_hom_d]) ≫
      cyclesMap (kunnethTorSumComplexMap L (fun i ↦ homologyMap f i) q) p := by
    rw [comp_liftCycles, liftCycles_comp_cyclesMap]
    congr 1
    rw [cyclesMap_i_assoc, kunnethFirstPageXIsoTorSum_hom_naturality, Category.assoc]
  rw [← cancel_epi (((kunnethSpectralSequence K L).page 2).homologyπ (-(q : ℤ) - 2 * p, p) ≫
    ((kunnethSpectralSequence K L).iso 2 3 (-(q : ℤ) - 2 * p, p)).hom)]
  rw [Category.assoc, Category.assoc,
    reassoc_of% (homologyπ_kunnethSpectralSequenceSecondPageXIso_hom K L p q),
    ← (kunnethSpectralSequenceMapLeft f L).comm_assoc 2 3, homologyπ_naturality_assoc,
    homologyπ_kunnethSpectralSequenceSecondPageXIso_hom, reassoc_of% hcycles,
    ← kunnethTorSumComplexHomologyIso_hom_naturality, homologyπ_naturality_assoc]

section Right

variable (K) {L₁ L₂ : ChainComplex (ModuleCat.{u} R) ℕ} (g : L₁ ⟶ L₂)

/-- **A morphism of Künneth spectral sequences in the second variable**: the morphism of the
spectral sequences of the column filtrations induced by
`HomologicalComplex.kunnethBicomplexMapRight K g`, over a chain map `g : L₁ ⟶ L₂`. It depends on
the choice of the lift of `g` to the Cartan–Eilenberg resolutions. -/
abbrev kunnethSpectralSequenceMapRight :
    kunnethSpectralSequence K L₁ ⟶ kunnethSpectralSequence K L₂ :=
  HomologicalComplex₂.columnFiltrationSpectralSequenceMap (kunnethBicomplexMapRight K g)

end Right

end HomologicalComplex

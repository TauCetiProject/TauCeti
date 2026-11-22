/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.SpectralSequence
public import TauCeti.Algebra.Homology.SpectralSequence.Bicomplex.Naturality

/-!
# Naturality of the Künneth spectral sequence in the first variable

A chain map `f : K ⟶ K'` of complexes of modules over a commutative ring induces a morphism of
Künneth bicomplexes `HomologicalComplex.kunnethBicomplexMapLeft f L`, which on column `p` is
`f ▷ Q.X p` for the Cartan–Eilenberg resolution `Q` of `L`. It is compatible with the
augmentations to `K ⊗ L` and `K' ⊗ L`
(`HomologicalComplex.total_map_kunnethBicomplexMapLeft_kunnethBicomplexAugmentation`), and induces
a morphism of Künneth spectral sequences
(`HomologicalComplex.kunnethSpectralSequenceMapLeft`), the morphism of the spectral sequences of
the column filtrations (`HomologicalComplex₂.rowFiltrationSpectralSequenceMap`).

The Künneth bicomplex is built from the Cartan–Eilenberg resolution of the second variable, so
naturality in the second variable needs a comparison of Cartan–Eilenberg resolutions and is not
treated here.

## Main definitions and results

* `HomologicalComplex.kunnethBicomplexMapLeft`: the morphism of Künneth bicomplexes, with
  `HomologicalComplex.kunnethBicomplexMapLeft_id` and
  `HomologicalComplex.kunnethBicomplexMapLeft_comp`.
* `HomologicalComplex.total_map_kunnethBicomplexMapLeft_kunnethBicomplexAugmentation`: its
  compatibility with the augmentations.
* `HomologicalComplex.kunnethSpectralSequenceMapLeft`: the morphism of Künneth spectral sequences,
  with `HomologicalComplex.kunnethSpectralSequenceMapLeft_id` and
  `HomologicalComplex.kunnethSpectralSequenceMapLeft_comp`.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Limits

universe u

namespace HomologicalComplex

variable {R : Type u} [CommRing R] {K K' K'' : ChainComplex (ModuleCat.{u} R) ℕ}
  (f : K ⟶ K') (f' : K' ⟶ K'') (L : ChainComplex (ModuleCat.{u} R) ℕ)

/-- The morphism of Künneth bicomplexes induced by a chain map `f : K ⟶ K'`: on column `p` it is
`f ▷ Q.X p`, for the Cartan–Eilenberg resolution `Q` of `L`. -/
def kunnethBicomplexMapLeft : kunnethBicomplex K L ⟶ kunnethBicomplex K' L where
  f p := f ▷ (ChainComplex.cartanEilenbergResolution L).X p
  comm' p p' _ := by
    rw [kunnethBicomplex_d, kunnethBicomplex_d]
    exact (whisker_exchange _ _).symm

/-- The morphism `HomologicalComplex.kunnethBicomplexMapLeft f L` is `f ▷ Q.X p` on column `p`. -/
lemma kunnethBicomplexMapLeft_f (p : ℕ) :
    (kunnethBicomplexMapLeft f L).f p = f ▷ (ChainComplex.cartanEilenbergResolution L).X p :=
  (rfl)

@[simp]
lemma kunnethBicomplexMapLeft_id : kunnethBicomplexMapLeft (𝟙 K) L = 𝟙 _ := by
  ext p : 1
  rw [kunnethBicomplexMapLeft_f, id_whiskerRight]
  rfl

@[simp]
lemma kunnethBicomplexMapLeft_comp :
    kunnethBicomplexMapLeft (f ≫ f') L =
      kunnethBicomplexMapLeft f L ≫ kunnethBicomplexMapLeft f' L := by
  ext p : 1
  rw [kunnethBicomplexMapLeft_f, comp_whiskerRight]
  rfl

/-- The morphism of Künneth bicomplexes induced by `f` is compatible with the augmentations of the
total complexes to `K ⊗ L` and `K' ⊗ L`. -/
@[reassoc]
lemma total_map_kunnethBicomplexMapLeft_kunnethBicomplexAugmentation :
    HomologicalComplex₂.total.map (kunnethBicomplexMapLeft f L) (ComplexShape.down ℕ) ≫
        kunnethBicomplexAugmentation K' L =
      kunnethBicomplexAugmentation K L ≫ f ▷ L := by
  have e : (kunnethBicomplexMapLeft f L).f 0 ≫ kunnethBicomplexε K' L =
      kunnethBicomplexε K L ≫ f ▷ L := by
    rw [kunnethBicomplexε_def, kunnethBicomplexε_def, kunnethBicomplexMapLeft_f]
    -- the column `0` of the Künneth bicomplex is `K ⊗ Q.X 0` only by definition
    change f ▷ _ ≫ K' ◁ _ = K ◁ _ ≫ f ▷ _
    exact (whisker_exchange _ _).symm
  rw [kunnethBicomplexAugmentation_def, kunnethBicomplexAugmentation_def,
    HomologicalComplex₂.total_map_totalAugmentation, HomologicalComplex₂.totalAugmentation_comp]
  simp only [e]

/-- **Naturality of the Künneth spectral sequence in the first variable**: the morphism of
Künneth spectral sequences induced by a chain map `f : K ⟶ K'`, that of the spectral sequences of
the column filtrations induced by `HomologicalComplex.kunnethBicomplexMapLeft f L`. -/
abbrev kunnethSpectralSequenceMapLeft :
    kunnethSpectralSequence K L ⟶ kunnethSpectralSequence K' L :=
  HomologicalComplex₂.rowFiltrationSpectralSequenceMap
    ((HomologicalComplex₂.flipFunctor _ _ _).map (kunnethBicomplexMapLeft f L))

@[simp]
lemma kunnethSpectralSequenceMapLeft_id : kunnethSpectralSequenceMapLeft (𝟙 K) L = 𝟙 _ := by
  simp [kunnethSpectralSequenceMapLeft]

lemma kunnethSpectralSequenceMapLeft_comp :
    kunnethSpectralSequenceMapLeft (f ≫ f') L =
      kunnethSpectralSequenceMapLeft f L ≫ kunnethSpectralSequenceMapLeft f' L := by
  simp [kunnethSpectralSequenceMapLeft,
    HomologicalComplex₂.rowFiltrationSpectralSequenceMap_comp]

end HomologicalComplex

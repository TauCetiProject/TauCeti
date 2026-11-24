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
Künneth spectral sequences (`HomologicalComplex.kunnethSpectralSequenceMapLeft`): the morphism of
the spectral sequences of the column filtrations
(`HomologicalComplex₂.columnFiltrationSpectralSequenceMap`) induced by the morphism of Künneth
bicomplexes `HomologicalComplex.kunnethBicomplexMapLeft f L`, `f ▷ Q.X p` on column `p` for the
Cartan–Eilenberg resolution `Q` of `L`.

The Künneth bicomplex is built from the Cartan–Eilenberg resolution of the second variable, so
naturality in the second variable needs a comparison of Cartan–Eilenberg resolutions and is not
treated here.

## Main definitions and results

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

end HomologicalComplex

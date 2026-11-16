/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Comparison

/-!
# The spectral sequence of a filtered space on cubical chains

Let `X : ℤ → Set Y` be an increasing family of subsets of a topological space `Y`. The
normalized cubical chains of the `X q` form an increasing filtration of the normalized cubical
chains of `Y` (`TauCeti.chainFiltration` for `TauCeti.normalizedCubicalChainComplex`), and its
spectral sequence (`TauCeti.cubicalFilteredSpaceSpectralSequence`) is the cubical counterpart of
the spectral sequence `TauCeti.filteredSpaceSpectralSequence` of the filtration of the simplicial
singular chains. As there, chains in degree `n` sit in cohomological degree `-n`, and the abutment
in degree `-n` is the cubical homology `Hₙ(Y)` (`TauCeti.chainFiltrationAbutmentIso`). The stage
at an empty subset is zero (`TauCeti.cubicalChainFiltration_eq_bot`), and the stage at the whole
space is everything (`TauCeti.chainFiltration_eq_top`).

The natural comparison map `TauCeti.singularToCubical` from simplicial to normalized cubical
chains carries the singular chains of `X q` into the cubical chains of `X q`, so it is a morphism
of filtered complexes (`TauCeti.chainFiltrationMap`). On the piece of the filtration at `q` it is
the comparison map of the space `X q`, a quasi-isomorphism
(`TauCeti.quasiIso_chainFiltrationMap_app`). By the comparison theorem for quasi-isomorphisms of
filtrations (`CochainComplex.isIso_spectralSequenceMap_hom_f_of_quasiIso`), the induced morphism
of spectral sequences (`TauCeti.singularToCubicalSpectralSequenceMap`) is an isomorphism on every
object of every page, from the first page on
(`TauCeti.isIso_singularToCubicalSpectralSequenceMap_hom_f`). So statements about the pages of
the spectral sequence of a filtered space on simplicial chains, such as the description of its
first page or its vanishing regions, transfer to cubical chains through these isomorphisms. The
abutment is identified with the cubical homology `Hₙ(Y)` separately, and its filtration is not
compared with the simplicial one here. Over the skeletal filtration of a Serre fibration this is
the Serre spectral sequence on cubical chains.

## Main definitions

* `TauCeti.cubicalFilteredSpaceSpectralSequence k hX`: the spectral sequence of the filtration of
  the normalized cubical chains of `Y` by those of the `X q`.
* `TauCeti.singularToCubicalSpectralSequenceMap k hX`: the induced morphism of spectral
  sequences.

## Main results

* `TauCeti.isIso_singularToCubicalSpectralSequenceMap_hom_f`: the comparison is an isomorphism on
  every page `r ≥ 2`.
* `TauCeti.singularCubicalSpectralSequencePageXIso`: the resulting isomorphism of the objects
  of the two spectral sequences.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII (the comparison of
  cubical and simplicial chains).
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II (the spectral sequence of a fibration on cubical chains).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2, the spectral sequence of a filtered complex.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace TauCeti

variable (k : Type u) [Ring k] {Y : TopCat.{u}} {X : ℤ → Set Y}

/-- The stage of the filtration of normalized cubical chains at an empty subset is zero. -/
@[simp]
lemma cubicalChainFiltration_eq_bot {a : ℤ} (ha : X a = ∅) :
    chainFiltration (normalizedCubicalChainComplex k) X a = ⊥ := by
  have : IsEmpty (TopPair.ofSubset (X a)).snd := by
    rw [ha]
    exact Set.isEmpty_coe_sort.2 rfl
  exact chainFiltration_eq_bot_of_isZero _ (isZero_normalizedCubicalChainComplex_obj_of_isEmpty _)

variable (hX : Monotone X)

/-- **The spectral sequence of a filtered space on cubical chains.** For an increasing family
`X : ℤ → Set Y` of subsets of a space `Y`, this is the spectral sequence of the filtration of the
normalized cubical chains of `Y` by those of the `X q`, in the cohomological indexing of
`CochainComplex.spectralSequence`: chains in degree `n` sit in degree `-n`. Its abutment in degree
`-n` is the cubical homology `Hₙ(Y)` (`TauCeti.chainFiltrationAbutmentIso`). -/
abbrev cubicalFilteredSpaceSpectralSequence :=
  CochainComplex.spectralSequence (CochainComplex.filtrationFunctor _
    (monotone_chainFiltration (normalizedCubicalChainComplex k) hX))

/-! ### The comparison with simplicial chains -/

/-- **The comparison of the simplicial and cubical spectral sequences of a filtered space**:
the morphism of spectral sequences induced by the morphism of filtrations
(`TauCeti.chainFiltrationMap`) given by the natural comparison map `TauCeti.singularToCubical`
from simplicial to normalized cubical chains, which carries the singular chains of each `X q`
into the cubical chains of `X q`. -/
def singularToCubicalSpectralSequenceMap :
    filteredSpaceSpectralSequence (ModuleCat.of k k) hX ⟶
      cubicalFilteredSpaceSpectralSequence k hX :=
  Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
    (CochainComplex.spectralObjectMap
      (chainFiltrationMap (singularToCubical k) hX hX (𝟙 Y) fun _ _ hx ↦ hx))

/-- `TauCeti.singularToCubicalSpectralSequenceMap` is the morphism of spectral sequences of the
morphism of spectral objects of `TauCeti.chainFiltrationMap` for `TauCeti.singularToCubical`. -/
lemma singularToCubicalSpectralSequenceMap_def :
    singularToCubicalSpectralSequenceMap k hX =
      Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
        (CochainComplex.spectralObjectMap
          (chainFiltrationMap (singularToCubical k) hX hX (𝟙 Y) fun _ _ hx ↦ hx)) :=
  (rfl)

/-- **Cubical and simplicial chains give the same spectral sequence of a filtered space.** The
comparison of the simplicial and cubical spectral sequences of a filtered space is an isomorphism
on every object of every page `r ≥ 2`, that is, from the first page on. -/
theorem isIso_singularToCubicalSpectralSequenceMap_hom_f (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    IsIso (((singularToCubicalSpectralSequenceMap k hX).hom r hr).f pq) :=
  CochainComplex.isIso_spectralSequenceMap_hom_f_of_quasiIso _
    (quasiIso_chainFiltrationMap_app (singularToCubical k) hX) r hr pq

/-- The isomorphism between the objects of the simplicial and cubical spectral sequences of a
filtered space, on every page `r ≥ 2`, given by their comparison. -/
def singularCubicalSpectralSequencePageXIso (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    ((filteredSpaceSpectralSequence (ModuleCat.of k k) hX).page r).X pq ≅
      ((cubicalFilteredSpaceSpectralSequence k hX).page r).X pq :=
  have := isIso_singularToCubicalSpectralSequenceMap_hom_f k hX r hr pq
  asIso (((singularToCubicalSpectralSequenceMap k hX).hom r hr).f pq)

/-- The isomorphism `TauCeti.singularCubicalSpectralSequencePageXIso` is the component of the
comparison of the simplicial and cubical spectral sequences. -/
@[simp]
lemma singularCubicalSpectralSequencePageXIso_hom (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    (singularCubicalSpectralSequencePageXIso k hX r hr pq).hom =
      ((singularToCubicalSpectralSequenceMap k hX).hom r hr).f pq :=
  (rfl)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic

/-!
# Comparison of the spectral objects of a filtered space for two chain functors

Let `X : ℤ → Set Y` be an increasing family of subsets of a space `Y`, and `F`, `G` two functors
from spaces to chain complexes sending inclusions of subspaces to monomorphisms, for instance
simplicial and cubical singular chains. Each filters its value on `Y` by its values on the `X q`
(`TauCeti.chainFiltration`). A natural transformation `α : F ⟶ G` sends `F(X q)` into `G(X q)`, so
it is a morphism of filtered complexes (`TauCeti.chainFiltrationMap` for the identity of `Y`). If
the components of `α` at `Y` and at the `X q` are quasi-isomorphisms, then so is every component
of this morphism, including those at `⊥` and `⊤`
(`TauCeti.quasiIso_chainFiltrationMap_app_of_quasiIso`), and it induces an isomorphism of the
spectral objects of the two filtrations (`TauCeti.chainFiltrationSpectralObjectIso`), hence of
their spectral sequences on every page (`TauCeti.chainFiltrationSpectralSequenceIso`), abutments
and filtrations of the abutments. No boundedness or exhaustiveness assumption on the filtration is
needed.

## Main definitions

* `TauCeti.chainFiltrationSpectralObjectIso`: the isomorphism of spectral objects induced by a
  natural transformation by quasi-isomorphisms.
* `TauCeti.chainFiltrationSpectralSequenceIso`: the induced isomorphism of spectral sequences.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2 and Theorem 3.5 (the comparison theorem).
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [Abelian A] {Y : TopCat.{w}} {X : ℤ → Set Y}
  {F G : TopCat.{w} ⥤ ChainComplex A ℕ} (α : F ⟶ G)
  [∀ P : TopPair.{w}, Mono (F.map P.map)] [∀ P : TopPair.{w}, Mono (G.map P.map)]
  (hX : Monotone X)
  [QuasiIso (α.app Y)] [∀ q, QuasiIso (α.app (TopPair.ofSubset (X q)).snd)]

/-- If the components of `α` at `Y` and at the `X q` are quasi-isomorphisms, so is every component
of the morphism of filtered complexes it induces, including those at `⊥` and `⊤`. -/
instance quasiIso_chainFiltrationMap_app_of_quasiIso (a : EInt) :
    QuasiIso ((chainFiltrationMap α hX hX (𝟙 Y) fun _ _ hx ↦ hx).app a) := by
  have : QuasiIso (F.map (𝟙 Y) ≫ α.app Y) := by
    rw [F.map_id, Category.id_comp]
    infer_instance
  -- Generalize the proof that the identity preserves the filtration, so that its type is literally
  -- the one expected by `TauCeti.chainFiltrationMap_def`.
  suffices ∀ hg : ∀ q, Set.MapsTo (𝟙 Y : Y ⟶ Y) (X q) (X q),
      (∀ q : ℤ, QuasiIso ((chainFiltrationMap α hX hX (𝟙 Y) hg).app q)) →
        QuasiIso ((chainFiltrationMap α hX hX (𝟙 Y) hg).app a) from
    this _ (quasiIso_chainFiltrationMap_app α hX)
  intro hg h
  rw [chainFiltrationMap_def] at h ⊢
  exact CochainComplex.quasiIso_filtrationFunctorMap_app _ _ h a

/-- **A natural transformation of chain functors by quasi-isomorphisms identifies the spectral
sequences of a filtered space.** The spectral objects of the filtrations of `F(Y)` and `G(Y)` by
the `F(X q)` and `G(X q)` are isomorphic through `α`. -/
def chainFiltrationSpectralObjectIso :
    CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_chainFiltration F hX)) ≅
      CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_chainFiltration G hX)) :=
  asIso (CochainComplex.spectralObjectMap (chainFiltrationMap α hX hX (𝟙 Y) fun _ _ hx ↦ hx))

/-- The isomorphism `TauCeti.chainFiltrationSpectralObjectIso α hX` is the morphism of spectral
objects induced by `TauCeti.chainFiltrationMap` for `α` and the identity of `Y`. -/
@[simp]
lemma chainFiltrationSpectralObjectIso_hom :
    (chainFiltrationSpectralObjectIso α hX).hom =
      CochainComplex.spectralObjectMap (chainFiltrationMap α hX hX (𝟙 Y) fun _ _ hx ↦ hx) :=
  (rfl)

/-- **A natural transformation of chain functors by quasi-isomorphisms identifies the spectral
sequences of a filtered space on every page.** The spectral sequences of the filtrations of `F(Y)`
and `G(Y)` by the `F(X q)` and `G(X q)` are isomorphic through `α`. -/
def chainFiltrationSpectralSequenceIso :
    chainFiltrationSpectralSequence F hX ≅ chainFiltrationSpectralSequence G hX :=
  asIso (Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
    (chainFiltrationSpectralObjectIso α hX).hom)

/-- The isomorphism `TauCeti.chainFiltrationSpectralSequenceIso α hX` is the morphism of spectral
sequences induced by `TauCeti.chainFiltrationMap` for `α` and the identity of `Y`. -/
@[simp]
lemma chainFiltrationSpectralSequenceIso_hom :
    (chainFiltrationSpectralSequenceIso α hX).hom =
      Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
        (CochainComplex.spectralObjectMap (chainFiltrationMap α hX hX (𝟙 Y) fun _ _ hx ↦ hx)) :=
  (rfl)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic

/-!
# Comparison of the spectral sequences of a filtered space for two chain functors

Let `X : ℤ → Set Y` be an increasing family of subsets of a space `Y`, and `Φ`, `Ψ` two functors
from spaces to chain complexes sending inclusions of subspaces to monomorphisms, for instance
simplicial and cubical singular chains. Each filters its value on `Y` by its values on the `X q`
(`TauCeti.chainFiltration`). A natural transformation `τ : Φ ⟶ Ψ` sends `Φ(X q)` into `Ψ(X q)`, so
it is a morphism of filtered complexes (`TauCeti.chainFiltrationMap`, in
`TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic`). If the
components of `τ` at `Y` and at the `X q` are quasi-isomorphisms, then so is every component of
this morphism, and it induces an
isomorphism of the spectral objects of the two filtrations
(`TauCeti.chainFiltrationSpectralObjectIso`), hence of their spectral sequences, abutments and
filtrations of the abutments.

## Main definitions

* `TauCeti.quasiIso_chainFiltrationMap_app`: the morphism of filtered complexes induced by a
  natural transformation by quasi-isomorphisms is a quasi-isomorphism on every stage.
* `TauCeti.chainFiltrationSpectralObjectIso`: the isomorphism of spectral objects induced by a
  natural transformation by quasi-isomorphisms.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2 and Theorem 3.5 (the comparison theorem).
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] {Y : TopCat.{w}} {X : ℤ → Set Y}

variable [Abelian A] {Φ Ψ : TopCat.{w} ⥤ ChainComplex A ℕ} (τ : Φ ⟶ Ψ)
  [∀ q, Mono (Φ.map (TopPair.ofSubset (X q)).map)] [∀ q, Mono (Ψ.map (TopPair.ofSubset (X q)).map)]
  (hX : Monotone X)

variable [QuasiIso (τ.app Y)] [∀ q, QuasiIso (τ.app (TopPair.ofSubset (X q)).snd)]

/-- If the components of `τ` at `Y` and at the `X q` are quasi-isomorphisms, so is every component
of the morphism of filtered complexes it induces. -/
instance quasiIso_chainFiltrationMap_app (a : EInt) :
    QuasiIso ((chainFiltrationMap τ hX).app a) := by
  have h (q : ℤ) : QuasiIso ((chainFiltrationMap τ hX).app q) :=
    (quasiIso_iff_of_arrow_mk_iso _
      (extendMap (τ.app (TopPair.ofSubset (X q)).snd) ComplexShape.embeddingDownNat)
      (Arrow.isoMk (CochainComplex.filtrationFunctorObjIsoOfEqMk _ _ (chainFiltrationι Φ X)
        (chainFiltration_def Φ X) q) (CochainComplex.filtrationFunctorObjIsoOfEqMk _ _
          (chainFiltrationι Ψ X) (chainFiltration_def Ψ X) q)
        (chainFiltrationMap_app_coe_comp τ hX q).symm)).2 inferInstance
  rw [chainFiltrationMap_def] at h ⊢
  exact CochainComplex.quasiIso_filtrationFunctorMap_app _ _ h a

/-- **A natural transformation of chain functors by quasi-isomorphisms identifies the spectral
sequences of a filtered space.** The spectral objects of the filtrations of `Φ(Y)` and `Ψ(Y)` by
the `Φ(X q)` and `Ψ(X q)` are isomorphic through `τ`. -/
def chainFiltrationSpectralObjectIso :
    CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_chainFiltration Φ hX)) ≅
      CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_chainFiltration Ψ hX)) :=
  asIso (CochainComplex.spectralObjectMap (chainFiltrationMap τ hX))

/-- The isomorphism `TauCeti.chainFiltrationSpectralObjectIso τ hX` is the morphism of spectral
objects induced by `TauCeti.chainFiltrationMap τ hX`. -/
@[simp]
lemma chainFiltrationSpectralObjectIso_hom :
    (chainFiltrationSpectralObjectIso τ hX).hom =
      CochainComplex.spectralObjectMap (chainFiltrationMap τ hX) := by
  simp [chainFiltrationSpectralObjectIso]

end TauCeti

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
it is a morphism of filtered complexes (`TauCeti.chainFiltrationMap`), functorial in `τ`. If the
components of `τ` at `Y` and at the `X q` are quasi-isomorphisms, then so is every component of
this morphism, and it induces an
isomorphism of the spectral objects of the two filtrations
(`TauCeti.chainFiltrationSpectralObjectIso`), hence of their spectral sequences, abutments and
filtrations of the abutments.

## Main definitions

* `TauCeti.chainFiltrationMap`: the morphism of filtration functors induced by `τ : Φ ⟶ Ψ`.
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

section

variable [HasZeroMorphisms A] [HasZeroObject A] {Φ Ψ : TopCat.{w} ⥤ ChainComplex A ℕ} (τ : Φ ⟶ Ψ)

/-- A natural transformation `τ : Φ ⟶ Ψ` carries `Φ(X q)` into `Ψ(X q)`. -/
@[reassoc]
lemma chainFiltrationι_comp_extendMap_app (q : ℤ) :
    chainFiltrationι Φ X q ≫ extendMap (τ.app Y) ComplexShape.embeddingDownNat =
      extendMap (τ.app (TopPair.ofSubset (X q)).snd) ComplexShape.embeddingDownNat ≫
        chainFiltrationι Ψ X q := by
  rw [chainFiltrationι_def, chainFiltrationι_def]
  exact (extendMap_comp _ _ _).symm.trans <|
    (congrArg (extendMap · _) (τ.naturality _)).trans (extendMap_comp _ _ _)

variable [HasPullbacks A] [∀ q, Mono (Φ.map (TopPair.ofSubset (X q)).map)]
  [∀ q, Mono (Ψ.map (TopPair.ofSubset (X q)).map)]

/-- Each stage of the filtration of `Φ(Y)` is carried into the same stage of the filtration of
`Ψ(Y)` by `τ`. -/
lemma factors_chainFiltration_arrow_comp_extendMap_app (q : ℤ) :
    (chainFiltration Ψ X q).Factors ((chainFiltration Φ X q).arrow ≫
      extendMap (τ.app Y) ComplexShape.embeddingDownNat) := by
  rw [chainFiltration_def Ψ, ← chainFiltrationIso_hom_comp_chainFiltrationι_assoc,
    chainFiltrationι_comp_extendMap_app, ← Category.assoc]
  exact Subobject.factors_of_factors_right _ (Subobject.mk_factors_self _)

end

variable [Abelian A] {Φ Ψ Θ : TopCat.{w} ⥤ ChainComplex A ℕ} (τ : Φ ⟶ Ψ)
  [∀ q, Mono (Φ.map (TopPair.ofSubset (X q)).map)] [∀ q, Mono (Ψ.map (TopPair.ofSubset (X q)).map)]
  (hX : Monotone X)

/-- **A natural transformation of chain functors is a morphism of filtered complexes**: the
morphism of the functors of the filtrations of `Φ(Y)` and `Ψ(Y)` by the `Φ(X q)` and `Ψ(X q)`
induced by `τ : Φ ⟶ Ψ`. -/
def chainFiltrationMap :
    CochainComplex.filtrationFunctor _ (monotone_chainFiltration Φ hX) ⟶
      CochainComplex.filtrationFunctor _ (monotone_chainFiltration Ψ hX) :=
  CochainComplex.filtrationFunctorMap _ _ (extendMap (τ.app Y) ComplexShape.embeddingDownNat)
    (factors_chainFiltration_arrow_comp_extendMap_app τ)

/-- The components of `TauCeti.chainFiltrationMap τ hX` are the restrictions of `τ.app Y`. -/
@[reassoc (attr := simp)]
lemma chainFiltrationMap_app_comp (a : EInt) :
    (chainFiltrationMap τ hX).app a ≫ (CochainComplex.filtrationFunctorObjIso _ _ a).hom ≫
        (CochainComplex.filtrationEInt (chainFiltration Ψ X) a).arrow =
      (CochainComplex.filtrationFunctorObjIso _ _ a).hom ≫
        (CochainComplex.filtrationEInt (chainFiltration Φ X) a).arrow ≫
          extendMap (τ.app Y) ComplexShape.embeddingDownNat :=
  CochainComplex.filtrationFunctorMap_app_comp _ _ _

variable (Φ) in
/-- The identity natural transformation induces the identity of the filtration functor. -/
@[simp]
lemma chainFiltrationMap_id : chainFiltrationMap (𝟙 Φ) hX = 𝟙 _ := by
  rw [chainFiltrationMap, CochainComplex.filtrationFunctorMap_congr (f' := 𝟙 _)
    (by rw [NatTrans.id_app, extendMap_id]),
    CochainComplex.filtrationFunctorMap_id]

/-- A composite of natural transformations induces the composite of the morphisms of filtration
functors. -/
@[reassoc]
lemma chainFiltrationMap_comp [∀ q, Mono (Θ.map (TopPair.ofSubset (X q)).map)] (σ : Ψ ⟶ Θ) :
    chainFiltrationMap (τ ≫ σ) hX = chainFiltrationMap τ hX ≫ chainFiltrationMap σ hX := by
  rw [chainFiltrationMap, chainFiltrationMap, chainFiltrationMap,
    CochainComplex.filtrationFunctorMap_congr
      (f' := extendMap (τ.app Y) _ ≫ extendMap (σ.app Y) _)
      (by rw [NatTrans.comp_app, extendMap_comp]),
    CochainComplex.filtrationFunctorMap_comp _ _
      (factors_chainFiltration_arrow_comp_extendMap_app τ)
      (factors_chainFiltration_arrow_comp_extendMap_app σ)]

/-- On the stage `X q`, under the identifications of the stages with `Φ(X q)` and `Ψ(X q)`, the
morphism of filtered complexes induced by `τ` is `τ.app (X q)`. -/
@[reassoc]
lemma chainFiltrationMap_app_coe_comp (q : ℤ) :
    (chainFiltrationMap τ hX).app q ≫ (CochainComplex.filtrationFunctorObjIsoOfEqMk _ _
        (chainFiltrationι Ψ X) (chainFiltration_def Ψ X) q).hom =
      (CochainComplex.filtrationFunctorObjIsoOfEqMk _ _ (chainFiltrationι Φ X)
        (chainFiltration_def Φ X) q).hom ≫
          extendMap (τ.app (TopPair.ofSubset (X q)).snd) ComplexShape.embeddingDownNat := by
  rw [← cancel_mono (chainFiltrationι Ψ X q)]
  simp only [Category.assoc, CochainComplex.filtrationFunctorObjIsoOfEqMk_hom_comp,
    ← chainFiltrationι_comp_extendMap_app,
    CochainComplex.filtrationFunctorObjIsoOfEqMk_hom_comp_assoc,
    CochainComplex.filtrationFunctorArrow, chainFiltrationMap_app_comp]

variable [QuasiIso (τ.app Y)] [∀ q, QuasiIso (τ.app (TopPair.ofSubset (X q)).snd)]

/-- If the components of `τ` at `Y` and at the `X q` are quasi-isomorphisms, so is every component
of the morphism of filtered complexes it induces. -/
instance quasiIso_chainFiltrationMap_app (a : EInt) :
    QuasiIso ((chainFiltrationMap τ hX).app a) :=
  CochainComplex.quasiIso_filtrationFunctorMap_app _ _ (fun q ↦
    (quasiIso_iff_of_arrow_mk_iso _
      (extendMap (τ.app (TopPair.ofSubset (X q)).snd) ComplexShape.embeddingDownNat)
      (Arrow.isoMk (CochainComplex.filtrationFunctorObjIsoOfEqMk _ _ (chainFiltrationι Φ X)
        (chainFiltration_def Φ X) q) (CochainComplex.filtrationFunctorObjIsoOfEqMk _ _
          (chainFiltrationι Ψ X) (chainFiltration_def Ψ X) q)
        (chainFiltrationMap_app_coe_comp τ hX q).symm)).2 inferInstance) a

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

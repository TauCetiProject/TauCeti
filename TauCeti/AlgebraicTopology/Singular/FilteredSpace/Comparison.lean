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
it is a morphism of filtered complexes (`TauCeti.chainFiltrationMap`). If every component of `τ`
is a quasi-isomorphism, then so is every component of this morphism, and it induces an
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

variable {A : Type u} [Category.{v} A] [Abelian A] {Y : TopCat.{w}} {X : ℤ → Set Y}
  {Φ Ψ : TopCat.{w} ⥤ ChainComplex A ℕ} (τ : Φ ⟶ Ψ)

/-- A natural transformation `τ : Φ ⟶ Ψ` carries `Φ(X q)` into `Ψ(X q)`. -/
@[reassoc]
lemma chainFiltrationι_comp_extendMap_app (q : ℤ) :
    chainFiltrationι Φ X q ≫ extendMap (τ.app Y) ComplexShape.embeddingDownNat =
      extendMap (τ.app (TopPair.ofSubset (X q)).snd) ComplexShape.embeddingDownNat ≫
        chainFiltrationι Ψ X q := by
  rw [chainFiltrationι_def, chainFiltrationι_def]
  exact (extendMap_comp _ _ _).symm.trans <|
    (congrArg (extendMap · _) (τ.naturality _)).trans (extendMap_comp _ _ _)

variable [∀ P : TopPair.{w}, Mono (Φ.map P.map)] [∀ P : TopPair.{w}, Mono (Ψ.map P.map)]

/-- Each stage of the filtration of `Φ(Y)` is carried into the same stage of the filtration of
`Ψ(Y)` by `τ`. -/
lemma factors_chainFiltration_arrow_comp_extendMap_app (q : ℤ) :
    (chainFiltration Ψ X q).Factors ((chainFiltration Φ X q).arrow ≫
      extendMap (τ.app Y) ComplexShape.embeddingDownNat) := by
  rw [chainFiltration_def Ψ]
  exact (Subobject.mk_factors_iff _ _).2 ⟨(chainFiltrationIso Φ X q).hom ≫
      extendMap (τ.app (TopPair.ofSubset (X q)).snd) ComplexShape.embeddingDownNat,
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·)
      (chainFiltrationι_comp_extendMap_app τ q).symm).trans <|
        chainFiltrationIso_hom_comp_chainFiltrationι_assoc _ _ _ _⟩

variable (hX : Monotone X)

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

/-- On the stage `X q`, under the identifications of the stages with `Φ(X q)` and `Ψ(X q)`, the
morphism of filtered complexes induced by `τ` is `τ.app (X q)`. -/
lemma chainFiltrationMap_app_coe_comp (q : ℤ) :
    (chainFiltrationMap τ hX).app q ≫ (CochainComplex.filtrationFunctorObjIso _ _ q).hom ≫
        (Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ q)).hom ≫
          (chainFiltrationIso Ψ X q).hom =
      (CochainComplex.filtrationFunctorObjIso _ _ q).hom ≫
        (Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ q)).hom ≫
          (chainFiltrationIso Φ X q).hom ≫
            extendMap (τ.app (TopPair.ofSubset (X q)).snd) ComplexShape.embeddingDownNat := by
  rw [← cancel_mono (chainFiltrationι Ψ X q)]
  simp only [Subobject.isoOfEq, Category.assoc, chainFiltrationIso_hom_comp_chainFiltrationι,
    Subobject.ofLE_arrow, ← chainFiltrationι_comp_extendMap_app,
    chainFiltrationIso_hom_comp_chainFiltrationι_assoc, Subobject.ofLE_arrow_assoc,
    chainFiltrationMap_app_comp]

/-- If every component of `τ` is a quasi-isomorphism, so is every component of the morphism of
filtered complexes it induces: at `⊥` both sides are zero, at `q` it is `τ.app (X q)`, and at `⊤`
it is `τ.app Y`. -/
instance quasiIso_chainFiltrationMap_app [∀ Z, QuasiIso (τ.app Z)] (a : EInt) :
    QuasiIso ((chainFiltrationMap τ hX).app a) := by
  induction a using WithBotTop.rec with
  | bot =>
    have : IsIso ((chainFiltrationMap τ hX).app ⊥) :=
      isIso_of_source_target_iso_zero _
        (CochainComplex.filtrationFunctorObjIso _ _ ⊥ ≪≫
          Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_bot _) ≪≫ Subobject.botCoeIsoZero)
        (CochainComplex.filtrationFunctorObjIso _ _ ⊥ ≪≫
          Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_bot _) ≪≫ Subobject.botCoeIsoZero)
    infer_instance
  | coe q =>
    have : QuasiIso (extendMap (τ.app (TopPair.ofSubset (X q)).snd)
        ComplexShape.embeddingDownNat) :=
      (quasiIso_extendMap_iff _ _).2 inferInstance
    exact (quasiIso_iff_of_arrow_mk_iso _
      (extendMap (τ.app (TopPair.ofSubset (X q)).snd) ComplexShape.embeddingDownNat) (Arrow.isoMk
      (CochainComplex.filtrationFunctorObjIso _ _ q ≪≫
        Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ q) ≪≫ chainFiltrationIso Φ X q)
      (CochainComplex.filtrationFunctorObjIso _ _ q ≪≫
        Subobject.isoOfEq _ _ (CochainComplex.filtrationEInt_coe _ q) ≪≫ chainFiltrationIso Ψ X q)
      (by
        simp only [Arrow.mk_hom, Iso.trans_hom, Category.assoc]
        exact (chainFiltrationMap_app_coe_comp τ hX q).symm))).2 inferInstance
  | top =>
    have : QuasiIso (extendMap (τ.app Y) ComplexShape.embeddingDownNat) :=
      (quasiIso_extendMap_iff _ _).2 inferInstance
    have : IsIso (CochainComplex.filtrationEInt (chainFiltration Φ X) ⊤).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 (CochainComplex.filtrationEInt_top _)
    have : IsIso (CochainComplex.filtrationEInt (chainFiltration Ψ X) ⊤).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 (CochainComplex.filtrationEInt_top _)
    rw [← quasiIso_iff_comp_right _ ((CochainComplex.filtrationFunctorObjIso _ _ ⊤).hom ≫
      (CochainComplex.filtrationEInt (chainFiltration Ψ X) ⊤).arrow), chainFiltrationMap_app_comp]
    infer_instance

/-- **A natural transformation of chain functors by quasi-isomorphisms identifies the spectral
sequences of a filtered space.** The spectral objects of the filtrations of `Φ(Y)` and `Ψ(Y)` by
the `Φ(X q)` and `Ψ(X q)` are isomorphic through `τ`. -/
def chainFiltrationSpectralObjectIso [∀ Z, QuasiIso (τ.app Z)] :
    CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_chainFiltration Φ hX)) ≅
      CochainComplex.spectralObject
        (CochainComplex.filtrationFunctor _ (monotone_chainFiltration Ψ hX)) :=
  have := CochainComplex.isIso_spectralObjectMap (chainFiltrationMap τ hX)
  asIso (CochainComplex.spectralObjectMap (chainFiltrationMap τ hX))

/-- The isomorphism `TauCeti.chainFiltrationSpectralObjectIso τ hX` is the morphism of spectral
objects induced by `TauCeti.chainFiltrationMap τ hX`. -/
@[simp]
lemma chainFiltrationSpectralObjectIso_hom [∀ Z, QuasiIso (τ.app Z)] :
    (chainFiltrationSpectralObjectIso τ hX).hom =
      CochainComplex.spectralObjectMap (chainFiltrationMap τ hX) := by
  simp [chainFiltrationSpectralObjectIso]

end TauCeti

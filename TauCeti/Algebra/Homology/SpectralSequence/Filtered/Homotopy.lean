/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.Algebra.Homology.SpectralObject.SpectralSequenceMap
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality

/-!
# Homotopy invariance of the spectral sequence of a filtered complex

Two morphisms `f, g : K ⟶ L` of cochain complexes sending each piece `F n` of an increasing
filtration of `K` into the piece `G n` of one of `L` induce morphisms of the spectral objects of
the filtrations, `CochainComplex.spectralObjectMap (CochainComplex.filtrationFunctorMap f hf)`,
and hence, through `CategoryTheory.Abelian.SpectralObject.spectralSequenceMap`, of their spectral
sequences, on every page. A *filtered homotopy* between `f` and `g` is a homotopy whose components
also send `F n` into `G n`, in each degree. This file shows that filtered homotopic morphisms
induce the same morphism of spectral objects
(`CochainComplex.spectralObjectMap_filtrationFunctorMap_eq_of_homotopy`), so the same morphism of
spectral sequences.

The proof restricts the homotopy to the pieces of the filtrations (`Homotopy.liftMono`), where
it is a homotopy between the components of the two morphisms of filtration functors, compatible
with the inclusions of the pieces. Compatible homotopies between natural transformations of
functors to cochain complexes induce the same morphism of spectral objects
(`CochainComplex.spectralObjectMap_eq_of_homotopy`), because they give homotopic maps of
mapping cones.

## Main results

* `CochainComplex.spectralObjectMap_filtrationFunctorMap_eq_of_homotopy`: filtered homotopic
  morphisms of filtered complexes induce the same morphism of spectral objects.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, second edition, Cambridge University
  Press, 2001, §2.2 (morphisms of filtered complexes and filtered homotopies).
-/

public section

open CategoryTheory Limits

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

section Filtration

variable {K L : CochainComplex C ℤ} {F : ℤ → Subobject K} {hF : Monotone F}
  {G : ℤ → Subobject L} {hG : Monotone G} {f g : K ⟶ L}

/-- A homotopy whose components send each piece `F n` into `G n` also sends the pieces of the
extensions of the filtrations to `EInt` into each other. -/
private lemma exists_comp_arrow_eq_filtrationEInt (H : Homotopy f g)
    (hH : ∀ n p q, ∃ k : (F n : CochainComplex C ℤ).X p ⟶ (G n : CochainComplex C ℤ).X q,
      k ≫ (G n).arrow.f q = (F n).arrow.f p ≫ H.hom p q) (a : EInt) (p q : ℤ) :
    ∃ k : (filtrationEInt F a : CochainComplex C ℤ).X p ⟶
        (filtrationEInt G a : CochainComplex C ℤ).X q,
      k ≫ (filtrationEInt G a).arrow.f q = (filtrationEInt F a).arrow.f p ≫ H.hom p q := by
  induction a using WithBotTop.rec with
  | bot =>
    rw [filtrationEInt_bot, filtrationEInt_bot]
    exact ⟨0, by simp [Subobject.bot_arrow]⟩
  | coe n =>
    rw [filtrationEInt_coe, filtrationEInt_coe]
    exact hH n p q
  | top =>
    rw [filtrationEInt_top, filtrationEInt_top]
    exact ⟨(⊤ : Subobject K).arrow.f p ≫ H.hom p q ≫ inv ((⊤ : Subobject L).arrow.f q), by simp⟩

variable (hF hG) in
/-- **Homotopy invariance of the spectral object of a filtered complex.** Two morphisms `f` and
`g` of filtered complexes which are homotopic through a homotopy `H` whose components send each
piece `F n` into `G n`, in each degree, induce the same morphism of spectral objects. -/
theorem spectralObjectMap_filtrationFunctorMap_eq_of_homotopy
    (hf : ∀ n, (G n).Factors ((F n).arrow ≫ f)) (hg : ∀ n, (G n).Factors ((F n).arrow ≫ g))
    (H : Homotopy f g)
    (hH : ∀ n p q, ∃ k : (F n : CochainComplex C ℤ).X p ⟶ (G n : CochainComplex C ℤ).X q,
      k ≫ (G n).arrow.f q = (F n).arrow.f p ≫ H.hom p q) :
    spectralObjectMap (filtrationFunctorMap hF hG f hf) =
      spectralObjectMap (filtrationFunctorMap hF hG g hg) := by
  choose k hk using exists_comp_arrow_eq_filtrationEInt H hH
  -- Restrict `H` to the pieces of the filtrations, through the inclusions of the pieces.
  let k' (a : EInt) (p q : ℤ) :
      ((filtrationFunctor F hF).obj a).X p ⟶ ((filtrationFunctor G hG).obj a).X q :=
    (filtrationFunctorObjIso F hF a).hom.f p ≫ k a p q ≫ (filtrationFunctorObjIso G hG a).inv.f q
  have hk' (a : EInt) (p q : ℤ) : k' a p q ≫ (filtrationFunctorArrow G hG a).f q =
      (filtrationFunctorArrow F hF a).f p ≫ H.hom p q := by
    simp only [k', filtrationFunctorArrow, HomologicalComplex.comp_f, Category.assoc]
    rw [← HomologicalComplex.comp_f_assoc, Iso.inv_hom_id, HomologicalComplex.id_f,
      Category.id_comp, hk]
  let h (a : EInt) : Homotopy ((filtrationFunctorMap hF hG f hf).app a)
      ((filtrationFunctorMap hF hG g hg).app a) :=
    Homotopy.liftMono H (filtrationFunctorArrow F hF a) (filtrationFunctorArrow G hG a) (k' a)
      (hk' a) (by simp [filtrationFunctorArrow]) (by simp [filtrationFunctorArrow])
  refine spectralObjectMap_eq_of_homotopy h fun a b u p q ↦ ?_
  -- Both sides are restrictions of `H`, as the inclusions of the pieces show.
  rw [← cancel_mono ((filtrationFunctorArrow G hG b).f q)]
  simp only [h, Homotopy.liftMono_hom, Category.assoc, hk']
  rw [← HomologicalComplex.comp_f_assoc, filtrationFunctor_map_comp_arrow,
    ← HomologicalComplex.comp_f, filtrationFunctor_map_comp_arrow, hk']

end Filtration

end CochainComplex

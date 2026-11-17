/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality

/-!
# Filtered homotopies induce equal maps of spectral sequences

Let `f g : K ⟶ L` be morphisms of cochain complexes which send each piece `F n` of an increasing
filtration of `K` into the piece `G n` of an increasing filtration of `L`, and let `h` be a chain
homotopy from `f` to `g` which is **filtered**: each of its components `Kᵖ ⟶ L^q` sends `(F n)ᵖ`
into `(G n)^q`. Then `f` and `g` induce the same morphism of spectral objects
(`CochainComplex.spectralObjectMap_filtrationFunctorMap_eq_of_homotopy`), and hence the same
morphism of spectral sequences, on every page. Consequently a filtered
homotopy equivalence induces an isomorphism of spectral objects
(`CochainComplex.isIso_spectralObjectMap_filtrationFunctorMap`), and so of spectral sequences.

This is the homotopy half of the naturality of the spectral sequence of a filtered complex, whose
functoriality in morphisms of filtered complexes is `CochainComplex.filtrationFunctorMap`. It is
what makes the spectral sequence of a filtered complex independent of choices made only up to
filtered homotopy, as for the filtered chain complexes of Morse and Floer theory.

The proof applies `CochainComplex.spectralObjectMap_eq_of_homotopy`: two natural transformations
`α β : F ⟶ G` of functors `ι ⥤ CochainComplex C ℤ` induce the same morphism of spectral objects as
soon as there are homotopies from each `α.app i` to `β.app i` which commute with the transition
maps. A filtered homotopy restricts to such homotopies between the maps of the pieces of the
filtrations (`CochainComplex.filtrationFunctorHomotopy`), and these restrictions commute with the
inclusions of the pieces.

## Main definitions

* `CochainComplex.filtrationFunctorHomotopy`: the restriction of a filtered homotopy to the pieces
  of the filtrations.

## Main results

* `CochainComplex.spectralObjectMap_filtrationFunctorMap_eq_of_homotopy`: filtered homotopic
  morphisms of filtered complexes induce the same morphism of spectral objects, and so of spectral
  sequences.
* `CochainComplex.isIso_spectralObjectMap_filtrationFunctorMap`: a filtered homotopy equivalence
  induces an isomorphism of spectral objects.

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Section 5.4 (the spectral sequence of a
  filtered complex).
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge Studies in Advanced
  Mathematics 58, Cambridge University Press, 2001, Section 2.2.
-/

public section

open CategoryTheory Limits

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

section Filtration

variable {K L : CochainComplex C ℤ} {F : ℤ → Subobject K} {hF : Monotone F}
  {G : ℤ → Subobject L} {hG : Monotone G} {f g : K ⟶ L}
  {hf : ∀ n, (G n).Factors ((F n).arrow ≫ f)} {hg : ∀ n, (G n).Factors ((F n).arrow ≫ g)}

variable (F hF) in
/-- At an integer `n`, the inclusion of the piece of the filtration functor is the inclusion of the
subcomplex `F n`. -/
private lemma filtrationFunctorArrow_coe (n : ℤ) :
    filtrationFunctorArrow F hF n = eqToHom (filtrationFunctor_obj_coe F hF n) ≫ (F n).arrow := by
  rw [← eqToHom_comp_filtrationFunctorArrow F hF n, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]

variable (hF hG) in
/-- A filtered homotopy restricts to the pieces of the extensions of the filtrations to `EInt`:
there it is automatic at `⊥`, where the source piece is zero, and at `⊤`, where the target piece
is the whole complex. -/
private lemma exists_comp_filtrationFunctorArrow_eq (h : Homotopy f g)
    (hh : ∀ n p q, ∃ k : (F n : CochainComplex C ℤ).X p ⟶ (G n : CochainComplex C ℤ).X q,
      k ≫ (G n).arrow.f q = (F n).arrow.f p ≫ h.hom p q) (a : EInt) (p q : ℤ) :
    ∃ k : ((filtrationFunctor F hF).obj a).X p ⟶ ((filtrationFunctor G hG).obj a).X q,
      k ≫ (filtrationFunctorArrow G hG a).f q =
        (filtrationFunctorArrow F hF a).f p ≫ h.hom p q := by
  induction a using WithBotTop.rec with
  | bot =>
    have hz : IsZero ((filtrationFunctor F hF).obj ⊥) := by
      rw [filtrationFunctor_obj, filtrationEInt_bot]
      exact IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero
    exact ⟨0, ((HomologicalComplex.eval C _ p).map_isZero hz).eq_of_src _ _⟩
  | coe n =>
    obtain ⟨k, hk⟩ := hh n p q
    refine ⟨(eqToHom (filtrationFunctor_obj_coe F hF n)).f p ≫ k ≫
      (eqToHom (filtrationFunctor_obj_coe G hG n).symm).f q, ?_⟩
    rw [filtrationFunctorArrow_coe, filtrationFunctorArrow_coe, HomologicalComplex.comp_f,
      HomologicalComplex.comp_f, Category.assoc, Category.assoc, ← HomologicalComplex.comp_f_assoc,
      eqToHom_trans, eqToHom_refl, HomologicalComplex.id_f, Category.id_comp, hk, Category.assoc]
  | top =>
    have : IsIso (filtrationEInt G (⊤ : EInt)).arrow := by
      rw [filtrationEInt_top]
      infer_instance
    have : IsIso ((HomologicalComplex.eval C _ q).map (filtrationFunctorArrow G hG ⊤)) :=
      inferInstance
    exact ⟨(filtrationFunctorArrow F hF ⊤).f p ≫ h.hom p q ≫
      inv ((filtrationFunctorArrow G hG ⊤).f q), by simp⟩

variable (hF hG) in
/-- **The restriction of a filtered homotopy to the pieces of the filtrations.** A homotopy `h`
from `f` to `g` whose components send each piece `F n` into `G n` restricts, for every
`a : EInt`, to a homotopy between the maps of the pieces at `a` of the filtrations, extended by
`⊥` and `⊤`, which `f` and `g` induce. Its components are characterized by
`filtrationFunctorHomotopy_hom_comp`. -/
noncomputable def filtrationFunctorHomotopy (h : Homotopy f g)
    (hh : ∀ n p q, ∃ k : (F n : CochainComplex C ℤ).X p ⟶ (G n : CochainComplex C ℤ).X q,
      k ≫ (G n).arrow.f q = (F n).arrow.f p ≫ h.hom p q) (a : EInt) :
    Homotopy ((filtrationFunctorMap hF hG f hf).app a) ((filtrationFunctorMap hF hG g hg).app a)
    where
  hom p q := (exists_comp_filtrationFunctorArrow_eq hF hG h hh a p q).choose
  zero p q hpq := by
    rw [← cancel_mono ((filtrationFunctorArrow G hG a).f q),
      (exists_comp_filtrationFunctorArrow_eq hF hG h hh a p q).choose_spec, h.zero p q hpq,
      comp_zero, zero_comp]
  comm p := by
    have hk : (fun p q ↦ (exists_comp_filtrationFunctorArrow_eq hF hG h hh a p q).choose ≫
        (filtrationFunctorArrow G hG a).f q) =
          fun p q ↦ (filtrationFunctorArrow F hF a).f p ≫ h.hom p q :=
      funext fun p ↦ funext fun q ↦
        (exists_comp_filtrationFunctorArrow_eq hF hG h hh a p q).choose_spec
    have hfa (u : K ⟶ L) (hu : ∀ n, (G n).Factors ((F n).arrow ≫ u)) :
        ((filtrationFunctorMap hF hG u hu).app a).f p ≫ (filtrationFunctorArrow G hG a).f p =
          (filtrationFunctorArrow F hF a).f p ≫ u.f p := by
      simpa only [HomologicalComplex.comp_f, Category.assoc] using
        HomologicalComplex.congr_hom (filtrationFunctorMap_app_comp (hF := hF) (hG := hG) u hu a) p
    rw [← cancel_mono ((filtrationFunctorArrow G hG a).f p), Preadditive.add_comp,
      Preadditive.add_comp, hfa f hf, hfa g hg, ← dNext_comp_right, ← prevD_comp_right, hk,
      dNext_comp_left, prevD_comp_left, ← Preadditive.comp_add, ← Preadditive.comp_add, ← h.comm p]

variable (hF hG) in
/-- The components of the restriction of a filtered homotopy are those of the homotopy, on the
pieces of the filtrations. -/
@[reassoc]
lemma filtrationFunctorHomotopy_hom_comp (h : Homotopy f g)
    (hh : ∀ n p q, ∃ k : (F n : CochainComplex C ℤ).X p ⟶ (G n : CochainComplex C ℤ).X q,
      k ≫ (G n).arrow.f q = (F n).arrow.f p ≫ h.hom p q) (a : EInt) (p q : ℤ) :
    (filtrationFunctorHomotopy hF hG (hf := hf) (hg := hg) h hh a).hom p q ≫
        (filtrationFunctorArrow G hG a).f q =
      (filtrationFunctorArrow F hF a).f p ≫ h.hom p q :=
  (exists_comp_filtrationFunctorArrow_eq hF hG h hh a p q).choose_spec

/-- **Filtered homotopic maps induce the same morphism of spectral sequences.** Let `f` and `g`
be morphisms of filtered complexes, sending each piece `F n` into `G n`, and `h` a homotopy from
`f` to `g` whose components send each piece `F n` into `G n`. Then `f` and `g` induce the same
morphism of spectral objects, and so the same morphism of spectral sequences on every page. -/
theorem spectralObjectMap_filtrationFunctorMap_eq_of_homotopy (h : Homotopy f g)
    (hh : ∀ n p q, ∃ k : (F n : CochainComplex C ℤ).X p ⟶ (G n : CochainComplex C ℤ).X q,
      k ≫ (G n).arrow.f q = (F n).arrow.f p ≫ h.hom p q) :
    spectralObjectMap (filtrationFunctorMap hF hG f hf) =
      spectralObjectMap (filtrationFunctorMap hF hG g hg) := by
  refine spectralObjectMap_eq_of_homotopy _ _ (filtrationFunctorHomotopy hF hG h hh)
    fun a b u p q ↦ ?_
  rw [← cancel_mono ((filtrationFunctorArrow G hG b).f q), Category.assoc,
    filtrationFunctorHomotopy_hom_comp, Category.assoc, ← HomologicalComplex.comp_f,
    filtrationFunctor_map_comp_arrow, filtrationFunctorHomotopy_hom_comp,
    ← HomologicalComplex.comp_f_assoc, filtrationFunctor_map_comp_arrow]

/-- **A filtered homotopy equivalence induces an isomorphism of spectral objects.** Let
`f : K ⟶ L` and `g : L ⟶ K` be morphisms of filtered complexes and `h₁`, `h₂` homotopies from
`f ≫ g` to the identity of `K` and from `g ≫ f` to the identity of `L` whose components preserve
the filtrations. Then the morphism of spectral objects induced by `f` is an isomorphism, and so is
the morphism of spectral sequences it induces
(`CategoryTheory.Abelian.SpectralObject.isIso_spectralSequenceMap`). -/
theorem isIso_spectralObjectMap_filtrationFunctorMap {g : L ⟶ K}
    {hg : ∀ n, (F n).Factors ((G n).arrow ≫ g)} (h₁ : Homotopy (f ≫ g) (𝟙 K))
    (hh₁ : ∀ n p q, ∃ k : (F n : CochainComplex C ℤ).X p ⟶ (F n : CochainComplex C ℤ).X q,
      k ≫ (F n).arrow.f q = (F n).arrow.f p ≫ h₁.hom p q) (h₂ : Homotopy (g ≫ f) (𝟙 L))
    (hh₂ : ∀ n p q, ∃ k : (G n : CochainComplex C ℤ).X p ⟶ (G n : CochainComplex C ℤ).X q,
      k ≫ (G n).arrow.f q = (G n).arrow.f p ≫ h₂.hom p q) :
    IsIso (spectralObjectMap (filtrationFunctorMap hF hG f hf)) := by
  have hfg (n : ℤ) : (F n).Factors ((F n).arrow ≫ f ≫ g) := by
    rw [← Category.assoc, ← Subobject.factorThru_arrow _ _ (hf n), Category.assoc]
    exact Subobject.factors_of_factors_right _ (hg n)
  have hgf (n : ℤ) : (G n).Factors ((G n).arrow ≫ g ≫ f) := by
    rw [← Category.assoc, ← Subobject.factorThru_arrow _ _ (hg n), Category.assoc]
    exact Subobject.factors_of_factors_right _ (hf n)
  refine ⟨spectralObjectMap (filtrationFunctorMap hG hF g hg), ?_, ?_⟩
  · rw [← spectralObjectMap_comp, ← filtrationFunctorMap_comp f g hf hg hfg,
      spectralObjectMap_filtrationFunctorMap_eq_of_homotopy
        (hg := fun n ↦ by simpa using (F n).factors_self) h₁ hh₁,
      filtrationFunctorMap_id, spectralObjectMap_id]
  · rw [← spectralObjectMap_comp, ← filtrationFunctorMap_comp g f hg hf hgf,
      spectralObjectMap_filtrationFunctorMap_eq_of_homotopy
        (hg := fun n ↦ by simpa using (G n).factors_self) h₂ hh₂,
      filtrationFunctorMap_id, spectralObjectMap_id]

end Filtration

end CochainComplex

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality
import TauCeti.CategoryTheory.Subobject.FactorThru

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

* `Homotopy.IsFiltered`: a homotopy is filtered when its components send each piece of the
  filtration of the source into the corresponding piece of that of the target.
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

variable {C : Type*} [Category* C] [Abelian C]

namespace Homotopy

variable {K L : CochainComplex C ℤ} {f g : K ⟶ L}

/-- A homotopy `h` between morphisms `K ⟶ L` of cochain complexes is **filtered** with respect to
families `F` of subcomplexes of `K` and `G` of subcomplexes of `L` when each of its components
`Kᵖ ⟶ L^q` sends `(F n)ᵖ` into `(G n)^q`; see `Homotopy.isFiltered_iff`. -/
def IsFiltered (h : Homotopy f g) (F : ℤ → Subobject K) (G : ℤ → Subobject L) : Prop :=
  ∀ n p q, ∃ k : (F n : CochainComplex C ℤ).X p ⟶ (G n : CochainComplex C ℤ).X q,
    k ≫ (G n).arrow.f q = (F n).arrow.f p ≫ h.hom p q

/-- A homotopy `h` is filtered exactly when, for all `n`, `p` and `q`, the restriction of its
component `Kᵖ ⟶ L^q` to `(F n)ᵖ` factors through `(G n)^q`. -/
lemma isFiltered_iff {h : Homotopy f g} {F : ℤ → Subobject K} {G : ℤ → Subobject L} :
    h.IsFiltered F G ↔
      ∀ n p q, ∃ k : (F n : CochainComplex C ℤ).X p ⟶ (G n : CochainComplex C ℤ).X q,
        k ≫ (G n).arrow.f q = (F n).arrow.f p ≫ h.hom p q :=
  Iff.rfl

end Homotopy

namespace CochainComplex

section Filtration

variable {K L : CochainComplex C ℤ} {F : ℤ → Subobject K} {hF : Monotone F}
  {G : ℤ → Subobject L} {hG : Monotone G} {f g : K ⟶ L}
  {hf : ∀ n, (G n).Factors ((F n).arrow ≫ f)} {hg : ∀ n, (G n).Factors ((F n).arrow ≫ g)}

variable (hF hG) in
/-- A filtered homotopy restricts to the pieces of the extensions of the filtrations to `EInt`:
there it is automatic at `⊥`, where the source piece is zero, and at `⊤`, where the target piece
is the whole complex. -/
private lemma exists_comp_filtrationFunctorArrow_eq (h : Homotopy f g) (hh : h.IsFiltered F G)
    (a : EInt) (p q : ℤ) :
    ∃ k : ((filtrationFunctor F hF).obj a).X p ⟶ ((filtrationFunctor G hG).obj a).X q,
      k ≫ (filtrationFunctorArrow G hG a).f q =
        (filtrationFunctorArrow F hF a).f p ≫ h.hom p q := by
  induction a using WithBotTop.rec with
  | bot =>
    exact ⟨0, ((HomologicalComplex.eval C _ p).map_isZero
      (isZero_filtrationFunctor_obj_bot F hF)).eq_of_src _ _⟩
  | coe n =>
    obtain ⟨k, hk⟩ := Homotopy.isFiltered_iff.1 hh n p q
    refine ⟨(eqToHom (filtrationFunctor_obj_coe F hF n)).f p ≫ k ≫
      (eqToHom (filtrationFunctor_obj_coe G hG n).symm).f q, ?_⟩
    simp [filtrationFunctorArrow_coe, hk]
  | top =>
    exact ⟨(filtrationFunctorArrow F hF ⊤).f p ≫ h.hom p q ≫
      inv ((filtrationFunctorArrow G hG ⊤).f q), by simp⟩

variable (hF hG) in
/-- **The restriction of a filtered homotopy to the pieces of the filtrations.** A filtered
homotopy `h` from `f` to `g` restricts, for every `a : EInt`, to a homotopy between the maps of
the pieces at `a` of the filtrations, extended by `⊥` and `⊤`, which `f` and `g` induce. Its
components are characterized by `filtrationFunctorHomotopy_hom_comp`. -/
noncomputable def filtrationFunctorHomotopy (h : Homotopy f g) (hh : h.IsFiltered F G)
    (a : EInt) :
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
pieces of the filtrations. Not `@[simp]`: `HomologicalComplex.comp_f` unfolds the abbreviation
`filtrationFunctorArrow` in its left-hand side. -/
@[reassoc]
lemma filtrationFunctorHomotopy_hom_comp (h : Homotopy f g) (hh : h.IsFiltered F G) (a : EInt)
    (p q : ℤ) :
    (filtrationFunctorHomotopy hF hG (hf := hf) (hg := hg) h hh a).hom p q ≫
        (filtrationFunctorArrow G hG a).f q =
      (filtrationFunctorArrow F hF a).f p ≫ h.hom p q :=
  (exists_comp_filtrationFunctorArrow_eq hF hG h hh a p q).choose_spec

/-- **Filtered homotopic maps induce the same morphism of spectral sequences.** Let `f` and `g`
be morphisms of filtered complexes, sending each piece `F n` into `G n`, and `h` a homotopy from
`f` to `g` whose components send each piece `F n` into `G n`. Then `f` and `g` induce the same
morphism of spectral objects, and so the same morphism of spectral sequences on every page. -/
theorem spectralObjectMap_filtrationFunctorMap_eq_of_homotopy (h : Homotopy f g)
    (hh : h.IsFiltered F G) :
    spectralObjectMap (filtrationFunctorMap hF hG f hf) =
      spectralObjectMap (filtrationFunctorMap hF hG g hg) := by
  refine spectralObjectMap_eq_of_homotopy _ _ (filtrationFunctorHomotopy hF hG h hh)
    fun a b u p q ↦ ?_
  rw [← cancel_mono ((filtrationFunctorArrow G hG b).f q)]
  simp [filtrationFunctorHomotopy_hom_comp, ← HomologicalComplex.comp_f,
    ← HomologicalComplex.comp_f_assoc]

/-- **A filtered homotopy equivalence induces an isomorphism of spectral objects.** Let
`f : K ⟶ L` and `g : L ⟶ K` be morphisms of filtered complexes and `h₁`, `h₂` homotopies from
`f ≫ g` to the identity of `K` and from `g ≫ f` to the identity of `L` whose components preserve
the filtrations. Then the morphism of spectral objects induced by `f` is an isomorphism, and so is
the morphism of spectral sequences it induces
(`CategoryTheory.Abelian.SpectralObject.isIso_spectralSequenceMap`). -/
theorem isIso_spectralObjectMap_filtrationFunctorMap {g : L ⟶ K}
    {hg : ∀ n, (F n).Factors ((G n).arrow ≫ g)} (h₁ : Homotopy (f ≫ g) (𝟙 K))
    (hh₁ : h₁.IsFiltered F F) (h₂ : Homotopy (g ≫ f) (𝟙 L)) (hh₂ : h₂.IsFiltered G G) :
    IsIso (spectralObjectMap (filtrationFunctorMap hF hG f hf)) := by
  refine ⟨spectralObjectMap (filtrationFunctorMap hG hF g hg), ?_, ?_⟩
  · rw [← spectralObjectMap_comp, ← filtrationFunctorMap_comp f g hf hg
        fun n ↦ Subobject.factors_comp_of_factors (hf n) (hg n),
      spectralObjectMap_filtrationFunctorMap_eq_of_homotopy
        (hg := fun n ↦ by simpa using (F n).factors_self) h₁ hh₁,
      filtrationFunctorMap_id, spectralObjectMap_id]
  · rw [← spectralObjectMap_comp, ← filtrationFunctorMap_comp g f hg hf
        fun n ↦ Subobject.factors_comp_of_factors (hg n) (hf n),
      spectralObjectMap_filtrationFunctorMap_eq_of_homotopy
        (hg := fun n ↦ by simpa using (G n).factors_self) h₂ hh₂,
      filtrationFunctorMap_id, spectralObjectMap_id]

end Filtration

end CochainComplex

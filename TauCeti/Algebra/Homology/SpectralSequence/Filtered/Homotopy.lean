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

A homotopy which only **raises the filtrations by at most `s`**, sending each `(F n)ᵖ` into
`(G (n + s))^q`, need not give equal morphisms of spectral objects, nor equal maps on the first
pages, but `f` and `g` still induce the same morphism on every page `r ≥ s + 2`
(`CochainComplex.spectralSequenceMap_filtrationFunctorMap_hom_eq_of_homotopy`), that is, in the
classical homological numbering in which Mathlib's page `r` is `E_{r-1}`, from `E_{s+1}` on. For
`s = 1` this is the case of a cellular homotopy, which carries the `p`-skeleton into the
`(p + 1)`-skeleton, and the maps agree from `E₂` on. Accordingly a homotopy equivalence of filtered
complexes whose two homotopies raise the filtrations by at most `s` induces isomorphisms on the
pages `r ≥ s + 2` (`CochainComplex.isIso_spectralSequenceMap_filtrationFunctorMap_hom`).

The proof compares the two maps on representatives. The object at `(p, q)` of page `r` is the
image of `H^n(F_{q+1}/F_{q-r+2}) ⟶ H^n(F_{q+r-1}/F_q)` (`CochainComplex.toSpectralSequencePageX`,
`CochainComplex.fromSpectralSequencePageX`), so it suffices that `f` and `g` induce the same map
`H^n(F_{q+1}/F_{q-r+2}) ⟶ H^n(G_{q+r-1}/G_q)`. For `r ≥ s + 2` the homotopy sends `F_{q+1}` into
`G_{q+r-1}` and `F_{q-r+2}` into `G_q`, so it restricts (`Homotopy.restrict`) and descends
(`Homotopy.descCokernel`) to a homotopy between the induced maps of quotient complexes.

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
* `CochainComplex.spectralSequenceMap_filtrationFunctorMap_hom_eq_of_homotopy`: morphisms of
  filtered complexes homotopic through a homotopy raising the filtrations by at most `s` induce the
  same morphism on every page `r ≥ s + 2`.
* `CochainComplex.isIso_spectralSequenceMap_filtrationFunctorMap_hom`: a homotopy equivalence
  through homotopies raising the filtrations by at most `s` induces isomorphisms on the pages
  `r ≥ s + 2`.

## References

* H. Cartan, S. Eilenberg, *Homological Algebra*, Princeton University Press, 1956, Chapter XV,
  §3 (homotopies raising the filtration).
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
    Homotopy ((filtrationFunctorMap hF hG f hf).app a) ((filtrationFunctorMap hF hG g hg).app a) :=
  h.restrict (filtrationFunctorArrow F hF a) (filtrationFunctorArrow G hG a)
    (by simp) (by simp)
    (fun p q ↦ (exists_comp_filtrationFunctorArrow_eq hF hG h hh a p q).choose)
    (fun p q ↦ (exists_comp_filtrationFunctorArrow_eq hF hG h hh a p q).choose_spec)

variable (hF hG) in
/-- The components of the restriction of a filtered homotopy are those of the homotopy, on the
pieces of the filtrations. Not `@[simp]`: `HomologicalComplex.comp_f` unfolds the abbreviation
`filtrationFunctorArrow` in its left-hand side. -/
@[reassoc]
lemma filtrationFunctorHomotopy_hom_comp (h : Homotopy f g) (hh : h.IsFiltered F G) (a : EInt)
    (p q : ℤ) :
    (filtrationFunctorHomotopy hF hG (hf := hf) (hg := hg) h hh a).hom p q ≫
        (filtrationFunctorArrow G hG a).f q =
      (filtrationFunctorArrow F hF a).f p ≫ h.hom p q := by
  rw [filtrationFunctorHomotopy, Homotopy.restrict_hom]
  exact (exists_comp_filtrationFunctorArrow_eq hF hG h hh a p q).choose_spec

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

section Shift

open TauCeti (eIntHomOfLE)
open Abelian.SpectralObject

variable {K L : CochainComplex C ℤ} {F : ℤ → Subobject K} {hF : Monotone F}
  {G : ℤ → Subobject L} {hG : Monotone G} {f g : K ⟶ L}
  {hf : ∀ n, (G n).Factors ((F n).arrow ≫ f)} {hg : ∀ n, (G n).Factors ((F n).arrow ≫ g)}

variable (hF hG) in
/-- A homotopy raising the filtrations by at most `s` sends the piece `F a` into every piece
`G b` with `a + s ≤ b`. -/
private lemma exists_comp_filtrationFunctorArrow_eq_of_add_le (h : Homotopy f g) {s : ℤ}
    (hh : h.IsFiltered F fun n ↦ G (n + s)) {a b : ℤ} (hab : a + s ≤ b) (p q : ℤ) :
    ∃ k : ((filtrationFunctor F hF).obj a).X p ⟶ ((filtrationFunctor G hG).obj b).X q,
      k ≫ (filtrationFunctorArrow G hG b).f q =
        (filtrationFunctorArrow F hF a).f p ≫ h.hom p q := by
  obtain ⟨k, hk⟩ := Homotopy.isFiltered_iff.1 hh a p q
  refine ⟨(eqToHom (filtrationFunctor_obj_coe F hF a)).f p ≫ k ≫
    (Subobject.ofLE _ _ (hG hab)).f q ≫ (eqToHom (filtrationFunctor_obj_coe G hG b).symm).f q, ?_⟩
  have hle : (Subobject.ofLE _ _ (hG hab)).f q ≫ (G b).arrow.f q = (G (a + s)).arrow.f q := by
    rw [← HomologicalComplex.comp_f, Subobject.ofLE_arrow]
  simp only [filtrationFunctorArrow_coe, HomologicalComplex.comp_f, Category.assoc,
    HomologicalComplex.eqToHom_f, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [hle, hk]

variable (hF hG) in
/-- The restriction of a homotopy raising the filtrations by at most `s` to a homotopy between
the maps `F a ⟶ G b` induced by `f` and `g`, for `a ≤ b` and `a + s ≤ b`. -/
private noncomputable def filtrationFunctorHomotopyOfAddLE (h : Homotopy f g) {s : ℤ}
    (hh : h.IsFiltered F fun n ↦ G (n + s)) {a b : ℤ} (hab : a ≤ b) (hsab : a + s ≤ b) :
    Homotopy ((filtrationFunctorMap hF hG f hf).app a ≫
        (filtrationFunctor G hG).map (eIntHomOfLE hab))
      ((filtrationFunctorMap hF hG g hg).app a ≫
        (filtrationFunctor G hG).map (eIntHomOfLE hab)) :=
  h.restrict (filtrationFunctorArrow F hF a) (filtrationFunctorArrow G hG b)
    (by simp [filtrationFunctor_map_comp_arrow]) (by simp [filtrationFunctor_map_comp_arrow])
    (fun p q ↦ (exists_comp_filtrationFunctorArrow_eq_of_add_le hF hG h hh hsab p q).choose)
    (fun p q ↦ (exists_comp_filtrationFunctorArrow_eq_of_add_le hF hG h hh hsab p q).choose_spec)

variable (hF hG) in
private lemma filtrationFunctorHomotopyOfAddLE_hom_comp (h : Homotopy f g) {s : ℤ}
    (hh : h.IsFiltered F fun n ↦ G (n + s)) {a b : ℤ} (hab : a ≤ b) (hsab : a + s ≤ b)
    (p q : ℤ) :
    (filtrationFunctorHomotopyOfAddLE hF hG (hf := hf) (hg := hg) h hh hab hsab).hom p q ≫
        (filtrationFunctorArrow G hG b).f q =
      (filtrationFunctorArrow F hF a).f p ≫ h.hom p q := by
  rw [filtrationFunctorHomotopyOfAddLE, Homotopy.restrict_hom]
  exact (exists_comp_filtrationFunctorArrow_eq_of_add_le hF hG h hh hsab p q).choose_spec

variable (hF hG) in
/-- The square through which a morphism of filtered complexes `u` induces the map of quotients
`F_{i₂}/F_{i₀} ⟶ G_{i₃}/G_{i₁}`, for `i₀ ≤ i₁`, `i₀ ≤ i₂`, `i₁ ≤ i₃` and `i₂ ≤ i₃`. -/
private lemma filtrationFunctorMap_quotient_w (u : K ⟶ L)
    (hu : ∀ n, (G n).Factors ((F n).arrow ≫ u)) {i₀ i₁ i₂ i₃ : ℤ} (h₀₁ : i₀ ≤ i₁) (h₀₂ : i₀ ≤ i₂)
    (h₁₃ : i₁ ≤ i₃) (h₂₃ : i₂ ≤ i₃) :
    ((filtrationFunctorMap hF hG u hu).app i₀ ≫ (filtrationFunctor G hG).map (eIntHomOfLE h₀₁)) ≫
        (filtrationFunctor G hG).map (eIntHomOfLE h₁₃) =
      (filtrationFunctor F hF).map (eIntHomOfLE h₀₂) ≫
        (filtrationFunctorMap hF hG u hu).app i₂ ≫
          (filtrationFunctor G hG).map (eIntHomOfLE h₂₃) := by
  symm
  rw [NatTrans.naturality_assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    -- the hom-types of the preorder `EInt` are subsingletons
    Subsingleton.elim (eIntHomOfLE h₀₂ ≫ eIntHomOfLE h₂₃) (eIntHomOfLE h₀₁ ≫ eIntHomOfLE h₁₃)]

variable (hF hG) in
/-- A homotopy raising the filtrations by at most `s` makes `f` and `g` induce the same map in
cohomology `H^n(F_{i₂}/F_{i₀}) ⟶ H^n(G_{i₃}/G_{i₁})` as soon as `i₀ + s ≤ i₁` and `i₂ + s ≤ i₃`:
it descends to a homotopy between the induced maps of quotients. -/
private lemma homologyMap_cokernelMap_eq_of_homotopy (h : Homotopy f g) {s : ℤ}
    (hh : h.IsFiltered F fun n ↦ G (n + s)) {i₀ i₁ i₂ i₃ : ℤ} (h₀₁ : i₀ ≤ i₁) (h₀₂ : i₀ ≤ i₂)
    (h₁₃ : i₁ ≤ i₃) (h₂₃ : i₂ ≤ i₃) (hs₀₁ : i₀ + s ≤ i₁) (hs₂₃ : i₂ + s ≤ i₃) (n : ℤ) :
    HomologicalComplex.homologyMap (cokernel.map ((filtrationFunctor F hF).map (eIntHomOfLE h₀₂))
        ((filtrationFunctor G hG).map (eIntHomOfLE h₁₃))
        ((filtrationFunctorMap hF hG f hf).app i₀ ≫ (filtrationFunctor G hG).map (eIntHomOfLE h₀₁))
        ((filtrationFunctorMap hF hG f hf).app i₂ ≫ (filtrationFunctor G hG).map (eIntHomOfLE h₂₃))
        (filtrationFunctorMap_quotient_w hF hG f hf h₀₁ h₀₂ h₁₃ h₂₃)) n =
      HomologicalComplex.homologyMap (cokernel.map ((filtrationFunctor F hF).map (eIntHomOfLE h₀₂))
        ((filtrationFunctor G hG).map (eIntHomOfLE h₁₃))
        ((filtrationFunctorMap hF hG g hg).app i₀ ≫ (filtrationFunctor G hG).map (eIntHomOfLE h₀₁))
        ((filtrationFunctorMap hF hG g hg).app i₂ ≫ (filtrationFunctor G hG).map (eIntHomOfLE h₂₃))
        (filtrationFunctorMap_quotient_w hF hG g hg h₀₁ h₀₂ h₁₃ h₂₃)) n := by
  refine (Homotopy.descCokernel
    (filtrationFunctorHomotopyOfAddLE hF hG (hf := hf) (hg := hg) h hh h₂₃ hs₂₃)
    ((filtrationFunctor F hF).map (eIntHomOfLE h₀₂)) (cokernel.π _) (cokernel.π _)
    (fun i ↦ by rw [← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f])
    (fun i ↦ isColimitCoforkMapOfIsColimit' (HomologicalComplex.eval C _ i)
      (cokernel.condition _) (cokernelIsCokernel _)) (fun i j ↦ ?_)
    (by simp [cokernel.map]) (by simp [cokernel.map])).homologyMap_eq n
  -- On `F_{i₀}`, the homotopy lands in `G_{i₁}`, which the quotient by `G_{i₁}` kills.
  obtain ⟨k, hk⟩ := exists_comp_filtrationFunctorArrow_eq_of_add_le hF hG h hh hs₀₁ i j
  have e : ((filtrationFunctor F hF).map (eIntHomOfLE h₀₂)).f i ≫
      (filtrationFunctorHomotopyOfAddLE hF hG (hf := hf) (hg := hg) h hh h₂₃ hs₂₃).hom i j =
        k ≫ ((filtrationFunctor G hG).map (eIntHomOfLE h₁₃)).f j := by
    rw [← cancel_mono ((filtrationFunctorArrow G hG i₃).f j), Category.assoc, Category.assoc,
      filtrationFunctorHomotopyOfAddLE_hom_comp, ← HomologicalComplex.comp_f_assoc,
      filtrationFunctor_map_comp_arrow, ← HomologicalComplex.comp_f,
      filtrationFunctor_map_comp_arrow, hk]
  rw [reassoc_of% e, ← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f,
    comp_zero]

/-- **Homotopies raising the filtration by `s` induce equal maps from page `s + 2` on.** Let `f`
and `g` be morphisms of filtered complexes, sending each piece `F n` into `G n`, and `h` a
homotopy from `f` to `g` whose components send each piece `F n` into `G (n + s)`. Then `f` and `g`
induce the same morphism on every page `r ≥ s + 2` of the spectral sequences. In the classical
homological numbering, in which Mathlib's page `r` is `E_{r - 1}`, they agree from `E_{s + 1}` on;
for a homotopy raising the filtration by one, from `E₂` on. -/
theorem spectralSequenceMap_filtrationFunctorMap_hom_eq_of_homotopy (h : Homotopy f g) (s : ℤ)
    (hh : h.IsFiltered F fun n ↦ G (n + s)) (r : ℤ) (hr : 2 ≤ r) (hsr : s + 2 ≤ r) :
    (spectralSequenceMap coreE₂Cohomological
        (spectralObjectMap (filtrationFunctorMap hF hG f hf))).hom r hr =
      (spectralSequenceMap coreE₂Cohomological
        (spectralObjectMap (filtrationFunctorMap hF hG g hg))).hom r hr := by
  ext pq : 1
  -- Compare both maps through the epimorphism from `H^n(F_{q+1}/F_{q-r+2})` and the monomorphism
  -- into `H^n(G_{q+r-1}/G_q)` that factor the page objects.
  rw [← cancel_epi (toSpectralSequencePageX (filtrationFunctor F hF) r hr pq (pq.2 - r + 2)
      (pq.2 + 1) rfl rfl (pq.1 + pq.2) rfl),
    ← cancel_mono (fromSpectralSequencePageX (filtrationFunctor G hG) r hr pq pq.2 (pq.2 + r - 1)
      rfl rfl (pq.1 + pq.2) rfl)]
  simp only [Category.assoc]
  rw [toSpectralSequencePageX_naturality_assoc, toSpectralSequencePageX_naturality_assoc,
    toSpectralSequencePageX_fromSpectralSequencePageX _ _ _ _ _ pq.2 _ _ rfl rfl rfl rfl,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  convert homologyMap_cokernelMap_eq_of_homotopy hF hG (hf := hf) (hg := hg) h hh
    (show pq.2 - r + 2 ≤ pq.2 by lia) (show pq.2 - r + 2 ≤ pq.2 + 1 by lia)
    (show pq.2 ≤ pq.2 + r - 1 by lia) (show pq.2 + 1 ≤ pq.2 + r - 1 by lia) (by lia) (by lia)
    (pq.1 + pq.2) using 2 <;>
  exact coequalizer.hom_ext (by simp [cokernel.map])

/-- If `f ≫ g` is homotopic to the identity through a homotopy raising the filtration by at most
`s`, then on every page `r ≥ s + 2` the map induced by `f` followed by that induced by `g` is the
identity. -/
private lemma spectralSequenceMap_filtrationFunctorMap_comp_hom_eq_id {g : L ⟶ K}
    {hg : ∀ n, (F n).Factors ((G n).arrow ≫ g)} (s : ℤ) (h : Homotopy (f ≫ g) (𝟙 K))
    (hh : h.IsFiltered F fun n ↦ F (n + s)) (r : ℤ) (hr : 2 ≤ r) (hsr : s + 2 ≤ r) :
    (spectralSequenceMap coreE₂Cohomological
        (spectralObjectMap (filtrationFunctorMap hF hG f hf))).hom r hr ≫
      (spectralSequenceMap coreE₂Cohomological
        (spectralObjectMap (filtrationFunctorMap hG hF g hg))).hom r hr = 𝟙 _ := by
  rw [← SpectralSequence.comp_hom _ _ r hr, ← spectralSequenceMap_comp, ← spectralObjectMap_comp,
    ← filtrationFunctorMap_comp f g hf hg fun n ↦ Subobject.factors_comp_of_factors (hf n) (hg n),
    spectralSequenceMap_filtrationFunctorMap_hom_eq_of_homotopy
      (hg := fun n ↦ by simpa using (F n).factors_self) h s hh r hr hsr,
    filtrationFunctorMap_id, spectralObjectMap_id, spectralSequenceMap_id,
    SpectralSequence.id_hom _ r hr]

/-- **A homotopy equivalence raising the filtrations by `s` induces isomorphisms from page `s + 2`
on.** Let `f : K ⟶ L` and `g : L ⟶ K` be morphisms of filtered complexes and `h₁`, `h₂` homotopies
from `f ≫ g` to the identity of `K` and from `g ≫ f` to the identity of `L` whose components raise
the filtrations by at most `s`. Then the morphism of spectral sequences induced by `f` is an
isomorphism on every page `r ≥ s + 2`. -/
theorem isIso_spectralSequenceMap_filtrationFunctorMap_hom {g : L ⟶ K}
    {hg : ∀ n, (F n).Factors ((G n).arrow ≫ g)} (s : ℤ) (h₁ : Homotopy (f ≫ g) (𝟙 K))
    (hh₁ : h₁.IsFiltered F fun n ↦ F (n + s)) (h₂ : Homotopy (g ≫ f) (𝟙 L))
    (hh₂ : h₂.IsFiltered G fun n ↦ G (n + s)) (r : ℤ) (hr : 2 ≤ r) (hsr : s + 2 ≤ r) :
    IsIso ((spectralSequenceMap coreE₂Cohomological
      (spectralObjectMap (filtrationFunctorMap hF hG f hf))).hom r hr) :=
  ⟨_, spectralSequenceMap_filtrationFunctorMap_comp_hom_eq_id (hg := hg) s h₁ hh₁ r hr hsr,
    spectralSequenceMap_filtrationFunctorMap_comp_hom_eq_id (hF := hG) (hG := hF) (f := g)
      (hf := hg) (hg := hf) s h₂ hh₂ r hr hsr⟩

end Shift

end CochainComplex

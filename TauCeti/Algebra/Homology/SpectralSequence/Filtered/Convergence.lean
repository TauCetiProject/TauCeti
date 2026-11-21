/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Stabilization
public import TauCeti.Algebra.Homology.SpectralObject.Naturality

/-!
# Convergence of the spectral sequence of a filtered complex

Let `F : ℤ → Subobject K` be an increasing filtration of a cochain complex `K`. The abutment
`H^n(⊥ ≤ ⊤)` of the spectral object of `F` is the cohomology `H^n(K)`
(`CochainComplex.filtrationAbutmentIso`), filtered by the images of the cohomology of the
subcomplexes `F_q` (`Abelian.SpectralObject.abutmentFiltration`): through `filtrationAbutmentIso`,
the `q`th piece is the image of the map `H^n(F_q) ⟶ H^n(K)` induced by the inclusion
(`CochainComplex.toFiltrationAbutmentFiltration_comp_filtrationAbutmentIso_hom`). The graded
pieces of this filtration are the limit objects `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)`
(`Abelian.SpectralObject.EInftyIsoCokernel`).

For a finite filtration (`F_a = ⊥` and `F_b = ⊤`) the spectral sequence converges strongly: the
filtration of `H^n(K)` vanishes at `a` and is everything at `b`
(`CochainComplex.isZero_filtrationAbutmentFiltration`,
`CochainComplex.isIso_filtrationAbutmentFiltrationι`), and the page-`r` object at `(p, q)` is the
graded piece `F_{q+1} H^{p+q} / F_q H^{p+q}` on every page `r` with `q - r + 2 ≤ a` and
`b ≤ q + r - 1` (`CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite`).

These identifications are natural in morphisms of filtered complexes. A morphism `f : K ⟶ L`
sending each `F_q` into `G_q` induces, through `filtrationAbutmentIso`, the map `H^n(f)` on the
abutments (`CochainComplex.filtrationAbutmentIso_hom_naturality`), and the maps
`H^n(F_q) ⟶ H^n(G_q)` on the pieces of their filtrations
(`CochainComplex.toFiltrationAbutmentFiltration_naturality`). For finite filtrations, the
morphism of spectral sequences induced by a morphism of filtrations is the induced map on the
graded pieces (`CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite_hom_naturality`).

## Main results

* `CochainComplex.filtrationAbutmentIso`: the abutment is `H^n(K)`.
* `CochainComplex.toFiltrationAbutmentFiltration`: the epimorphism from `H^n(F_q)` onto the `q`th
  piece of the filtration of the abutment, and
  `CochainComplex.toFiltrationAbutmentFiltration_comp_filtrationAbutmentIso_hom`: the filtration
  of the abutment is the image filtration of `H^n(K)`.
* `CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite`: strong convergence for a
  finite filtration.
* `CochainComplex.filtrationAbutmentIso_hom_naturality`,
  `CochainComplex.toFiltrationAbutmentFiltration_naturality`,
  `CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite_hom_naturality`: naturality in
  morphisms of filtered complexes.
-/

public section

open CategoryTheory Limits ComposableArrows Abelian.SpectralObject

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ} (F : ℤ → Subobject K)
  (hF : Monotone F)

/-- The abutment `H^n(⊥ ≤ ⊤)` of the spectral object of a filtration of `K` is `H^n(K)`. -/
noncomputable def filtrationAbutmentIso (n : ℤ) :
    (spectralObject (filtrationFunctor F hF)).abutment n ≅ K.homology n :=
  spectralObjectHIsoCokernel _ _ n ≪≫ HomologicalComplex.homologyMapIso
    (cokernelIsoOfEq (filtrationFunctor_map_bot F hF ⊤) ≪≫ cokernelZeroIsoTarget ≪≫
      asIso (filtrationFunctorArrow F hF ⊤)) n

/-- The isomorphism `filtrationAbutmentIso` is induced by the map from the cokernel of
`F_⊥ ⟶ K`, which is zero, to `K`. -/
lemma filtrationAbutmentIso_hom (n : ℤ) :
    (filtrationAbutmentIso F hF n).hom = (spectralObjectHIsoCokernel _ _ n).hom ≫
      HomologicalComplex.homologyMap (cokernel.desc _ (filtrationFunctorArrow F hF ⊤)
        (by rw [filtrationFunctor_map_bot, zero_comp])) n := by
  rw [filtrationAbutmentIso, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom]
  congr 2
  refine coequalizer.hom_ext ?_
  simp [cokernelZeroIsoTarget_hom]

/-- The map from `H^n(F_q)` onto the `q`th piece `opZ^n(⊥ ≤ q, q ≤ ⊤)` of the filtration of the
abutment. Through `filtrationAbutmentIso`, the latter is embedded in `H^n(K)` as the image of the
map induced by the inclusion `F_q ⟶ K`
(`CochainComplex.toFiltrationAbutmentFiltration_comp_filtrationAbutmentIso_hom`). -/
noncomputable def toFiltrationAbutmentFiltration (q n : ℤ) :
    (F q : CochainComplex C ℤ).homology n ⟶
      (spectralObject (filtrationFunctor F hF)).abutmentFiltration q n :=
  HomologicalComplex.homologyMap (eqToHom (filtrationFunctor_obj_coe F hF q).symm ≫
      cokernel.π ((filtrationFunctor F hF).map (homOfLE (bot_le : (⊥ : EInt) ≤ q)))) n ≫
    (spectralObjectHIsoCokernel _ _ n).inv ≫ (spectralObject _).pOpcycles _ _ n

instance (q n : ℤ) : Epi (toFiltrationAbutmentFiltration F hF q n) := by
  have := cokernel.π_of_zero (filtrationFunctor_map_bot F hF q)
  dsimp only [toFiltrationAbutmentFiltration]
  infer_instance

/-- **The filtration of the abutment is the image filtration.** Through `filtrationAbutmentIso`,
the `q`th piece of the filtration of the abutment is the image of the map
`H^n(F_q) ⟶ H^n(K)` induced by the inclusion of the subcomplex `F_q`: this map factors as the
epimorphism `toFiltrationAbutmentFiltration` followed by the embedding of the `q`th piece. -/
@[reassoc (attr := simp)]
lemma toFiltrationAbutmentFiltration_comp_filtrationAbutmentIso_hom (q n : ℤ) :
    toFiltrationAbutmentFiltration F hF q n ≫
        (spectralObject (filtrationFunctor F hF)).abutmentFiltrationι q n ≫
          (filtrationAbutmentIso F hF n).hom =
      HomologicalComplex.homologyMap (F q).arrow n := by
  simp only [toFiltrationAbutmentFiltration, filtrationAbutmentIso_hom, Category.assoc,
    Abelian.SpectralObject.pOpcycles_abutmentFiltrationι_assoc,
    spectralObject_H_map_comp_spectralObjectHIsoCokernel_hom_assoc, Iso.inv_hom_id_assoc,
    ← HomologicalComplex.homologyMap_comp]
  congr 1
  simp

/-- The `a`th piece of the filtration of `H^n(K)` vanishes when `F_a = ⊥`. -/
lemma isZero_filtrationAbutmentFiltration {a : ℤ} (ha : F a = ⊥) (n : ℤ) :
    IsZero ((spectralObject (filtrationFunctor F hF)).abutmentFiltration a n) :=
  Abelian.SpectralObject.isZero_abutmentFiltration _
    (isZero_spectralObject_H_bot F hF a n ((F a).isZero_homology_of_eq_bot ha n))

/-- The `s`th piece of the filtration of `H^n(K)` vanishes when the stage `F_s` vanishes in
degree `n`: a filtration bounded below in degree `n` induces a filtration of `H^n(K)` bounded
below. -/
lemma isZero_filtrationAbutmentFiltration_of_isZero_X {s n : ℤ}
    (hs : IsZero ((F s : CochainComplex C ℤ).X n)) :
    IsZero ((spectralObject (filtrationFunctor F hF)).abutmentFiltration s n) :=
  Abelian.SpectralObject.isZero_abutmentFiltration _
    (isZero_spectralObject_H_bot_of_isZero_X F hF hs le_rfl)

/-- The `b`th piece of the filtration of `H^n(K)` is everything when `F_b = ⊤`. -/
lemma isIso_filtrationAbutmentFiltrationι {b : ℤ} (hb : F b = ⊤) (n : ℤ) :
    IsIso ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationι b n) :=
  Abelian.SpectralObject.isIso_abutmentFiltrationι _
    (isZero_spectralObject_H_top F hF b n ((F b).isZero_homology_cokernel_of_eq_top hb n))

/-- **Strong convergence for a finite filtration.** If `F_a = ⊥` and `F_b = ⊤`, then on every page
`r ≥ 2` with `q - r + 2 ≤ a` and `b ≤ q + r - 1`, the object at `pq = (p, q)` is the graded piece
`F_{q+1} H^{p+q} / F_q H^{p+q}` of the filtration of the abutment `H^{p+q}(K)`. -/
noncomputable def filtrationSpectralSequencePageXIsoGradedOfFinite {a b : ℤ} (ha : F a = ⊥)
    (hb : F b = ⊤) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (hra : pq.2 - r + 2 ≤ a)
    (hrb : b ≤ pq.2 + r - 1) :
    ((spectralSequence (filtrationFunctor F hF)).page r).X pq ≅
      cokernel ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationMap pq.2
        (pq.1 + pq.2)) :=
  filtrationSpectralSequencePageXIsoEInftyOfFinite F hF ha hb r hr pq hra hrb ≪≫
    (spectralObject _).EInftyIsoCokernel _ _

section Naturality

variable {F hF} {L : CochainComplex C ℤ} {G : ℤ → Subobject L} {hG : Monotone G}

/-- **The identification of the abutment with the cohomology of the complex is natural.** Let
`f : K ⟶ L` send each piece `F_q` into `G_q`. Through `filtrationAbutmentIso`, the map induced by
`f` on the abutments `H^n(⊥ ≤ ⊤)` is the map `H^n(K) ⟶ H^n(L)` induced by `f`. -/
@[reassoc]
lemma filtrationAbutmentIso_hom_naturality (f : K ⟶ L)
    (hf : ∀ q, (G q).Factors ((F q).arrow ≫ f)) (n : ℤ) :
    ((spectralObjectMap (filtrationFunctorMap hF hG f hf)).hom n).app
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≫ (filtrationAbutmentIso G hG n).hom =
      (filtrationAbutmentIso F hF n).hom ≫ HomologicalComplex.homologyMap f n := by
  rw [filtrationAbutmentIso_hom, filtrationAbutmentIso_hom,
    reassoc_of% spectralObjectMap_hom_app_spectralObjectHIsoCokernel_hom, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  congr 2
  refine coequalizer.hom_ext ?_
  simp

/-- **The filtration of the abutment is natural.** Let `f : K ⟶ L` send each piece `F_q` into
`G_q`. The epimorphisms `toFiltrationAbutmentFiltration` from `H^n(F_q)` and `H^n(G_q)` onto the
`q`th pieces of the filtrations of the abutments intertwine the map `H^n(F_q) ⟶ H^n(G_q)` induced
by the restriction of `f` with the map induced by `f` on these pieces. -/
@[reassoc]
lemma toFiltrationAbutmentFiltration_naturality (f : K ⟶ L)
    (hf : ∀ q, (G q).Factors ((F q).arrow ≫ f)) (q n : ℤ) :
    HomologicalComplex.homologyMap ((G q).factorThru _ (hf q)) n ≫
        toFiltrationAbutmentFiltration G hG q n =
      toFiltrationAbutmentFiltration F hF q n ≫
        opcyclesMapOfHom (spectralObjectMap (filtrationFunctorMap hF hG f hf))
          (homOfLE (bot_le : (⊥ : EInt) ≤ q)) (homOfLE (le_top : (q : EInt) ≤ ⊤)) n := by
  rw [← cancel_mono ((spectralObject (filtrationFunctor G hG)).abutmentFiltrationι q n ≫
    (filtrationAbutmentIso G hG n).hom)]
  simp only [Category.assoc, toFiltrationAbutmentFiltration_comp_filtrationAbutmentIso_hom,
    abutmentFiltrationι_naturality_assoc, filtrationAbutmentIso_hom_naturality,
    toFiltrationAbutmentFiltration_comp_filtrationAbutmentIso_hom_assoc,
    ← HomologicalComplex.homologyMap_comp, Subobject.factorThru_arrow]

/-- **Strong convergence for finite filtrations is natural.** Let `α` be a morphism between the
functors of increasing filtrations `F` of `K` and `G` of `L` with `F_a = G_a = ⊥` and
`F_b = G_b = ⊤`. Through `filtrationSpectralSequencePageXIsoGradedOfFinite`, the morphism of
spectral sequences induced by `α` is, on the object at `(p, q)` of every page `r ≥ 2` with
`q - r + 2 ≤ a` and `b ≤ q + r - 1`, the map induced by `α` on the graded pieces
`F_{q+1} H^{p+q} / F_q H^{p+q}` of the filtrations of the abutments. -/
@[reassoc]
lemma filtrationSpectralSequencePageXIsoGradedOfFinite_hom_naturality
    (α : filtrationFunctor F hF ⟶ filtrationFunctor G hG) {a b : ℤ} (hFa : F a = ⊥)
    (hGa : G a = ⊥) (hFb : F b = ⊤) (hGb : G b = ⊤) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (hra : pq.2 - r + 2 ≤ a) (hrb : b ≤ pq.2 + r - 1) :
    ((spectralSequenceMap coreE₂Cohomological (spectralObjectMap α)).hom r hr).f pq ≫
        (filtrationSpectralSequencePageXIsoGradedOfFinite G hG hGa hGb r hr pq hra hrb).hom =
      (filtrationSpectralSequencePageXIsoGradedOfFinite F hF hFa hFb r hr pq hra hrb).hom ≫
        abutmentGradedMap (spectralObjectMap α) pq.2 (pq.1 + pq.2) := by
  simp only [filtrationSpectralSequencePageXIsoGradedOfFinite, Iso.trans_hom,
    filtrationSpectralSequencePageXIsoEInftyOfFinite_hom, spectralSequenceMap_hom,
    spectralSequencePageMap_f]
  rw [Category.assoc, spectralSequencePageXToEInfty_comp_EInftyIsoCokernel_hom_naturality]

end Naturality

end CochainComplex

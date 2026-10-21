/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject
public import TauCeti.Algebra.Homology.SpectralObject.Stabilization
public import TauCeti.Algebra.Homology.Subobject

/-!
# Stabilization of the pages of the spectral sequence of a filtered complex

Let `F : ℤ → Subobject K` be an increasing filtration of a cochain complex `K`. On the spectral
sequence of `CochainComplex.filtrationFunctor F hF`, the object at `(p, q)` on page `r ≥ 2` is
isomorphic to the limit object `E^{p+q}(⊥ ≤ q ≤ q + 1 ≤ ⊤)` as soon as
`H^{p+q+1}(F_{q-r+2}) = 0` and `H^{p+q-1}(K / F_{q+r-1}) = 0`
(`CochainComplex.filtrationSpectralSequencePageXIsoEInfty`). For a finite filtration,
`F_a = ⊥` and `F_b = ⊤`, this holds on every page `r` with `q - r + 2 ≤ a` and
`b ≤ q + r - 1` (`CochainComplex.filtrationSpectralSequencePageXIsoEInftyOfFinite`).

## Main results

* `CochainComplex.isZero_spectralObject_H_bot`, `CochainComplex.isZero_spectralObject_H_top`: the
  vanishing of `H^m(⊥ ≤ a)` and `H^m(b ≤ ⊤)` for the spectral object of a filtration, from the
  vanishing of `H^m(F_a)` and `H^m(K / F_b)`.
* `CochainComplex.filtrationSpectralSequencePageXIsoEInfty`: identification of the page objects
  with `EInfty` under the two vanishing conditions.
* `CochainComplex.filtrationSpectralSequencePageXIsoEInftyOfFinite`: the case of a finite
  filtration.
-/

public section

open CategoryTheory Limits ComposableArrows

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ} (F : ℤ → Subobject K)
  (hF : Monotone F)

/-- `H^m(⊥ ≤ a)` vanishes for the spectral object of a filtration when `H^m(F_a)` does. -/
lemma isZero_spectralObject_H_bot (a m : ℤ)
    (h : IsZero ((F a : CochainComplex C ℤ).homology m)) :
    IsZero (((spectralObject (filtrationFunctor F hF)).H m).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ a)))) := by
  refine IsZero.of_iso ?_ (spectralObjectHIsoCokernel _ _ m)
  have hz : (filtrationFunctor F hF).map (homOfLE (bot_le : (⊥ : EInt) ≤ a)) = 0 := by
    refine IsZero.eq_of_src ?_ _ _
    rw [filtrationFunctor_obj, filtrationEInt_bot]
    exact IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero
  have h' : IsZero (((filtrationFunctor F hF).obj (a : EInt)).homology m) := by
    rw [filtrationFunctor_obj_coe]
    exact h
  exact IsZero.of_iso h' ((HomologicalComplex.homologyFunctor C _ m).mapIso
    (cokernelIsoOfEq hz ≪≫ cokernelZeroIsoTarget))

/-- `H^m(b ≤ ⊤)` vanishes for the spectral object of a filtration when `H^m(K / F_b)` does. -/
lemma isZero_spectralObject_H_top (b m : ℤ)
    (h : IsZero ((cokernel (F b).arrow).homology m)) :
    IsZero (((spectralObject (filtrationFunctor F hF)).H m).obj
      (mk₁ (homOfLE (le_top : (b : EInt) ≤ ⊤)))) := by
  refine IsZero.of_iso ?_ (spectralObjectHIsoCokernel _ _ m)
  have : IsIso (filtrationEInt F ⊤).arrow := by
    rw [filtrationEInt_top]
    infer_instance
  -- The transition map to `⊤` followed by the inclusion `K ≅ ⊤ ⟶ K` is the inclusion of `F_b`.
  have e : (filtrationFunctor F hF).map (homOfLE (le_top : (b : EInt) ≤ ⊤)) ≫
      (filtrationFunctorObjIso F hF ⊤).hom ≫ (filtrationEInt F ⊤).arrow =
      (filtrationFunctorObjIso F hF b).hom ≫ (filtrationEInt F b).arrow := by
    rw [reassoc_of% filtrationFunctor_map_comp_objIso_hom, Subobject.ofLE_arrow]
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor C _ m).mapIso
    ((cokernelCompIsIso _ ((filtrationFunctorObjIso F hF ⊤).hom ≫
      (filtrationEInt F ⊤).arrow)).symm ≪≫ cokernelIsoOfEq e ≪≫ cokernelEpiComp _ _))
  rw [HomologicalComplex.homologyFunctor_obj]
  convert h using 1
  rw [filtrationEInt_coe]

/-- **Stabilization of the pages of the spectral sequence of a filtered complex.** The object at
`pq = (p, q)` on page `r ≥ 2` is `E^{p+q}(⊥ ≤ q ≤ q + 1 ≤ ⊤)` when `H^{p+q+1}(F_{q-r+2})` and
`H^{p+q-1}(K / F_{q+r-1})` vanish. -/
noncomputable def filtrationSpectralSequencePageXIsoEInfty (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (n : ℤ) (hn : n = pq.1 + pq.2)
    (h₀ : IsZero ((F (pq.2 - r + 2) : CochainComplex C ℤ).homology (n + 1)))
    (h₃ : IsZero ((cokernel (F (pq.2 + r - 1)).arrow).homology (n - 1))) :
    ((spectralSequence (filtrationFunctor F hF)).page r).X pq ≅
      (spectralObject (filtrationFunctor F hF)).EInfty pq.2 n :=
  (spectralObject _).spectralSequencePageXIsoEInfty r hr pq n hn
    (isZero_spectralObject_H_bot F hF _ _ h₀) (isZero_spectralObject_H_top F hF _ _ h₃)

/-- **Stabilization for a finite filtration.** If `F_a = ⊥` and `F_b = ⊤`, then the object at
`pq = (p, q)` on every page `r ≥ 2` with `q - r + 2 ≤ a` and `b ≤ q + r - 1` is
`E^{p+q}(⊥ ≤ q ≤ q + 1 ≤ ⊤)`. -/
noncomputable def filtrationSpectralSequencePageXIsoEInftyOfFinite {a b : ℤ} (ha : F a = ⊥)
    (hb : F b = ⊤) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (hra : pq.2 - r + 2 ≤ a)
    (hrb : b ≤ pq.2 + r - 1) :
    ((spectralSequence (filtrationFunctor F hF)).page r).X pq ≅
      (spectralObject (filtrationFunctor F hF)).EInfty pq.2 (pq.1 + pq.2) :=
  filtrationSpectralSequencePageXIsoEInfty F hF r hr pq _ rfl
    ((F _).isZero_homology_of_eq_bot (eq_bot_iff.2 ((hF hra).trans ha.le)) _)
    ((F _).isZero_homology_cokernel_of_eq_top (eq_top_iff.2 (hb.ge.trans (hF hrb))) _)

end CochainComplex

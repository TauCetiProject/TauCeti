/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Stabilization
public import TauCeti.Algebra.Homology.SpectralObject.Abutment

/-!
# Convergence of the spectral sequence of a filtered complex

Let `F : ℤ → Subobject K` be an increasing filtration of a cochain complex `K`. The abutment
`H^n(⊥ ≤ ⊤)` of the spectral object of `F` is the cohomology `H^n(K)`
(`CochainComplex.filtrationAbutmentIso`), filtered by the images of the cohomology of the
subcomplexes `F_q` (`Abelian.SpectralObject.abutmentFiltration`), whose graded pieces are the
limit objects `E^n(⊥ ≤ q ≤ q + 1 ≤ ⊤)` (`Abelian.SpectralObject.EInftyIsoCokernel`).

For a finite filtration (`F_a = ⊥` and `F_b = ⊤`) the spectral sequence converges strongly: the
filtration of `H^n(K)` vanishes at `a` and is everything at `b`
(`CochainComplex.isZero_filtrationAbutmentFiltration`,
`CochainComplex.isIso_filtrationAbutmentFiltrationι`), and the page-`r` object at `(p, q)` is the
graded piece `F_{q+1} H^{p+q} / F_q H^{p+q}` on every page `r` with `q - r + 2 ≤ a` and
`b ≤ q + r - 1` (`CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite`).

## Main results

* `CochainComplex.filtrationAbutmentIso`: the abutment is `H^n(K)`.
* `CochainComplex.filtrationSpectralSequencePageXIsoGradedOfFinite`: strong convergence for a
  finite filtration.
-/

public section

open CategoryTheory Limits ComposableArrows

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ} (F : ℤ → Subobject K)
  (hF : Monotone F)

/-- The abutment `H^n(⊥ ≤ ⊤)` of the spectral object of a filtration of `K` is `H^n(K)`. -/
noncomputable def filtrationAbutmentIso (n : ℤ) :
    (spectralObject (filtrationFunctor F hF)).abutment n ≅ K.homology n :=
  spectralObjectHIsoCokernel _ _ n ≪≫ (HomologicalComplex.homologyFunctor C _ n).mapIso
    (cokernelIsoOfEq (filtrationFunctor_map_bot_top F hF) ≪≫ cokernelZeroIsoTarget ≪≫
      filtrationFunctorObjIso F hF ⊤ ≪≫
      eqToIso (congrArg (fun S : Subobject K => (S : CochainComplex C ℤ))
        (filtrationEInt_top F)) ≪≫ asIso (⊤ : Subobject K).arrow)

/-- The `a`th piece of the filtration of `H^n(K)` vanishes when `F_a = ⊥`. -/
lemma isZero_filtrationAbutmentFiltration {a : ℤ} (ha : F a = ⊥) (n : ℤ) :
    IsZero ((spectralObject (filtrationFunctor F hF)).abutmentFiltration a n) :=
  Abelian.SpectralObject.isZero_abutmentFiltration _
    (isZero_spectralObject_H_bot F hF a n (isZero_homology_of_eq_bot F ha n))

/-- The `b`th piece of the filtration of `H^n(K)` is everything when `F_b = ⊤`. -/
lemma isIso_filtrationAbutmentFiltrationι {b : ℤ} (hb : F b = ⊤) (n : ℤ) :
    IsIso ((spectralObject (filtrationFunctor F hF)).abutmentFiltrationι b n) :=
  Abelian.SpectralObject.isIso_abutmentFiltrationι _
    (isZero_spectralObject_H_top F hF b n (isZero_homology_cokernel_of_eq_top F hb n))

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

end CochainComplex

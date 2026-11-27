/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport

/-!
# Transporting finite places along an isomorphism of number fields

A field isomorphism `e : K ≃+* L` of number fields induces an isomorphism
`NumberField.RingOfIntegers.mapRingEquiv e : 𝓞 K ≃+* 𝓞 L` of rings of integers, and so a
bijection `IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv` between the finite places of `K` and
of `L`. The image `e w` of a finite place `w` carries the `w`-adic valuation along `e`,
`|e x|_{e w} = |x|_w`, and is the only finite place of `L` doing so. This is the finite-place
counterpart of `NumberField.InfinitePlace.eq_equivOfRingEquiv_iff`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valuation_equivOfRingEquiv_mapRingEquiv`:
  `|e x|_{e w} = |x|_w`.
* `IsDedekindDomain.HeightOneSpectrum.eq_equivOfRingEquiv_mapRingEquiv_iff`: a finite place `w'`
  of `L` is `e w` exactly when `|e x|_{w'} = |x|_w` for every `x ∈ K`.
-/

public section

open NumberField

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

/-- **The image of a finite place.** A field isomorphism `e : K ≃+* L` carries the `w`-adic
valuation of `K` to the valuation of `L` at the image of `w` under the induced isomorphism
`𝓞 K ≃+* 𝓞 L`: `|e x|_{e w} = |x|_w`. -/
theorem valuation_equivOfRingEquiv_mapRingEquiv (e : K ≃+* L) (w : HeightOneSpectrum (𝓞 K))
    (x : K) :
    (equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) w).valuation L (e x) = w.valuation K x := by
  simpa only [RingOfIntegers.ringEquivOfRingEquiv_mapRingEquiv] using
    valuation_ringEquivOfRingEquiv (K := K) (K' := L) (RingOfIntegers.mapRingEquiv e)
      (asIdeal_equivOfRingEquiv _ w) x

/-- **The image of a finite place is characterised by its valuation**: a finite place `w'` of `L`
satisfies `|e x|_{w'} = |x|_w` for all `x ∈ K` exactly when it is the image of `w` under the
isomorphism `𝓞 K ≃+* 𝓞 L` induced by `e`. -/
theorem eq_equivOfRingEquiv_mapRingEquiv_iff (e : K ≃+* L) {w : HeightOneSpectrum (𝓞 K)}
    {w' : HeightOneSpectrum (𝓞 L)} :
    w' = equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) w ↔
      ∀ x, w'.valuation L (e x) = w.valuation K x := by
  refine ⟨fun h ↦ h ▸ valuation_equivOfRingEquiv_mapRingEquiv e w, fun hw ↦ ?_⟩
  refine valuation_injective L (Valuation.ext fun y ↦ ?_)
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [hw, valuation_equivOfRingEquiv_mapRingEquiv]

end IsDedekindDomain.HeightOneSpectrum

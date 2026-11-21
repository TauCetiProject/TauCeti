/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport

/-!
# Transporting adic valuations of number fields along field isomorphisms

An isomorphism of fields `e : K ≃+* L` restricts to
`NumberField.RingOfIntegers.mapRingEquiv e : 𝓞 K ≃+* 𝓞 L` on the rings of integers, whose
extension back to the fraction fields is `e` itself
(`NumberField.RingOfIntegers.ringEquivOfRingEquiv_mapRingEquiv`). Specializing
`IsDedekindDomain.HeightOneSpectrum.valuation_ringEquivOfRingEquiv` to this restriction shows
that `e` intertwines the `v`-adic and `w`-adic valuations whenever `w.asIdeal` is the image of
`v.asIdeal` under `RingOfIntegers.mapRingEquiv e`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valuation_mapRingEquiv`: a field isomorphism `e : K ≃+* L`
  intertwines `v.valuation K` and `w.valuation L` when `w` is the image of `v` under
  `NumberField.RingOfIntegers.mapRingEquiv e`.
-/

public section

open NumberField

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [Field L]
  [IsDedekindDomain (𝓞 K)] [IsFractionRing (𝓞 K) K]
  [IsDedekindDomain (𝓞 L)] [IsFractionRing (𝓞 L) L]

/-- **The adic valuation of a field transports along a ring isomorphism via `RingOfIntegers`.** If
`e : K ≃+* L` carries the height-one prime `v` of `𝓞 K` to the height-one prime `w` of `𝓞 L`
under `RingOfIntegers.mapRingEquiv e`, then `w.valuation L (e x) = v.valuation K x` for all
`x : K`. -/
theorem valuation_mapRingEquiv (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (e : K ≃+* L)
    (hvw : w.asIdeal = Ideal.map (RingOfIntegers.mapRingEquiv e) v.asIdeal) (x : K) :
    w.valuation L (e x) = v.valuation K x := by
  have h := valuation_ringEquivOfRingEquiv (K := K) (K' := L) (RingOfIntegers.mapRingEquiv e) hvw x
  rwa [RingOfIntegers.ringEquivOfRingEquiv_mapRingEquiv] at h

end IsDedekindDomain.HeightOneSpectrum

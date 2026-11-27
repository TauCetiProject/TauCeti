/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport

/-!
# Transporting finite-place valuations along isomorphisms of number fields

A ring isomorphism `e : K ≃+* L` of number fields restricts to the isomorphism
`NumberField.RingOfIntegers.mapRingEquiv e : 𝓞 K ≃+* 𝓞 L` of rings of integers, which carries a
finite place `v` of `K` to the finite place
`HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v` of `L`. This file records
that `e` itself carries the `v`-adic valuation to the valuation of any finite place `w` of `L`
whose ideal is the image of that of `v`, and in particular to the valuation of the corresponding
place. This is the hypothesis `adicCompletionCongr` needs to extend `e` to the adic completions.
The corresponding place is the only finite place of `L` doing so; this is the finite-place
counterpart of `NumberField.InfinitePlace.eq_equivOfRingEquiv_iff`. These two statements about
the corresponding place are the case of rings of integers of
`IsDedekindDomain.HeightOneSpectrum.valuation_equivOfRingEquiv` and
`IsDedekindDomain.HeightOneSpectrum.eq_equivOfRingEquiv_iff` for Dedekind domains, as the
isomorphism of fraction fields induced by `mapRingEquiv e` is `e`.

## Main results

* `RingEquiv.valuation_apply_of_asIdeal_eq`: if `w.asIdeal` is the image of `v.asIdeal`, then
  `w.valuation L (e x) = v.valuation K x`.
* `RingEquiv.valuation_equivOfRingEquiv`: the same for the finite place of `L` corresponding to
  `v`.
* `IsDedekindDomain.HeightOneSpectrum.eq_equivOfRingEquiv_mapRingEquiv_iff`: a finite place `w'`
  of `L` is the place corresponding to `w` exactly when `|e x|_{w'} = |x|_w` for every `x ∈ K`.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace RingEquiv

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

/-- A ring isomorphism `e : K ≃+* L` of number fields carries the `v`-adic valuation to the
`w`-adic valuation whenever the ideal of `w` is the image of the ideal of `v`. -/
theorem valuation_apply_of_asIdeal_eq (e : K ≃+* L) {v : HeightOneSpectrum (𝓞 K)}
    {w : HeightOneSpectrum (𝓞 L)}
    (hvw : w.asIdeal = Ideal.map (RingOfIntegers.mapRingEquiv e) v.asIdeal) (x : K) :
    w.valuation L (e x) = v.valuation K x := by
  simpa using valuation_ringEquivOfRingEquiv (K := K) (K' := L) (RingOfIntegers.mapRingEquiv e)
    hvw x

-- Not `@[simp]`: the simp lemma `HeightOneSpectrum.equivOfRingEquiv_apply` rewrites the place on
-- the left-hand side, so the simpNF linter rejects it.
/-- A ring isomorphism `e : K ≃+* L` of number fields carries the `v`-adic valuation to the
valuation of the corresponding finite place of `L`. -/
theorem valuation_equivOfRingEquiv (e : K ≃+* L) (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v).valuation L (e x) =
      v.valuation K x :=
  e.valuation_apply_of_asIdeal_eq (asIdeal_equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v) x

end RingEquiv

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

/-- **The image of a finite place is characterised by its valuation**: a finite place `w'` of `L`
satisfies `|e x|_{w'} = |x|_w` for all `x ∈ K` exactly when it is the image of `w` under the
isomorphism `𝓞 K ≃+* 𝓞 L` induced by `e`. -/
theorem eq_equivOfRingEquiv_mapRingEquiv_iff (e : K ≃+* L) {w : HeightOneSpectrum (𝓞 K)}
    {w' : HeightOneSpectrum (𝓞 L)} :
    w' = equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) w ↔
      ∀ x, w'.valuation L (e x) = w.valuation K x := by
  simpa only [RingOfIntegers.ringEquivOfRingEquiv_mapRingEquiv] using
    eq_equivOfRingEquiv_iff (K := K) (K' := L) (RingOfIntegers.mapRingEquiv e)

end IsDedekindDomain.HeightOneSpectrum

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Hasse
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Transporting regular-form classes and local Hasse invariants at adic completions

For a valuation-preserving isomorphism `e : K ≃+* K'` between the fraction fields of Dedekind
domains `R` and `R'` intertwining height-one primes `v` and `w`, the induced completion
isomorphism `adicCompletionCongr v w e he : K_v ≃+* K'_w` commutes with extending regular-form
isometry classes to the completions. When the residue fields `R ⧸ v` and `R' ⧸ w` are finite, both
completions are nonarchimedean local fields and transporting a regular-form class along `e`
preserves its local Hasse invariant at the corresponding completion.

## Main results

* `TauCeti.RegularFormClass.mapRingEquiv_adicCompletionCongr_baseChange`: `adicCompletionCongr`
  commutes with extending regular-form classes to adic completions.
* `TauCeti.RegularFormClass.localHasse_baseChange_adicCompletion_mapRingEquiv_of_valuation_eq`:
  transporting a regular-form class along a valuation-preserving isomorphism preserves its local
  Hasse invariant at the corresponding adic completion.
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace TauCeti.RegularFormClass

variable {R R' K K' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']
  [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K'] [IsFractionRing R' K']

-- Not `@[simp]`: firing bottom-up inside `localHasse` would block `@[simp] localHasse_mapRingEquiv`
-- from cancelling `mapRingEquiv`, matching the non-`simp` naturality lemma
-- `mapRingEquiv_baseChange`.
/-- Transporting the `K_v`-scalar extension of a regular-form class along `adicCompletionCongr`
agrees with extending scalars of the `e`-transported class to `K'_w`. -/
theorem mapRingEquiv_adicCompletionCongr_baseChange
    {v : HeightOneSpectrum R} {w : HeightOneSpectrum R'}
    [Invertible (2 : K)] [Invertible (2 : K')]
    [Invertible (2 : v.adicCompletion K)] [Invertible (2 : w.adicCompletion K')]
    {e : K ≃+* K'} (he : ∀ x, w.valuation K' (e x) = v.valuation K x)
    (x : RegularFormClass K) :
    mapRingEquiv (adicCompletionCongr v w e he) (baseChange (v.adicCompletion K) x) =
      baseChange (w.adicCompletion K') (mapRingEquiv e x) :=
  mapRingEquiv_baseChange e (adicCompletionCongr v w e he) (adicCompletionCongr_algebraMap he) x

/-- Along a valuation-preserving isomorphism `e : K ≃+* K'` of fraction fields of Dedekind domains
with finite residue fields at `v` and `w`, the local Hasse invariant at `w` of a transported
regular-form class equals the local Hasse invariant at `v` of the original class. -/
theorem localHasse_baseChange_adicCompletion_mapRingEquiv_of_valuation_eq
    {v : HeightOneSpectrum R} {w : HeightOneSpectrum R'}
    [Finite (R ⧸ v.asIdeal)] [Finite (R' ⧸ w.asIdeal)]
    [Invertible (2 : K)] [Invertible (2 : K')]
    [Invertible (2 : v.adicCompletion K)] [Invertible (2 : w.adicCompletion K')]
    {e : K ≃+* K'} (he : ∀ x, w.valuation K' (e x) = v.valuation K x)
    (x : RegularFormClass K) :
    localHasse (baseChange (w.adicCompletion K') (mapRingEquiv e x)) =
      localHasse (baseChange (v.adicCompletion K) x) := by
  rw [← mapRingEquiv_adicCompletionCongr_baseChange he, localHasse_mapRingEquiv]

end TauCeti.RegularFormClass

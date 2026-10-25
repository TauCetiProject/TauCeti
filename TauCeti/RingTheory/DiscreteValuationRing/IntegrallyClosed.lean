/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.KrullDimension.Field

/-!
# Integrally closed local domains of dimension one

A Noetherian integrally closed local domain of Krull dimension one is a discrete valuation ring
(Stacks, Lemma 10.119.7 (00PD)). Mathlib proves the equivalence of the conditions in
`tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`, one of which asks for integral closedness
together with "every nonzero prime is the maximal ideal"; this file supplies that condition from
the dimension.

## Main results

* `IsDiscreteValuationRing.of_krullDimLE_one`: a Noetherian integrally closed local domain of
  Krull dimension at most one that is not a field is a discrete valuation ring.
* `IsDiscreteValuationRing.of_ringKrullDim_eq_one`: the dimension-one specialization.

## References

* [Stacks Project, Lemma 10.119.7](https://stacks.math.columbia.edu/tag/00PD).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0): the ring-level step of
  `Pcf.isDiscreteValuationRing_localizationAtPrime_of_heightOne` in
  `lean/Pcf/Bounding/Divisors.lean`, stated there for the localization of a Noetherian
  integrally closed domain at a prime of height one.
-/

public section

open IsLocalRing

namespace IsDiscreteValuationRing

/-- A Noetherian integrally closed local domain of Krull dimension at most one that is not a
field is a discrete valuation ring. -/
theorem of_krullDimLE_one {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Ring.KrullDimLE 1 R]
    (hnot : ¬ IsField R) : _root_.IsDiscreteValuationRing R := by
  have hmax : maximalIdeal R ≠ ⊥ := fun hbot ↦ hnot (isField_iff_maximalIdeal_eq.mpr hbot)
  have hnormal : IsIntegrallyClosed R ∧
      ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = maximalIdeal R :=
    ⟨inferInstance, fun P hP _ ↦ eq_maximalIdeal (Ideal.isMaximal_of_isPrime_of_ne_bot P hP)⟩
  have : IsPrincipalIdealRing R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 4 1).mp hnormal
  exact { not_a_field' := hmax }

/-- A Noetherian integrally closed local domain of Krull dimension one is a discrete valuation
ring. Stacks, Lemma 10.119.7 (00PD). -/
@[stacks 00PD]
theorem of_ringKrullDim_eq_one {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (h : ringKrullDim R = 1) :
    _root_.IsDiscreteValuationRing R := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr h.le
  apply of_krullDimLE_one
  intro hfield
  rw [ringKrullDim_eq_zero_of_isField hfield] at h
  exact zero_ne_one h

end IsDiscreteValuationRing

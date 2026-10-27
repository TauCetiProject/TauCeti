/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import TauCeti.RingTheory.LocalRing.Localization

/-!
# Artinian fibres at quasi-finite primes

For a prime `q` at which `S` is quasi-finite over `R`, the local-ring localization equivalence
identifies the fibre `S_q ⧸ (q.under R) S_q` with an Artinian quotient of the localization of
`S_q` at its maximal ideal.

## Main results

* `Ideal.isArtinianRing_quotient_of_quasiFiniteAt`: the local fibre at a quasi-finite prime is
  Artinian.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If `S` is quasi-finite over `R` at a prime `q`, the quotient of `S_q` by the extension of
`q.under R` is an Artinian ring. -/
instance isArtinianRing_quotient_of_quasiFiniteAt (q : Ideal S) [q.IsPrime]
    [Algebra.QuasiFiniteAt R q] :
    IsArtinianRing (Localization.AtPrime q ⧸
      (q.under R).map (algebraMap R (Localization.AtPrime q))) := by
  let Sq := Localization.AtPrime q
  let m := IsLocalRing.maximalIdeal Sq
  have hunder : m.under R = q.under R := by
    rw [← Ideal.under_under (B := S), Localization.AtPrime.under_maximalIdeal]
  have : m.LiesOver (q.under R) := ⟨hunder.symm⟩
  let e := IsLocalRing.algEquivLocalizationAtMaximalIdeal R Sq
  have hmap : ((q.under R).map (algebraMap R Sq)).map
      (e.toAlgHom : Sq →+* Localization.AtPrime m) =
      (q.under R).map (algebraMap R (Localization.AtPrime m)) := by
    rw [Ideal.map_map, AlgHom.comp_algebraMap]
  exact (Ideal.quotientEquiv _ _ e.toRingEquiv hmap.symm).symm.isArtinianRing

end Ideal

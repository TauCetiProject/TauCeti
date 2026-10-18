/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import TauCeti.RingTheory.LocalRing.Localization

/-!
# Positivity of the ramification index at a quasi-finite prime

Mathlib's `Ideal.ramificationIdx q R` is the length of `S_q ⧸ p S_q`, where `p` is the contraction
of `q`. Mathlib's criterion `Ideal.ramificationIdx_pos_of_mem_minimalPrimes` shows it is positive
when `q` is minimal over `p S` and `S_q ⧸ p S_q` is Noetherian; Mathlib applies it to integral
algebras (`Ideal.ramificationIdx_pos`) and Dedekind domains
(`Ideal.ramificationIdx_pos_of_isDedekindDomain`).

This file discharges both hypotheses when `S` is quasi-finite over `R` at `q`
(`Algebra.QuasiFiniteAt R q`): `q` is then the only prime of `S` below `q` over `p`
(`Algebra.QuasiFiniteAt.eq_of_le_of_under_eq`), so it is minimal over `p S`, and `S_q ⧸ p S_q` is
Artinian. This covers the stalk homomorphisms of a quasi-finite morphism of schemes, which are
neither integral nor maps of Dedekind domains in general.

## Main results

* `Ideal.isArtinianRing_quotient_of_quasiFiniteAt`: if `S` is quasi-finite over `R` at a prime `q`
  over `p`, then `S_q ⧸ p S_q` is an Artinian ring (an instance, the pointwise form of Mathlib's
  instance for a quasi-finite algebra).
* `Ideal.ramificationIdx_pos_of_quasiFiniteAt`: if `S` is quasi-finite over `R` at `q`, then the
  ramification index of `q` over `R` is positive.

## References

* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Bounding/SchemeDynamics.lean`: `ramificationIdx_pos_of_quasiFiniteAt` generalizes its
  `Pcf.ramificationIdx_pos_of_quasiFinite`, stated there for a quasi-finite algebra.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If `S` is quasi-finite over `R` at a prime `q` lying over `p`, the quotient of `S_q` by the
extension of `p` is an Artinian ring. -/
instance isArtinianRing_quotient_of_quasiFiniteAt (p : Ideal R) (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] [Algebra.QuasiFiniteAt R q] :
    IsArtinianRing (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := by
  -- `S_q` is quasi-finite over `R`, so Mathlib's instance applies to the maximal ideal `m` of
  -- `S_q`; the localization of the local ring `S_q` at `m` is `S_q` itself
  -- (`IsLocalRing.algEquivLocalizationAtMaximalIdeal`).
  let Sq := Localization.AtPrime q
  let m := IsLocalRing.maximalIdeal Sq
  have hunder : m.under R = p := by
    rw [← Ideal.under_under (B := S), Localization.AtPrime.under_maximalIdeal, ← q.over_def p]
  have : m.LiesOver p := ⟨hunder.symm⟩
  let e := IsLocalRing.algEquivLocalizationAtMaximalIdeal R Sq
  have hmap : (p.map (algebraMap R Sq)).map (e.toAlgHom : Sq →+* Localization.AtPrime m) =
      p.map (algebraMap R (Localization.AtPrime m)) := by
    rw [Ideal.map_map, AlgHom.comp_algebraMap]
  exact (Ideal.quotientEquiv _ _ e.toRingEquiv hmap.symm).symm.isArtinianRing

/-- If `S` is quasi-finite over `R` at the prime `q`, the ramification index of `q` over `R` is
positive. -/
theorem ramificationIdx_pos_of_quasiFiniteAt (q : Ideal S) [q.IsPrime]
    [Algebra.QuasiFiniteAt R q] : 0 < q.ramificationIdx R := by
  have hmin : q ∈ ((q.under R).map (algebraMap R S)).minimalPrimes := by
    refine ⟨⟨inferInstance, Ideal.map_comap_le⟩, fun P ⟨_, hpP⟩ hPq ↦ ?_⟩
    have hunder : P.under R = q.under R :=
      le_antisymm (Ideal.comap_mono hPq) (Ideal.map_le_iff_le_comap.mp hpP)
    exact (Algebra.QuasiFiniteAt.eq_of_le_of_under_eq hPq hunder).ge
  exact ramificationIdx_pos_of_mem_minimalPrimes (q.under R) q hmin

end Ideal

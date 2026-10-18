/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# The ramification index over a discrete valuation ring

Let `S → T` be a local homomorphism from a local ring to a discrete valuation ring such that the
maximal ideal `𝔪_S` of `S` does not map to zero. Then `𝔪_S T` is a nonzero ideal of `T`, hence a
power `𝔪_T ^ e` of the maximal ideal of `T`, and `e` is Mathlib's ramification index
`(maximalIdeal T).ramificationIdx S`, the length of `T ⧸ 𝔪_S T`. For an extension of discrete
valuation rings this is the ramification index of Stacks, Definition 15.113.1 (09E4): the
exponent `e` with `π_S = u π_T ^ e` for uniformizers `π_S`, `π_T` and a unit `u`.

## Main results

* `IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx`: `𝔪_S T = 𝔪_T ^ e` with `e` the
  ramification index of `𝔪_T` over `S`.

## References

* [Stacks Project, Definition 15.113.1](https://stacks.math.columbia.edu/tag/09E4).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0), `lean/Pcf/Bounding/Divisors.lean`:
  `map_maximalIdeal_eq_pow_ramificationIdx` is the local form of its
  `Pcf.heightOneRamificationIdx_eq_dvrExponent` with `Pcf.heightOneDvrExponent_spec`, stated
  there at a height-one prime of a finite extension of normal Noetherian domains.
-/

public section

open IsLocalRing

namespace IsDiscreteValuationRing

variable {S T : Type*} [CommRing S] [CommRing T] [IsLocalRing S] [IsDomain T]
  [IsDiscreteValuationRing T] [Algebra S T] [IsLocalHom (algebraMap S T)]

/-- For a local homomorphism from a local ring `S` to a discrete valuation ring `T` under which
the maximal ideal of `S` does not vanish, `𝔪_S T = 𝔪_T ^ e` with `e` the ramification index of the
maximal ideal of `T` over `S`. -/
theorem map_maximalIdeal_eq_pow_ramificationIdx
    (h : (maximalIdeal S).map (algebraMap S T) ≠ ⊥) :
    (maximalIdeal S).map (algebraMap S T) =
      maximalIdeal T ^ (maximalIdeal T).ramificationIdx S := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible T
  obtain ⟨n, hn⟩ := ideal_eq_span_pow_irreducible h hϖ
  have hpow : (maximalIdeal S).map (algebraMap S T) = maximalIdeal T ^ n := by
    rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  -- The ramification index is the length of `T_𝔪 ⧸ 𝔪_S T_𝔪 = T_𝔪 ⧸ 𝔪_{T_𝔪} ^ n`, which is `n`.
  let Tm := Localization.AtPrime (maximalIdeal T)
  have hunder : (maximalIdeal T).under S = maximalIdeal S :=
    maximalIdeal_comap (algebraMap S T)
  have hmapTm : (maximalIdeal S).map (algebraMap S Tm) = maximalIdeal Tm ^ n := by
    rw [IsScalarTower.algebraMap_eq S T Tm, ← Ideal.map_map, hpow, Ideal.map_pow,
      Localization.AtPrime.map_eq_maximalIdeal]
  have : IsDiscreteValuationRing Tm :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain T
      (IsDiscreteValuationRing.not_a_field T) Tm
  have hidx : (maximalIdeal T).ramificationIdx S = n := by
    rw [Ideal.ramificationIdx_def, hunder, hmapTm, length_quotient_pow_maximalIdeal,
      ENat.toNat_natCast]
  rw [hidx, hpow]

end IsDiscreteValuationRing

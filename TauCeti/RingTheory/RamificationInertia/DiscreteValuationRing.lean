/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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

* `TauCeti.IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx`: `𝔪_S T = 𝔪_T ^ e` with
  `e` the ramification index of `𝔪_T` over `S`.
* `TauCeti.IsDiscreteValuationRing.ramificationIdx_eq_of_map_maximalIdeal_eq_pow`: the index equals
  any exponent satisfying this maximal-ideal identity.
* `TauCeti.IsDiscreteValuationRing.addVal_algebraMap`: for an injective local homomorphism of
  discrete valuation rings `S → T`, `addVal T (algebraMap S T a) = e • addVal S a`.

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

open IsLocalRing IsDiscreteValuationRing

namespace TauCeti.IsDiscreteValuationRing

section

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
  -- The length-based ramification index agrees with the exponent-based one over the Dedekind
  -- domain `T` (`Ideal.ramificationIdx'_eq_ramificationIdx'`), and the latter is `n`.
  have : (maximalIdeal T).LiesOver (maximalIdeal S) :=
    ⟨(maximalIdeal_comap (algebraMap S T)).symm⟩
  have hidx : (maximalIdeal T).ramificationIdx S = n := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx' (maximalIdeal S) (maximalIdeal T) h]
    refine Ideal.ramificationIdx'_spec hpow.le ?_
    rw [hpow]
    exact (Ideal.pow_succ_lt_pow (not_a_field T) n).not_ge
  rw [hidx, hpow]

/-- For a local homomorphism to a DVR, the exponent in a maximal-ideal power identity is the
ramification index. This is the exponent characterization of Stacks, Definition 15.113.1 (09E4),
with no DVR assumption on the base ring. -/
@[stacks 09E4 "exponent characterization with arbitrary local base ring"]
theorem ramificationIdx_eq_of_map_maximalIdeal_eq_pow {exponent : ℕ}
    (hexponent : (maximalIdeal S).map (algebraMap S T) = maximalIdeal T ^ exponent) :
    (maximalIdeal T).ramificationIdx S = exponent := by
  have hpowers : StrictAnti (fun power : ℕ ↦ maximalIdeal T ^ power) :=
    Ideal.pow_right_strictAnti (maximalIdeal T) (not_a_field T) (maximalIdeal.isMaximal T).ne_top
  have hmap : (maximalIdeal S).map (algebraMap S T) ≠ ⊥ := by
    rw [hexponent]
    exact ne_of_gt (lt_of_le_of_lt bot_le (hpowers (Nat.lt_succ_self exponent)))
  exact hpowers.injective ((map_maximalIdeal_eq_pow_ramificationIdx hmap).symm.trans hexponent)

end

/-- **Valuation scaling along an extension of discrete valuation rings.** For a faithful local
algebra of discrete valuation rings `S → T`, the additive valuation of `T` restricts to `e` times
the additive valuation of `S`, where `e` is the ramification index
`(maximalIdeal T).ramificationIdx S`. -/
theorem addVal_algebraMap {S T : Type*} [CommRing S] [IsDomain S] [_root_.IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [_root_.IsDiscreteValuationRing T] [Algebra S T]
    [IsLocalHom (algebraMap S T)] [FaithfulSMul S T] (a : S) :
    _root_.IsDiscreteValuationRing.addVal T (algebraMap S T a) =
      (maximalIdeal T).ramificationIdx S • _root_.IsDiscreteValuationRing.addVal S a := by
  obtain ⟨ϖS, hϖS⟩ := exists_irreducible S
  obtain ⟨ϖT, hϖT⟩ := exists_irreducible T
  have hmap_ne : (maximalIdeal S).map (algebraMap S T) ≠ ⊥ := by
    intro hbot
    have hmem : algebraMap S T ϖS ∈ (maximalIdeal S).map (algebraMap S T) :=
      Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).2 hϖS.not_isUnit)
    rw [hbot, Ideal.mem_bot, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective S T)] at hmem
    exact hϖS.ne_zero hmem
  have hmap := map_maximalIdeal_eq_pow_ramificationIdx (S := S) (T := T) hmap_ne
  set e := (maximalIdeal T).ramificationIdx S
  have he_ne : e ≠ 0 := by
    intro he0
    rw [he0, pow_zero, Ideal.one_eq_top] at hmap
    exact (IsLocalRing.map_maximalIdeal_lt_top (algebraMap S T)).ne hmap
  have hval_ϖS : _root_.IsDiscreteValuationRing.addVal T (algebraMap S T ϖS) = e := by
    rw [← hϖT.addVal_pow e, addVal_eq_iff_associated, ← Ideal.span_singleton_eq_span_singleton,
      ← Set.image_singleton, ← Ideal.map_span, ← hϖS.maximalIdeal_eq, hmap, hϖT.maximalIdeal_eq,
      Ideal.span_singleton_pow]
  by_cases ha : a = 0
  · subst ha
    rw [map_zero, addVal_zero, addVal_zero, nsmul_eq_mul, ENat.mul_top (Nat.cast_ne_zero.2 he_ne)]
  · obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hϖS
    rw [addVal_def' u hϖS n, map_mul, map_pow, addVal_mul, addVal_pow, hval_ϖS,
      addVal_eq_zero_iff.2 (u.isUnit.map (algebraMap S T)), zero_add, nsmul_eq_mul, nsmul_eq_mul,
      mul_comm]

end TauCeti.IsDiscreteValuationRing

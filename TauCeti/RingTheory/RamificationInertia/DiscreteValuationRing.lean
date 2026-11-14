/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang, The Tau Ceti contributors
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
exponent `e` with `π_S = u π_T ^ e` for uniformizers `π_S`, `π_T` and a unit `u`, and the
additive valuation scales by `e` along `algebraMap S T`.

## Main results

* `TauCeti.IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx`: `𝔪_S T = 𝔪_T ^ e` with
  `e` the ramification index of `𝔪_T` over `S`.
* `TauCeti.IsDiscreteValuationRing.ramificationIdx_eq_of_map_maximalIdeal_eq_pow`: the index equals
  any exponent satisfying this maximal-ideal identity.
* `TauCeti.IsDiscreteValuationRing.addVal_algebraMap`: for an injective local homomorphism of
  discrete valuation rings `S → T`, `addVal T (algebraMap S T x) = e • addVal S x`.

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

section AddVal

/-- Under an injective local homomorphism of discrete valuation rings `S → T`, the additive
valuation scales by the ramification index `(maximalIdeal T).ramificationIdx S`.

Not marked `@[simp]` so it does not compete with `TauCeti.addVal_algebraMap` (whose right-hand side
uses `ramificationIndex K L`) on integer rings of local fields; this generalizes that scaling
formula to arbitrary discrete valuation rings. -/
theorem addVal_algebraMap {S T : Type*} [CommRing S] [CommRing T] [IsDomain S] [IsDomain T]
    [IsDiscreteValuationRing S] [IsDiscreteValuationRing T] [Algebra S T]
    [IsLocalHom (algebraMap S T)] [FaithfulSMul S T] (x : S) :
    addVal T (algebraMap S T x) = (maximalIdeal T).ramificationIdx S • addVal S x := by
  obtain ⟨π, hπ⟩ := exists_irreducible S
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible T
  have hπT : algebraMap S T π ≠ 0 := fun h ↦
    hπ.ne_zero (FaithfulSMul.algebraMap_injective S T (h.trans (map_zero _).symm))
  obtain ⟨e, v, hπe⟩ := eq_unit_mul_pow_irreducible hπT hϖ
  have hmap : (maximalIdeal S).map (algebraMap S T) = maximalIdeal T ^ e := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hπe,
      Ideal.span_singleton_mul_left_unit v.isUnit, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  have he : (maximalIdeal T).ramificationIdx S = e :=
    ramificationIdx_eq_of_map_maximalIdeal_eq_pow hmap
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hπ.not_isUnit
      (isUnit_of_map_unit (algebraMap S T) π (by simp [hπe]))
  by_cases hx : x = 0
  · simp [hx, he, nsmul_eq_mul, ENat.mul_top (Nat.cast_ne_zero.2 he0)]
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hπ
  rw [addVal_def' u hπ n, he, map_mul, map_pow, addVal_mul,
    addVal_eq_zero_iff.2 (u.isUnit.map (algebraMap S T)), zero_add, addVal_pow, hπe,
    addVal_def' v hϖ e, nsmul_eq_mul, nsmul_eq_mul, mul_comm]

end AddVal

end TauCeti.IsDiscreteValuationRing

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import TauCeti.NumberTheory.NumberField.Units.Torsion
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import TauCeti.Data.Nat.Totient
import TauCeti.NumberTheory.EffectiveBounds.Regulator
import TauCeti.NumberTheory.NumberField.Quadratic.Radicand
import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers
import TauCeti.RingTheory.RootsOfUnity.Sixth

/-!
# The roots of unity of a quadratic field

A primitive `n`-th root of unity has degree `φ(n)` over `ℚ`, so a quadratic field contains only
roots of unity of order `n` with `φ(n) ≤ 2`, that is `n ∈ {1, 2, 3, 4, 6}`. Since `-1` is always
present, the torsion order `w` of a quadratic field `K` is `2`, `4` or `6`. A primitive fourth root
of unity is a square root of `-1`, and twice a primitive sixth root of unity minus one is a square
root of `-3`; by the uniqueness of the squarefree radicand, these occur only in `ℚ(i)` and in
`ℚ(√-3)`. Hence, for the squarefree radicand `d` and discriminant `D` of `K`,

* `w = 4` when `d = -1` (`D = -4`), the roots of unity being the powers of `√-1`;
* `w = 6` when `d = -3` (`D = -3`), the roots of unity being the powers of `(1 + √-3) / 2`;
* `w = 2` otherwise.

An imaginary quadratic field has unit rank `0`, so its units are exactly its roots of unity: there
are six of them for `D = -3`, four for `D = -4`, and only `±1` otherwise.

## Main results

* `TauCeti.NumberField.Units.torsionOrder_eq_two_or_four_or_six`: in degree `2`, `w ∈ {2, 4, 6}`.
* `TauCeti.NumberField.Units.torsionOrder_eq_of_squarefree`: `w` in terms of the squarefree
  radicand.
* `TauCeti.NumberField.Units.torsionOrder_eq_of_finrank_eq_two`: `w` in terms of the
  discriminant.
* `TauCeti.NumberField.Units.natCard_units_eq_of_isTotallyComplex`: the number of units of an
  imaginary quadratic field.
* `TauCeti.NumberField.Units.units_eq_one_or_neg_one_of_isTotallyComplex`: apart from
  discriminants `-3` and `-4`, the only units of an imaginary quadratic field are `±1`.
-/

public section

open Polynomial Module NumberField NumberField.Units
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **The torsion order of a quadratic field is `2`, `4` or `6`.** Every root of unity in a
quadratic field has order dividing `4` or `6`. -/
theorem torsionOrder_eq_two_or_four_or_six (hK : finrank ℚ K = 2) :
    torsionOrder K = 2 ∨ torsionOrder K = 4 ∨ torsionOrder K = 6 := by
  have hle : (torsionOrder K).totient ≤ 2 := hK ▸ totient_torsionOrder_le_finrank
  have hpos := Nat.totient_pos.mpr (torsionOrder_pos K)
  have heven := even_torsionOrder K
  rcases (show (torsionOrder K).totient = 1 ∨ (torsionOrder K).totient = 2 by omega) with h | h
  · rcases Nat.totient_eq_one_iff.mp h with h | h
    · rw [h] at heven
      exact absurd heven (by decide)
    · exact .inl h
  · rcases TauCeti.Nat.totient_eq_two_iff.mp h with h | h | h
    · rw [h] at heven
      exact absurd heven (by decide)
    · exact .inr (.inl h)
    · exact .inr (.inr h)

/-- **The torsion order of a quadratic field from its squarefree radicand.** For `K = ℚ(√d)` with
`d` squarefree, the number of roots of unity in `K` is `4` if `d = -1`, `6` if `d = -3`, and `2`
otherwise. -/
theorem torsionOrder_eq_of_squarefree (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hd : Squarefree d) :
    torsionOrder K = if d = -1 then 4 else if d = -3 then 6 else 2 := by
  have hK := finrank_rat_eq_two hmin hgen
  -- A square root `z ∈ K` of a negative squarefree integer `n` is irrational, so `n` is the
  -- radicand.
  have key (z : K) (n : ℤ) (hz : z ^ 2 = n) (hn : n < 0) (hsq : Squarefree n) : d = n := by
    refine radicand_eq_of_sq_eq_intCast hK hmin hd hz (fun ⟨q, hq⟩ => ?_) hsq
    have : q ^ 2 = n := (algebraMap ℚ K).injective (by rw [map_pow, hq, hz, map_intCast])
    nlinarith [sq_nonneg q, (by exact_mod_cast hn : (n : ℚ) < 0)]
  split_ifs with h1 h3
  · -- `θ ^ 2 = -1`, so `θ` is a primitive fourth root of unity.
    subst h1
    have hsq : (θ : K) ^ 2 = -1 := by simpa using coe_gen_sq hmin
    have h4 := dvd_torsionOrder_of_isPrimitiveRoot (IsPrimitiveRoot.iff_orderOf.mpr
      (orderOf_eq_prime_pow (x := (θ : K)) (p := 2) (n := 1) (by norm_num [hsq])
        (by rw [pow_succ, pow_mul, pow_one, hsq]; norm_num)))
    rcases torsionOrder_eq_two_or_four_or_six hK with h | h | h <;> rw [h] at h4 <;> omega
  · -- `θ ^ 2 = -3`, so `(1 + θ) / 2` is a primitive sixth root of unity.
    subst h3
    have h6 := dvd_torsionOrder_of_isPrimitiveRoot
      (isPrimitiveRoot_one_add_div_two (x := (θ : K)) (by simpa using coe_gen_sq hmin))
    rcases torsionOrder_eq_two_or_four_or_six hK with h | h | h <;> rw [h] at h6 <;> omega
  · obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_torsionOrder (K := K)
    rcases torsionOrder_eq_two_or_four_or_six hK with h | h | h
    · exact h
    · -- A primitive fourth root of unity is a square root of `-1`.
      rw [h] at hζ
      have hsq : ζ ^ 2 = -1 :=
        (hζ.pow (by norm_num) (by norm_num : 4 = 2 * 2)).eq_neg_one_of_two_right
      refine absurd (key ζ (-1) (by simp [hsq]) (by norm_num) ?_) h1
      rw [← Int.squarefree_natAbs]
      exact squarefree_one
    · -- For a primitive sixth root of unity `ζ`, `(2ζ - 1)² = -3`.
      rw [h] at hζ
      refine absurd (key (2 * ζ - 1) (-3) ?_ (by norm_num) ?_) h3
      · push_cast
        linear_combination 4 * isPrimitiveRoot_six_iff.mp hζ
      · rw [← Int.squarefree_natAbs]
        exact Nat.prime_three.squarefree

/-- **The torsion order of a quadratic field from its discriminant.** The number of roots of unity
in a quadratic field of discriminant `D` is `4` if `D = -4`, `6` if `D = -3`, and `2`
otherwise. -/
theorem torsionOrder_eq_of_finrank_eq_two (hK : finrank ℚ K = 2) :
    torsionOrder K = if discr K = -4 then 4 else if discr K = -3 then 6 else 2 := by
  obtain ⟨θ, d, hmin, hgen, hd⟩ := exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top hK
  rw [torsionOrder_eq_of_squarefree hmin hgen hd]
  by_cases h4 : d % 4 = 1
  · rw [discr_eq_of_squarefree_of_mod_four_eq_one hmin hgen hd h4]
    have h1 : d ≠ -1 := by rintro rfl; norm_num at h4
    have h4' : d ≠ -4 := by rintro rfl; norm_num at h4
    simp [h1, h4']
  · rw [discr_eq_four_mul_of_mod_four_ne_one hmin hgen hd h4]
    have h3 : d ≠ -3 := by rintro rfl; norm_num at h4
    have h3' : 4 * d ≠ -3 := by omega
    simp [h3, h3', show 4 * d = -4 ↔ d = -1 by omega]

/-- **The units of an imaginary quadratic field.** An imaginary quadratic field of discriminant
`D` has `4` units if `D = -4`, `6` units if `D = -3`, and `2` units otherwise. Its unit rank is
`0`, so all its units are roots of unity. -/
theorem natCard_units_eq_of_isTotallyComplex [IsTotallyComplex K] (hK : finrank ℚ K = 2) :
    Nat.card (𝓞 K)ˣ = if discr K = -4 then 4 else if discr K = -3 then 6 else 2 := by
  rw [← torsionOrder_eq_of_finrank_eq_two hK, torsionOrder,
    torsion_eq_top_of_rank_eq_zero (rank_eq_zero_of_isTotallyComplex_of_finrank_eq_two K hK),
    Subgroup.card_top]

/-- **The units of an imaginary quadratic field are `±1`**, unless its discriminant is `-3` or
`-4`. -/
theorem units_eq_one_or_neg_one_of_isTotallyComplex [IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (h4 : discr K ≠ -4) (h3 : discr K ≠ -3) (u : (𝓞 K)ˣ) :
    u = 1 ∨ u = -1 := by
  have hu : u ∈ torsion K := by
    rw [torsion_eq_top_of_rank_eq_zero (rank_eq_zero_of_isTotallyComplex_of_finrank_eq_two K hK)]
    exact Subgroup.mem_top u
  exact torsion_eq_one_or_neg_one_of_torsionOrder_eq_two
    (by simpa [h4, h3] using torsionOrder_eq_of_finrank_eq_two hK) ⟨u, hu⟩

end TauCeti.NumberField.Units

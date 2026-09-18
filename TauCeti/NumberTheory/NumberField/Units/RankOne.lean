/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Units of a number field of unit rank one

A number field `K` with `NumberField.Units.rank K = 1` has exactly two infinite places, and the
product formula ties the absolute values of a unit at the two places to each other. This file
records the consequences for certifying a fundamental unit:

* a unit is torsion as soon as it has absolute value `1` at one infinite place;
* the norm of the logarithmic embedding of a unit is `mult w * |log (w u)|` at either place `w`;
* **the rank-one criterion**: a unit `u` with `1 < w u` at an infinite place `w` generates the
  unit group modulo torsion if and only if no unit `v` satisfies `1 < w v < w u`.

The criterion is what turns "`u` is a fundamental unit" into a statement about a bounded set of
units, which is finite; an explicit fundamental unit and an exact value of the regulator can
then be certified by a finite search.

## Main results

* `TauCeti.NumberField.Units.mem_torsion_iff_apply_eq_one_of_rank_eq_one`: at unit rank one, a
  unit is torsion if and only if it has absolute value `1` at a given infinite place.
* `TauCeti.NumberField.Units.norm_logEmbedding_eq_of_rank_eq_one`: at unit rank one,
  `‖logEmbedding K u‖ = mult w * |log (w u)|` for every infinite place `w`.
* `TauCeti.NumberField.Units.logEmbedding_norm_lt_iff_at_place`: the comparison of the norms of
  the logarithmic embeddings of two units reads `|log (w v)| < log (w u)` at a place `w` with
  `1 < w u`.
* `TauCeti.NumberField.Units.closure_sup_torsion_eq_top_iff_of_rank_eq_one`: the rank-one
  criterion.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §7.
* H. Cohen, *A Course in Computational Algebraic Number Theory*, §5.7.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- The absolute value of an integer power of a unit at an infinite place. -/
@[simp] theorem NumberField.InfinitePlace.apply_coe_zpow (w : InfinitePlace K) (u : (𝓞 K)ˣ)
    (n : ℤ) : w ((u ^ n : (𝓞 K)ˣ) : K) = w u ^ n := by
  rw [Units.coe_zpow, map_zpow₀]

namespace TauCeti.NumberField.Units

/-- A number field of unit rank one has exactly two infinite places. -/
theorem card_infinitePlace_eq_two_of_rank_eq_one (hrank : rank K = 1) :
    Fintype.card (InfinitePlace K) = 2 := by
  have := Fintype.card_pos (α := InfinitePlace K)
  unfold rank at hrank
  omega

/-- At unit rank one, every infinite place has exactly one other infinite place. -/
theorem subsingleton_ne_of_rank_eq_one (hrank : rank K = 1) (w : InfinitePlace K) :
    Subsingleton {w' : InfinitePlace K // w' ≠ w} := by
  classical
  rw [← Fintype.card_le_one_iff_subsingleton, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, card_infinitePlace_eq_two_of_rank_eq_one hrank]

/-- **The product formula at unit rank one.** The absolute values of a unit at the two infinite
places determine each other: `mult w * log (w u) + mult w' * log (w' u) = 0`. -/
theorem mult_mul_log_add_mult_mul_log_eq_zero_of_rank_eq_one (hrank : rank K = 1)
    {w w' : InfinitePlace K} (hne : w' ≠ w) (u : (𝓞 K)ˣ) :
    w.mult * Real.log (w u) + w'.mult * Real.log (w' u) = 0 := by
  classical
  have h := sum_mult_mul_log u
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w] at h
  have := subsingleton_ne_of_rank_eq_one hrank w
  rwa [Fintype.sum_subsingleton _ ⟨w', hne⟩] at h

/-- At unit rank one, a unit of absolute value `1` at one infinite place is torsion. -/
theorem mem_torsion_iff_apply_eq_one_of_rank_eq_one (hrank : rank K = 1) (w : InfinitePlace K)
    {u : (𝓞 K)ˣ} : u ∈ torsion K ↔ w u = 1 := by
  refine ⟨fun h => (mem_torsion K).mp h w, fun h => (mem_torsion K).mpr fun w' => ?_⟩
  by_cases hw : w' = w
  · exact hw ▸ h
  · have h0 := mult_mul_log_add_mult_mul_log_eq_zero_of_rank_eq_one hrank hw u
    rw [h, Real.log_one, mul_zero, zero_add] at h0
    exact mult_log_place_eq_zero.mp h0

open scoped Classical in
/-- At unit rank one, the norm of the logarithmic embedding of a unit is `mult w * |log (w u)|`
at either infinite place `w`. -/
theorem norm_logEmbedding_eq_of_rank_eq_one (hrank : rank K = 1) (w : InfinitePlace K)
    (u : (𝓞 K)ˣ) :
    ‖logEmbedding K (Additive.ofMul u)‖ = w.mult * |Real.log (w u)| := by
  -- The log space has a single coordinate, at the infinite place `w₁ ≠ w₀`.
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : InfinitePlace K, w₁ ≠ w₀ :=
    Fintype.exists_ne_of_one_lt_card
      (by rw [card_infinitePlace_eq_two_of_rank_eq_one hrank]; exact one_lt_two) w₀
  have := subsingleton_ne_of_rank_eq_one hrank w₀
  have hnorm : ‖logEmbedding K (Additive.ofMul u)‖ =
      ‖logEmbedding K (Additive.ofMul u) ⟨w₁, hw₁⟩‖ := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_)
      (norm_le_pi_norm _ _)
    rw [Subsingleton.elim i ⟨w₁, hw₁⟩]
  rw [hnorm, logEmbedding_component, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  dsimp only
  by_cases hw : w = w₁
  · rw [hw]
  -- Otherwise `w` is the other place, and the product formula transfers the value.
  have h0 := mult_mul_log_add_mult_mul_log_eq_zero_of_rank_eq_one hrank (Ne.symm hw) u
  rw [← Nat.abs_cast w₁.mult, ← abs_mul, eq_neg_of_add_eq_zero_right h0, abs_neg, abs_mul,
    Nat.abs_cast]

open scoped Classical in
/-- **Comparing logarithmic embeddings at a chosen place.** At unit rank one, for an infinite
place `w` and a unit `u` with `1 < w u`, the norm of the logarithmic embedding of a unit `v` is
smaller than that of `u` if and only if `|log (w v)| < log (w u)`. -/
theorem logEmbedding_norm_lt_iff_at_place (hrank : rank K = 1) (w : InfinitePlace K)
    (u v : (𝓞 K)ˣ) (hu : 1 < w u) :
    ‖logEmbedding K (Additive.ofMul v)‖ < ‖logEmbedding K (Additive.ofMul u)‖ ↔
      |Real.log (w v)| < Real.log (w u) := by
  rw [norm_logEmbedding_eq_of_rank_eq_one hrank w, norm_logEmbedding_eq_of_rank_eq_one hrank w,
    abs_of_pos (Real.log_pos hu)]
  have hmult : (0 : ℝ) < w.mult := by exact_mod_cast mult_pos
  exact ⟨fun h => lt_of_mul_lt_mul_left h hmult.le, fun h => mul_lt_mul_of_pos_left h hmult⟩

/-- **The rank-one criterion for a fundamental unit.** Let `K` have unit rank one, let `w` be an
infinite place and let `u` be a unit with `1 < w u` (so `u` is not torsion). Then `u` generates
the unit group modulo torsion if and only if no unit `v` satisfies `1 < w v < w u`. -/
theorem closure_sup_torsion_eq_top_iff_of_rank_eq_one (hrank : rank K = 1)
    (w : InfinitePlace K) {u : (𝓞 K)ˣ} (hu : 1 < w u) :
    Subgroup.closure {u} ⊔ torsion K = ⊤ ↔ ∀ v : (𝓞 K)ˣ, w v ≤ 1 ∨ w u ≤ w v := by
  constructor
  · -- A unit `v = u ^ n * z` with `z` torsion has `w v = (w u) ^ n`, which is never strictly
    -- between `1` and `w u`.
    intro h v
    by_contra! hv
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp (h ▸ Subgroup.mem_top v)
    obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.mp hy
    have hz1 : w z = 1 := (mem_torsion K).mp hz w
    rw [Units.val_mul, map_mul, map_mul, hz1, mul_one, apply_coe_zpow] at hv
    have h1 := (one_lt_zpow_iff_right₀ hu).mp hv.1
    have h2 := (zpow_lt_zpow_iff_right₀ hu).mp (by simpa using hv.2 : _ < _ ^ (1 : ℤ))
    omega
  · -- Given `v`, the power `u ^ n` with `n = ⌊log (w v) / log (w u)⌋` brings `w (v * u⁻ⁿ)` into
    -- `[1, w u)`, so `v * u⁻ⁿ` is torsion by the hypothesis and the rank-one torsion criterion.
    intro h
    rw [eq_top_iff]
    rintro v -
    have ha : 0 < Real.log (w u) := Real.log_pos hu
    have hv : 0 < w v := pos_at_place v w
    have hu0 : 0 < w u := pos_at_place u w
    set n : ℤ := ⌊Real.log (w v) / Real.log (w u)⌋
    have hval : w ((v * u ^ (-n) : (𝓞 K)ˣ) : K) = w v / w u ^ n := by
      rw [Units.val_mul, map_mul, map_mul, apply_coe_zpow, zpow_neg, div_eq_mul_inv]
    have hpow : 0 < w u ^ n := zpow_pos hu0 n
    have hge : 1 ≤ w ((v * u ^ (-n) : (𝓞 K)ˣ) : K) := by
      rw [hval, le_div_iff₀ hpow, one_mul, ← Real.log_le_log_iff hpow hv, Real.log_zpow,
        ← le_div_iff₀ ha]
      exact Int.floor_le _
    have hlt : w ((v * u ^ (-n) : (𝓞 K)ˣ) : K) < w u := by
      rw [hval, div_lt_iff₀ hpow, ← zpow_one_add₀ hu0.ne',
        ← Real.log_lt_log_iff hv (zpow_pos hu0 _), Real.log_zpow, ← div_lt_iff₀ ha, Int.cast_add,
        Int.cast_one, add_comm]
      exact Int.lt_floor_add_one _
    have htor : v * u ^ (-n) ∈ torsion K := by
      rw [mem_torsion_iff_apply_eq_one_of_rank_eq_one hrank w]
      rcases h (v * u ^ (-n)) with h1 | h1
      · exact le_antisymm h1 hge
      · exact absurd h1 (not_le.mpr hlt)
    refine Subgroup.mem_sup.mpr ⟨u ^ n, Subgroup.mem_closure_singleton.mpr ⟨n, rfl⟩,
      v * u ^ (-n), htor, ?_⟩
    rw [zpow_neg, mul_comm v, mul_inv_cancel_left]

end TauCeti.NumberField.Units

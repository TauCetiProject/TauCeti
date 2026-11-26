/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
import Mathlib.Analysis.Asymptotics.Arith
import TauCeti.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting integers detected by large weights

Suppose that at scale `T` a finite family of nonnegative weights on `[1, T²]` has sums
`O(T^a)`. If every integer in a set `S` with `q * n ≤ T²` is detected by a weight of size at
least `T^b` in some member of the family, then `S` has counting function `O(x^((a - b)/2))`.
For theta tails in quadratic-twist zero detection, the exponents are `a = 2 + δ` and
`b = 2 * δ`, giving the power saving `δ/2`.

The theta-tail application uses the counting argument in `New.exists_card_zero_quadTwist_le`
from [lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207),
`grh/src/Lib/Analytic/QuadraticTwist.lean`.
-/

public section

open Asymptotics Filter Finset Real

namespace Set

/-- Detection at threshold `T ^ b` and total weights of order `T ^ a` give a count of order
`x ^ ((a - b) / 2)`. The count starts at `1`, as does the sum supplying the bound. The parameter
`q` allows the detection range to be shortened to `q * n ≤ T²` without changing the exponent. -/
theorem isBigO_ncard_of_threshold_sums {ι : Type*} [Finite ι] (S : Set ℕ)
    (w : ι → ℝ → ℕ → ℝ) (q a b : ℝ)
    (hw : ∀ᶠ T : ℝ in atTop, ∀ i n, n ∈ Finset.Icc 1 ⌊T ^ 2⌋₊ → 0 ≤ w i T n)
    (havg : ∀ i, (fun T : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, w i T n) =O[atTop] (· ^ a))
    (hdetect : ∀ᶠ T : ℝ in atTop, ∀ n ∈ S, 1 ≤ n → q * n ≤ T ^ 2 → ∃ i, T ^ b ≤ w i T n) :
    (fun x : ℝ ↦ ({n ∈ S | 1 ≤ n ∧ (n : ℝ) ≤ x}.ncard : ℝ)) =O[atTop] (· ^ ((a - b) / 2)) := by
  let := Fintype.ofFinite ι
  let Q := max 1 q
  have hQ : 0 < Q := zero_lt_one.trans_le (le_max_left ..)
  let T (x : ℝ) := √(Q * x)
  have hT : Tendsto T atTop atTop := tendsto_sqrt_atTop.comp
    ((tendsto_const_mul_atTop_of_pos hQ).2 tendsto_id)
  have hsum : (fun t : ℝ ↦ ∑ i, ∑ n ∈ Finset.Icc 1 ⌊t ^ 2⌋₊, w i t n) =O[atTop] (· ^ a) := by
    convert IsBigO.sum (s := Finset.univ) (fun i _ ↦ havg i) using 1
    funext t
    simp only [Finset.sum_apply]
  obtain ⟨C, hC⟩ := isBigO_iff.mp hsum
  refine IsBigO.of_bound (C * Q ^ ((a - b) / 2)) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ), hT.eventually hw, hT.eventually hdetect,
    hT.eventually hC] with x hx hpos hdet hbound
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hTx : 0 < T x := sqrt_pos_of_pos (mul_pos hQ hx₀)
  have hsquare : T x ^ 2 = Q * x := sq_sqrt (by positivity)
  have hxT : x ≤ T x ^ 2 := by
    simpa only [hsquare, one_mul] using mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) q) hx₀.le
  let A : Set ℕ := {n ∈ S | 1 ≤ n ∧ (n : ℝ) ≤ x}
  have hA : A ⊆ Set.Icc 1 ⌊T x ^ 2⌋₊ := fun _ hn ↦ ⟨hn.2.1, Nat.le_floor (hn.2.2.trans hxT)⟩
  have hfin := (finite_Icc _ _).subset hA
  have hcnt : (A.ncard : ℝ) * T x ^ b ≤ ∑ i, ∑ n ∈ Finset.Icc 1 ⌊T x ^ 2⌋₊, w i (T x) n := by
    rw [ncard_eq_toFinset_card A hfin, ← nsmul_eq_mul]
    refine hfin.toFinset.card_nsmul_le_sum_sum_of_exists_le (fun n hn ↦ ?_) Finset.univ _
      (fun i _ n hn ↦ hpos i n hn) (fun n hn ↦ ?_)
    · simpa using hA (hfin.mem_toFinset.mp hn)
    have hn' := hfin.mem_toFinset.mp hn
    have hqn : q * (n : ℝ) ≤ T x ^ 2 := calc
      _ ≤ Q * (n : ℝ) := mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)
      _ ≤ T x ^ 2 := hsquare ▸ mul_le_mul_of_nonneg_left hn'.2.2 hQ.le
    simpa using hdet n hn'.1 hn'.2.1 hqn
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ (A.ncard : ℝ)),
    Real.norm_of_nonneg (rpow_nonneg hx₀.le _)]
  have hquot : (A.ncard : ℝ) ≤ C * T x ^ (a - b) := by
    refine le_of_mul_le_mul_right ?_ (rpow_pos_of_pos hTx b)
    rw [mul_assoc, ← rpow_add hTx, sub_add_cancel]
    refine hcnt.trans ((le_abs_self _).trans ?_)
    simpa only [Real.norm_eq_abs, abs_of_pos (rpow_pos_of_pos hTx a)] using hbound
  have hrescale : T x ^ (a - b) = Q ^ ((a - b) / 2) * x ^ ((a - b) / 2) := by
    dsimp [T]
    rw [← Real.rpow_div_two_eq_sqrt (a - b) (mul_nonneg hQ.le hx₀.le), mul_rpow hQ.le hx₀.le]
  simpa only [hrescale, mul_assoc] using hquot

end Set

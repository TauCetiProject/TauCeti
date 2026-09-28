/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import TauCeti.NumberTheory.LocalField.FactorialValuation

/-!
# The local exponential series

Let `K` be a finite extension of `ℚ_[p]`, with absolute ramification index `e`.  At every
integral depth `i` satisfying `e < (p - 1) * i`, the exponential series

`∑ n, x ^ n / n !`

converges for `x ∈ 𝓂[K] ^ i`, and this file proves that convergence.  Its sum is Mathlib's
`NormedSpace.exp`, so no new exponential is introduced here.

The threshold `e < (p - 1) * i` is exactly the range in which the term valuations tend to
infinity throughout the ideal: there the normalized valuation of `x ^ n / n !` grows linearly in
`n` for every `x ∈ 𝓂[K] ^ i`, so the series converges on all of `𝓂[K] ^ i` rather than on a
smaller ball.  The strictness matters: at `e = (p - 1) * i` an `x` of normalized valuation
exactly `i` has `x ^ n / n !` of valuation `i * s` with `s` the sum of the base `p` digits of
`n`, so the term valuations stay bounded along `n = p ^ k` and the terms do not tend to zero.
Convergence on the whole ideal is what makes the exponential a map from the deep additive
group `𝓂[K] ^ i` to the deep unit group `1 + 𝓂[K] ^ i`, whose inverse is the logarithm; that
identification of a deep additive group with a deep unit group is what computes the power
classes, and hence the square classes, of `K`.

## Main results

* `TauCeti.tendsto_expSeries_term_zero_of_le_normalizedValuation`: exponential terms tend to zero
  when the argument has sufficiently large normalized valuation.
* `TauCeti.summable_expSeries_of_mem_maximalIdeal_pow`: the exponential series is summable on
  `𝓂[K] ^ i` in the convergence range.
* `TauCeti.hasSum_exp_of_mem_maximalIdeal_pow`: on `𝓂[K] ^ i` in the convergence range the
  exponential series sums to `NormedSpace.exp`.

## References

* J.-P. Serre, *Local Fields*, Chapter II, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

open Filter ValuativeRel IsNonarchimedeanLocalField

open scoped Topology

namespace TauCeti

variable {K : Type*} [Field K]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {p : ℕ} [Fact p.Prime] [FinitePadicExtension K p]

/-- The additive normalized valuation of an exponential-series term is the valuation of the
numerator minus the factorial valuation. -/
private theorem toAdd_normalizedValuation_expSeries_term {x : K} (hx : x ≠ 0) (n : ℕ)
    (hfac : (n.factorial : K) ≠ 0) :
    (normalizedValuation K
        (Units.mk0 (x ^ n / (n.factorial : K))
          (div_ne_zero (pow_ne_zero n hx) hfac))).toAdd =
      (n : ℤ) * (normalizedValuation K (Units.mk0 x hx)).toAdd -
        natCastValuation K n.factorial hfac := by
  have hunit :
      Units.mk0 (x ^ n / (n.factorial : K))
          (div_ne_zero (pow_ne_zero n hx) hfac) =
        Units.mk0 x hx ^ n / Units.mk0 (n.factorial : K) hfac := by
    ext
    simp
  rw [hunit, map_div, map_pow, toAdd_div, toAdd_pow,
    toAdd_normalizedValuation_natCast]
  simp only [nsmul_eq_mul]

/-- At a depth `i` in the exponential convergence range, the normalized valuation of the term
`x ^ n / n !` grows at least linearly in `n`: scaled by `p - 1` it exceeds `n`. -/
private theorem lt_sub_one_mul_toAdd_normalizedValuation_expSeries_term {i n : ℕ} {x : K}
    (hx : x ≠ 0) (hfac : (n.factorial : K) ≠ 0) (hn : n ≠ 0)
    (hxi : (i : ℤ) ≤ (normalizedValuation K (Units.mk0 x hx)).toAdd)
    (hi : absoluteRamificationIndex K p < (p - 1) * i) :
    (n : ℤ) < (p - 1 : ℕ) *
      (normalizedValuation K
        (Units.mk0 (x ^ n / (n.factorial : K))
          (div_ne_zero (pow_ne_zero n hx) hfac))).toAdd := by
  -- The term valuation is `n * v(x) - v(n !)`, where `(p - 1) * v(n !) < e * n` and
  -- `(p - 1) * n * v(x) ≥ (p - 1) * n * i ≥ (e + 1) * n`, leaving a margin of `n`.
  have hfact := sub_one_mul_natCastValuation_factorial_lt_of_ne_zero K p hn
  have hgapn : (absoluteRamificationIndex K p + 1) * n ≤ ((p - 1) * i) * n :=
    Nat.mul_le_mul_right n (by omega)
  have hxmul := mul_le_mul_of_nonneg_left hxi
    (mul_nonneg (Int.natCast_nonneg (p - 1)) (Int.natCast_nonneg n))
  rw [toAdd_normalizedValuation_expSeries_term (K := K) hx n hfac]
  nlinarith

/-- At a depth in the exponential convergence range, the terms `x ^ n / n !` tend to zero for
every nonzero `x` whose normalized valuation is at least that depth. -/
theorem tendsto_expSeries_term_zero_of_le_normalizedValuation {i : ℕ} {x : K} (hx : x ≠ 0)
    (hxi : (i : ℤ) ≤ (normalizedValuation K (Units.mk0 x hx)).toAdd)
    (hi : absoluteRamificationIndex K p < (p - 1) * i) :
    Tendsto (fun n : ℕ => x ^ n / (n.factorial : K)) atTop (𝓝 0) := by
  -- The valuation balls `{z | v z < v y}` with `y ≠ 0` are a neighbourhood basis of `0`, so it
  -- suffices to push the term valuation past that of an arbitrary nonzero `y`.
  refine (IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff.mpr ?_
  intro γ hγ
  obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective γ
  have hy : y ≠ 0 := by simpa using hγ
  have hp : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hpz : (0 : ℤ) < (p - 1 : ℕ) := by exact_mod_cast hp
  -- Linear growth with slope `1 / (p - 1)` passes the valuation of `y` after this many terms.
  refine eventually_atTop.2
    ⟨(p - 1) * ((normalizedValuation K (Units.mk0 y hy)).toAdd.natAbs + 1), fun n hn => ?_⟩
  have hn0 : n ≠ 0 := ((Nat.mul_pos hp (Nat.succ_pos _)).trans_le hn).ne'
  have hfac : (n.factorial : K) ≠ 0 := by
    simpa only [map_natCast] using
      (map_ne_zero_iff (algebraMap ℚ_[p] K) (algebraMap ℚ_[p] K).injective).mpr
        (Nat.cast_ne_zero.mpr n.factorial_ne_zero : (n.factorial : ℚ_[p]) ≠ 0)
  have hdepth := lt_sub_one_mul_toAdd_normalizedValuation_expSeries_term hx hfac hn0 hxi hi
  have hvterm : (normalizedValuation K (Units.mk0 y hy)).toAdd <
      (normalizedValuation K
        (Units.mk0 (x ^ n / (n.factorial : K))
          (div_ne_zero (pow_ne_zero n hx) hfac))).toAdd := by
    have hN : ((p - 1 : ℕ) : ℤ) *
        (((normalizedValuation K (Units.mk0 y hy)).toAdd.natAbs + 1 : ℕ) : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast hn
    refine lt_of_mul_lt_mul_left ?_ hpz.le
    calc ((p - 1 : ℕ) : ℤ) * (normalizedValuation K (Units.mk0 y hy)).toAdd
        < ((p - 1 : ℕ) : ℤ) *
            (((normalizedValuation K (Units.mk0 y hy)).toAdd.natAbs + 1 : ℕ) : ℤ) :=
          Int.mul_lt_mul_of_pos_left
            (Int.le_natAbs.trans_lt (by exact_mod_cast Nat.lt_succ_self _)) hpz
      _ ≤ (n : ℤ) := hN
      _ < _ := hdepth
  -- Membership in the basic neighbourhood is exactly the valuation inequality.
  simp only [Set.mem_ofPred_eq]
  rw [lt_iff_not_ge]
  intro hval
  exact (not_le_of_gt hvterm)
    ((toAdd_normalizedValuation_le_iff_valuation_le
      (Units.mk0 (x ^ n / (n.factorial : K))
        (div_ne_zero (pow_ne_zero n hx) hfac))
      (Units.mk0 y hy)).mpr (by simpa using hval))

/-- The exponential series is summable for an element of `𝓂[K] ^ i` whenever
`e(K/ℚ_p) < (p - 1) * i`. -/
theorem summable_expSeries_of_mem_maximalIdeal_pow {i : ℕ}
    (x : (𝓂[K] ^ i : Ideal 𝒪[K]))
    (hi : absoluteRamificationIndex K p < (p - 1) * i) :
    Summable (fun n : ℕ => (x : K) ^ n / (n.factorial : K)) := by
  let _ : NonarchimedeanRing K := by
    rw [(valuation K).toTopologicalSpace_eq]
    exact ValuativeRel.nonarchimedeanRing K
  let _ := IsTopologicalAddGroup.rightUniformSpace K
  let _ := isUniformAddGroup_of_addCommGroup (G := K)
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]
  by_cases hx : (x : K) = 0
  · convert tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    simp [hx, Nat.ne_zero_of_lt hn]
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
    have hxval : valuation K (x : K) ≤ valuation K (π : K) ^ i :=
      (Set.ext_iff.mp (hπ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) i) x).mp x.2
    have hxi : (i : ℤ) ≤ (normalizedValuation K (Units.mk0 (x : K) hx)).toAdd :=
      (le_toAdd_normalizedValuation_iff_valuation_le_zpow
        (normalizedValuation_irreducible hπ) (i : ℤ) (Units.mk0 (x : K) hx)).mpr
        (by simpa only [Units.val_mk0, zpow_natCast] using hxval)
    exact tendsto_expSeries_term_zero_of_le_normalizedValuation hx hxi hi

/-- The exponential series of a deep element sums to Mathlib's exponential `NormedSpace.exp`. -/
theorem hasSum_exp_of_mem_maximalIdeal_pow {i : ℕ} (x : (𝓂[K] ^ i : Ideal 𝒪[K]))
    (hi : absoluteRamificationIndex K p < (p - 1) * i) :
    HasSum (fun n : ℕ => (x : K) ^ n / (n.factorial : K)) (NormedSpace.exp (x : K)) := by
  rw [NormedSpace.exp_eq_expSeries_sum ℚ_[p], NormedSpace.expSeries_sum_eq_div]
  exact (summable_expSeries_of_mem_maximalIdeal_pow x hi).hasSum

end TauCeti

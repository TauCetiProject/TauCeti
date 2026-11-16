/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.NumberTheory.Padics.Factorial

/-!
# The `p`-adic exponential on its disc of convergence

Using the `p`-adic factorial norm estimates from `TauCeti.NumberTheory.Padics.Factorial`, for any
nontrivially normed field `K` over `ℚ_[p]` and normed `K`-algebra `A`, `NormedSpace.expSeries K A`
has radius of convergence at least `ρ = p ^ (-1 / (p - 1))`
(`TauCeti.PadicExp.le_radius_expSeries_of_normedAlgebra`, `TauCeti.PadicExp.radius_expSeries_pos`),
so when `A` is complete `NormedSpace.exp` has the power series expansion `NormedSpace.expSeries K A`
on the open ball of radius `ρ` (`TauCeti.PadicExp.hasFPowerSeriesOnBall_exp`). Over any nontrivially
normed field `L` over `ℚ_[p]` (including infinite or non-locally-compact extensions such as
`ℂ_[p]`), `NormedSpace.expSeries L L` has exact radius `ρ`
(`TauCeti.PadicExp.radius_expSeries`, `TauCeti.PadicExp.le_radius_expSeries`).

When `L` is complete, `NormedSpace.exp` on the open disc `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`
satisfies the functional equation `exp (x + y) = exp x * exp y` (`TauCeti.PadicExp.exp_add`),
carries finite sums in the disc to products (`TauCeti.PadicExp.exp_sum`), satisfies the
second-order remainder estimate `‖exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * p ^ (1 / (p - 1))`
(`TauCeti.PadicExp.norm_exp_sub_one_sub_le`), preserves the distance to the origin via
`‖exp x - 1‖ = ‖x‖` (`TauCeti.PadicExp.norm_exp_sub_one`), takes unit values `‖exp x‖ = 1`
(`TauCeti.PadicExp.norm_exp`), is an isometry via `‖exp x - exp y‖ = ‖x - y‖`
(`TauCeti.PadicExp.norm_exp_sub_exp`), and is therefore injective (`TauCeti.PadicExp.injOn_exp`).

Outside the open disc (`p ^ (-1 / (p - 1)) ≤ ‖x‖`), the subsequence `n = p ^ k` keeps norm at least
`ρ`, so `∑ x ^ n / n!` diverges (`TauCeti.PadicExp.not_summable_pow_div_factorial_of_le_norm`) and
`NormedSpace.exp x = 0` (`TauCeti.PadicExp.exp_eq_zero_of_le_norm`, in particular
`NormedSpace.exp (1 : L) = 0` in `TauCeti.PadicExp.exp_one_eq_zero`, and divergence at `x = 2` for
`p = 2` in `TauCeti.PadicExp.not_summable_two_pow_div_factorial`). For odd primes `p ≠ 2`, by
contrast, `‖p‖ = p ^ (-1) < p ^ (-1 / (p - 1))` lies strictly inside the disc
(`TauCeti.PadicExp.norm_natCast_prime_lt`).

## Main results

* `TauCeti.PadicExp.le_radius_expSeries_of_normedAlgebra`, `TauCeti.PadicExp.le_radius_expSeries`,
  `TauCeti.PadicExp.radius_expSeries`, `TauCeti.PadicExp.radius_expSeries_pos`,
  `TauCeti.PadicExp.hasFPowerSeriesOnBall_exp`: radius of convergence and power-series expansion of
  `NormedSpace.expSeries K A` (exact radius `ENNReal.ofReal (p ^ (-(p - 1)⁻¹))` for `L L`).
* `TauCeti.PadicExp.exp_add`, `TauCeti.PadicExp.exp_neg`, `TauCeti.PadicExp.exp_sub`,
  `TauCeti.PadicExp.exp_nsmul`, `TauCeti.PadicExp.exp_zsmul`, `TauCeti.PadicExp.exp_sum`:
  homomorphism properties of `NormedSpace.exp` on `{x : L | ‖x‖ < p ^ (-(p - 1)⁻¹)}`.
* `TauCeti.PadicExp.norm_exp_sub_one_sub_le`, `TauCeti.PadicExp.norm_exp_sub_one`,
  `TauCeti.PadicExp.norm_exp`, `TauCeti.PadicExp.norm_exp_sub_exp`, `TauCeti.PadicExp.injOn_exp`:
  metric and injectivity properties on the disc of convergence.
* `TauCeti.PadicExp.norm_natCast_prime_lt`,
  `TauCeti.PadicExp.not_summable_pow_div_factorial_of_le_norm`,
  `TauCeti.PadicExp.exp_eq_zero_of_le_norm`, `TauCeti.PadicExp.exp_one_eq_zero`,
  `TauCeti.PadicExp.not_summable_two_pow_div_factorial`: `p` lies in the open disc for `p ≠ 2`,
  while the series diverges (so `NormedSpace.exp` vanishes) whenever `p ^ (-(p - 1)⁻¹) ≤ ‖x‖`.

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press (1975), Chapter 2.
* A. Brumer, *On the units of algebraic number fields*, Mathematika **14** (1967), 121–124.
* A. M. Robert, *A Course in p-adic Analysis*, Springer GTM **198** (2000), §5.4.
* M. Karatarakis, `Exp.lean` in `mkaratarakis/mathlib4`, commit
  `65cdef5722194f07709ab40ff46eede531f52f5d`, `Mathlib/NumberTheory/Transcendental/Baker/Padic/`.
-/

public section

open scoped Nat NNReal Topology

namespace TauCeti.PadicExp

section Radius

variable {p : ℕ} [hp : Fact p.Prime]

/-- In a normed algebra `A` over a nontrivially normed `ℚ_[p]`-algebra field `K`, the weighted
terms of `NormedSpace.expSeries K A` at radius `r ≤ p ^ (-1 / (p - 1))` are bounded by
`max 1 ‖(1 : A)‖`. -/
theorem norm_expSeries_mul_pow_le {K A : Type*} [NontriviallyNormedField K] [NormedAlgebra ℚ_[p] K]
    [NormedRing A] [NormedAlgebra K A] {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (n : ℕ) :
    ‖NormedSpace.expSeries K A n‖ * r ^ n ≤ max 1 ‖(1 : A)‖ := by
  rw [NormedSpace.expSeries_eq_ofScalars, FormalMultilinearSeries.ofScalars_norm_eq_mul,
    mul_right_comm]
  calc
    ‖(n !⁻¹ : K)‖ * r ^ n * ‖ContinuousMultilinearMap.mkPiAlgebraFin K n A‖
        ≤ 1 * max 1 ‖(1 : A)‖ :=
          mul_le_mul (norm_inv_factorial_mul_pow_le hr0 hr n)
            ContinuousMultilinearMap.norm_mkPiAlgebraFin_le
            (ContinuousMultilinearMap.opNorm_nonneg _) zero_le_one
    _ = max 1 ‖(1 : A)‖ := one_mul _

/-- For any nontrivially normed field `K` over `ℚ_[p]` and normed `K`-algebra `A`, the exponential
series `NormedSpace.expSeries K A` has radius of convergence at least `p ^ (-1 / (p - 1))`. -/
theorem le_radius_expSeries_of_normedAlgebra {K A : Type*} [NontriviallyNormedField K]
    [NormedAlgebra ℚ_[p] K] [NormedRing A] [NormedAlgebra K A] :
    ENNReal.ofReal ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ≤ (NormedSpace.expSeries K A).radius := by
  have hpos : 0 ≤ (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
    Real.rpow_nonneg (Nat.cast_nonneg p) _
  rw [ENNReal.ofReal_eq_coe_nnreal hpos]
  exact (NormedSpace.expSeries K A).le_radius_of_bound (max 1 ‖(1 : A)‖) fun n ↦
    norm_expSeries_mul_pow_le hpos le_rfl n

/-- **Radius lower bound for the `p`-adic exponential series.** In a nontrivially normed field `L`
over `ℚ_[p]`, `NormedSpace.expSeries L L` has radius of convergence at least
`p ^ (-1 / (p - 1))`. -/
theorem le_radius_expSeries {L : Type*} [NontriviallyNormedField L] [NormedAlgebra ℚ_[p] L] :
    ENNReal.ofReal ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) ≤ (NormedSpace.expSeries L L).radius :=
  le_radius_expSeries_of_normedAlgebra

/-- When `‖(1 : A)‖ = 1`, the radius of `NormedSpace.expSeries K A` is at most
`p ^ (-1 / (p - 1))`, because the terms of degree `p ^ k` have operator norm
`p ^ ((p ^ k - 1) / (p - 1))`. -/
theorem radius_expSeries_le_of_normOneClass {K A : Type*} [NontriviallyNormedField K]
    [NormedAlgebra ℚ_[p] K] [NormedRing A] [NormOneClass A] [NormedAlgebra K A] :
    (NormedSpace.expSeries K A).radius ≤ ENNReal.ofReal ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) := by
  by_contra! hlt
  obtain ⟨r, hρr, hr_rad⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  have hρ_pos : 0 < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
  have hρr' : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) < (r : ℝ) := by
    simpa using (ENNReal.ofReal_lt_iff_lt_toReal hρ_pos.le ENNReal.coe_ne_top).mp hρr
  have hsum := (NormedSpace.expSeries K A).summable_norm_mul_pow hr_rad
  have ht : Filter.Tendsto
      (fun k : ℕ ↦ ‖NormedSpace.expSeries K A (p ^ k)‖ * (r : ℝ) ^ (p ^ k))
      Filter.atTop (𝓝 0) :=
    hsum.tendsto_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hp.out.one_lt)
  have hge : ∀ k : ℕ, (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤
      ‖NormedSpace.expSeries K A (p ^ k)‖ * (r : ℝ) ^ (p ^ k) := fun k ↦ by
    rw [NormedSpace.expSeries_eq_ofScalars, FormalMultilinearSeries.ofScalars_norm_eq_mul,
      ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one]
    exact le_norm_inv_factorial_pow_prime_mul_pow hρr'.le k
  exact not_le_of_gt hρ_pos (ge_of_tendsto' ht hge)

/-- **Exact radius of the `p`-adic exponential series.** In any nontrivially normed field `L` over
`ℚ_[p]`, `(NormedSpace.expSeries L L).radius = ENNReal.ofReal (p ^ (-1 / (p - 1)))`. -/
theorem radius_expSeries {L : Type*} [NontriviallyNormedField L] [NormedAlgebra ℚ_[p] L] :
    (NormedSpace.expSeries L L).radius = ENNReal.ofReal ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :=
  le_antisymm radius_expSeries_le_of_normOneClass le_radius_expSeries

/-- The exponential series on a normed algebra over a nontrivially normed `ℚ_[p]`-algebra field
has positive radius of convergence. -/
theorem radius_expSeries_pos (p : ℕ) [hp : Fact p.Prime] {K A : Type*}
    [NontriviallyNormedField K] [NormedAlgebra ℚ_[p] K] [NormedRing A] [NormedAlgebra K A] :
    0 < (NormedSpace.expSeries K A).radius :=
  (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _)).trans_le
    (le_radius_expSeries_of_normedAlgebra (p := p))

/-- Any element of norm `< p ^ (-1 / (p - 1))` lies in the `eball` of convergence of
`NormedSpace.expSeries K A`. -/
theorem mem_eball_expSeries_of_norm_lt {K A : Type*} [NontriviallyNormedField K]
    [NormedAlgebra ℚ_[p] K] [NormedRing A] [NormedAlgebra K A] {x : A}
    (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    x ∈ Metric.eball (0 : A) (NormedSpace.expSeries K A).radius := by
  rw [Metric.mem_eball, edist_dist, dist_zero_right]
  exact (ENNReal.ofReal_lt_ofReal_iff
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _)).mpr hx |>.trans_le
    le_radius_expSeries_of_normedAlgebra

/-- In a complete normed algebra `A` over a nontrivially normed `ℚ_[p]`-algebra field `K`,
`NormedSpace.exp` has the power series expansion `NormedSpace.expSeries K A` on the open ball of
radius `p ^ (-1 / (p - 1))`. -/
theorem hasFPowerSeriesOnBall_exp {K A : Type*} [NontriviallyNormedField K]
    [NormedAlgebra ℚ_[p] K] [NormedRing A] [NormedAlgebra K A] [CompleteSpace A] :
    HasFPowerSeriesOnBall NormedSpace.exp (NormedSpace.expSeries K A) 0
      (ENNReal.ofReal ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))) := by
  have : CharZero K := charZero_of_inj_zero fun n hn ↦
    Nat.cast_eq_zero.mp ((algebraMap ℚ_[p] K).injective (by rw [map_natCast, map_zero]; exact hn))
  exact (NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos (𝕂 := K) (𝔸 := A)
    (radius_expSeries_pos p)).mono
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _))
    le_radius_expSeries_of_normedAlgebra

end Radius

section Disc

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
  [CompleteSpace L]

omit [CompleteSpace L] in
/-- For `‖x‖ < p ^ (-1 / (p - 1))`, the norms `‖x ^ n / n!‖` are summable. -/
theorem summable_norm_pow_div_factorial {x : L}
    (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    Summable fun n : ℕ ↦ ‖x ^ n / (n ! : L)‖ :=
  NormedSpace.norm_expSeries_div_summable_of_mem_ball ℚ_[p] x
    (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hx)

/-- On the open disc `‖x‖ < p ^ (-1 / (p - 1))`, `∑ x ^ n / n!` converges to
`NormedSpace.exp x`. -/
theorem hasSum_exp {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    HasSum (fun n : ℕ ↦ x ^ n / (n ! : L)) (NormedSpace.exp x) :=
  NormedSpace.expSeries_div_hasSum_exp_of_mem_ball ℚ_[p] x
    (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hx)

/-- **Functional equation of the `p`-adic exponential** on its open disc of convergence. -/
theorem exp_add {x y : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hy : ‖y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y :=
  NormedSpace.exp_add_of_mem_ball
    (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hx)
    (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hy)

/-- On the open disc of convergence, `exp (-x) = (exp x)⁻¹`. -/
theorem exp_neg {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp (-x) = (NormedSpace.exp x)⁻¹ :=
  NormedSpace.exp_neg_of_mem_ball ℚ_[p] (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hx)

/-- On the open disc of convergence, `exp (x - y) = exp x / exp y`. -/
theorem exp_sub {x y : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hy : ‖y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp (x - y) = NormedSpace.exp x / NormedSpace.exp y := by
  have hny : ‖-y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by simpa using hy
  rw [sub_eq_add_neg, exp_add hx hny, exp_neg hy, div_eq_mul_inv]

/-- Because the open disc `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}` is an additive subgroup in an
ultrametric field, `exp (n • x) = exp x ^ n` for every `n : ℕ` whenever `x` lies in the disc. -/
theorem exp_nsmul {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (n : ℕ) :
    NormedSpace.exp (n • x) = NormedSpace.exp x ^ n := by
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[p]
  induction n with
  | zero => simp
  | succ n ih =>
    have hnx : ‖n • x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
      (IsUltrametricDist.norm_nsmul_le x n).trans_lt hx
    rw [succ_nsmul, exp_add hnx hx, ih, pow_succ]

theorem exp_natCast_mul {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (n : ℕ) :
    NormedSpace.exp ((n : L) * x) = NormedSpace.exp x ^ n := by
  rw [← nsmul_eq_mul, exp_nsmul hx]

/-- On the open disc of convergence, `exp (z • x) = exp x ^ z` for every integer `z : ℤ`. -/
theorem exp_zsmul {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (z : ℤ) :
    NormedSpace.exp (z • x) = NormedSpace.exp x ^ z := by
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[p]
  cases z with
  | ofNat n => simpa using exp_nsmul hx n
  | negSucc n =>
    have hnx : ‖(n + 1) • x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
      (IsUltrametricDist.norm_nsmul_le x (n + 1)).trans_lt hx
    rw [negSucc_zsmul, exp_neg hnx, exp_nsmul hx, zpow_negSucc]

theorem exp_intCast_mul {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (z : ℤ) :
    NormedSpace.exp ((z : L) * x) = NormedSpace.exp x ^ z := by
  rw [← zsmul_eq_mul, exp_zsmul hx]

/-- The exponential of a finite sum of elements in `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}` is the
product of their exponentials. -/
theorem exp_sum {ι : Type*} (s : Finset ι) {f : ι → L}
    (hf : ∀ i ∈ s, ‖f i‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp (∑ i ∈ s, f i) = ∏ i ∈ s, NormedSpace.exp (f i) := by
  classical
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[p]
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ha_lt : ‖f a‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := hf a (Finset.mem_insert_self a s)
    have hs_lt : ∀ i ∈ s, ‖f i‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
      fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have hsum_lt : ‖∑ i ∈ s, f i‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
      rcases s.eq_empty_or_nonempty with rfl | hne
      · simpa using Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
      · obtain ⟨j, hj, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne f
        exact hle.trans_lt (hs_lt j hj)
    rw [Finset.sum_insert ha, Finset.prod_insert ha, exp_add ha_lt hsum_lt, ih hs_lt]

/-- Second-order ultrametric remainder bound on the open disc:
`‖exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * p ^ (1 / (p - 1))`. -/
theorem norm_exp_sub_one_sub_le {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) := by
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[p]
  have h2 := hasSum_exp hx
  rw [← hasSum_nat_add_iff' 2] at h2
  have hrange : ∑ i ∈ Finset.range 2, x ^ i / (i ! : L) = 1 + x := by
    simp [Finset.sum_range_succ]
  rw [hrange, sub_add_eq_sub_sub] at h2
  rw [← h2.tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun k ↦ ?_
  simpa only [div_eq_mul_inv] using
    norm_pow_mul_inv_factorial_le_sq (p := p) hx.le (Nat.le_add_left 2 k)

/-- **Isometry to the origin on the disc of convergence**: for `‖x‖ < p ^ (-1 / (p - 1))`,
`‖exp x - 1‖ = ‖x‖`. -/
theorem norm_exp_sub_one {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖NormedSpace.exp x - 1‖ = ‖x‖ := by
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[p]
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
  have hprod : ‖x‖ * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) < 1 := by
    calc
      ‖x‖ * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹)
          < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) :=
            mul_lt_mul_of_pos_right hx (Real.rpow_pos_of_pos hp0 _)
      _ = 1 := by rw [← Real.rpow_add hp0, neg_add_cancel, Real.rpow_zero]
  have hrem : ‖NormedSpace.exp x - 1 - x‖ < ‖x‖ := by
    calc
      ‖NormedSpace.exp x - 1 - x‖
          ≤ ‖x‖ ^ 2 * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) := norm_exp_sub_one_sub_le hx
      _ = ‖x‖ * (‖x‖ * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹)) := by ring
      _ < ‖x‖ * 1 := mul_lt_mul_of_pos_left hprod (norm_pos_iff.mpr hx0)
      _ = ‖x‖ := mul_one _
  have hdecomp : NormedSpace.exp x - 1 = x + (NormedSpace.exp x - 1 - x) := by ring
  rw [hdecomp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hrem.ne', max_eq_left hrem.le]

/-- Every element in the open disc of convergence has exponential of norm `1`. -/
theorem norm_exp {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖NormedSpace.exp x‖ = 1 := by
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[p]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hlt1 : ‖NormedSpace.exp x - 1‖ < ‖(1 : L)‖ := by
    rw [norm_exp_sub_one hx, norm_one]
    exact hx.trans_le (Real.rpow_le_one_of_one_le_of_nonpos hp1.le
      (neg_nonpos.mpr (inv_nonneg.mpr (sub_nonneg.mpr hp1.le))))
  have hdecomp : NormedSpace.exp x = 1 + (NormedSpace.exp x - 1) := by ring
  rw [hdecomp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt1.ne', max_eq_left hlt1.le,
    norm_one]

/-- On the open disc of convergence, `NormedSpace.exp x ≠ 0`. -/
theorem exp_ne_zero {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp x ≠ 0 := by
  intro h
  have h1 := norm_exp hx
  simp [h] at h1

/-- **Isometry property of `NormedSpace.exp`** on `{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`:
`‖exp x - exp y‖ = ‖x - y‖`. -/
theorem norm_exp_sub_exp {x y : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hy : ‖y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖NormedSpace.exp x - NormedSpace.exp y‖ = ‖x - y‖ := by
  have : IsUltrametricDist L := .of_normedAlgebra ℚ_[p]
  have hsub : ‖x - y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    have hle : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
      simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max x (-y)
    exact hle.trans_lt (max_lt hx hy)
  have hfactor : NormedSpace.exp x - NormedSpace.exp y =
      NormedSpace.exp y * (NormedSpace.exp (x - y) - 1) := by
    rw [mul_sub, mul_one, ← exp_add hy hsub, add_sub_cancel]
  simp [hfactor, norm_exp hy, norm_exp_sub_one hsub]

/-- On the open disc of convergence, `exp x = 1` if and only if `x = 0`. -/
theorem exp_eq_one_iff {x : L} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp x = 1 ↔ x = 0 := by
  rw [← sub_eq_zero, ← norm_eq_zero, norm_exp_sub_one hx, norm_eq_zero]

/-- **Injectivity of `NormedSpace.exp`** on its open disc of convergence
`{x : L | ‖x‖ < p ^ (-1 / (p - 1))}`. -/
theorem injOn_exp :
    Set.InjOn (NormedSpace.exp : L → L) {x | ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)} := by
  intro x hx y hy hxy
  rw [← sub_eq_zero, ← norm_eq_zero, ← norm_exp_sub_exp hx hy, hxy]
  simp

omit [CompleteSpace L] in
/-- For every odd prime `p ≠ 2`, `(p : L)` has norm `p⁻¹ < p ^ (-1 / (p - 1))` and therefore lies
strictly inside the disc of convergence of `NormedSpace.exp`. -/
theorem norm_natCast_prime_lt (hp2 : p ≠ 2) :
    ‖(p : L)‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
  have hp_gt2 : 2 < p := hp.out.two_le.lt_of_ne' hp2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hsub1 : (1 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp_gt2
    linarith
  rw [TauCeti.norm_natCast_eq_norm_padic (p := p) p, Padic.norm_p, ← Real.rpow_neg_one]
  exact Real.rpow_lt_rpow_of_exponent_lt hp1 (neg_lt_neg (inv_lt_one_of_one_lt₀ hsub1))

/-- For every odd prime `p ≠ 2`, `‖exp p - 1‖ = p⁻¹` in any complete normed field over `ℚ_[p]`. -/
theorem norm_exp_natCast_prime_sub_one (hp2 : p ≠ 2) :
    ‖NormedSpace.exp (p : L) - 1‖ = (p : ℝ)⁻¹ := by
  rw [norm_exp_sub_one (norm_natCast_prime_lt hp2), TauCeti.norm_natCast_eq_norm_padic (p := p) p,
    Padic.norm_p]

end Disc

section Divergence

/-- Whenever `p ^ (-1 / (p - 1)) ≤ ‖x‖` in a normed division algebra `D` over `ℚ_[p]`, the
exponential series `∑ x ^ n / n!` diverges, because the terms of degree `p ^ k` have norm at least
`p ^ (-1 / (p - 1))`. -/
theorem not_summable_pow_div_factorial_of_le_norm {p : ℕ} [hp : Fact p.Prime] {D : Type*}
    [NormedDivisionRing D] [NormedAlgebra ℚ_[p] D] {x : D}
    (hx : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ ‖x‖) :
    ¬ Summable fun n : ℕ ↦ x ^ n / (n ! : D) := by
  intro h
  have hρ_pos : 0 < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
  have ht : Filter.Tendsto (fun k : ℕ ↦ ‖x ^ (p ^ k) / (((p ^ k)! : ℕ) : D)‖)
      Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, norm_zero] using
      h.tendsto_atTop_zero.norm.comp (tendsto_pow_atTop_atTop_of_one_lt hp.out.one_lt)
  have hge : ∀ k : ℕ, (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤
      ‖x ^ (p ^ k) / (((p ^ k)! : ℕ) : D)‖ := fun k ↦ by
    rw [div_eq_mul_inv, norm_mul, norm_pow, mul_comm]
    exact le_norm_inv_factorial_pow_prime_mul_pow hx k
  exact not_le_of_gt hρ_pos (ge_of_tendsto' ht hge)

/-- Outside the open disc (`p ^ (-1 / (p - 1)) ≤ ‖x‖`), `NormedSpace.exp x = 0` by `tsum`
junk-value convention, since the defining series diverges. -/
theorem exp_eq_zero_of_le_norm {p : ℕ} [hp : Fact p.Prime] {D : Type*}
    [NormedDivisionRing D] [NormedAlgebra ℚ_[p] D] {x : D}
    (hx : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ ‖x‖) :
    NormedSpace.exp x = 0 := by
  have : CharZero D := charZero_of_inj_zero fun n hn ↦
    Nat.cast_eq_zero.mp ((algebraMap ℚ_[p] D).injective (by rw [map_natCast, map_zero]; exact hn))
  rw [NormedSpace.exp_eq_tsum_div]
  exact tsum_eq_zero_of_not_summable (not_summable_pow_div_factorial_of_le_norm hx)

/-- In any normed division algebra `D` over `ℚ_[p]`, `NormedSpace.exp (1 : D) = 0`, since
`‖(1 : D)‖ = 1 ≥ p ^ (-1 / (p - 1))` lies outside the open disc of convergence. -/
theorem exp_one_eq_zero (p : ℕ) [hp : Fact p.Prime] {D : Type*} [NormedDivisionRing D]
    [NormedAlgebra ℚ_[p] D] : NormedSpace.exp (1 : D) = 0 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  refine exp_eq_zero_of_le_norm (p := p) ?_
  rw [norm_one]
  exact Real.rpow_le_one_of_one_le_of_nonpos hp1
    (neg_nonpos.mpr (inv_nonneg.mpr (sub_nonneg.mpr hp1)))

/-- At `p = 2`, the boundary point `x = 2` has `‖(2 : L)‖ = 1 / 2 = 2 ^ (-1 / (2 - 1))`, so the
exponential series `∑ 2 ^ n / n!` diverges. -/
theorem not_summable_two_pow_div_factorial {L : Type*} [NormedField L] [NormedAlgebra ℚ_[2] L] :
    ¬ Summable fun n : ℕ ↦ (2 : L) ^ n / (n ! : L) := by
  refine not_summable_pow_div_factorial_of_le_norm (p := 2) ?_
  rw [← Nat.cast_two (R := L), TauCeti.norm_natCast_eq_norm_padic (p := 2) 2, Padic.norm_p]
  norm_num

end Divergence

end TauCeti.PadicExp

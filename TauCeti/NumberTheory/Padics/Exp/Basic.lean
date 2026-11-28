/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.NumberTheory.Padics.AmiceRadius
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.NumberTheory.Padics.Factorial

/-!
# Exact radius, isometry, and divergence of the `p`-adic exponential

Using the `p`-adic factorial norm estimates from `TauCeti.NumberTheory.Padics.Factorial`, for any
nontrivially normed field `K` over `ℚ_[p]` and normed `K`-algebra `A`, `NormedSpace.expSeries K A`
has radius of convergence at least `amiceRadius p 0 = p ^ (-1 / (p - 1))`
(`TauCeti.PadicExp.le_radius_expSeries_of_normedAlgebra`, `TauCeti.PadicExp.radius_expSeries_pos`),
and exact radius `amiceRadius p 0` whenever `‖(1 : A)‖ = 1`
(`TauCeti.PadicExp.radius_expSeries_of_normOneClass`), so when `A` is complete `NormedSpace.exp`
has the power series expansion `NormedSpace.expSeries K A` on the open ball of radius
`amiceRadius p 0` (`TauCeti.PadicExp.hasFPowerSeriesOnBall_exp`). See also
`TauCeti.NumberTheory.Padics.Exp.Disc` for the functional equation, `TauCeti.norm_exp_of_norm_lt`,
`TauCeti.norm_log_of_norm_sub_one_lt`, and the logarithm identities on
`{x | ‖x‖ < amiceRadius p 0}`.

On the open disc `{x | ‖x‖ < amiceRadius p 0}`:
* In any complete normed division algebra `D` over `ℚ_[p]`, `exp (x - y) = exp x / exp y` for
  commuting `x` and `y` (`TauCeti.PadicExp.exp_sub_of_commute`); over a complete normed field `L`
  over `ℚ_[p]`, `exp (x - y) = exp x / exp y` (`TauCeti.PadicExp.exp_sub`).
* In any complete ultrametric normed `ℚ_[p]`-algebra `A`, `NormedSpace.exp` satisfies the
  second-order remainder estimate `‖exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * p ^ (1 / (p - 1))`
  (`TauCeti.PadicExp.norm_exp_sub_one_sub_le`), is an isometry via `‖exp x - exp y‖ = ‖x - y‖`
  (`TauCeti.PadicExp.norm_exp_sub_exp`) and `‖exp x - 1‖ = ‖x‖`
  (`TauCeti.PadicExp.norm_exp_sub_one_of_norm_lt`), satisfies `exp x = 1 ↔ x = 0`
  (`TauCeti.PadicExp.exp_eq_one_iff`), and satisfies `‖exp (p : A) - 1‖ = p⁻¹` for odd `p`
  (`TauCeti.PadicExp.norm_exp_natCast_prime_sub_one`).

Outside the open disc (`amiceRadius p 0 ≤ ‖x‖`) in a normed division algebra `D` over `ℚ_[p]`,
the subsequence `n = p ^ k` keeps norm at least `amiceRadius p 0`, so `∑ x ^ n / n!` diverges
(`TauCeti.PadicExp.not_summable_pow_div_factorial_of_le_norm`) and `NormedSpace.exp x = 0`
(`TauCeti.PadicExp.exp_eq_zero_of_le_norm`, in particular `NormedSpace.exp (1 : D) = 0` in
`TauCeti.PadicExp.exp_one_eq_zero`, and divergence at `x = 2` for `p = 2` in
`TauCeti.PadicExp.not_summable_two_pow_div_factorial`). For odd primes `p ≠ 2`, by contrast,
`‖p‖ = p ^ (-1) < amiceRadius p 0` lies strictly inside the disc in any seminormed
`ℚ_[p]`-algebra with `‖1‖ = 1` (`TauCeti.PadicExp.norm_natCast_prime_lt`).

## Main results

* `TauCeti.PadicExp.le_radius_expSeries_of_normedAlgebra`,
  `TauCeti.PadicExp.radius_expSeries_of_normOneClass`,
  `TauCeti.PadicExp.radius_expSeries_pos`, `TauCeti.PadicExp.hasFPowerSeriesOnBall_exp`: radius of
  convergence and power-series expansion of `NormedSpace.expSeries K A` (exact radius
  `ENNReal.ofReal (amiceRadius p 0)` whenever `NormOneClass A`).
* `TauCeti.PadicExp.exp_sub_of_commute`, `TauCeti.PadicExp.exp_sub`: quotient identity on
  `{x | ‖x‖ < amiceRadius p 0}`.
* `TauCeti.PadicExp.norm_exp_sub_one_sub_le`, `TauCeti.PadicExp.norm_exp_sub_exp`,
  `TauCeti.PadicExp.norm_exp_sub_one_of_norm_lt`, `TauCeti.PadicExp.exp_eq_one_iff`,
  `TauCeti.PadicExp.norm_exp_natCast_prime_sub_one`:
  quadratic remainder and full isometry properties on the disc of convergence.
* `TauCeti.PadicExp.norm_natCast_prime_lt`,
  `TauCeti.PadicExp.not_summable_pow_div_factorial_of_le_norm`,
  `TauCeti.PadicExp.exp_eq_zero_of_le_norm`, `TauCeti.PadicExp.exp_one_eq_zero`,
  `TauCeti.PadicExp.not_summable_two_pow_div_factorial`: `p` lies in the open disc for `p ≠ 2`,
  while the series diverges (so `NormedSpace.exp` vanishes) whenever `amiceRadius p 0 ≤ ‖x‖`.

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
terms of `NormedSpace.expSeries K A` at radius `r ≤ amiceRadius p 0` are bounded by
`max 1 ‖(1 : A)‖`. -/
theorem norm_expSeries_mul_pow_le {K A : Type*} [NontriviallyNormedField K] [NormedAlgebra ℚ_[p] K]
    [NormedRing A] [NormedAlgebra K A] {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ amiceRadius p 0) (n : ℕ) :
    ‖NormedSpace.expSeries K A n‖ * r ^ n ≤ max 1 ‖(1 : A)‖ := by
  rw [NormedSpace.expSeries_eq_ofScalars, FormalMultilinearSeries.ofScalars_norm_eq_mul,
    mul_right_comm]
  calc
    ‖(n !⁻¹ : K)‖ * r ^ n * ‖ContinuousMultilinearMap.mkPiAlgebraFin K n A‖
        ≤ 1 * max 1 ‖(1 : A)‖ :=
          mul_le_mul (norm_inv_factorial_mul_pow_le hr0 (hr.trans_eq (amiceRadius_zero p)) n)
            ContinuousMultilinearMap.norm_mkPiAlgebraFin_le
            (ContinuousMultilinearMap.opNorm_nonneg _) zero_le_one
    _ = max 1 ‖(1 : A)‖ := one_mul _

/-- For any nontrivially normed field `K` over `ℚ_[p]` and normed `K`-algebra `A`, the exponential
series `NormedSpace.expSeries K A` has radius of convergence at least `amiceRadius p 0`. -/
theorem le_radius_expSeries_of_normedAlgebra {K A : Type*} [NontriviallyNormedField K]
    [NormedAlgebra ℚ_[p] K] [NormedRing A] [NormedAlgebra K A] :
    ENNReal.ofReal (amiceRadius p 0) ≤ (NormedSpace.expSeries K A).radius := by
  have hpos : 0 ≤ amiceRadius p 0 := (amiceRadius_pos (p := p) 0).le
  rw [ENNReal.ofReal_eq_coe_nnreal hpos]
  exact (NormedSpace.expSeries K A).le_radius_of_bound (max 1 ‖(1 : A)‖) fun n ↦
    norm_expSeries_mul_pow_le hpos le_rfl n

/-- When `‖(1 : A)‖ = 1`, the radius of `NormedSpace.expSeries K A` is at most
`amiceRadius p 0`, because the terms of degree `p ^ k` have operator norm
`p ^ ((p ^ k - 1) / (p - 1))`. -/
theorem radius_expSeries_le_of_normOneClass {K A : Type*} [NontriviallyNormedField K]
    [NormedAlgebra ℚ_[p] K] [NormedRing A] [NormOneClass A] [NormedAlgebra K A] :
    (NormedSpace.expSeries K A).radius ≤ ENNReal.ofReal (amiceRadius p 0) := by
  by_contra! hlt
  obtain ⟨r, hρr, hr_rad⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  have hρ_pos : 0 < amiceRadius p 0 := amiceRadius_pos 0
  have hρr' : amiceRadius p 0 < (r : ℝ) := by
    simpa using (ENNReal.ofReal_lt_iff_lt_toReal hρ_pos.le ENNReal.coe_ne_top).mp hρr
  have hsum := (NormedSpace.expSeries K A).summable_norm_mul_pow hr_rad
  have ht : Filter.Tendsto
      (fun k : ℕ ↦ ‖NormedSpace.expSeries K A (p ^ k)‖ * (r : ℝ) ^ (p ^ k))
      Filter.atTop (𝓝 0) :=
    hsum.tendsto_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hp.out.one_lt)
  have hge : ∀ k : ℕ, amiceRadius p 0 ≤
      ‖NormedSpace.expSeries K A (p ^ k)‖ * (r : ℝ) ^ (p ^ k) := fun k ↦ by
    rw [NormedSpace.expSeries_eq_ofScalars, FormalMultilinearSeries.ofScalars_norm_eq_mul,
      ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one, amiceRadius_zero]
    exact le_norm_inv_factorial_pow_prime_mul_pow ((amiceRadius_zero p).symm.trans_le hρr'.le) k
  exact not_le_of_gt hρ_pos (ge_of_tendsto' ht hge)

/-- **Exact radius of the `p`-adic exponential series in a normed algebra.** For any nontrivially
normed field `K` over `ℚ_[p]` and normed `K`-algebra `A` with `‖(1 : A)‖ = 1`,
`(NormedSpace.expSeries K A).radius = ENNReal.ofReal (amiceRadius p 0)`. -/
theorem radius_expSeries_of_normOneClass {K A : Type*} [NontriviallyNormedField K]
    [NormedAlgebra ℚ_[p] K] [NormedRing A] [NormOneClass A] [NormedAlgebra K A] :
    (NormedSpace.expSeries K A).radius = ENNReal.ofReal (amiceRadius p 0) :=
  le_antisymm radius_expSeries_le_of_normOneClass le_radius_expSeries_of_normedAlgebra

/-- The exponential series on a normed algebra over a nontrivially normed `ℚ_[p]`-algebra field
has positive radius of convergence. -/
theorem radius_expSeries_pos (p : ℕ) [Fact p.Prime] {K A : Type*}
    [NontriviallyNormedField K] [NormedAlgebra ℚ_[p] K] [NormedRing A] [NormedAlgebra K A] :
    0 < (NormedSpace.expSeries K A).radius :=
  (ENNReal.ofReal_pos.mpr (amiceRadius_pos 0)).trans_le
    (le_radius_expSeries_of_normedAlgebra (p := p))

/-- Any element of norm `< amiceRadius p 0` lies in the `eball` of convergence of
`NormedSpace.expSeries K A`. -/
theorem mem_eball_expSeries_of_norm_lt {K A : Type*} [NontriviallyNormedField K]
    [NormedAlgebra ℚ_[p] K] [NormedRing A] [NormedAlgebra K A] {x : A}
    (hx : ‖x‖ < amiceRadius p 0) :
    x ∈ Metric.eball (0 : A) (NormedSpace.expSeries K A).radius := by
  rw [Metric.mem_eball, edist_dist, dist_zero_right]
  exact ((ENNReal.ofReal_lt_ofReal_iff (amiceRadius_pos 0)).mpr hx).trans_le
    le_radius_expSeries_of_normedAlgebra

/-- In a complete normed algebra `A` over a nontrivially normed `ℚ_[p]`-algebra field `K`,
`NormedSpace.exp` has the power series expansion `NormedSpace.expSeries K A` on the open ball of
radius `amiceRadius p 0`. -/
theorem hasFPowerSeriesOnBall_exp {K A : Type*} [NontriviallyNormedField K]
    [NormedAlgebra ℚ_[p] K] [NormedRing A] [NormedAlgebra K A] [CompleteSpace A] :
    HasFPowerSeriesOnBall NormedSpace.exp (NormedSpace.expSeries K A) 0
      (ENNReal.ofReal (amiceRadius p 0)) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  exact (NormedSpace.hasFPowerSeriesOnBall_exp_of_radius_pos (𝕂 := K) (𝔸 := A)
    (radius_expSeries_pos p)).mono
    (ENNReal.ofReal_pos.mpr (amiceRadius_pos 0))
    le_radius_expSeries_of_normedAlgebra

end Radius

section Disc

variable {p : ℕ} [hp : Fact p.Prime]

/-- For every odd prime `p ≠ 2`, `(p : A)` has norm `p⁻¹ < amiceRadius p 0` and therefore lies
strictly inside the disc of convergence of `NormedSpace.exp`. -/
theorem norm_natCast_prime_lt {A : Type*} [SeminormedRing A] [NormOneClass A]
    [NormedAlgebra ℚ_[p] A] (hp2 : p ≠ 2) :
    ‖(p : A)‖ < amiceRadius p 0 := by
  rw [TauCeti.norm_natCast_p]
  exact inv_lt_amiceRadius_zero_iff.mpr hp2

section DivisionAlgebra

variable {D : Type*} [NormedDivisionRing D] [NormedAlgebra ℚ_[p] D]

/-- On the open disc of convergence in a complete normed division algebra over `ℚ_[p]`,
`exp (x - y) = exp x / exp y` for commuting elements `x` and `y`. -/
theorem exp_sub_of_commute [CompleteSpace D] {x y : D} (hxy : Commute x y)
    (hx : ‖x‖ < amiceRadius p 0) (hy : ‖y‖ < amiceRadius p 0) :
    NormedSpace.exp (x - y) = NormedSpace.exp x / NormedSpace.exp y := by
  have hny : ‖-y‖ < amiceRadius p 0 := by simpa using hy
  rw [sub_eq_add_neg,
    NormedSpace.exp_add_of_commute_of_mem_ball hxy.neg_right
      (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hx)
      (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hny),
    NormedSpace.exp_neg_of_mem_ball ℚ_[p] (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hy),
    div_eq_mul_inv]

end DivisionAlgebra

section UltrametricBanachAlgebra

/-- For `‖x‖, ‖y‖ < r₀`, the ratio `max ‖x‖ ‖y‖ * p ^ (1 / (p - 1))` is strictly less than `1`. -/
private theorem max_norm_mul_rpow_inv_lt_one {A : Type*} [Norm A] {x y : A}
    (hx : ‖x‖ < amiceRadius p 0) (hy : ‖y‖ < amiceRadius p 0) :
    max ‖x‖ ‖y‖ * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) < 1 := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
  calc
    max ‖x‖ ‖y‖ * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹)
        < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) :=
          mul_lt_mul_of_pos_right ((max_lt hx hy).trans_eq (amiceRadius_zero p))
            (Real.rpow_pos_of_pos hp0 _)
    _ = 1 := by rw [← Real.rpow_add hp0, neg_add_cancel, Real.rpow_zero]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ_[p] A] [IsUltrametricDist A]
  [CompleteSpace A]

/-- Second-order remainder estimate for the difference `exp x - exp y - (x - y)` on the open
disc of convergence. -/
private theorem norm_exp_sub_exp_sub_le {x y : A}
    (hx : ‖x‖ < amiceRadius p 0) (hy : ‖y‖ < amiceRadius p 0) :
    ‖NormedSpace.exp x - NormedSpace.exp y - (x - y)‖ ≤
      max ‖x‖ ‖y‖ * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) * ‖x - y‖ := by
  set M : ℝ := max ‖x‖ ‖y‖
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
  have hprod : M * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) < 1 := max_norm_mul_rpow_inv_lt_one hx hy
  have h2 : HasSum (fun k : ℕ ↦ (((k + 2)! : ℚ_[p])⁻¹) • (x ^ (k + 2) - y ^ (k + 2)))
      (NormedSpace.exp x - NormedSpace.exp y - (x - y)) := by
    have hsub := (NormedSpace.expSeries_hasSum_exp_of_mem_ball' x
      (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hx)).sub
      (NormedSpace.expSeries_hasSum_exp_of_mem_ball' y
        (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hy))
    rw [← hasSum_nat_add_iff' 2] at hsub
    have hrange : ∑ i ∈ Finset.range 2, ((i !⁻¹ : ℚ_[p]) • x ^ i - (i !⁻¹ : ℚ_[p]) • y ^ i) =
        x - y := by
      simp [Finset.sum_range_succ]
    rw [hrange] at hsub
    simpa only [smul_sub] using hsub
  rw [← h2.tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun k ↦ ?_
  have hexp : (((k + 2 : ℕ) : ℝ) - 1) / ((p : ℝ) - 1) = ((p : ℝ) - 1)⁻¹ * (k + 1 : ℕ) := by
    push_cast; ring
  have hpow_le : (M * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹)) ^ (k + 1) ≤
      M * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) :=
    pow_le_of_le_one (by positivity) hprod.le (Nat.succ_ne_zero k)
  calc
    ‖(((k + 2)! : ℚ_[p])⁻¹) • (x ^ (k + 2) - y ^ (k + 2))‖
        ≤ ‖(((k + 2)! : ℚ_[p])⁻¹)‖ * ‖x ^ (k + 2) - y ^ (k + 2)‖ := norm_smul_le _ _
    _ ≤ (p : ℝ) ^ ((((k + 2 : ℕ) : ℝ) - 1) / ((p : ℝ) - 1)) * (M ^ (k + 1) * ‖x - y‖) :=
          mul_le_mul (norm_inv_factorial_le_rpow_sub_one_div (p := p) (Nat.succ_ne_zero _))
            (TauCeti.norm_pow_sub_pow_le x y (k + 2)) (norm_nonneg _) (by positivity)
    _ = (M * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹)) ^ (k + 1) * ‖x - y‖ := by
          rw [hexp, Real.rpow_mul hp0.le, Real.rpow_natCast, mul_pow]; ring
    _ ≤ M * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right hpow_le (norm_nonneg _)

/-- Second-order ultrametric remainder bound on the open disc:
`‖exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * p ^ (1 / (p - 1))`. -/
theorem norm_exp_sub_one_sub_le {x : A} (hx : ‖x‖ < amiceRadius p 0) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) := by
  have h0 : ‖(0 : A)‖ < amiceRadius p 0 := by simpa using amiceRadius_pos (p := p) 0
  have h := norm_exp_sub_exp_sub_le hx h0
  simp only [NormedSpace.exp_zero, sub_zero, norm_zero, max_eq_left (norm_nonneg x)] at h
  refine h.trans_eq ?_
  ring

/-- **Isometry property of `NormedSpace.exp`** on `{x : A | ‖x‖ < amiceRadius p 0}`:
`‖exp x - exp y‖ = ‖x - y‖`. -/
theorem norm_exp_sub_exp {x y : A} (hx : ‖x‖ < amiceRadius p 0) (hy : ‖y‖ < amiceRadius p 0) :
    ‖NormedSpace.exp x - NormedSpace.exp y‖ = ‖x - y‖ := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  have hprod : max ‖x‖ ‖y‖ * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) < 1 := max_norm_mul_rpow_inv_lt_one hx hy
  have hrem : ‖NormedSpace.exp x - NormedSpace.exp y - (x - y)‖ < ‖x - y‖ :=
    (norm_exp_sub_exp_sub_le hx hy).trans_lt <|
      (mul_lt_mul_of_pos_right hprod (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))).trans_eq (one_mul _)
  have hdecomp : NormedSpace.exp x - NormedSpace.exp y =
      (x - y) + (NormedSpace.exp x - NormedSpace.exp y - (x - y)) := by abel
  rw [hdecomp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hrem.ne', max_eq_left hrem.le]

/-- **The `p`-adic exponential preserves norms on its disc.** For `‖x‖ < r₀`,
`‖exp x - 1‖ = ‖x‖`: every term `xⁿ / n!` of degree `n ≥ 2` is strictly smaller than `x`. -/
theorem norm_exp_sub_one_of_norm_lt {x : A} (hx : ‖x‖ < amiceRadius p 0) :
    ‖NormedSpace.exp x - 1‖ = ‖x‖ := by
  have h0 : ‖(0 : A)‖ < amiceRadius p 0 := by simpa using amiceRadius_pos (p := p) 0
  simpa using norm_exp_sub_exp hx h0

/-- On the open disc of convergence, `exp x = 1` if and only if `x = 0`. -/
theorem exp_eq_one_iff {x : A} (hx : ‖x‖ < amiceRadius p 0) :
    NormedSpace.exp x = 1 ↔ x = 0 := by
  rw [← sub_eq_zero, ← norm_eq_zero, norm_exp_sub_one_of_norm_lt hx, norm_eq_zero]

/-- For every odd prime `p ≠ 2`, `‖exp p - 1‖ = p⁻¹` in any complete ultrametric normed algebra
over `ℚ_[p]` with `‖(1 : A)‖ = 1`. -/
theorem norm_exp_natCast_prime_sub_one [NormOneClass A] (hp2 : p ≠ 2) :
    ‖NormedSpace.exp (p : A) - 1‖ = (p : ℝ)⁻¹ :=
  (norm_exp_sub_one_of_norm_lt (norm_natCast_prime_lt hp2)).trans TauCeti.norm_natCast_p

end UltrametricBanachAlgebra

/-- On the open disc of convergence in a complete normed field over `ℚ_[p]`,
`exp (x - y) = exp x / exp y`. -/
theorem exp_sub {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L] {x y : L}
    (hx : ‖x‖ < amiceRadius p 0) (hy : ‖y‖ < amiceRadius p 0) :
    NormedSpace.exp (x - y) = NormedSpace.exp x / NormedSpace.exp y :=
  exp_sub_of_commute (Commute.all x y) hx hy

end Disc

section Divergence

/-- Whenever `amiceRadius p 0 ≤ ‖x‖` in a normed division algebra `D` over `ℚ_[p]`, the
exponential series `∑ x ^ n / n!` diverges, because the terms of degree `p ^ k` have norm at least
`amiceRadius p 0`. -/
theorem not_summable_pow_div_factorial_of_le_norm {p : ℕ} [hp : Fact p.Prime] {D : Type*}
    [NormedDivisionRing D] [NormedAlgebra ℚ_[p] D] {x : D}
    (hx : amiceRadius p 0 ≤ ‖x‖) :
    ¬ Summable fun n : ℕ ↦ x ^ n / (n ! : D) := by
  intro h
  have hρ_pos : 0 < amiceRadius p 0 := amiceRadius_pos 0
  have ht : Filter.Tendsto (fun k : ℕ ↦ ‖x ^ (p ^ k) / (((p ^ k)! : ℕ) : D)‖)
      Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, norm_zero] using
      h.tendsto_atTop_zero.norm.comp (tendsto_pow_atTop_atTop_of_one_lt hp.out.one_lt)
  have hge : ∀ k : ℕ, amiceRadius p 0 ≤
      ‖x ^ (p ^ k) / (((p ^ k)! : ℕ) : D)‖ := fun k ↦ by
    rw [div_eq_mul_inv, norm_mul, norm_pow, mul_comm, amiceRadius_zero]
    exact le_norm_inv_factorial_pow_prime_mul_pow ((amiceRadius_zero p).symm.trans_le hx) k
  exact not_le_of_gt hρ_pos (ge_of_tendsto' ht hge)

/-- Outside the open disc (`amiceRadius p 0 ≤ ‖x‖`), `NormedSpace.exp x = 0` by `tsum`
junk-value convention, since the defining series diverges. -/
theorem exp_eq_zero_of_le_norm {p : ℕ} [hp : Fact p.Prime] {D : Type*}
    [NormedDivisionRing D] [NormedAlgebra ℚ_[p] D] {x : D}
    (hx : amiceRadius p 0 ≤ ‖x‖) :
    NormedSpace.exp x = 0 := by
  have : CharZero D := charZero_of_injective_algebraMap (algebraMap ℚ_[p] D).injective
  rw [NormedSpace.exp_eq_tsum_div]
  exact tsum_eq_zero_of_not_summable (not_summable_pow_div_factorial_of_le_norm hx)

/-- In any normed division algebra `D` over `ℚ_[p]`, `NormedSpace.exp (1 : D) = 0`, since
`‖(1 : D)‖ = 1 ≥ amiceRadius p 0` lies outside the open disc of convergence. -/
theorem exp_one_eq_zero (p : ℕ) [hp : Fact p.Prime] {D : Type*} [NormedDivisionRing D]
    [NormedAlgebra ℚ_[p] D] : NormedSpace.exp (1 : D) = 0 := by
  refine exp_eq_zero_of_le_norm (p := p) ?_
  rw [norm_one]
  exact (amiceRadius_lt_one 0).le

/-- At `p = 2`, the boundary point `x = 2` has `‖(2 : D)‖ = 1 / 2 = amiceRadius 2 0`, so the
exponential series `∑ 2 ^ n / n!` diverges. -/
theorem not_summable_two_pow_div_factorial {D : Type*} [NormedDivisionRing D]
    [NormedAlgebra ℚ_[2] D] :
    ¬ Summable fun n : ℕ ↦ (2 : D) ^ n / (n ! : D) := by
  refine not_summable_pow_div_factorial_of_le_norm (p := 2) ?_
  rw [← Nat.cast_two (R := D), TauCeti.norm_natCast_p (p := 2),
    ← amiceRadius_zero_pow_sub_one (p := 2)]
  norm_num

end Divergence

end TauCeti.PadicExp

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
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.NumberTheory.Padics.Factorial

/-!
# The `p`-adic exponential on its disc of convergence

Using the `p`-adic factorial norm estimates from `TauCeti.NumberTheory.Padics.Factorial`, for any
nontrivially normed field `K` over `ℚ_[p]` and normed `K`-algebra `A`, `NormedSpace.expSeries K A`
has radius of convergence at least `ρ = p ^ (-1 / (p - 1))`
(`TauCeti.PadicExp.le_radius_expSeries_of_normedAlgebra`, `TauCeti.PadicExp.radius_expSeries_pos`),
and exact radius `ρ` whenever `‖(1 : A)‖ = 1` (`TauCeti.PadicExp.radius_expSeries_of_normOneClass`),
so when `A` is complete `NormedSpace.exp` has the power series expansion `NormedSpace.expSeries K A`
on the open ball of radius `ρ` (`TauCeti.PadicExp.hasFPowerSeriesOnBall_exp`). In particular, over
any nontrivially normed field `L` over `ℚ_[p]` (including infinite or non-locally-compact extensions
such as `ℂ_[p]`), `NormedSpace.expSeries L L` has exact radius `ρ`
(`TauCeti.PadicExp.radius_expSeries`, `TauCeti.PadicExp.le_radius_expSeries`).

On the open disc `{x | ‖x‖ < p ^ (-1 / (p - 1))}`:
* In any complete normed `ℚ_[p]`-algebra `A`, `exp (n • x) = exp x ^ n`
  (`TauCeti.PadicExp.exp_nsmul`, `TauCeti.PadicExp.exp_natCast_mul`), and `exp x ≠ 0` when `A` is
  nontrivial (`TauCeti.PadicExp.exp_ne_zero`).
* In any complete commutative normed `ℚ_[p]`-algebra `A`, `NormedSpace.exp` satisfies the
  functional equation `exp (x + y) = exp x * exp y` (`TauCeti.PadicExp.exp_add`) and carries finite
  sums in the disc to products (`TauCeti.PadicExp.exp_sum`).
* In any complete normed division algebra `D` over `ℚ_[p]`, `∑ x ^ n / n!` converges to
  `NormedSpace.exp x` (`TauCeti.PadicExp.hasSum_exp`), `exp (-x) = (exp x)⁻¹`
  (`TauCeti.PadicExp.exp_neg`), `exp (z • x) = exp x ^ z` (`TauCeti.PadicExp.exp_zsmul`), and
  `NormedSpace.exp` satisfies the second-order remainder estimate
  `‖exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * p ^ (1 / (p - 1))` (`TauCeti.PadicExp.norm_exp_sub_one_sub_le`), is
  an isometry via `‖exp x - exp y‖ = ‖x - y‖` (`TauCeti.PadicExp.norm_exp_sub_exp`), preserves the
  distance to the origin via `‖exp x - 1‖ = ‖x‖` (`TauCeti.PadicExp.norm_exp_sub_one`), takes unit
  values `‖exp x‖ = 1` (`TauCeti.PadicExp.norm_exp`), and is therefore injective
  (`TauCeti.PadicExp.injOn_exp`). Over a complete normed field `L` over `ℚ_[p]`,
  `exp (x - y) = exp x / exp y` (`TauCeti.PadicExp.exp_sub`).

Outside the open disc (`p ^ (-1 / (p - 1)) ≤ ‖x‖`) in a normed division algebra `D` over `ℚ_[p]`,
the subsequence `n = p ^ k` keeps norm at least `ρ`, so `∑ x ^ n / n!` diverges
(`TauCeti.PadicExp.not_summable_pow_div_factorial_of_le_norm`) and `NormedSpace.exp x = 0`
(`TauCeti.PadicExp.exp_eq_zero_of_le_norm`, in particular `NormedSpace.exp (1 : D) = 0` in
`TauCeti.PadicExp.exp_one_eq_zero`, and divergence at `x = 2` for `p = 2` in
`TauCeti.PadicExp.not_summable_two_pow_div_factorial`). For odd primes `p ≠ 2`, by contrast,
`‖p‖ = p ^ (-1) < p ^ (-1 / (p - 1))` lies strictly inside the disc in any seminormed
`ℚ_[p]`-algebra with `‖1‖ = 1` (`TauCeti.PadicExp.norm_natCast_prime_lt`).

## Main results

* `TauCeti.PadicExp.le_radius_expSeries_of_normedAlgebra`, `TauCeti.PadicExp.le_radius_expSeries`,
  `TauCeti.PadicExp.radius_expSeries_of_normOneClass`, `TauCeti.PadicExp.radius_expSeries`,
  `TauCeti.PadicExp.radius_expSeries_pos`, `TauCeti.PadicExp.hasFPowerSeriesOnBall_exp`: radius of
  convergence and power-series expansion of `NormedSpace.expSeries K A` (exact radius
  `ENNReal.ofReal (p ^ (-(p - 1)⁻¹))` whenever `NormOneClass A`, in particular for `L L`).
* `TauCeti.PadicExp.exp_add`, `TauCeti.PadicExp.exp_neg`, `TauCeti.PadicExp.exp_sub`,
  `TauCeti.PadicExp.exp_nsmul`, `TauCeti.PadicExp.exp_zsmul`, `TauCeti.PadicExp.exp_sum`:
  homomorphism properties of `NormedSpace.exp` on `{x | ‖x‖ < p ^ (-(p - 1)⁻¹)}`.
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

/-- **Exact radius of the `p`-adic exponential series in a normed algebra.** For any nontrivially
normed field `K` over `ℚ_[p]` and normed `K`-algebra `A` with `‖(1 : A)‖ = 1`,
`(NormedSpace.expSeries K A).radius = ENNReal.ofReal (p ^ (-1 / (p - 1)))`. -/
theorem radius_expSeries_of_normOneClass {K A : Type*} [NontriviallyNormedField K]
    [NormedAlgebra ℚ_[p] K] [NormedRing A] [NormOneClass A] [NormedAlgebra K A] :
    (NormedSpace.expSeries K A).radius = ENNReal.ofReal ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :=
  le_antisymm radius_expSeries_le_of_normOneClass le_radius_expSeries_of_normedAlgebra

/-- **Exact radius of the `p`-adic exponential series.** In any nontrivially normed field `L` over
`ℚ_[p]`, `(NormedSpace.expSeries L L).radius = ENNReal.ofReal (p ^ (-1 / (p - 1)))`. -/
theorem radius_expSeries {L : Type*} [NontriviallyNormedField L] [NormedAlgebra ℚ_[p] L] :
    (NormedSpace.expSeries L L).radius = ENNReal.ofReal ((p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :=
  radius_expSeries_of_normOneClass

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

variable {p : ℕ} [hp : Fact p.Prime]

/-- For every odd prime `p ≠ 2`, `(p : A)` has norm `p⁻¹ < p ^ (-1 / (p - 1))` and therefore lies
strictly inside the disc of convergence of `NormedSpace.exp`. -/
theorem norm_natCast_prime_lt {A : Type*} [SeminormedRing A] [NormOneClass A]
    [NormedAlgebra ℚ_[p] A] (hp2 : p ≠ 2) :
    ‖(p : A)‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
  have hp_gt2 : 2 < p := hp.out.two_le.lt_of_ne' hp2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hsub1 : (1 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp_gt2
    linarith
  rw [TauCeti.norm_natCast_eq_norm_padic (p := p) p, Padic.norm_p, ← Real.rpow_neg_one]
  exact Real.rpow_lt_rpow_of_exponent_lt hp1 (neg_lt_neg (inv_lt_one_of_one_lt₀ hsub1))

section NormedAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ_[p] A] [CompleteSpace A]

/-- In a complete normed `ℚ_[p]`-algebra `A`, since `‖n • x‖ ≤ ‖(n : ℚ_[p])‖ * ‖x‖ ≤ ‖x‖`,
`exp (n • x) = exp x ^ n` for every `n : ℕ` whenever `x` lies in the open disc of convergence. -/
theorem exp_nsmul {x : A} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (n : ℕ) :
    NormedSpace.exp (n • x) = NormedSpace.exp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnx : ‖n • x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
      calc
        ‖n • x‖ = ‖(n : ℚ_[p]) • x‖ := by rw [Nat.cast_smul_eq_nsmul]
        _ ≤ ‖(n : ℚ_[p])‖ * ‖x‖ := norm_smul_le _ _
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
              (IsUltrametricDist.norm_natCast_le_one ℚ_[p] n) (norm_nonneg x)
        _ = ‖x‖ := one_mul _
        _ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := hx
    rw [succ_nsmul, NormedSpace.exp_add_of_commute_of_mem_ball ((Commute.refl x).smul_left n)
      (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hnx)
      (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hx), ih, pow_succ]

/-- On the open disc of convergence, `exp (n * x) = exp x ^ n` for every `n : ℕ`. -/
theorem exp_natCast_mul {x : A} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (n : ℕ) :
    NormedSpace.exp ((n : A) * x) = NormedSpace.exp x ^ n := by
  rw [← nsmul_eq_mul, exp_nsmul hx]

/-- On the open disc of convergence in a nontrivial complete normed `ℚ_[p]`-algebra,
`NormedSpace.exp x ≠ 0`. -/
theorem exp_ne_zero [Nontrivial A] {x : A} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp x ≠ 0 :=
  (NormedSpace.isUnit_exp_of_mem_ball (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hx)).ne_zero

end NormedAlgebra

section CommAlgebra

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℚ_[p] A]

private theorem expSeries_term_add (u v : A) (n : ℕ) :
    (n !⁻¹ : ℚ_[p]) • (u + v) ^ n =
      ∑ kl ∈ Finset.antidiagonal n,
        ((kl.1 !⁻¹ : ℚ_[p]) • u ^ kl.1) * ((kl.2 !⁻¹ : ℚ_[p]) • v ^ kl.2) := by
  rw [(Commute.all u v).add_pow' n, Finset.smul_sum]
  refine Finset.sum_congr rfl fun kl hkl ↦ ?_
  rw [← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul, smul_mul_smul_comm,
    ← Finset.mem_antidiagonal.mp hkl, Nat.cast_add_choose, Finset.mem_antidiagonal.mp hkl]
  congr 1
  field_simp [n.factorial_ne_zero]

variable [CompleteSpace A]

/-- **Functional equation of the `p`-adic exponential** on its open disc of convergence in a
complete commutative normed `ℚ_[p]`-algebra. -/
theorem exp_add {x y : A} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hy : ‖y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y :=
  NormedSpace.exp_add_of_mem_ball
    (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hx)
    (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hy)

/-- The exponential of a finite sum of elements in `{x : A | ‖x‖ < p ^ (-1 / (p - 1))}` is the
product of their exponentials. -/
theorem exp_sum {ι : Type*} (s : Finset ι) {f : ι → A}
    (hf : ∀ i ∈ s, ‖f i‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp (∑ i ∈ s, f i) = ∏ i ∈ s, NormedSpace.exp (f i) := by
  classical
  suffices Summable (fun n : ℕ ↦ ‖(n !⁻¹ : ℚ_[p]) • (∑ i ∈ s, f i) ^ n‖) ∧
      NormedSpace.exp (∑ i ∈ s, f i) = ∏ i ∈ s, NormedSpace.exp (f i) from this.2
  induction s using Finset.induction_on with
  | empty =>
    have h0 : ‖(0 : A)‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
      simpa using Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
    refine ⟨?_, by simp⟩
    simpa using NormedSpace.norm_expSeries_summable_of_mem_ball' (𝕂 := ℚ_[p]) (0 : A)
      (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) h0)
  | insert a s ha ih =>
    have ha_lt : ‖f a‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := hf a (Finset.mem_insert_self a s)
    have hs_lt : ∀ i ∈ s, ‖f i‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
      fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have ha_sum : Summable fun n : ℕ ↦ ‖(n !⁻¹ : ℚ_[p]) • (f a) ^ n‖ :=
      NormedSpace.norm_expSeries_summable_of_mem_ball' (𝕂 := ℚ_[p]) (f a)
        (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) ha_lt)
    obtain ⟨hs_sum, hs_exp⟩ := ih hs_lt
    have hterm := expSeries_term_add (p := p) (f a) (∑ i ∈ s, f i)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨?_, ?_⟩
    · simpa only [hterm] using summable_norm_sum_mul_antidiagonal_of_summable_norm ha_sum hs_sum
    · rw [← hs_exp, NormedSpace.exp_eq_tsum ℚ_[p],
        tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha_sum hs_sum]
      exact tsum_congr hterm

end CommAlgebra

section DivisionAlgebra

variable {D : Type*} [NormedDivisionRing D] [NormedAlgebra ℚ_[p] D]

/-- For `‖x‖ < p ^ (-1 / (p - 1))`, the norms `‖x ^ n / n!‖` are summable. -/
theorem summable_norm_pow_div_factorial {x : D}
    (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    Summable fun n : ℕ ↦ ‖x ^ n / (n ! : D)‖ :=
  NormedSpace.norm_expSeries_div_summable_of_mem_ball ℚ_[p] x
    (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hx)

variable [CompleteSpace D]

/-- On the open disc `‖x‖ < p ^ (-1 / (p - 1))`, `∑ x ^ n / n!` converges to
`NormedSpace.exp x`. -/
theorem hasSum_exp {x : D} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    HasSum (fun n : ℕ ↦ x ^ n / (n ! : D)) (NormedSpace.exp x) :=
  NormedSpace.expSeries_div_hasSum_exp_of_mem_ball ℚ_[p] x
    (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hx)

/-- On the open disc of convergence, `exp (-x) = (exp x)⁻¹`. -/
theorem exp_neg {x : D} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp (-x) = (NormedSpace.exp x)⁻¹ :=
  NormedSpace.exp_neg_of_mem_ball ℚ_[p] (mem_eball_expSeries_of_norm_lt (K := ℚ_[p]) hx)

/-- On the open disc of convergence, `exp (z • x) = exp x ^ z` for every integer `z : ℤ`. -/
theorem exp_zsmul {x : D} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (z : ℤ) :
    NormedSpace.exp (z • x) = NormedSpace.exp x ^ z := by
  have : IsUltrametricDist D := .of_normedAlgebra ℚ_[p]
  cases z with
  | ofNat n => simpa using exp_nsmul hx n
  | negSucc n =>
    have hnx : ‖(n + 1) • x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
      (IsUltrametricDist.norm_nsmul_le x (n + 1)).trans_lt hx
    rw [negSucc_zsmul, exp_neg hnx, exp_nsmul hx, zpow_negSucc]

/-- On the open disc of convergence, `exp (z * x) = exp x ^ z` for every integer `z : ℤ`. -/
theorem exp_intCast_mul {x : D} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (z : ℤ) :
    NormedSpace.exp ((z : D) * x) = NormedSpace.exp x ^ z := by
  rw [← zsmul_eq_mul, exp_zsmul hx]

/-- Second-order ultrametric remainder bound on the open disc:
`‖exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * p ^ (1 / (p - 1))`. -/
theorem norm_exp_sub_one_sub_le {x : D} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖NormedSpace.exp x - 1 - x‖ ≤ ‖x‖ ^ 2 * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) := by
  have : IsUltrametricDist D := .of_normedAlgebra ℚ_[p]
  have h2 := hasSum_exp hx
  rw [← hasSum_nat_add_iff' 2] at h2
  have hrange : ∑ i ∈ Finset.range 2, x ^ i / (i ! : D) = 1 + x := by
    simp [Finset.sum_range_succ]
  rw [hrange, sub_add_eq_sub_sub] at h2
  rw [← h2.tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le fun k ↦ ?_
  simpa only [div_eq_mul_inv] using
    norm_pow_mul_inv_factorial_le_sq (p := p) hx.le (Nat.le_add_left 2 k)

/-- **Isometry property of `NormedSpace.exp`** on `{x : D | ‖x‖ < p ^ (-1 / (p - 1))}`:
`‖exp x - exp y‖ = ‖x - y‖`. -/
theorem norm_exp_sub_exp {x y : D} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹))
    (hy : ‖y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖NormedSpace.exp x - NormedSpace.exp y‖ = ‖x - y‖ := by
  have : IsUltrametricDist D := .of_normedAlgebra ℚ_[p]
  rcases eq_or_ne x y with rfl | hxy
  · simp
  set M : ℝ := max ‖x‖ ‖y‖
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
  have hprod : M * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) < 1 := by
    calc
      M * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹)
          < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) :=
            mul_lt_mul_of_pos_right (max_lt hx hy) (Real.rpow_pos_of_pos hp0 _)
      _ = 1 := by rw [← Real.rpow_add hp0, neg_add_cancel, Real.rpow_zero]
  have h2 : HasSum (fun k : ℕ ↦ (x ^ (k + 2) - y ^ (k + 2)) / (((k + 2)! : ℕ) : D))
      (NormedSpace.exp x - NormedSpace.exp y - (x - y)) := by
    have hsub := (hasSum_exp hx).sub (hasSum_exp hy)
    rw [← hasSum_nat_add_iff' 2] at hsub
    have hrange : ∑ i ∈ Finset.range 2, (x ^ i / (i ! : D) - y ^ i / (i ! : D)) = x - y := by
      simp [Finset.sum_range_succ]
    rw [hrange] at hsub
    simpa only [sub_div] using hsub
  have hrem_le : ‖NormedSpace.exp x - NormedSpace.exp y - (x - y)‖ ≤
      M * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) * ‖x - y‖ := by
    rw [← h2.tsum_eq]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le fun k ↦ ?_
    have hexp : (((k + 2 : ℕ) : ℝ) - 1) / ((p : ℝ) - 1) = ((p : ℝ) - 1)⁻¹ * (k + 1 : ℕ) := by
      push_cast; ring
    have hpow_le : (M * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹)) ^ (k + 1) ≤
        M * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) :=
      pow_le_of_le_one (by positivity) hprod.le (Nat.succ_ne_zero k)
    rw [div_eq_mul_inv, norm_mul]
    calc
      ‖x ^ (k + 2) - y ^ (k + 2)‖ * ‖(((k + 2)! : ℕ) : D)⁻¹‖
          ≤ (M ^ (k + 1) * ‖x - y‖) * (p : ℝ) ^ ((((k + 2 : ℕ) : ℝ) - 1) / ((p : ℝ) - 1)) :=
            mul_le_mul (TauCeti.norm_pow_sub_pow_le x y (k + 2))
              (norm_inv_factorial_le_rpow_sub_one_div (p := p) (Nat.succ_ne_zero _))
              (norm_nonneg _) (by positivity)
      _ = (M * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹)) ^ (k + 1) * ‖x - y‖ := by
            rw [hexp, Real.rpow_mul hp0.le, Real.rpow_natCast, mul_pow]; ring
      _ ≤ M * (p : ℝ) ^ (((p : ℝ) - 1)⁻¹) * ‖x - y‖ :=
            mul_le_mul_of_nonneg_right hpow_le (norm_nonneg _)
  have hrem : ‖NormedSpace.exp x - NormedSpace.exp y - (x - y)‖ < ‖x - y‖ :=
    hrem_le.trans_lt <|
      (mul_lt_mul_of_pos_right hprod (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))).trans_eq (one_mul _)
  have hdecomp : NormedSpace.exp x - NormedSpace.exp y =
      (x - y) + (NormedSpace.exp x - NormedSpace.exp y - (x - y)) := by abel
  rw [hdecomp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hrem.ne', max_eq_left hrem.le]

/-- **Isometry to the origin on the disc of convergence**: for `‖x‖ < p ^ (-1 / (p - 1))`,
`‖exp x - 1‖ = ‖x‖`. -/
theorem norm_exp_sub_one {x : D} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖NormedSpace.exp x - 1‖ = ‖x‖ := by
  have h0 : ‖(0 : D)‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    simpa using Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
  simpa using norm_exp_sub_exp hx h0

/-- Every element in the open disc of convergence has exponential of norm `1`. -/
theorem norm_exp {x : D} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    ‖NormedSpace.exp x‖ = 1 := by
  have : IsUltrametricDist D := .of_normedAlgebra ℚ_[p]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hlt1 : ‖NormedSpace.exp x - 1‖ < ‖(1 : D)‖ := by
    rw [norm_exp_sub_one hx, norm_one]
    exact hx.trans_le (Real.rpow_le_one_of_one_le_of_nonpos hp1.le
      (neg_nonpos.mpr (inv_nonneg.mpr (sub_nonneg.mpr hp1.le))))
  have hdecomp : NormedSpace.exp x = 1 + (NormedSpace.exp x - 1) := by abel
  rw [hdecomp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt1.ne', max_eq_left hlt1.le,
    norm_one]

/-- On the open disc of convergence, `exp x = 1` if and only if `x = 0`. -/
theorem exp_eq_one_iff {x : D} (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp x = 1 ↔ x = 0 := by
  rw [← sub_eq_zero, ← norm_eq_zero, norm_exp_sub_one hx, norm_eq_zero]

/-- **Injectivity of `NormedSpace.exp`** on its open disc of convergence
`{x : D | ‖x‖ < p ^ (-1 / (p - 1))}`. -/
theorem injOn_exp :
    Set.InjOn (NormedSpace.exp : D → D) {x | ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)} := by
  intro x hx y hy hxy
  rw [← sub_eq_zero, ← norm_eq_zero, ← norm_exp_sub_exp hx hy, hxy]
  simp

/-- For every odd prime `p ≠ 2`, `‖exp p - 1‖ = p⁻¹` in any complete normed division algebra
over `ℚ_[p]`. -/
theorem norm_exp_natCast_prime_sub_one (hp2 : p ≠ 2) :
    ‖NormedSpace.exp (p : D) - 1‖ = (p : ℝ)⁻¹ := by
  rw [norm_exp_sub_one (norm_natCast_prime_lt hp2), TauCeti.norm_natCast_eq_norm_padic (p := p) p,
    Padic.norm_p]

end DivisionAlgebra

/-- On the open disc of convergence in a complete normed field over `ℚ_[p]`,
`exp (x - y) = exp x / exp y`. -/
theorem exp_sub {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L] {x y : L}
    (hx : ‖x‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) (hy : ‖y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹)) :
    NormedSpace.exp (x - y) = NormedSpace.exp x / NormedSpace.exp y := by
  have hny : ‖-y‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by simpa using hy
  rw [sub_eq_add_neg, exp_add hx hny, exp_neg hy, div_eq_mul_inv]

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

/-- At `p = 2`, the boundary point `x = 2` has `‖(2 : D)‖ = 1 / 2 = 2 ^ (-1 / (2 - 1))`, so the
exponential series `∑ 2 ^ n / n!` diverges. -/
theorem not_summable_two_pow_div_factorial {D : Type*} [NormedDivisionRing D]
    [NormedAlgebra ℚ_[2] D] :
    ¬ Summable fun n : ℕ ↦ (2 : D) ^ n / (n ! : D) := by
  refine not_summable_pow_div_factorial_of_le_norm (p := 2) ?_
  rw [← Nat.cast_two (R := D), TauCeti.norm_natCast_eq_norm_padic (p := 2) 2, Padic.norm_p]
  norm_num

end Divergence

end TauCeti.PadicExp

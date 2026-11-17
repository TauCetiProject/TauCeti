/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.NumberTheory.NewtonPolygon.Radius
public import TauCeti.NumberTheory.Padics.LogGauge
public import TauCeti.RingTheory.PowerSeries.Convergence
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Intrinsic radius vs convergence-point radius for `∑ p^⌈n/2⌉ Xⁿ` over `ℚ_[p]` and `ℂ_[p]`

Over a discretely valued field, the supremum `PowerSeries.convergencePointRadius` of norms of
points at which a power series converges can be strictly smaller than its coefficient-intrinsic
radius `PowerSeries.radius`. This file works out the series

`ceilHalfSeries p = ∑_{n ≥ 0} p ^ ⌈n / 2⌉ X ^ n`

over `ℚ_[p]`, with respect to `TauCeti.padicRealValuation p` (`v(p) = 1`):

* Its coefficient heights `v(aₙ) = ⌈n / 2⌉` equal `n / 2` at even `n` and `(n + 1) / 2` at odd `n`,
  so its Newton polygon is the line `n ↦ n / 2` of constant unit slope `1 / 2`, and the lower
  linear growth of its coefficient heights is `1 / 2`.
* Its intrinsic radius is therefore `PowerSeries.radius (ceilHalfSeries p) = √p`.
* At the boundary radius `√p` itself, the even-indexed weighted coefficient norms equal `1`, so the
  series is **not** restricted at `√p`.
* Over `ℚ_[p]`, no element has norm strictly between `1` and `p`, and `1 < √p < p`. Thus the exact
  convergence set in `ℚ_[p]` is the closed unit disc `Metric.closedBall 0 1`, and
  `(ceilHalfSeries p).convergencePointRadius ℚ_[p] = 1 < √p = (ceilHalfSeries p).radius`. Moreover,
  because every `x : ℚ_[p]` with `‖x‖ ≤ √p` actually satisfies `‖x‖ ≤ 1`, the series converges at
  every `ℚ_[p]`-point of `{x : ℚ_[p] | ‖x‖ ≤ √p}` even though it is not restricted at `√p` —
  showing that attainment of the radius by a norm is indispensable in
  `PowerSeries.forall_norm_le_summable_smul_pow_iff_isRestricted`.
* Over `ℂ_[p]`, whose positive norms are the rational powers of `p` and hence dense in `(0, ∞)`,
  the exact convergence set is the open disc `Metric.ball 0 √p`:
  `(ceilHalfSeries p).convergencePointRadius ℂ_[p] = √p = (ceilHalfSeries p).radius`, while at any
  element `z : ℂ_[p]` of norm `√p` (such as the inverse of a square root of `p`) the series
  diverges.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren der mathematischen
  Wissenschaften 261, Springer, 1984, §5.1.4.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., Graduate Texts in
  Mathematics 58, Springer, 1984, Chapter IV, §§1, 4.
-/

public section

open Filter LinearGrowth PowerSeries TauCeti
open scoped ENNReal Topology

namespace TauCeti.NewtonPolygonConvergenceExample

variable (p : ℕ) [Fact p.Prime]

/-- The power series `∑_{n ≥ 0} p ^ ⌈n / 2⌉ X ^ n` over `ℚ_[p]`. -/
noncomputable def ceilHalfSeries : PowerSeries ℚ_[p] :=
  PowerSeries.mk fun n ↦ (p : ℚ_[p]) ^ ((n + 1) / 2)

/-- The `n`-th coefficient of `ceilHalfSeries p` is `p ^ ((n + 1) / 2)`. -/
@[simp]
theorem coeff_ceilHalfSeries (n : ℕ) :
    coeff n (ceilHalfSeries p) = (p : ℚ_[p]) ^ ((n + 1) / 2) :=
  PowerSeries.coeff_mk n _

/-- The `(2 * k)`-th coefficient of `ceilHalfSeries p` is `p ^ k`. -/
theorem coeff_ceilHalfSeries_two_mul (k : ℕ) :
    coeff (2 * k) (ceilHalfSeries p) = (p : ℚ_[p]) ^ k := by
  have hk : (2 * k + 1) / 2 = k := by omega
  rw [coeff_ceilHalfSeries, hk]

/-- In ceiling notation, the `n`-th coefficient of `ceilHalfSeries p` is `p ^ ⌈(n : ℝ) / 2⌉₊`. -/
theorem coeff_ceilHalfSeries_eq_pow_ceil (n : ℕ) :
    coeff n (ceilHalfSeries p) = (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊ := by
  have hceil : ⌈(n : ℝ) / 2⌉₊ = (n + 1) / 2 := by
    simpa [Nat.ceilDiv_eq_add_pred_div] using Nat.ceil_div_eq_ceilDiv (K := ℝ) n 2
  rw [coeff_ceilHalfSeries, hceil]

/-- The real `p`-adic valuation of the `n`-th coefficient of `ceilHalfSeries p` is
`((n + 1) / 2 : ℕ)`. -/
theorem padicRealValuation_coeff_ceilHalfSeries (n : ℕ) :
    padicRealValuation p (coeff n (ceilHalfSeries p)) = (((n + 1) / 2 : ℕ) : ℝ) := by
  simp

/-- The real `p`-adic valuation of the `n`-th coefficient of `ceilHalfSeries p` is at least
`n / 2`. -/
theorem half_le_padicRealValuation_coeff_ceilHalfSeries (n : ℕ) :
    (((n : ℝ) / 2 : ℝ) : WithTop ℝ) ≤ padicRealValuation p (coeff n (ceilHalfSeries p)) := by
  rw [coeff_ceilHalfSeries_eq_pow_ceil]
  simpa using WithTop.coe_le_coe.mpr (Nat.le_ceil ((n : ℝ) / 2))

/-- The `p`-adic norm of the `n`-th coefficient of `ceilHalfSeries p` is `p ^ (-⌈n / 2⌉)`. -/
theorem norm_coeff_ceilHalfSeries (n : ℕ) :
    ‖coeff n (ceilHalfSeries p)‖ = (p : ℝ) ^ (-(((n + 1) / 2 : ℕ) : ℤ)) := by
  rw [coeff_ceilHalfSeries, norm_pow, Padic.norm_p, inv_pow, ← zpow_natCast, zpow_neg]

/-- The coefficient heights of `ceilHalfSeries p` are admissible, being minorised by `n / 2`. -/
theorem isAdmissible_ceilHalfSeries :
    IsAdmissible fun n ↦ padicRealValuation p (coeff n (ceilHalfSeries p)) := by
  refine isAdmissible_iff.mpr ⟨0, 1 / 2, fun n ↦ ?_⟩
  simpa [div_eq_inv_mul] using half_le_padicRealValuation_coeff_ceilHalfSeries p n

/-- **Newton polygon of `∑ p^⌈n/2⌉ Xⁿ`.** The Newton polygon of `ceilHalfSeries p` is the line
`n ↦ n / 2`: the even-indexed coefficients sit directly on this line, while each odd-indexed
coefficient sits `1 / 2` above the midpoint of its two even neighbours. -/
theorem newtonPolygon_ceilHalfSeries (n : ℕ) :
    (ceilHalfSeries p).newtonPolygon (padicRealValuation p) n =
      (((n : ℝ) / 2 : ℝ) : WithTop ℝ) := by
  set g := (ceilHalfSeries p).newtonPolygon (padicRealValuation p)
  have hminor : (fun k : ℕ ↦ ((0 + (1 / 2 : ℝ) * k : ℝ) : WithTop ℝ)) ≤ g :=
    le_newtonPolygon (isConvexSeq_affine 0 (1 / 2)) fun k ↦ by
      simpa [div_eq_inv_mul] using half_le_padicRealValuation_coeff_ceilHalfSeries p k
  have heven (k : ℕ) : g (2 * k) = ((0 + (1 / 2 : ℝ) * (2 * k : ℕ) : ℝ) : WithTop ℝ) := by
    refine le_antisymm ?_ (hminor (2 * k))
    refine ((ceilHalfSeries p).newtonPolygon_le (isAdmissible_ceilHalfSeries p) (2 * k)).trans ?_
    rw [coeff_ceilHalfSeries_two_mul]
    simp
  have hconv := (ceilHalfSeries p).isConvexSeq_newtonPolygon (padicRealValuation p)
  have hline := hconv.eq_affine_of_affine_le (heven 0) (heven n) (Nat.zero_le n) (by omega)
    (hminor n)
  simpa [div_eq_inv_mul] using hline

/-- Every unit edge of the Newton polygon of `ceilHalfSeries p` has slope `1 / 2`. -/
theorem unitSlope_newtonPolygon_ceilHalfSeries (n : ℕ) :
    unitSlope ((ceilHalfSeries p).newtonPolygon (padicRealValuation p)) n = 1 / 2 := by
  rw [unitSlope_def, newtonPolygon_ceilHalfSeries, newtonPolygon_ceilHalfSeries,
    WithTop.untop₀_coe, WithTop.untop₀_coe]
  push_cast
  ring

/-- The lower linear growth of the coefficient heights of `ceilHalfSeries p` is `1 / 2`. -/
theorem linearGrowthInf_ceilHalfSeries :
    (linearGrowthInf fun n ↦ (padicRealValuation p (coeff n (ceilHalfSeries p))).toEReal) =
      ((1 / 2 : ℝ) : EReal) := by
  rw [← ((ceilHalfSeries p).isLowerConvexEnvelope_newtonPolygon
    (isAdmissible_ceilHalfSeries p)).linearGrowthInf_eq]
  have hfun : (fun n : ℕ ↦ ((ceilHalfSeries p).newtonPolygon (padicRealValuation p) n).toEReal) =
      fun n : ℕ ↦ ((1 / 2 : ℝ) : EReal) * (n : EReal) := by
    ext n
    rw [newtonPolygon_ceilHalfSeries, WithTop.toEReal_coe, ← EReal.coe_natCast, ← EReal.coe_mul]
    congr 1
    ring
  rw [hfun, linearGrowthInf_const_mul_self]

/-- **Intrinsic radius of `∑ p^⌈n/2⌉ Xⁿ`.** Over `ℚ_[p]`, `ceilHalfSeries p` has intrinsic radius
`√p`. -/
theorem radius_ceilHalfSeries :
    (ceilHalfSeries p).radius = ENNReal.ofReal (Real.sqrt p) := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  rw [radius_eq_ofReal_rpow (ceilHalfSeries p) (padicRealValuation p) hp1
    (fun _ hx ↦ norm_eq_rpow_neg_padicRealValuation hx) (linearGrowthInf_ceilHalfSeries p),
    ← Real.sqrt_eq_rpow]

/-- `ceilHalfSeries p` is restricted at the radius `1`. -/
theorem isRestricted_one_ceilHalfSeries : (ceilHalfSeries p).IsRestricted 1 := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hsqrt : (1 : ℝ) < Real.sqrt p := (Real.lt_sqrt zero_le_one).mpr (by simpa using hp1)
  refine isRestricted_of_lt_radius ?_
  rw [radius_ceilHalfSeries, Real.eNorm_eq_ofReal zero_le_one]
  exact (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hsqrt)).mpr hsqrt

/-- **Failure of restrictedness at the boundary radius `√p`.** Even-indexed weighted coefficient
norms of `ceilHalfSeries p` at `√p` are constantly `1`, so the series is not restricted at `√p`. -/
theorem not_isRestricted_sqrt_ceilHalfSeries :
    ¬(ceilHalfSeries p).IsRestricted (Real.sqrt p) := by
  intro hf
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have heven : Tendsto (fun k : ℕ ↦ ‖coeff (2 * k) (ceilHalfSeries p)‖ * (Real.sqrt p) ^ (2 * k))
      atTop (𝓝 0) :=
    ((isRestricted_iff' _ _).mp hf).comp (tendsto_id.const_mul_atTop' two_pos)
  have hconst (k : ℕ) : ‖coeff (2 * k) (ceilHalfSeries p)‖ * (Real.sqrt p) ^ (2 * k) = 1 := by
    rw [coeff_ceilHalfSeries_two_mul, norm_pow, Padic.norm_p, inv_pow, pow_mul,
      Real.sq_sqrt hp0.le, inv_mul_cancel₀ (pow_ne_zero k hp0.ne')]
  simp only [hconst] at heven
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds heven)

/-- **Pointwise convergence criterion in `ℚ_[p]`.** At `x : ℚ_[p]`, `ceilHalfSeries p` converges if
and only if `‖x‖ ≤ 1`. -/
theorem summable_padic_ceilHalfSeries_iff {x : ℚ_[p]} :
    (Summable fun n ↦ coeff n (ceilHalfSeries p) • x ^ n) ↔ ‖x‖ ≤ 1 := by
  refine ⟨fun h ↦ ?_, fun hx ↦ ((isRestricted_one_ceilHalfSeries p).hasSum_evalAt hx).summable⟩
  rcases Padic.norm_le_one_or_natCast_le_norm x with hx1 | hpx
  · exact hx1
  · refine (not_isRestricted_sqrt_ceilHalfSeries p ?_).elim
    refine (ceilHalfSeries p).isRestricted_of_abs_le_norm_of_summable_smul_pow ?_ h
    rw [abs_of_nonneg (Real.sqrt_nonneg p)]
    have hsqrt : Real.sqrt p < p :=
      Real.sqrt_lt_self_iff.mpr (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
    exact hsqrt.le.trans hpx

/-- **Exact convergence set in `ℚ_[p]`.** The set of points of `ℚ_[p]` at which `ceilHalfSeries p`
converges is the closed unit disc `Metric.closedBall 0 1`. -/
theorem setOf_summable_padic_ceilHalfSeries :
    {x : ℚ_[p] | Summable fun n ↦ coeff n (ceilHalfSeries p) • x ^ n} = Metric.closedBall 0 1 := by
  ext x
  simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right,
    summable_padic_ceilHalfSeries_iff]

/-- **Closed-ball convergence without restrictedness over `ℚ_[p]`.** Every element `x : ℚ_[p]` with
`‖x‖ ≤ √p` actually has `‖x‖ ≤ 1`, so `ceilHalfSeries p` converges at every `ℚ_[p]`-point of the
closed ball of numerical radius `√p`, despite failing `IsRestricted √p`. -/
theorem hasSum_evalAt_ceilHalfSeries_of_norm_le_sqrt {x : ℚ_[p]} (hx : ‖x‖ ≤ Real.sqrt p) :
    HasSum (fun n ↦ coeff n (ceilHalfSeries p) • x ^ n) ((ceilHalfSeries p).evalAt x) := by
  rcases Padic.norm_le_one_or_natCast_le_norm x with hx1 | hpx
  · exact (isRestricted_one_ceilHalfSeries p).hasSum_evalAt hx1
  · have hsqrt : Real.sqrt p < p :=
      Real.sqrt_lt_self_iff.mpr (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
    exact (not_lt_of_ge hpx (hx.trans_lt hsqrt)).elim

/-- **Convergence-point radius in `ℚ_[p]`.** Because `ℚ_[p]` has no elements of norm strictly
between `1` and `p`, the convergence-point supremum of `ceilHalfSeries p` in `ℚ_[p]` is `1`. -/
theorem convergencePointRadius_padic_ceilHalfSeries :
    (ceilHalfSeries p).convergencePointRadius ℚ_[p] = 1 := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hnp : ¬(ceilHalfSeries p).IsRestricted p :=
    not_isRestricted_of_radius_lt <| by
      rw [radius_ceilHalfSeries, Real.eNorm_eq_ofReal hp0.le]
      exact (ENNReal.ofReal_lt_ofReal_iff hp0).mpr (Real.sqrt_lt_self_iff.mpr hp1)
  simpa using (ceilHalfSeries p).convergencePointRadius_eq_ofReal_of_norm_le_or_le hp0.le
    (isRestricted_one_ceilHalfSeries p) ⟨1, norm_one⟩ Padic.norm_le_one_or_natCast_le_norm hnp

/-- **Strict inequality over `ℚ_[p]`.** The convergence-point supremum of `ceilHalfSeries p` in
`ℚ_[p]` is strictly smaller than its intrinsic radius `√p`. -/
theorem convergencePointRadius_padic_lt_radius_ceilHalfSeries :
    (ceilHalfSeries p).convergencePointRadius ℚ_[p] < (ceilHalfSeries p).radius := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hsqrt : (1 : ℝ) < Real.sqrt p := (Real.lt_sqrt zero_le_one).mpr (by simpa using hp1)
  rw [convergencePointRadius_padic_ceilHalfSeries, radius_ceilHalfSeries, ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hsqrt)).mpr hsqrt

/-- **Convergence-point radius in `ℂ_[p]`.** Over `ℂ_[p]`, whose positive norms are dense in
`(0, ∞)`, the convergence-point supremum of `ceilHalfSeries p` recovers its intrinsic radius
`√p`. -/
theorem convergencePointRadius_padicComplex_ceilHalfSeries :
    (ceilHalfSeries p).convergencePointRadius ℂ_[p] = ENNReal.ofReal (Real.sqrt p) := by
  rw [(ceilHalfSeries p).convergencePointRadius_eq_radius ℂ_[p], radius_ceilHalfSeries]

/-- At any element `z : ℂ_[p]` of norm `√p` (such as the inverse of a square root of `p`),
`ceilHalfSeries p` diverges. -/
theorem not_summable_padicComplex_ceilHalfSeries_of_norm_eq_sqrt {z : ℂ_[p]}
    (hz : ‖z‖ = Real.sqrt p) :
    ¬Summable fun n ↦ coeff n (ceilHalfSeries p) • z ^ n := by
  rw [(ceilHalfSeries p).summable_smul_pow_iff_isRestricted_of_norm_eq hz]
  exact not_isRestricted_sqrt_ceilHalfSeries p

/-- **Pointwise convergence criterion in `ℂ_[p]`.** At `z : ℂ_[p]`, `ceilHalfSeries p` converges if
and only if `‖z‖ < √p`. -/
theorem summable_padicComplex_ceilHalfSeries_iff {z : ℂ_[p]} :
    (Summable fun n ↦ coeff n (ceilHalfSeries p) • z ^ n) ↔ ‖z‖ < Real.sqrt p := by
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)
  refine ⟨fun h ↦ ?_, fun hz ↦ (ceilHalfSeries p).summable_smul_pow_of_lt_radius ?_⟩
  · have hle : ‖z‖ ≤ Real.sqrt p := by
      have he := (ceilHalfSeries p).le_radius_of_summable_smul_pow h
      rw [radius_ceilHalfSeries, ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hsqrt.le] at he
      exact he
    exact hle.lt_of_ne fun heq ↦
      not_summable_padicComplex_ceilHalfSeries_of_norm_eq_sqrt p heq h
  · rw [radius_ceilHalfSeries, ← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff hsqrt).mpr hz

/-- **Exact convergence set in `ℂ_[p]`.** The set of points of `ℂ_[p]` at which `ceilHalfSeries p`
converges is the open disc `Metric.ball 0 √p`. -/
theorem setOf_summable_padicComplex_ceilHalfSeries :
    {z : ℂ_[p] | Summable fun n ↦ coeff n (ceilHalfSeries p) • z ^ n} =
      Metric.ball 0 (Real.sqrt p) := by
  ext z
  simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right,
    summable_padicComplex_ceilHalfSeries_iff]

end TauCeti.NewtonPolygonConvergenceExample

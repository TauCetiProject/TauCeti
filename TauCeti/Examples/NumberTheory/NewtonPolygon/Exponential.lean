/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Convergence
public import TauCeti.NumberTheory.Padics.ExponentialDisc
public import TauCeti.NumberTheory.Padics.Factorial
public import TauCeti.NumberTheory.Padics.LogGauge
public import TauCeti.RingTheory.PowerSeries.Weierstrass.ZeroCount
import TauCeti.RingTheory.PowerSeries.Exp.Padic
import TauCeti.RingTheory.PowerSeries.Log

/-!
# The Newton polygon and radius of the `p`-adic exponential

The exponential series `exp = ∑ Xⁿ / n!` over `ℚ_[p]`, with respect to the real `p`-adic additive
valuation `TauCeti.padicRealValuation p` normalised by `v(p) = 1`, has coefficient heights
`v(1 / n!) = -v_p(n!)`. By Legendre's formula `(p - 1) v_p(n!) = n - s_p(n)`, where `s_p(n)` is
the sum of the base-`p` digits of `n`, these heights are

```text
-v_p(n!) = -n / (p - 1) + s_p(n) / (p - 1).
```

The digit sum is positive for `n ≠ 0` and equals `1` at every power `n = pᵏ`. So the points lie
on or above the line of slope `-1 / (p - 1)` through the origin, meet it only at the origin, and
approach it along `n = pᵏ`, at the constant height `1 / (p - 1)` above it. The minimal slope from
the origin is therefore not attained, and the Newton polygon is the terminal ray
`n ↦ -n / (p - 1)`: every unit slope equals `-1 / (p - 1)`, although no coefficient after the
constant one lies on the polygon.

The intrinsic radius of `exp` is consequently `p ^ (-1 / (p - 1))`, the radius
`r₀ = TauCeti.amiceRadius p 0` of `TauCeti.NumberTheory.Padics.ExponentialDisc`. The series is
not restricted at `r₀` itself: its terms of degree `pᵏ` all have weighted norm `r₀`. In every
complete normed field `L` over `ℚ_[p]`, such as `ℂ_[p]`, it therefore converges exactly on the
open disc `‖x‖ < r₀`, where it evaluates to the analytic exponential, which has norm one. So
`exp` has no zeros in that disc. In particular it is not entire.

## Main results

* `TauCeti.NewtonPolygonExponentialExample.padicRealValuation_coeff_exp`: the coefficient heights
  `-v_p(n!)`.
* `TauCeti.NewtonPolygonExponentialExample.newtonPolygon_exp`: the Newton polygon is the ray
  `n ↦ -n / (p - 1)`.
* `TauCeti.NewtonPolygonExponentialExample.unitSlope_newtonPolygon_exp` and
  `TauCeti.NewtonPolygonExponentialExample.padicRealValuation_coeff_exp_eq_newtonPolygon_iff`:
  every unit slope is `-1 / (p - 1)`, and the coefficient points meet the polygon only at `0`.
* `TauCeti.NewtonPolygonExponentialExample.radius_exp` and
  `TauCeti.NewtonPolygonExponentialExample.isRestricted_exp_iff`: the intrinsic radius is
  `p ^ (-1 / (p - 1))`, and `exp` is restricted exactly at radii of absolute value below it.
* `TauCeti.NewtonPolygonExponentialExample.summable_exp_iff`: in a complete normed field over
  `ℚ_[p]`, the series converges at `x` exactly when `‖x‖ < p ^ (-1 / (p - 1))`.
* `TauCeti.NewtonPolygonExponentialExample.evalAt_exp_ne_zero` and
  `TauCeti.NewtonPolygonExponentialExample.zeroMultiset_exp`: `exp` has no zeros in the open disc
  of convergence.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV §§1, 4.
-/

public section

open Filter LinearGrowth _root_.PowerSeries TauCeti
open scoped Nat

namespace TauCeti.NewtonPolygonExponentialExample

variable {p : ℕ} [Fact p.Prime]

private theorem one_lt_p : (1 : ℝ) < p :=
  Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt

private theorem p_sub_one_pos : (0 : ℝ) < (p : ℝ) - 1 :=
  sub_pos.mpr one_lt_p

/-! ### Coefficient heights -/

/-- The `n`-th coefficient `1 / n!` of the exponential series over `ℚ_[p]` has valuation
`-v_p(n!)`. -/
theorem padicRealValuation_coeff_exp (n : ℕ) :
    padicRealValuation p (coeff n (exp ℚ_[p])) = ((-(multiplicity p n ! : ℝ) : ℝ) : WithTop ℝ) := by
  have hn : (n ! : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [coeff_exp_eq_inv_factorial, AddValuation.map_inv, padicRealValuation_eq_map,
    Padic.addValuation.apply hn, Padic.valuation_natCast]
  simp

/-! ### The Newton polygon -/

/-- The coefficient heights of `exp` sheared by the slope `1 / (p - 1)`. They are `s_p(n) / (p - 1)`
for the base-`p` digit sum `s_p(n)`. -/
private noncomputable def shearedHeight (p n : ℕ) : WithTop ℝ :=
  (((n : ℝ) / ((p : ℝ) - 1) - multiplicity p n ! : ℝ) : WithTop ℝ)

/-- The sheared heights have the horizontal ray `0` as their lower convex envelope: they are
nonnegative, vanish at `0`, and stay bounded along `n = pᵏ`. -/
private theorem isLowerConvexEnvelope_shearedHeight :
    IsLowerConvexEnvelope (shearedHeight p) 0 := by
  refine isLowerConvexEnvelope_zero_of_linearGrowthInf_nonpos (by simp [shearedHeight])
    (fun n ↦ WithTop.coe_nonneg.mpr (sub_nonneg.mpr (multiplicity_factorial_le_div p n))) ?_
  refine (linearGrowthInf_le_linearGrowthSup_of_frequently_le
    (v := fun _ ↦ ((((p : ℝ) - 1)⁻¹ : ℝ) : EReal)) ?_).trans_eq
    (linearGrowthSup_const (EReal.coe_ne_bot _) (EReal.coe_ne_top _))
  refine frequently_atTop.mpr fun N ↦
    ⟨p ^ N, (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le, le_of_eq ?_⟩
  rw [shearedHeight, WithTop.toEReal_coe, EReal.coe_eq_coe_iff, cast_multiplicity_factorial_pow]
  field_simp [p_sub_one_pos.ne']
  push_cast
  ring

/-- **The Newton polygon of the `p`-adic exponential as an envelope.** The coefficient heights
`-v_p(n!)` of `exp` over `ℚ_[p]` have the line `n ↦ -n / (p - 1)` as their lower convex
envelope. -/
theorem isLowerConvexEnvelope_padicRealValuation_coeff_exp :
    IsLowerConvexEnvelope (fun n ↦ padicRealValuation p (coeff n (exp ℚ_[p])))
      fun n : ℕ ↦ ((-((p : ℝ) - 1)⁻¹ * n : ℝ) : WithTop ℝ) := by
  have h := (isLowerConvexEnvelope_shearedHeight (p := p)).add_affine 0 (-((p : ℝ) - 1)⁻¹)
  have ha : (fun n : ℕ ↦ shearedHeight p n + ((0 + -((p : ℝ) - 1)⁻¹ * n : ℝ) : WithTop ℝ)) =
      fun n ↦ padicRealValuation p (coeff n (exp ℚ_[p])) := by
    funext n
    rw [padicRealValuation_coeff_exp, shearedHeight, ← WithTop.coe_add, WithTop.coe_eq_coe]
    ring
  have hh : (fun n : ℕ ↦ (0 : ℕ → WithTop ℝ) n + ((0 + -((p : ℝ) - 1)⁻¹ * n : ℝ) : WithTop ℝ)) =
      fun n : ℕ ↦ ((-((p : ℝ) - 1)⁻¹ * n : ℝ) : WithTop ℝ) := by
    funext n
    rw [Pi.zero_apply, zero_add, zero_add]
  rwa [ha, hh] at h

/-- **The Newton polygon of the `p`-adic exponential** over `ℚ_[p]` is the ray
`n ↦ -n / (p - 1)`. -/
theorem newtonPolygon_exp :
    (exp ℚ_[p]).newtonPolygon (padicRealValuation p) =
      fun n : ℕ ↦ ((-((p : ℝ) - 1)⁻¹ * n : ℝ) : WithTop ℝ) := by
  rw [newtonPolygon_def,
    ← isLowerConvexEnvelope_padicRealValuation_coeff_exp.eq_lowerConvexEnvelope]

/-- Every index is a finite unit edge of the Newton polygon of `exp`. -/
theorem finiteEdges_newtonPolygon_exp :
    finiteEdges ((exp ℚ_[p]).newtonPolygon (padicRealValuation p)) = Set.univ := by
  ext n
  rw [mem_finiteEdges, newtonPolygon_exp]
  exact iff_of_true ⟨WithTop.coe_ne_top, WithTop.coe_ne_top⟩ (Set.mem_univ n)

/-- Every unit slope of the Newton polygon of `exp` is `-1 / (p - 1)`. -/
theorem unitSlope_newtonPolygon_exp (n : ℕ) :
    unitSlope ((exp ℚ_[p]).newtonPolygon (padicRealValuation p)) n = -((p : ℝ) - 1)⁻¹ := by
  rw [unitSlope_def, newtonPolygon_exp]
  simp only [WithTop.untop₀_coe, Nat.cast_add, Nat.cast_one]
  ring

/-- **The coefficients meet the polygon only at the origin.** The coefficient point of index `n`
of `exp` lies on its Newton polygon exactly when `n = 0`, although the polygon is a single ray. -/
theorem padicRealValuation_coeff_exp_eq_newtonPolygon_iff {n : ℕ} :
    padicRealValuation p (coeff n (exp ℚ_[p])) =
        (exp ℚ_[p]).newtonPolygon (padicRealValuation p) n ↔ n = 0 := by
  rw [padicRealValuation_coeff_exp, newtonPolygon_exp, WithTop.coe_eq_coe]
  refine ⟨fun h ↦ by_contra fun hn ↦ (multiplicity_factorial_lt_div p hn).ne ?_,
    fun h ↦ by simp [h]⟩
  rw [div_eq_inv_mul]
  linarith

/-- The coefficient heights of `exp` have lower linear growth `-1 / (p - 1)`. -/
theorem linearGrowthInf_padicRealValuation_coeff_exp :
    (linearGrowthInf fun n ↦ (padicRealValuation p (coeff n (exp ℚ_[p]))).toEReal) =
      ((-((p : ℝ) - 1)⁻¹ : ℝ) : EReal) := by
  rw [← isLowerConvexEnvelope_padicRealValuation_coeff_exp.linearGrowthInf_eq]
  simp_rw [WithTop.toEReal_coe, EReal.coe_mul, EReal.coe_natCast]
  exact linearGrowthInf_const_mul_self

/-! ### The radius -/

/-- **The radius of the `p`-adic exponential.** The intrinsic radius of `exp` over `ℚ_[p]` is
`p ^ (-1 / (p - 1))`. -/
theorem radius_exp : (exp ℚ_[p]).radius = ENNReal.ofReal (amiceRadius p 0) := by
  rw [(exp ℚ_[p]).radius_eq_ofReal_rpow (padicRealValuation p) one_lt_p
    (fun _ hx ↦ norm_eq_rpow_neg_padicRealValuation hx)
    linearGrowthInf_padicRealValuation_coeff_exp, amiceRadius_def, pow_zero, mul_one, one_div]

/-- The `p`-adic exponential is not entire. -/
theorem not_isEntire_exp : ¬(exp ℚ_[p]).IsEntire := by
  rw [← radius_eq_top_iff, radius_exp]
  exact ENNReal.ofReal_ne_top

/-- The `p`-adic exponential is restricted at the radius `r` exactly when
`|r| < p ^ (-1 / (p - 1))`. -/
theorem isRestricted_exp_iff {r : ℝ} :
    (exp ℚ_[p]).IsRestricted r ↔ |r| < amiceRadius p 0 := by
  have h := isRestricted_rescale_exp_iff (p := p) (K := ℚ_[p]) (x := 1) (abs_nonneg r)
  rw [rescale_one, RingHom.id_apply, norm_one, one_mul] at h
  rw [← isRestricted_abs_iff, h, amiceRadius_def, pow_zero, mul_one, one_div]

/-- **No restrictedness at the boundary.** The `p`-adic exponential is not restricted at its
radius `p ^ (-1 / (p - 1))`: its terms of degree `pᵏ` all have weighted norm
`p ^ (-1 / (p - 1))` there. -/
theorem not_isRestricted_exp_amiceRadius : ¬(exp ℚ_[p]).IsRestricted (amiceRadius p 0) :=
  fun h ↦ (isRestricted_exp_iff.mp h).ne (abs_of_pos (amiceRadius_pos 0))

/-! ### Convergence and zeros in extensions -/

variable {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [CompleteSpace L]

/-- **Convergence in extensions.** In every complete normed field `L` over `ℚ_[p]`, such as
`ℂ_[p]`, the exponential series `∑ xⁿ / n!` converges at `x` exactly when
`‖x‖ < p ^ (-1 / (p - 1))`. -/
theorem summable_exp_iff {x : L} :
    (Summable fun n ↦ coeff n (exp ℚ_[p]) • x ^ n) ↔ ‖x‖ < amiceRadius p 0 := by
  have := IsUltrametricDist.of_normedAlgebra ℚ_[p] (L := L)
  rw [summable_smul_pow_iff_isRestricted, isRestricted_exp_iff, abs_norm]

/-- In every complete densely normed field `L` over `ℚ_[p]`, such as `ℂ_[p]`, the pointwise
convergence radius of the exponential series is `p ^ (-1 / (p - 1))`. -/
theorem convergenceRadius_exp (L : Type*) [DenselyNormedField L] [NormedAlgebra ℚ_[p] L]
    [CompleteSpace L] :
    (exp ℚ_[p]).convergenceRadius L = ENNReal.ofReal (amiceRadius p 0) := by
  rw [convergenceRadius_eq_radius, radius_exp]

/-- On the open disc `‖x‖ < p ^ (-1 / (p - 1))` of a complete normed field over `ℚ_[p]`, the
formal exponential evaluates to the analytic exponential `NormedSpace.exp x`. -/
theorem evalAt_exp {x : L} (hx : ‖x‖ < amiceRadius p 0) :
    (exp ℚ_[p]).evalAt x = NormedSpace.exp x := by
  rw [evalAt_def, ← (expSeries_div_hasSum_exp_of_norm_lt hx).tsum_eq]
  congr 1 with n
  rw [coeff_exp_eq_inv_factorial, Algebra.smul_def, map_inv₀, map_natCast, inv_mul_eq_div]

/-- **No zeros in the disc of convergence.** On the open disc `‖x‖ < p ^ (-1 / (p - 1))` of a
complete normed field over `ℚ_[p]`, such as `ℂ_[p]`, the exponential series does not vanish:
its value has norm one. -/
theorem evalAt_exp_ne_zero {x : L} (hx : ‖x‖ < amiceRadius p 0) :
    (exp ℚ_[p]).evalAt x ≠ 0 := by
  rw [evalAt_exp hx, ← norm_ne_zero_iff, norm_exp_of_norm_lt hx]
  exact one_ne_zero

/-- For every radius `0 < r < p ^ (-1 / (p - 1))`, the zero multiset of the exponential series on
the closed disc of radius `r` of a complete normed field over `ℚ_[p]` is empty. -/
theorem zeroMultiset_exp {r : ℝ} (hr0 : 0 < r) (hr : r < amiceRadius p 0) :
    (exp ℚ_[p]).zeroMultiset r L = 0 := by
  have hres : (exp ℚ_[p]).IsRestricted r := isRestricted_exp_iff.mpr (by rwa [abs_of_pos hr0])
  have hne : exp ℚ_[p] ≠ 0 := fun h ↦ by simpa using congrArg (constantCoeff ·) h
  refine Multiset.eq_zero_of_forall_notMem fun x hx ↦ ?_
  obtain ⟨hxr, hx0⟩ := (hres.mem_zeroMultiset_iff hr0 hne).mp hx
  rw [evalAt_map_algebraMap] at hx0
  exact evalAt_exp_ne_zero (hxr.trans_lt hr) hx0

end TauCeti.NewtonPolygonExponentialExample

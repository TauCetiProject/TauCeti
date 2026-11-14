/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Radius
public import TauCeti.NumberTheory.Padics.Complex.Valuation
public import TauCeti.NumberTheory.Padics.LogGauge
public import TauCeti.RingTheory.PowerSeries.Convergence
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.NumberTheory.Padics.Factorial
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Convergence of power series in valued extensions and Newton slopes

Fix a normed field `K` and a complete ultrametric normed field extension `L / K` equipped with real
additive valuations `v_K`, `v_L` and a base `b > 1` recovering the norms via
`‖x‖ = b ^ (-(v x).untop₀)` for `x ≠ 0`. By `PowerSeries.summable_smul_pow_iff_isRestricted`, a
power series `f = ∑ aₙ Xⁿ ∈ K⟦X⟧` converges at a nonzero point `x : L` if and only if it is
restricted at `b ^ (-(v_L x).untop₀)`. Comparing with the asymptotic coefficient growth
`λ = liminf_{n → ∞} v_K(aₙ) / n` (`PowerSeries.radius_eq_exp_linearGrowthInf`), `f` converges at
every `x : L` with `-v_L(x) < λ` and diverges at every `x ≠ 0` with `λ < -v_L(x)`.

When `L` is densely normed — in particular for `ℂ_[p]` via `PadicComplex.denselyNormedField` — the
pointwise convergence radius `f.convergenceRadius L` coincides with the intrinsic radius
`f.radius = b ^ λ`, hence for admissible infinitely supported series with `b` to the supremum of
the finite Newton slopes.

When the nonzero norms of `L` form a discrete group `b ^ ℤ` — as in `ℚ_[p]` with `b = p` —
`f.convergenceRadius L` can be strictly smaller than `f.radius` for two distinct reasons:

1. *Fractional limiting slope:* if `λ = t ∈ ℝ \ ℤ` (so `⌊t⌋ < t`), no element of `L` has norm in
   `(b ^ ⌊t⌋, b ^ t]`, so `f.convergenceRadius L = b ^ ⌊t⌋ < b ^ t = f.radius`
   (`PowerSeries.convergenceRadius_eq_ofReal_zpow_floor`). In particular, for any `θ ≥ 0` the
   series `∑ₙ ϖ ^ ⌈θ n⌉₊ Xⁿ` over a uniformiser `ϖ` of valuation `1` has intrinsic radius `b ^ θ`,
   so `∑ₙ p ^ ⌈n / 2⌉₊ Xⁿ ∈ ℚ_[p]⟦X⟧` has intrinsic radius and `ℂ_[p]`-convergence radius `√p`
   while its `ℚ_[p]`-convergence radius is `1`.
2. *Boundary divergence at an attained norm:* if `f.radius = b ^ k` (`k ∈ ℤ`) and `f` is not
   restricted at `b ^ k`, the next smaller norm in `L` is `b ^ (k - 1)`, so
   `f.convergenceRadius L = b ^ (k - 1) < b ^ k = f.radius` (for example `∑ₙ Xⁿ` over `ℚ_[p]` has
   radius `1` and `ℚ_[p]`-convergence radius `p⁻¹`).

Finally, Legendre's formula gives the exact intrinsic radius `p ^ (-1 / (p - 1))` of the `p`-adic
exponential `PowerSeries.exp ℚ_[p]` (and `PowerSeries.exp ℂ_[p]`), its non-restrictedness on the
boundary `‖x‖ = p ^ (-1 / (p - 1))`, its `ℂ_[p]`-convergence radius, and its nonvanishing
throughout the open disc `‖x‖ < p ^ (-1 / (p - 1))`.

## Main results

* `PowerSeries.summable_smul_pow_iff_isRestricted_rpow`,
  `PowerSeries.hasSum_evalAt_of_neg_untop₀_lt_linearGrowthInf`, and
  `PowerSeries.not_summable_smul_pow_of_linearGrowthInf_lt_neg_untop₀`: valuation criteria for
  pointwise convergence and divergence in a complete ultrametric field extension.
* `PowerSeries.convergenceRadius_eq_exp_linearGrowthInf` and
  `PowerSeries.convergenceRadius_eq_exp_iSup_unitSlope_newtonPolygon`: Newton-slope formulas for
  `f.convergenceRadius L` over a complete ultrametric densely normed extension.
* `PowerSeries.convergenceRadius_eq_ofReal_zpow_floor` and
  `PowerSeries.convergenceRadius_padic_eq_ofReal_zpow_floor`: over a discretely normed extension
  with norm group `b ^ ℤ` (in particular `ℚ_[p]`), a non-integral limiting slope `t` gives
  `f.convergenceRadius L = ENNReal.ofReal (b ^ ⌊t⌋) < f.radius`.
* `PowerSeries.radius_mk_pow_ceil_mul`: for `v ϖ = 1` and `θ ≥ 0`, `∑ₙ ϖ ^ ⌈θ n⌉₊ Xⁿ` has
  intrinsic radius `ENNReal.ofReal (b ^ θ)`.
* `PowerSeries.radius_mk_padic_pow_ceil_half`,
  `PowerSeries.convergenceRadius_padic_mk_pow_ceil_half`, and
  `PowerSeries.convergenceRadius_padic_lt_radius_mk_pow_ceil_half`: `∑ₙ p ^ ⌈n / 2⌉₊ Xⁿ` has
  intrinsic and `ℂ_[p]`-convergence radius `√p`, `ℚ_[p]`-convergence radius `1`, and strict
  inequality between the two.
* `PowerSeries.not_isRestricted_exp_padic`, `PowerSeries.radius_exp_padic`,
  `PowerSeries.radius_exp_padicComplex`, and `PowerSeries.evalAt_exp_padic_ne_zero`: radius,
  boundary non-restrictedness, and nonvanishing of the `p`-adic exponential.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition, Graduate
  Texts in Mathematics 58, Springer, 1984, Chapter IV §§1, 4.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 5 §4.
-/

public section

open Filter TauCeti LinearGrowth
open scoped NNReal ENNReal Topology

namespace PowerSeries

section ValuedExtension

variable {K L : Type*} [NormedField K] [NormedField L] [NormedAlgebra K L]
  [IsUltrametricDist L] [CompleteSpace L] (f : K⟦X⟧)
  (vK : AddValuation K (WithTop ℝ)) (vL : AddValuation L (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hvK : ∀ x ≠ 0, ‖x‖ = b ^ (-(vK x).untop₀)) (hvL : ∀ y ≠ 0, ‖y‖ = b ^ (-(vL y).untop₀))

include hvL in
/-- At a nonzero point `x : L`, `f` converges if and only if `f` is restricted at the radius
`b ^ (-(vL x).untop₀)`. -/
theorem summable_smul_pow_iff_isRestricted_rpow {x : L} (hx : x ≠ 0) :
    Summable (fun n ↦ coeff n f • x ^ n) ↔ f.IsRestricted (b ^ (-(vL x).untop₀)) :=
  summable_smul_pow_iff_isRestricted (hvL x hx)

include hb hvK hvL in
/-- If `x : L` is zero or satisfies `-(vL x).untop₀ < liminf vK(aₙ) / n`, then `∑ₙ aₙ • xⁿ`
converges to `f.evalAt x`. -/
theorem hasSum_evalAt_of_neg_untop₀_lt_linearGrowthInf {x : L}
    (hx : x = 0 ∨ ((-(vL x).untop₀ : ℝ) : EReal) <
      linearGrowthInf fun n ↦ (vK (coeff n f)).toEReal) :
    HasSum (fun n ↦ coeff n f • x ^ n) (f.evalAt x) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [evalAt_def]
    exact (summable_smul_pow_zero f).hasSum
  have hlt := hx.resolve_left hx0
  have hb0 : 0 < b := zero_lt_one.trans hb
  apply hasSum_evalAt_of_lt_radius
  rw [radius_eq_exp_linearGrowthInf f vK hb hvK]
  have henorm : ‖x‖ₑ = EReal.exp (((-(vL x).untop₀ : ℝ) : EReal) * Real.log b) := by
    rw [← EReal.coe_mul, EReal.exp_coe, mul_comm, ← Real.rpow_def_of_pos hb0, ← hvL x hx0,
      eNorm_eq_nnNorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg x)]
    rfl
  rw [henorm, EReal.exp_lt_exp_iff, mul_comm _ (Real.log b : EReal),
    mul_comm _ (Real.log b : EReal), ← not_le, EReal.coe_mul_le_coe_mul_iff (Real.log_pos hb),
    not_le]
  exact hlt

omit [IsUltrametricDist L] [CompleteSpace L] in
include hb hvK hvL in
/-- If `x : L` is nonzero and `liminf vK(aₙ) / n < -(vL x).untop₀`, then `∑ₙ aₙ • xⁿ` diverges. -/
theorem not_summable_smul_pow_of_linearGrowthInf_lt_neg_untop₀ {x : L} (hx0 : x ≠ 0)
    (hx : (linearGrowthInf fun n ↦ (vK (coeff n f)).toEReal) < (-(vL x).untop₀ : ℝ)) :
    ¬Summable fun n ↦ coeff n f • x ^ n := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  apply not_summable_smul_pow_of_radius_lt
  rw [radius_eq_exp_linearGrowthInf f vK hb hvK]
  have henorm : ‖x‖ₑ = EReal.exp (((-(vL x).untop₀ : ℝ) : EReal) * Real.log b) := by
    rw [← EReal.coe_mul, EReal.exp_coe, mul_comm, ← Real.rpow_def_of_pos hb0, ← hvL x hx0,
      eNorm_eq_nnNorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg x)]
    rfl
  rw [henorm, EReal.exp_lt_exp_iff, mul_comm _ (Real.log b : EReal),
    mul_comm _ (Real.log b : EReal), ← not_le, EReal.coe_mul_le_coe_mul_iff (Real.log_pos hb),
    not_le]
  exact hx

end ValuedExtension

section DenseValuedExtension

variable {K : Type*} [NormedField K] (L : Type*) [DenselyNormedField L] [NormedAlgebra K L]
  [IsUltrametricDist L] [CompleteSpace L] (f : K⟦X⟧)
  (vK : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hvK : ∀ x ≠ 0, ‖x‖ = b ^ (-(vK x).untop₀))

include hb hvK in
/-- Over a complete ultrametric densely normed extension `L / K`, the pointwise convergence radius
is `b ^ λ` where `λ = liminf vK(aₙ) / n`. -/
theorem convergenceRadius_eq_exp_linearGrowthInf :
    f.convergenceRadius L =
      EReal.exp ((linearGrowthInf fun n ↦ (vK (coeff n f)).toEReal) * Real.log b) := by
  rw [convergenceRadius_eq_radius L f, radius_eq_exp_linearGrowthInf f vK hb hvK]

include hb hvK in
/-- Over a complete ultrametric densely normed extension `L / K`, for admissible infinitely
supported `f`, the pointwise convergence radius is `b` to the supremum of the finite Newton
slopes. -/
theorem convergenceRadius_eq_exp_iSup_unitSlope_newtonPolygon
    (hf : IsAdmissible fun n ↦ vK (coeff n f)) (hinf : {n | coeff n f ≠ 0}.Infinite) :
    f.convergenceRadius L = EReal.exp ((⨆ i : finiteEdges (f.newtonPolygon vK),
      (unitSlope (f.newtonPolygon vK) i : EReal)) * Real.log b) := by
  rw [convergenceRadius_eq_radius L f,
    radius_eq_exp_iSup_unitSlope_newtonPolygon f vK hb hvK hf hinf]

end DenseValuedExtension

section DiscreteValueGroup

/-- **Exact pointwise convergence radius over a discretely normed extension at a non-integral
exponent.** Suppose the nonzero norms of `L` are integer powers of `b > 1` and every `b ^ k`
(`k : ℤ`) is attained. If `f.radius = ENNReal.ofReal (b ^ t)` with `(⌊t⌋ : ℝ) < t`, then
`f.convergenceRadius L = ENNReal.ofReal (b ^ ⌊t⌋)`. -/
theorem convergenceRadius_eq_ofReal_zpow_floor {K L : Type*} [NormedField K] [NormedField L]
    [NormedAlgebra K L] [IsUltrametricDist L] [CompleteSpace L] {f : K⟦X⟧} {b t : ℝ}
    (hb : 1 < b) (hdisc : ∀ x : L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = b ^ k)
    (hsurj : ∀ k : ℤ, ∃ x : L, ‖x‖ = b ^ k)
    (hr : f.radius = ENNReal.ofReal (b ^ t)) (ht : (⌊t⌋ : ℝ) < t) :
    f.convergenceRadius L = ENNReal.ofReal (b ^ ⌊t⌋) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hlt : b ^ ⌊t⌋ < b ^ t := by
    rw [← Real.rpow_intCast]
    exact (Real.rpow_lt_rpow_left_iff hb).mpr ht
  refine convergenceRadius_eq_ofReal_of_forall_norm_le (hsurj ⌊t⌋)
    (Real.rpow_pos_of_pos hb0 t).le ?_ hr.le fun x hx ↦ ?_
  · rw [hr]
    exact (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hb0 t)).mpr hlt
  · rcases eq_or_ne x 0 with rfl | hx0
    · simpa using (zpow_pos hb0 ⌊t⌋).le
    obtain ⟨k, hk⟩ := hdisc x hx0
    rw [hk] at hx ⊢
    have hkt : (k : ℝ) ≤ t :=
      (Real.rpow_le_rpow_left_iff hb).mp (by rwa [Real.rpow_intCast])
    exact zpow_le_zpow_right₀ hb.le (Int.le_floor.mpr hkt)

/-- Under the hypotheses of `PowerSeries.convergenceRadius_eq_ofReal_zpow_floor`, the pointwise
convergence radius in `L` is strictly smaller than the intrinsic radius `f.radius`. -/
theorem convergenceRadius_lt_radius_of_zpow_floor {K L : Type*} [NormedField K] [NormedField L]
    [NormedAlgebra K L] [IsUltrametricDist L] [CompleteSpace L] {f : K⟦X⟧} {b t : ℝ}
    (hb : 1 < b) (hdisc : ∀ x : L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = b ^ k)
    (hsurj : ∀ k : ℤ, ∃ x : L, ‖x‖ = b ^ k)
    (hr : f.radius = ENNReal.ofReal (b ^ t)) (ht : (⌊t⌋ : ℝ) < t) :
    f.convergenceRadius L < f.radius := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  rw [convergenceRadius_eq_ofReal_zpow_floor hb hdisc hsurj hr ht, hr,
    ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hb0 t), ← Real.rpow_intCast]
  exact (Real.rpow_lt_rpow_left_iff hb).mpr ht

/-- For an element `ϖ : K` of valuation `1` under a real additive valuation `v` recovering the
norm in base `b > 1`, and any `θ ≥ 0`, the series `∑ₙ ϖ ^ ⌈θ n⌉₊ Xⁿ` has linear coefficient growth
`θ`. -/
theorem linearGrowthInf_addValuation_pow_ceil_mul {K : Type*} [DivisionRing K]
    (v : AddValuation K (WithTop ℝ)) {ϖ : K} (hϖ : v ϖ = 1) {θ : ℝ} (hθ : 0 ≤ θ) :
    (linearGrowthInf fun n : ℕ ↦ (v (ϖ ^ ⌈θ * (n : ℝ)⌉₊)).toEReal) = (θ : EReal) := by
  have hvpow (n : ℕ) : v (ϖ ^ n) = ((n : ℝ) : WithTop ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [_root_.pow_succ, v.map_mul, ih, hϖ, ← WithTop.coe_one, ← WithTop.coe_add, Nat.cast_add,
        Nat.cast_one]
  apply le_antisymm
  · rw [← linearGrowthInf_const_mul_self (a := (θ : EReal))]
    refine linearGrowthInf_le_of_eventually_le (b := ((1 : ℝ) : EReal)) (EReal.coe_ne_top 1)
      (.of_forall fun n ↦ ?_)
    rw [hvpow, WithTop.toEReal_coe]
    have hceil : (⌈θ * (n : ℝ)⌉₊ : ℝ) ≤ θ * (n : ℝ) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    exact_mod_cast hceil
  · refine le_linearGrowthInf_of_affine_le (c := 0) fun n ↦ ?_
    rw [hvpow, zero_add, WithTop.coe_le_coe]
    exact Nat.le_ceil (θ * (n : ℝ))

/-- For an element `ϖ : K` of valuation `1` in base `b > 1` and any `θ ≥ 0`, the series
`∑ₙ ϖ ^ ⌈θ n⌉₊ Xⁿ` has intrinsic radius `ENNReal.ofReal (b ^ θ)`. -/
theorem radius_mk_pow_ceil_mul {K : Type*} [NormedDivisionRing K]
    (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {ϖ : K} (hϖ : v ϖ = 1) {θ : ℝ} (hθ : 0 ≤ θ) :
    (mk fun n : ℕ ↦ ϖ ^ ⌈θ * (n : ℝ)⌉₊).radius = ENNReal.ofReal (b ^ θ) := by
  refine radius_eq_ofReal_rpow _ v hb hv ?_
  simpa using linearGrowthInf_addValuation_pow_ceil_mul v hϖ hθ

end DiscreteValueGroup

section Padics

variable {p : ℕ} [Fact p.Prime]

/-- Every nonzero element of `ℚ_[p]` has norm `p ^ k` for some `k : ℤ`. -/
private theorem padic_exists_int_norm_eq_zpow {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = (p : ℝ) ^ k :=
  ⟨-x.valuation, Padic.norm_eq_zpow_neg_valuation hx⟩

/-- Every integer power `p ^ k` (`k : ℤ`) is the norm of `(p : ℚ_[p]) ^ (-k)` in `ℚ_[p]`. -/
private theorem padic_exists_norm_eq_zpow (k : ℤ) :
    ∃ x : ℚ_[p], ‖x‖ = (p : ℝ) ^ k :=
  ⟨(p : ℚ_[p]) ^ (-k), by rw [norm_zpow, Padic.norm_p, inv_zpow, zpow_neg, inv_inv]⟩

/-- For any power series `f ∈ ℚ_[p]⟦X⟧`, its pointwise convergence radius in `ℂ_[p]` equals its
intrinsic radius `f.radius`. -/
@[simp]
theorem convergenceRadius_padicComplex (f : ℚ_[p]⟦X⟧) :
    f.convergenceRadius ℂ_[p] = f.radius :=
  convergenceRadius_eq_radius ℂ_[p] f

/-- For `f ∈ ℚ_[p]⟦X⟧` whose `p`-adic coefficient valuations have non-integral real lower linear
growth `t` (`⌊t⌋ < t`), the pointwise convergence radius in `ℚ_[p]` is `p ^ ⌊t⌋`. -/
theorem convergenceRadius_padic_eq_ofReal_zpow_floor {f : ℚ_[p]⟦X⟧} {t : ℝ}
    (ht_growth : (linearGrowthInf fun n ↦ (padicRealValuation p (coeff n f)).toEReal) = t)
    (ht : (⌊t⌋ : ℝ) < t) :
    f.convergenceRadius ℚ_[p] = ENNReal.ofReal ((p : ℝ) ^ ⌊t⌋) := by
  have hp1 : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  exact convergenceRadius_eq_ofReal_zpow_floor hp1 (fun _ ↦ padic_exists_int_norm_eq_zpow)
    padic_exists_norm_eq_zpow
    (radius_eq_ofReal_rpow f (padicRealValuation p) hp1
      (fun _ ↦ norm_eq_rpow_neg_padicRealValuation) ht_growth) ht

/-- **Intrinsic radius of `∑ₙ p ^ ⌈n / 2⌉₊ Xⁿ`.** In `ℚ_[p]⟦X⟧`, the series
`∑ₙ p ^ ⌈n / 2⌉₊ Xⁿ` has intrinsic radius `√p`. -/
theorem radius_mk_padic_pow_ceil_half :
    (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).radius = ENNReal.ofReal (Real.sqrt p) := by
  have hp1 : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  have heq : (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊) =
      mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(1 / 2 : ℝ) * (n : ℝ)⌉₊ := by
    ext n
    simp [div_eq_inv_mul]
  rw [heq, radius_mk_pow_ceil_mul (padicRealValuation p) hp1
    (fun _ ↦ norm_eq_rpow_neg_padicRealValuation) padicRealValuation_p (by positivity),
    Real.sqrt_eq_rpow]

/-- In `ℂ_[p]`, the pointwise convergence radius of `∑ₙ p ^ ⌈n / 2⌉₊ Xⁿ` equals `√p`. -/
theorem convergenceRadius_padicComplex_mk_pow_ceil_half :
    (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).convergenceRadius ℂ_[p] =
      ENNReal.ofReal (Real.sqrt p) := by
  rw [convergenceRadius_padicComplex, radius_mk_padic_pow_ceil_half]

/-- **Pointwise convergence radius of `∑ₙ p ^ ⌈n / 2⌉₊ Xⁿ` in `ℚ_[p]`.** Because the nonzero
norms of `ℚ_[p]` are integer powers of `p`, the supremum of norms of convergence points in `ℚ_[p]`
is `1`. -/
theorem convergenceRadius_padic_mk_pow_ceil_half :
    (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).convergenceRadius ℚ_[p] = 1 := by
  have hp1 : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  have hfloor : (⌊(1 / 2 : ℝ)⌋ : ℤ) = 0 := by
    rw [Int.floor_eq_iff]
    norm_num
  have hr : (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).radius =
      ENNReal.ofReal ((p : ℝ) ^ (1 / 2 : ℝ)) := by
    rw [radius_mk_padic_pow_ceil_half, Real.sqrt_eq_rpow]
  rw [convergenceRadius_eq_ofReal_zpow_floor hp1 (fun _ ↦ padic_exists_int_norm_eq_zpow)
    padic_exists_norm_eq_zpow hr (by rw [hfloor]; norm_num), hfloor, zpow_zero, ENNReal.ofReal_one]

/-- **Strict inequality between pointwise and intrinsic radius over `ℚ_[p]`.** For
`f = ∑ₙ p ^ ⌈n / 2⌉₊ Xⁿ ∈ ℚ_[p]⟦X⟧`, `f.convergenceRadius ℚ_[p] < f.radius`. -/
theorem convergenceRadius_padic_lt_radius_mk_pow_ceil_half :
    (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).convergenceRadius ℚ_[p] <
      (mk fun n : ℕ ↦ (p : ℚ_[p]) ^ ⌈(n : ℝ) / 2⌉₊).radius := by
  have hp1 : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  rw [convergenceRadius_padic_mk_pow_ceil_half, radius_mk_padic_pow_ceil_half,
    ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (Real.sqrt_pos.mpr (zero_lt_one.trans hp1)),
    Real.sqrt_eq_rpow]
  exact Real.one_lt_rpow hp1 (by positivity)

/-- The geometric series `∑ₙ Xⁿ` over `ℚ_[p]` has pointwise convergence radius `p⁻¹`, strictly
below its intrinsic radius `1`, because it is not restricted on the unit sphere and the largest
smaller norm in `ℚ_[p]` is `p⁻¹`. -/
theorem convergenceRadius_padic_mk_one :
    (mk 1 : ℚ_[p]⟦X⟧).convergenceRadius ℚ_[p] = (p : ℝ≥0∞)⁻¹ := by
  have hp1 : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  have hrad : (mk 1 : ℚ_[p]⟦X⟧).radius = 1 := by
    have hmk : (mk 1 : ℚ_[p]⟦X⟧) = mk fun n ↦ (1 : ℚ_[p]) ^ n := by
      ext n
      simp
    rw [hmk, radius_mk_pow]
    simp
  have heq := convergenceRadius_eq_ofReal_of_not_isRestricted (A := ℚ_[p]) (f := mk 1)
    (r := (p : ℝ)⁻¹) (s := 1) ⟨p, Padic.norm_p⟩ zero_le_one
    (by rw [hrad, ← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff zero_lt_one];
        exact inv_lt_one_of_one_lt₀ hp1)
    (by simp [hrad]) TauCeti.PowerSeries.not_isRestricted_mk_one fun x hx ↦ ?_
  · rw [heq, ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp [hp0.le]
    obtain ⟨k, hk⟩ := padic_exists_int_norm_eq_zpow hx0
    rw [hk] at hx ⊢
    have hk0 : k < 0 := by
      by_contra hge
      exact hx.not_ge (one_le_zpow₀ hp1.le (not_lt.mp hge))
    have hk1 : k ≤ -1 := by omega
    simpa [zpow_neg_one] using zpow_le_zpow_right₀ hp1.le hk1

section Exp

/-- **The `p`-adic exponential is not restricted at its boundary radius `p ^ (-1 / (p - 1))`.**
Along prime powers `n = p ^ k`, Legendre's formula gives `((p - 1) v_p((p ^ k)!)) = p ^ k - 1`, so
the weighted coefficient norm equals `p ^ (-1 / (p - 1)) ≠ 0` for every `k`. -/
theorem not_isRestricted_exp_padic :
    ¬(exp ℚ_[p]).IsRestricted ((p : ℝ) ^ (-1 / ((p : ℝ) - 1))) := by
  have hp := (Fact.out : p.Prime)
  have hp1 : (1 : ℝ) < p := mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  set r₀ : ℝ := (p : ℝ) ^ (-1 / ((p : ℝ) - 1))
  have hr₀ : 0 < r₀ := Real.rpow_pos_of_pos hp0 _
  intro hf
  have htend := ((isRestricted_iff' r₀ (exp ℚ_[p])).mp hf).comp
    (tendsto_pow_atTop_atTop_of_one_lt hp.one_lt)
  have hconst : ((fun t ↦ ‖coeff t (exp ℚ_[p])‖ * r₀ ^ t) ∘ fun k ↦ p ^ k) = fun _ ↦ r₀ := by
    ext k
    have hleg : ((p : ℝ) - 1) * (padicValNat p (p ^ k).factorial : ℝ) = (p : ℝ) ^ k - 1 := by
      have hc := congrArg (Nat.cast : ℕ → ℝ) (sub_one_mul_padicValNat_factorial_pow p k)
      rwa [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one,
        Nat.cast_sub (Nat.one_le_pow k p hp.pos), Nat.cast_pow, Nat.cast_one] at hc
    have hval : (padicValNat p (p ^ k).factorial : ℝ) = ((p : ℝ) ^ k - 1) / ((p : ℝ) - 1) := by
      rw [eq_div_iff (sub_pos.mpr hp1).ne', mul_comm, hleg]
    have hnorm : ‖coeff (p ^ k) (exp ℚ_[p])‖ =
        (p : ℝ) ^ (((p : ℝ) ^ k - 1) / ((p : ℝ) - 1)) := by
      rw [coeff_exp, one_div, map_inv₀, map_natCast, norm_inv,
        Padic.norm_natCast_eq_zpow (Nat.factorial_ne_zero _), ← zpow_neg, neg_neg, zpow_natCast,
        ← Real.rpow_natCast, hval]
    have hpow : r₀ ^ (p ^ k) = (p : ℝ) ^ (-(p : ℝ) ^ k / ((p : ℝ) - 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, Nat.cast_pow]
      congr 1
      ring
    rw [Function.comp_apply, hnorm, hpow, ← Real.rpow_add hp0]
    congr 1
    ring
  rw [hconst] at htend
  exact hr₀.ne' (tendsto_nhds_unique tendsto_const_nhds htend)

/-- **Radius of the `p`-adic exponential.** In `ℚ_[p]⟦X⟧`, `PowerSeries.exp ℚ_[p]` has intrinsic
radius `p ^ (-1 / (p - 1))`. -/
theorem radius_exp_padic :
    (exp ℚ_[p]).radius = ENNReal.ofReal ((p : ℝ) ^ (-1 / ((p : ℝ) - 1))) := by
  have hp1 : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  set r₀ : ℝ := (p : ℝ) ^ (-1 / ((p : ℝ) - 1))
  have hr₀ : 0 < r₀ := Real.rpow_pos_of_pos hp0 _
  apply le_antisymm
  · refine le_of_not_gt fun hlt ↦ not_isRestricted_exp_padic (p := p) (isRestricted_of_lt_radius ?_)
    have heq : ENNReal.ofReal r₀ = ‖r₀‖ₑ := by
      rw [eNorm_eq_nnNorm, ENNReal.ofReal_eq_coe_nnreal hr₀.le]
      congr 1
      ext
      simp [Real.norm_eq_abs, abs_of_pos hr₀]
    rwa [heq] at hlt
  · rw [ENNReal.ofReal_eq_coe_nnreal hr₀.le]
    refine le_radius_of_bound 1 fun n ↦ ?_
    have hfn : (n.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hpow :
        ((NNReal.mk r₀ hr₀.le : ℝ≥0) : ℝ) ^ n = (p : ℝ) ^ (-((n : ℝ) / ((p : ℝ) - 1))) := by
      rw [NNReal.coe_mk, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
      congr 1
      ring
    rw [coeff_exp, one_div, map_inv₀, map_natCast, norm_inv, hpow]
    exact (inv_mul_le_iff₀ (norm_pos_iff.mpr hfn)).mpr
      (by simpa using Padic.rpow_neg_div_le_norm_factorial (p := p) n)

/-- In `ℂ_[p]⟦X⟧`, `PowerSeries.exp ℂ_[p]` has intrinsic radius `p ^ (-1 / (p - 1))`. -/
theorem radius_exp_padicComplex :
    (exp ℂ_[p]).radius = ENNReal.ofReal ((p : ℝ) ^ (-1 / ((p : ℝ) - 1))) := by
  rw [← map_exp (algebraMap ℚ_[p] ℂ_[p]), radius_map _ (norm_algebraMap' ℂ_[p]), radius_exp_padic]

/-- The `p`-adic exponential series is not entire. -/
theorem not_isEntire_exp_padic : ¬(exp ℚ_[p]).IsEntire := by
  rw [← radius_eq_top_iff, radius_exp_padic]
  exact ENNReal.ofReal_ne_top

/-- In `ℂ_[p]`, the pointwise convergence radius of `PowerSeries.exp ℚ_[p]` is
`p ^ (-1 / (p - 1))`. -/
theorem convergenceRadius_padicComplex_exp :
    (exp ℚ_[p]).convergenceRadius ℂ_[p] = ENNReal.ofReal ((p : ℝ) ^ (-1 / ((p : ℝ) - 1))) := by
  rw [convergenceRadius_padicComplex, radius_exp_padic]

/-- **Nonvanishing of the `p`-adic exponential on its disc of convergence.** In any nontrivial
complete ultrametric normed `ℚ_[p]`-algebra `A` (such as `ℚ_[p]` or `ℂ_[p]`),
`(exp ℚ_[p]).evalAt x` is nonzero for every `x : A` with `‖x‖ < p ^ (-1 / (p - 1))`. -/
theorem evalAt_exp_padic_ne_zero {A : Type*} [NormedRing A] [Algebra ℚ_[p] A]
    [IsBoundedSMul ℚ_[p] A] [IsUltrametricDist A] [CompleteSpace A] [Nontrivial A] {x : A}
    (hx : ‖x‖ < (p : ℝ) ^ (-1 / ((p : ℝ) - 1))) :
    (exp ℚ_[p]).evalAt x ≠ 0 := by
  apply evalAt_exp_ne_zero_of_lt_radius
  have hr : 0 ≤ (p : ℝ) ^ (-1 / ((p : ℝ) - 1)) := (norm_nonneg x).trans hx.le
  rw [radius_exp_padic, eNorm_eq_nnNorm, ENNReal.ofReal_eq_coe_nnreal hr, ENNReal.coe_lt_coe,
    ← NNReal.coe_lt_coe, coe_nnNorm, NNReal.coe_mk]
  exact hx

end Exp

end Padics

end PowerSeries

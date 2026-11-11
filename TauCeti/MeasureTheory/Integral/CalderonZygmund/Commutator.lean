/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.MeasureTheory.Integral.CalderonZygmund.BoundedMeanOscillation
public import TauCeti.MeasureTheory.Integral.JohnNirenberg
public import TauCeti.MeasureTheory.Integral.SharpMaximalFunction
public import TauCeti.MeasureTheory.Integral.UncenteredMaximalFunction

/-!
# The sharp maximal function of a commutator with a singular integral

Let `T` be a Calderón–Zygmund operator and `b` a function of bounded mean oscillation. The
**commutator** `[b, T] f = b T f - T (b f)` is bounded on `Lᵖ` for `1 < p < ∞` with norm
controlled by `‖b‖_{BMO}` (Coifman–Rochberg–Weiss), although multiplication by `b` alone is not.
The engine of the proof is a pointwise bound on its sharp maximal function: for `r > s ≥ 1`,

`([b, T] f)^# (x) ≤ C ‖b‖_{BMO} ((M |T f|^r)(x)^(1/r) + (M |f|^r)(x)^(1/r))`,

where `g^#` is the sharp maximal function (`TauCeti.sharpMaximalFunction`) and `M` the uncentred
Hardy–Littlewood maximal function (`TauCeti.uncenteredMaximalFunction`). This file proves the
pointwise bound. Since `M` is bounded on `L^{p/r}` for `p > r`, the Fefferman–Stein inequality
`‖g‖_p ≤ C ‖g^#‖_p` is what turns it into an `Lᵖ` bound for the commutator.

Here `μ` is an additive Haar measure on a finite-dimensional real normed space `V` of dimension
`n`, and `T` is a bounded linear operator on `L²(μ)` such that, whenever `g` vanishes on a ball,
`T g x = ∫ K x y (g y) dy` for almost every `x` in that ball. The kernel satisfies the standard
smoothness estimate in the first variable,

`‖K x y - K x' y‖ ≤ A |x - x'| ^ δ |y - x'| ^ (-(n + δ))` whenever `2 |x - x'| < |y - x'|`,

with `δ > 0`, and `T` is bounded in the `Lˢ` norm on `L²` for some `1 ≤ s`. The multiplier `b`
is bounded, so that `b f ∈ L²` and the commutator is defined on `L²`; the constants do not depend
on `‖b‖_∞`. The statement `TauCeti.exists_sharpMaximalFunction_commutator_le` measures `b` by a
bound `M` for its `q`-th mean oscillation `(⨍_B |b - b_B|^q)^(1/q)` on every ball, where
`q⁻¹ + r⁻¹ = s⁻¹`. On Euclidean space, the `Lᵖ` form of the John–Nirenberg inequality bounds `M`
by a multiple of `‖b‖_{BMO}` (`TauCeti.exists_sharpMaximalFunction_commutator_le_bmoSeminorm`).

## The argument

Fix a ball `B = B(c, R)` containing `x`, let `2B = B(c, 2R)` and `a₀ = b_{2B}`. Split
`(b - a₀) f = g₁ + g₂` with `g₁` the part on `2B`. Since `T` is linear,

`[b, T] f = (b - a₀) T f - T g₁ - T g₂`,

and its mean oscillation on `B` is at most twice its mean distance from the constant
`-∫ K c y (g₂ y) dy`.

* On `B`, Hölder's inequality with exponents `q` and `r` bounds the mean of `|b - a₀| |T f|` by
  `(M + |b_B - a₀|) (⨍_B |T f|^r)^(1/r)`, and `|b_B - b_{2B}| ≤ 2ⁿ M`.
* The `Lˢ` bound of `T` and Hölder's inequality on `2B` bound the mean of `|T g₁|` on `B` by
  `N 2^(n/s) M (⨍_{2B} |f|^r)^(1/r)`.
* For `z ∈ B` the smoothness of the kernel bounds `|T g₂ z - ∫ K c y (g₂ y) dy|` by
  `A R^δ ∫_{|y - c| ≥ 2R} |y - c|^(-(n + δ)) |b - a₀| |f|`. On the dyadic annulus
  `2ᵏ · 2R ≤ |y - c| < 2ᵏ⁺¹ · 2R` the average of `b` differs from `a₀` by at most `(k + 1) 2ⁿ M`,
  so the annulus contributes `2ⁿ |B(0, 1)| (2^(-δ))^(k + 1) (1 + (k + 1) 2ⁿ) M (M |f|^r)(x)^(1/r)`,
  and these sum because `δ > 0`.

## Main declarations

* `TauCeti.exists_sharpMaximalFunction_commutator_le`: the pointwise bound for `b` whose `q`-th
  mean oscillation on every ball is at most `M ^ q`.
* `TauCeti.exists_sharpMaximalFunction_commutator_le_bmoSeminorm`: the pointwise bound in terms of
  `‖b‖_{BMO}` on Euclidean space.

## References

* R. R. Coifman, R. Rochberg, G. Weiss, *Factorization theorems for Hardy spaces in several
  variables*, Ann. of Math. **103** (1976), 611–635.
* J.-O. Strömberg, *Bounded mean oscillation with Orlicz norms and duality of Hardy spaces*,
  Indiana Univ. Math. J. **28** (1979), 511–544 (the sharp maximal function proof).
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 3.5.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal

section General

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A bound `M ^ q` on the `q`-th mean oscillation, `q ≥ 1`, bounds the mean oscillation by `M`. -/
private theorem setLAverage_enorm_sub_setAverage_le_of_rpow {b : X → ℝ} {S : Set X} {q : ℝ}
    (hq : 1 ≤ q) (hb : AEStronglyMeasurable b (μ.restrict S)) {M : ℝ≥0∞}
    (hM : ⨍⁻ y in S, ‖b y - ⨍ z in S, b z ∂μ‖ₑ ^ q ∂μ ≤ M ^ q) :
    ⨍⁻ y in S, ‖b y - ⨍ z in S, b z ∂μ‖ₑ ∂μ ≤ M := by
  refine (laverage_le_laverage_rpow_rpow
    (hb.sub (aestronglyMeasurable_const (b := ⨍ z in S, b z ∂μ))).enorm hq).trans ?_
  calc (⨍⁻ y in S, ‖b y - ⨍ z in S, b z ∂μ‖ₑ ^ q ∂μ) ^ (1 / q) ≤ (M ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hM (by positivity)
    _ = M := by rw [one_div, ENNReal.rpow_rpow_inv (one_pos.trans_le hq).ne']

/-- **The weighted mean of `‖b - a‖`.** If the `q`-th mean oscillation of `b` on `S` is at most
`M ^ q`, `q⁻¹ + r⁻¹ = s⁻¹` and `1 ≤ s`, then for every constant `a` and every `ψ ≥ 0`,
`⨍_S ‖b - a‖ ψ ≤ (M + ‖b_S - a‖) (⨍_S ψ ^ r) ^ (1 / r)`. -/
private theorem setLAverage_enorm_sub_mul_le {b : X → ℝ} {S : Set X} {q r s : ℝ}
    (hqrs : q.HolderTriple r s) (hs : 1 ≤ s) (hb : AEStronglyMeasurable b (μ.restrict S))
    {M : ℝ≥0∞} (hM : ⨍⁻ y in S, ‖b y - ⨍ z in S, b z ∂μ‖ₑ ^ q ∂μ ≤ M ^ q) {ψ : X → ℝ≥0∞}
    (hψ : AEMeasurable ψ (μ.restrict S)) (a : ℝ) :
    ⨍⁻ y in S, ‖b y - a‖ₑ * ψ y ∂μ ≤
      (M + ‖(⨍ z in S, b z ∂μ) - a‖ₑ) * (⨍⁻ y in S, ψ y ^ r ∂μ) ^ (1 / r) := by
  set bS := ⨍ z in S, b z ∂μ
  set κ := ‖bS - a‖ₑ
  have hr : 1 ≤ r := hs.trans hqrs.symm.lt.le
  have hu : AEMeasurable (fun y => ‖b y - bS‖ₑ) (μ.restrict S) :=
    (hb.sub (aestronglyMeasurable_const (b := bS))).enorm
  have h₁ : ⨍⁻ y in S, ‖b y - bS‖ₑ * ψ y ∂μ ≤ M * (⨍⁻ y in S, ψ y ^ r ∂μ) ^ (1 / r) := by
    refine (laverage_mul_le_Lq_mul_Lr hu hψ hqrs hs).trans ?_
    gcongr
    calc (⨍⁻ y in S, ‖b y - bS‖ₑ ^ q ∂μ) ^ (1 / q) ≤ (M ^ q) ^ (1 / q) :=
          ENNReal.rpow_le_rpow hM (by have := hqrs.pos; positivity)
      _ = M := by rw [one_div, ENNReal.rpow_rpow_inv hqrs.pos.ne']
  have h₂ := laverage_le_laverage_rpow_rpow hψ hr
  calc ⨍⁻ y in S, ‖b y - a‖ₑ * ψ y ∂μ
      ≤ ⨍⁻ y in S, (‖b y - bS‖ₑ * ψ y + κ * ψ y) ∂μ := by
        refine setLAverage_mono_ae S (.of_forall fun y => ?_)
        simp only [← add_mul]
        gcongr
        calc ‖b y - a‖ₑ = ‖(b y - bS) + (bS - a)‖ₑ := by ring_nf
          _ ≤ _ := enorm_add_le _ _
    _ = ⨍⁻ y in S, ‖b y - bS‖ₑ * ψ y ∂μ + κ * ⨍⁻ y in S, ψ y ∂μ := by
        simp only [laverage_eq']
        rw [lintegral_add_left' (f := fun y => ‖b y - bS‖ₑ * ψ y) ((hu.mul hψ).smul_measure _),
          lintegral_const_mul' _ _ enorm_ne_top]
    _ ≤ M * (⨍⁻ y in S, ψ y ^ r ∂μ) ^ (1 / r) + κ * (⨍⁻ y in S, ψ y ^ r ∂μ) ^ (1 / r) := by
        gcongr
    _ = _ := by rw [add_mul]

/-- The average of `u + v + κ` over a set of finite positive measure. -/
private theorem setLAverage_add_add_const {S : Set X} (h0 : μ S ≠ 0) (ht : μ S ≠ ∞)
    {u v : X → ℝ≥0∞} (hu : AEMeasurable u (μ.restrict S)) (κ : ℝ≥0∞) :
    ⨍⁻ x in S, (u x + v x + κ) ∂μ = ⨍⁻ x in S, u x ∂μ + ⨍⁻ x in S, v x ∂μ + κ := by
  rw [setLAverage_eq, setLAverage_eq, setLAverage_eq, lintegral_add_right _ measurable_const,
    lintegral_add_left' hu, setLIntegral_const, ENNReal.add_div, ENNReal.add_div,
    ENNReal.mul_div_cancel_right h0 ht]

end General

section Haar

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

/-- Doubling the radius of a ball multiplies its Haar measure by `2ⁿ`. -/
private theorem measure_ball_two_mul (c : V) {ρ : ℝ} (hρ : 0 < ρ) :
    μ (ball c (2 * ρ)) = 2 ^ finrank ℝ V * μ (ball c ρ) := by
  rw [Measure.addHaar_ball_of_pos μ c (by positivity), Measure.addHaar_ball_of_pos μ c hρ,
    mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat, mul_assoc]

/-- The weight of the `k`-th dyadic annulus in the tail estimate:
`R^δ (2ᵏ · 2R)^(-(n + δ)) (2ᵏ⁺¹ · 2R)ⁿ = 2ⁿ (2^(-δ))^(k + 1)`. -/
private theorem rpow_mul_rpow_mul_pow_eq {R : ℝ} (hR : 0 < R) (n : ℕ) (δ : ℝ) (k : ℕ) :
    R ^ δ * (2 ^ k * (2 * R)) ^ (-((n : ℝ) + δ)) * (2 ^ (k + 1) * (2 * R)) ^ n =
      2 ^ n * ((2 : ℝ) ^ (-δ)) ^ (k + 1) := by
  set t : ℝ := 2 ^ (k + 1) * R
  have ht : 0 < t := by positivity
  have h₁ : 2 ^ k * (2 * R) = t := by simp only [t]; ring
  have h₂ : 2 ^ (k + 1) * (2 * R) = 2 * t := by simp only [t]; ring
  have h₃ : t ^ (-((n : ℝ) + δ)) * t ^ n = t ^ (-δ) := by
    rw [neg_add, Real.rpow_add ht, Real.rpow_neg ht.le (n : ℝ), Real.rpow_natCast,
      mul_right_comm, inv_mul_cancel₀ (pow_pos ht n).ne', one_mul]
  have h₄ : R ^ δ * t ^ (-δ) = ((2 : ℝ) ^ (-δ)) ^ (k + 1) := by
    rw [Real.mul_rpow (by positivity) hR.le]
    calc R ^ δ * ((2 ^ (k + 1)) ^ (-δ) * R ^ (-δ)) = (2 ^ (k + 1)) ^ (-δ) * (R ^ δ * R ^ (-δ)) := by
          ring
      _ = ((2 : ℝ) ^ (k + 1)) ^ (-δ) := by
          rw [← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero, mul_one]
      _ = ((2 : ℝ) ^ (-δ)) ^ (k + 1) := by
          rw [← Real.rpow_natCast (2 : ℝ) (k + 1), ← Real.rpow_mul zero_le_two, mul_comm,
            Real.rpow_mul zero_le_two, Real.rpow_natCast]
  rw [h₁, h₂, mul_pow]
  calc R ^ δ * t ^ (-((n : ℝ) + δ)) * (2 ^ n * t ^ n)
      = 2 ^ n * (R ^ δ * (t ^ (-((n : ℝ) + δ)) * t ^ n)) := by ring
    _ = _ := by rw [h₃, h₄]

/-- The constant `∑ₖ (2^(-δ))^(k + 1) (1 + (k + 1) 2ⁿ)` of the tail estimate is finite for
`δ > 0`. -/
private theorem tsum_ofReal_mul_ne_top (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∑' k : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ (k + 1)) * (1 + (k + 1) * 2 ^ n) ≠ ∞ := by
  set ε : ℝ := (2 : ℝ) ^ (-δ)
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  set g : ℕ → ℝ := fun k => ε ^ (k + 1) * (1 + (k + 1) * 2 ^ n)
  have hg : Summable g := by
    have h₀ : Summable fun k : ℕ => ε ^ (k + 1) :=
      (summable_geometric_of_lt_one hε0 hε1).mul_left ε |>.congr fun k => by ring
    have h₁ : Summable fun k : ℕ => (k : ℝ) ^ 1 * ε ^ k :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_of_nonneg hε0])
    have h₁' : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ 1 * ε ^ (k + 1) :=
      (summable_nat_add_iff (f := fun k : ℕ => (k : ℝ) ^ 1 * ε ^ k) 1).2 h₁
    refine (h₀.add (h₁'.mul_left (2 ^ n))).congr fun k => ?_
    simp only [g, Nat.cast_add, Nat.cast_one, pow_one]
    ring
  have heq : ∀ k : ℕ, ENNReal.ofReal (ε ^ (k + 1)) * (1 + (k + 1) * 2 ^ n) =
      ENNReal.ofReal (g k) := fun k => by
    simp only [g]
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show (1 : ℝ) + (k + 1) * 2 ^ n = ((1 + (k + 1) * 2 ^ n : ℕ) : ℝ) by push_cast; ring,
      ENNReal.ofReal_natCast]
    push_cast
    ring
  simp only [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hg]
  exact ENNReal.ofReal_ne_top

/-- **One dyadic annulus of the tail estimate.** Under the hypotheses of the tail estimate, the
integral over `2ᵏ · 2R ≤ |y - c| < 2ᵏ⁺¹ · 2R` is at most
`2ⁿ |B(0, 1)| (2^(-δ))^(k + 1) (1 + (k + 1) 2ⁿ) M (M ψ^r)(x)^(1/r)`: the weight is at most its
value on the inner sphere, and the average of `b` over `B(c, 2ᵏ⁺¹ · 2R)` is within
`(k + 1) 2ⁿ M` of `b_{B(c, 2R)}`. -/
private theorem setLIntegral_annulus_ofReal_mul_le {b : V → ℝ} (hb : AEStronglyMeasurable b μ)
    {q r s : ℝ} (hqrs : q.HolderTriple r s) (hs : 1 ≤ s) {M : ℝ≥0∞}
    (hM : ∀ c ρ, ⨍⁻ y in ball c ρ, ‖b y - ⨍ z in ball c ρ, b z ∂μ‖ₑ ^ q ∂μ ≤ M ^ q)
    {ψ : V → ℝ≥0∞} (hψ : AEMeasurable ψ μ) {δ : ℝ} (hδ : 0 < δ) {c x : V} {R : ℝ}
    (hx : x ∈ ball c R) (k : ℕ) :
    ∫⁻ y in ball c (2 ^ (k + 1) * (2 * R)) \ ball c (2 ^ k * (2 * R)),
        ENNReal.ofReal (R ^ δ * dist y c ^ (-((finrank ℝ V : ℝ) + δ))) *
          (‖b y - ⨍ z in ball c (2 * R), b z ∂μ‖ₑ * ψ y) ∂μ ≤
      2 ^ finrank ℝ V * μ (ball 0 1) *
        (ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ (k + 1)) * (1 + (k + 1) * 2 ^ finrank ℝ V)) * M *
        uncenteredMaximalFunction μ (fun y => ψ y ^ r) x ^ (1 / r) := by
  set n := finrank ℝ V
  have hR : 0 < R := pos_of_mem_ball hx
  set ρ := 2 * R with hρdef
  have hρ : 0 < ρ := by positivity
  set a₀ := ⨍ z in ball c ρ, b z ∂μ
  set Φ : V → ℝ≥0∞ := fun y => ‖b y - a₀‖ₑ * ψ y
  set Mx := uncenteredMaximalFunction μ (fun y => ψ y ^ r) x ^ (1 / r)
  have hr0 : 0 < r := hqrs.symm.pos
  have hM₁ : ∀ c ρ, ⨍⁻ y in ball c ρ, ‖b y - ⨍ z in ball c ρ, b z ∂μ‖ₑ ∂μ ≤ M := fun c ρ =>
    setLAverage_enorm_sub_setAverage_le_of_rpow (hs.trans hqrs.lt.le) hb.restrict (hM c ρ)
  set ρk := 2 ^ (k + 1) * ρ
  have hρk : 0 < ρk := by positivity
  set Sk := ball c ρk \ ball c (2 ^ k * ρ)
  have hS : MeasurableSet Sk := measurableSet_ball.diff measurableSet_ball
  have hxk : x ∈ ball c ρk := by
    refine mem_ball.2 ((mem_ball.1 hx).trans_le ?_)
    have : (1 : ℝ) ≤ 2 ^ (k + 1) * 2 := by
      have := one_le_pow₀ (M₀ := ℝ) (n := k + 1) one_le_two; linarith
    simp only [ρk, ρ]; nlinarith
  -- On the annulus the weight is at most its value `w` at the inner radius.
  set w := ENNReal.ofReal (R ^ δ * (2 ^ k * ρ) ^ (-((n : ℝ) + δ)))
  have hw : ∀ y ∈ Sk, ENNReal.ofReal (R ^ δ * dist y c ^ (-((n : ℝ) + δ))) * Φ y ≤ w * Φ y := by
    intro y hy
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left ?_ (by positivity))) _
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (not_lt.1 fun h => hy.2 (mem_ball.2 h))
      (neg_nonpos.2 (by positivity))
  -- The weighted mean of `Φ` over the enclosing ball.
  have havg : ⨍⁻ y in ball c ρk, Φ y ∂μ ≤ (M + (k + 1) * (2 ^ n * M)) * Mx := by
    refine (setLAverage_enorm_sub_mul_le hqrs hs hb.restrict (hM c ρk) hψ.restrict a₀).trans ?_
    gcongr
    · refine (enorm_setAverage_ball_two_pow_mul_sub_le hb c hρ (k + 1)).trans ?_
      push_cast
      gcongr
      exact bmoSeminorm_le hM₁
    · refine ENNReal.rpow_le_rpow ?_ (by positivity)
      simpa only [enorm_eq_self] using
        setLAverage_le_uncenteredMaximalFunction μ (fun y => ψ y ^ r) hxk
  have hcoef :
      w * ENNReal.ofReal (ρk ^ n) = 2 ^ n * ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ (k + 1)) := by
    rw [← ENNReal.ofReal_mul (by positivity), hρdef, rpow_mul_rpow_mul_pow_eq hR n δ k,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  calc ∫⁻ y in Sk, ENNReal.ofReal (R ^ δ * dist y c ^ (-((n : ℝ) + δ))) * Φ y ∂μ
      ≤ ∫⁻ y in Sk, w * Φ y ∂μ := setLIntegral_mono' hS hw
    _ = w * ∫⁻ y in Sk, Φ y ∂μ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ w * (μ (ball c ρk) * ⨍⁻ y in ball c ρk, Φ y ∂μ) := by
        rw [measure_mul_setLAverage _ measure_ball_lt_top.ne]
        gcongr
        exact sdiff_subset
    _ ≤ w * (ENNReal.ofReal (ρk ^ n) * μ (ball 0 1) * ((M + (k + 1) * (2 ^ n * M)) * Mx)) := by
        rw [Measure.addHaar_ball_of_pos μ c hρk]
        gcongr
    _ = w * ENNReal.ofReal (ρk ^ n) * μ (ball 0 1) * ((M + (k + 1) * (2 ^ n * M)) * Mx) := by
        ring
    _ = 2 ^ n * μ (ball 0 1) *
          (ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ (k + 1)) * (1 + (k + 1) * 2 ^ n)) * M * Mx := by
        rw [hcoef]
        ring

/-- **The tail estimate.** Let the `q`-th mean oscillation of `b` on every ball be at most `M ^ q`,
with `q⁻¹ + r⁻¹ = s⁻¹` and `1 ≤ s`, and let `x ∈ B(c, R)`. Integrating
`‖b - b_{B(c, 2R)}‖ ψ` against the kernel bound `R^δ |y - c|^(-(n + δ))` off `B(c, 2R)` gives at
most `2ⁿ |B(0, 1)| S M (M ψ^r)(x)^(1/r)`, where `S = ∑ₖ (2^(-δ))^(k + 1) (1 + (k + 1) 2ⁿ)` and
`M ψ^r` is the uncentred maximal function of `ψ ^ r`. The integral is split over the dyadic
annuli `2ᵏ · 2R ≤ |y - c| < 2ᵏ⁺¹ · 2R`. -/
private theorem setLIntegral_compl_ball_ofReal_mul_le {b : V → ℝ} (hb : AEStronglyMeasurable b μ)
    {q r s : ℝ} (hqrs : q.HolderTriple r s) (hs : 1 ≤ s) {M : ℝ≥0∞}
    (hM : ∀ c ρ, ⨍⁻ y in ball c ρ, ‖b y - ⨍ z in ball c ρ, b z ∂μ‖ₑ ^ q ∂μ ≤ M ^ q)
    {ψ : V → ℝ≥0∞} (hψ : AEMeasurable ψ μ) {δ : ℝ} (hδ : 0 < δ) {c x : V} {R : ℝ}
    (hx : x ∈ ball c R) :
    ∫⁻ y in (ball c (2 * R))ᶜ, ENNReal.ofReal (R ^ δ * dist y c ^ (-((finrank ℝ V : ℝ) + δ))) *
        (‖b y - ⨍ z in ball c (2 * R), b z ∂μ‖ₑ * ψ y) ∂μ ≤
      2 ^ finrank ℝ V * μ (ball 0 1) *
        (∑' k : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ (k + 1)) *
          (1 + (k + 1) * 2 ^ finrank ℝ V)) * M *
        uncenteredMaximalFunction μ (fun y => ψ y ^ r) x ^ (1 / r) := by
  set n := finrank ℝ V
  have hR : 0 < R := pos_of_mem_ball hx
  set ρ := 2 * R with hρdef
  have hρ : 0 < ρ := by positivity
  set a₀ := ⨍ z in ball c ρ, b z ∂μ
  set Φ : V → ℝ≥0∞ := fun y => ‖b y - a₀‖ₑ * ψ y
  set Mx := uncenteredMaximalFunction μ (fun y => ψ y ^ r) x ^ (1 / r)
  -- The annuli cover the complement of `B(c, ρ)`.
  set S : ℕ → Set V := fun k => ball c (2 ^ (k + 1) * ρ) \ ball c (2 ^ k * ρ)
  have hcover : (ball c ρ)ᶜ ⊆ ⋃ k, S k := by
    intro y hy
    have hy' : 1 ≤ dist y c / ρ := by
      rw [le_div_iff₀ hρ, one_mul]
      simpa [mem_ball] using hy
    obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near hy' one_lt_two
    refine mem_iUnion.2 ⟨k, mem_ball.2 ?_, fun h => ?_⟩
    · rwa [div_lt_iff₀ hρ] at hk₂
    · rw [le_div_iff₀ hρ] at hk₁
      exact (mem_ball.1 h).not_ge hk₁
  calc ∫⁻ y in (ball c ρ)ᶜ, ENNReal.ofReal (R ^ δ * dist y c ^ (-((n : ℝ) + δ))) * Φ y ∂μ
      ≤ ∫⁻ y in ⋃ k, S k, ENNReal.ofReal (R ^ δ * dist y c ^ (-((n : ℝ) + δ))) * Φ y ∂μ :=
        lintegral_mono_set hcover
    _ ≤ ∑' k, ∫⁻ y in S k, ENNReal.ofReal (R ^ δ * dist y c ^ (-((n : ℝ) + δ))) * Φ y ∂μ :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' k : ℕ, 2 ^ n * μ (ball 0 1) *
          (ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ (k + 1)) * (1 + (k + 1) * 2 ^ n)) * M * Mx :=
        tsum_le_tsum fun k =>
          setLIntegral_annulus_ofReal_mul_le hb hqrs hs hM hψ hδ hx k
    _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The local part.** If `T` is bounded in the `Lˢ` norm with constant `N` and `‖g‖ ≤ Φ` on
`B(c, 2R)` with `g = 0` off it, then
`⨍_{B(c, R)} ‖T g‖ ≤ N (2ⁿ)^(1/s) (⨍_{B(c, 2R)} Φ ^ s)^(1/s)`. -/
private theorem setLAverage_enorm_apply_le (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) {s : ℝ} (hs : 1 ≤ s)
    {N : ℝ≥0∞}
    (hT : ∀ g, eLpNorm (T g) (ENNReal.ofReal s) μ ≤ N * eLpNorm g (ENNReal.ofReal s) μ)
    {g : Lp E 2 μ} {c : V} {R : ℝ} (hR : 0 < R) {Φ : V → ℝ≥0∞}
    (hg : ∀ᵐ y ∂μ, ‖g y‖ₑ ^ s ≤ (ball c (2 * R)).indicator (fun y => Φ y ^ s) y) :
    ⨍⁻ z in ball c R, ‖T g z‖ₑ ∂μ ≤
      N * (2 ^ finrank ℝ V) ^ (1 / s) * (⨍⁻ y in ball c (2 * R), Φ y ^ s ∂μ) ^ (1 / s) := by
  have hs0 : 0 < s := one_pos.trans_le hs
  have hs' : (ENNReal.ofReal s).toReal = s := ENNReal.toReal_ofReal hs0.le
  have hs0' : ENNReal.ofReal s ≠ 0 := by simpa using hs0
  have hB0 : μ (ball c R) ≠ 0 := (measure_ball_pos μ c hR).ne'
  have hBt : μ (ball c R) ≠ ∞ := measure_ball_lt_top.ne
  set P := ⨍⁻ y in ball c (2 * R), Φ y ^ s ∂μ
  -- Multiplied by `μ(B(c, R)) ^ (1 / s)`, the `s`-th mean of `T g` is at most `‖T g‖_s`.
  have key : μ (ball c R) ^ (1 / s) * (⨍⁻ z in ball c R, ‖T g z‖ₑ ^ s ∂μ) ^ (1 / s) ≤
      μ (ball c R) ^ (1 / s) * (N * (2 ^ finrank ℝ V) ^ (1 / s) * P ^ (1 / s)) := by
    calc μ (ball c R) ^ (1 / s) * (⨍⁻ z in ball c R, ‖T g z‖ₑ ^ s ∂μ) ^ (1 / s)
        = (∫⁻ z in ball c R, ‖T g z‖ₑ ^ s ∂μ) ^ (1 / s) := by
          rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), measure_mul_setLAverage _ hBt]
      _ ≤ eLpNorm (T g) (ENNReal.ofReal s) μ := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hs0' ENNReal.ofReal_ne_top
            (Lp.aestronglyMeasurable _), hs']
          exact ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _) (by positivity)
      _ ≤ N * eLpNorm g (ENNReal.ofReal s) μ := hT g
      _ ≤ N * (∫⁻ y in ball c (2 * R), Φ y ^ s ∂μ) ^ (1 / s) := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hs0' ENNReal.ofReal_ne_top
            (Lp.aestronglyMeasurable _), hs', ← lintegral_indicator measurableSet_ball]
          have := ENNReal.rpow_le_rpow (z := 1 / s) (lintegral_mono_ae hg) (by positivity)
          gcongr
      _ = μ (ball c R) ^ (1 / s) * (N * (2 ^ finrank ℝ V) ^ (1 / s) * P ^ (1 / s)) := by
          rw [← measure_mul_setLAverage _ measure_ball_lt_top.ne, measure_ball_two_mul c hR,
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
          ring
  calc ⨍⁻ z in ball c R, ‖T g z‖ₑ ∂μ ≤ (⨍⁻ z in ball c R, ‖T g z‖ₑ ^ s ∂μ) ^ (1 / s) :=
        laverage_le_laverage_rpow_rpow (Lp.aestronglyMeasurable _).enorm.restrict hs
    _ ≤ _ := (ENNReal.mul_le_mul_iff_right (by simp [hB0, hs0.le])
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) hBt)).1 key

omit [FiniteDimensional ℝ V] [μ.IsAddHaarMeasure] in
/-- **The far part.** Let `T` be given by the kernel `K` on balls where its argument vanishes,
with the standard smoothness estimate in the first variable. If `‖g‖ ≤ Φ` and `g` vanishes on
`B(c, 2R)`, then for almost every `z ∈ B(c, R)`,
`‖T g z - ∫ K c y (g y) dy‖ ≤ A ∫_{|y - c| ≥ 2R} R^δ |y - c|^(-(n + δ)) Φ(y) dy`. -/
private theorem ae_enorm_apply_sub_integral_le (T : Lp E 2 μ →L[ℝ] Lp F 2 μ)
    {K : V → V → E →L[ℝ] F} (hK : ∀ x, AEStronglyMeasurable (K x) μ) {A : ℝ≥0} {δ : ℝ}
    (hKs : ∀ x x' y, 2 * dist x x' < dist y x' →
      ‖K x y - K x' y‖ ≤ A * (dist x x' ^ δ * dist y x' ^ (-((finrank ℝ V : ℝ) + δ))))
    (hrep : ∀ (g : Lp E 2 μ) (y : V) (ρ : ℝ), (∀ᵐ z ∂μ, z ∈ ball y ρ → g z = 0) →
      ∀ᵐ x ∂μ, x ∈ ball y ρ → T g x = ∫ z, K x z (g z) ∂μ)
    (hδ : 0 ≤ δ) {g : Lp E 2 μ} {c : V} {R : ℝ} {Φ : V → ℝ≥0∞}
    (hg : ∀ᵐ y ∂μ, ‖g y‖ₑ ≤ (ball c (2 * R))ᶜ.indicator Φ y) :
    ∀ᵐ z ∂μ.restrict (ball c R), ‖T g z - ∫ y, K c y (g y) ∂μ‖ₑ ≤
      A * ∫⁻ y in (ball c (2 * R))ᶜ,
        ENNReal.ofReal (R ^ δ * dist y c ^ (-((finrank ℝ V : ℝ) + δ))) * Φ y ∂μ := by
  rw [ae_restrict_iff' measurableSet_ball]
  have hvan : ∀ᵐ y ∂μ, y ∈ ball c (2 * R) → g y = 0 := by
    filter_upwards [hg] with y hy hyB
    simpa [indicator_of_notMem (notMem_compl_iff.2 hyB)] using hy
  filter_upwards [hrep g c (2 * R) hvan] with z hz hzB
  have hR : 0 < R := pos_of_mem_ball hzB
  rw [hz (ball_subset_ball (by linarith) hzB)]
  refine (enorm_integral_sub_integral_le_lintegral (hK z) (hK c)
    (Lp.aestronglyMeasurable g)).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top,
    ← lintegral_indicator measurableSet_ball.compl]
  refine lintegral_mono_ae ?_
  filter_upwards [hg] with y hy
  by_cases hyB : y ∈ ball c (2 * R)
  · rw [indicator_of_notMem (notMem_compl_iff.2 hyB)] at hy ⊢
    simp [nonpos_iff_eq_zero.1 hy]
  rw [indicator_of_mem hyB] at hy ⊢
  rw [← mul_assoc (A : ℝ≥0∞)]
  refine mul_le_mul' ?_ hy
  -- The kernel estimate, with `|z - c| < R` and `|y - c| ≥ 2R`.
  have hzc : dist z c < R := mem_ball.1 hzB
  have hyc : 2 * R ≤ dist y c := not_lt.1 fun h => hyB (mem_ball.2 h)
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul A.coe_nonneg]
  refine ENNReal.ofReal_le_ofReal ((hKs z c y (by linarith)).trans ?_)
  gcongr

variable [CompleteSpace F]

/-- **The sharp maximal function of a commutator with a singular integral operator**
(Coifman–Rochberg–Weiss). Let `μ` be an additive Haar measure on a finite-dimensional real normed
space `V` of dimension `n`, and let `T` be a bounded linear operator on `L²(μ)` given, on any ball
on which its argument vanishes, by a kernel `K` satisfying the standard smoothness estimate in the
first variable,

`‖K x y - K x' y‖ ≤ A |x - x'| ^ δ |y - x'| ^ (-(n + δ))` whenever `2 |x - x'| < |y - x'|`,

with `δ > 0`, and bounded in the `Lˢ` norm on `L²`: `‖T g‖_s ≤ N ‖g‖_s`. Let `q⁻¹ + r⁻¹ = s⁻¹`
with `1 ≤ s`. Then there is a constant `C` such that for every bounded `b` whose `q`-th mean
oscillation on every ball is at most `M ^ q`, every `f ∈ L²` and every point `x`,

`(b T f - T (b f))^# (x) ≤ C M ((M |T f|^r)(x)^(1/r) + (M |f|^r)(x)^(1/r))`,

where `g^#` is the sharp maximal function and `M` the uncentred Hardy–Littlewood maximal
function. The constant depends only on `V`, `μ`, `s`, `q`, `r`, `δ`, `A` and `N`, not on `T`,
`b`, `f` or `x`. -/
theorem exists_sharpMaximalFunction_commutator_le {q r s δ : ℝ} (hqrs : q.HolderTriple r s)
    (hs : 1 ≤ s) (hδ : 0 < δ) (A N : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (K : V → V → E →L[ℝ] F),
      (∀ x, AEStronglyMeasurable (K x) μ) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖K x y - K x' y‖ ≤ A * (dist x x' ^ δ * dist y x' ^ (-((finrank ℝ V : ℝ) + δ)))) →
      (∀ (g : Lp E 2 μ) (y : V) (ρ : ℝ), (∀ᵐ z ∂μ, z ∈ ball y ρ → g z = 0) →
        ∀ᵐ x ∂μ, x ∈ ball y ρ → T g x = ∫ z, K x z (g z) ∂μ) →
      (∀ g : Lp E 2 μ,
        eLpNorm (T g) (ENNReal.ofReal s) μ ≤ N * eLpNorm g (ENNReal.ofReal s) μ) →
      ∀ (b : Lp ℝ ∞ μ) (M : ℝ≥0∞),
        (∀ c ρ, ⨍⁻ y in ball c ρ, ‖b y - ⨍ z in ball c ρ, b z ∂μ‖ₑ ^ q ∂μ ≤ M ^ q) →
        ∀ (f : Lp E 2 μ) (x : V),
          sharpMaximalFunction μ (⇑(b • T f - T (b • f))) x ≤
            C * M * (uncenteredMaximalFunction μ (fun y => ‖T f y‖ₑ ^ r) x ^ (1 / r) +
              uncenteredMaximalFunction μ (fun y => ‖f y‖ₑ ^ r) x ^ (1 / r)) := by
  set n := finrank ℝ V
  set S := ∑' k : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ (k + 1)) * (1 + (k + 1) * 2 ^ n)
  have hS : S ≠ ∞ := tsum_ofReal_mul_ne_top n hδ
  set K₀ : ℝ≥0∞ := 1 + 2 ^ n + N * (2 ^ n) ^ (1 / s) + A * (2 ^ n * μ (ball 0 1) * S)
  have hK₀ : 2 * K₀ ≠ ∞ := by
    have : μ (ball (0 : V) 1) ≠ ∞ := measure_ball_lt_top.ne
    have : (2 ^ n : ℝ≥0∞) ^ (1 / s) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp)
    finiteness
  refine ⟨(2 * K₀).toNNReal, fun T K hK hKs hrep hTs b M hb f x => ?_⟩
  rw [ENNReal.coe_toNNReal hK₀]
  set MTf := uncenteredMaximalFunction μ (fun y => ‖T f y‖ₑ ^ r) x ^ (1 / r)
  set Mf := uncenteredMaximalFunction μ (fun y => ‖f y‖ₑ ^ r) x ^ (1 / r)
  have hbm : AEStronglyMeasurable (b : V → ℝ) μ := Lp.aestronglyMeasurable b
  have hq1 : 1 ≤ q := hs.trans hqrs.lt.le
  have hM₁ : ∀ c ρ, ⨍⁻ y in ball c ρ, ‖b y - ⨍ z in ball c ρ, b z ∂μ‖ₑ ∂μ ≤ M := fun c ρ =>
    setLAverage_enorm_sub_setAverage_le_of_rpow hq1 hbm.restrict (hb c ρ)
  refine sharpMaximalFunction_le fun c R hx => ?_
  have hR : 0 < R := pos_of_mem_ball hx
  set a₀ := ⨍ z in ball c (2 * R), b z ∂μ
  -- Split `(b - a₀) f = g₁ + g₂` with `g₁` supported in `B(c, 2R)` and `g₂` vanishing there.
  have hmem : MemLp (fun y => (b y - a₀) • f y) 2 μ :=
    ((Lp.memLp b).sub (memLp_top_const a₀)).smul (Lp.memLp f)
  obtain ⟨g₂, hg₂⟩ : ∃ g₂ : Lp E 2 μ,
      g₂ =ᵐ[μ] (ball c (2 * R))ᶜ.indicator fun y => (b y - a₀) • f y :=
    ⟨_, (hmem.indicator measurableSet_ball.compl.nullMeasurableSet).coeFn_toLp⟩
  set g₁ : Lp E 2 μ := b • f - a₀ • f - g₂
  have hg₁ : ⇑g₁ =ᵐ[μ] (ball c (2 * R)).indicator fun y => (b y - a₀) • f y := by
    filter_upwards [Lp.coeFn_sub (b • f - a₀ • f) g₂, Lp.coeFn_sub (b • f) (a₀ • f),
      Lp.coeFn_lpSMul (r := 2) b f, Lp.coeFn_smul a₀ f, hg₂] with z h1 h2 h3 h4 h5
    rw [h1, Pi.sub_apply, h2, Pi.sub_apply, h3, h4, h5]
    simp only [Pi.smul_apply', Pi.smul_apply]
    by_cases hz : z ∈ ball c (2 * R) <;> simp [hz, sub_smul]
  have hsplit : T (b • f) = T g₁ + T g₂ + a₀ • T f := by
    simp only [g₁, map_sub, map_smul]
    abel
  have hh : ⇑(b • T f - T (b • f)) =ᵐ[μ] fun z => (b z - a₀) • T f z - T g₁ z - T g₂ z := by
    rw [hsplit]
    filter_upwards [Lp.coeFn_sub (b • T f) (T g₁ + T g₂ + a₀ • T f),
      Lp.coeFn_lpSMul (r := 2) b (T f),
      Lp.coeFn_add (T g₁ + T g₂) (a₀ • T f), Lp.coeFn_add (T g₁) (T g₂),
      Lp.coeFn_smul a₀ (T f)] with z h1 h2 h3 h4 h5
    rw [h1, Pi.sub_apply, h2, h3, Pi.add_apply, h4, Pi.add_apply, h5]
    simp only [Pi.smul_apply', Pi.smul_apply, sub_smul]
    abel
  -- The far part: on `B(c, R)`, `T g₂` stays within `A J` of the constant `∫ K c y (g₂ y) dy`.
  set a : F := ∫ y, K c y (g₂ y) ∂μ
  set J := ∫⁻ y in (ball c (2 * R))ᶜ,
    ENNReal.ofReal (R ^ δ * dist y c ^ (-((n : ℝ) + δ))) * (‖b y - a₀‖ₑ * ‖f y‖ₑ) ∂μ
  have hfar : ∀ᵐ z ∂μ.restrict (ball c R), ‖T g₂ z - a‖ₑ ≤ A * J := by
    refine ae_enorm_apply_sub_integral_le T hK hKs hrep hδ.le ?_
    filter_upwards [hg₂] with y hy
    rw [hy]
    by_cases hyB : y ∈ (ball c (2 * R))ᶜ
    · simp [hyB, enorm_smul]
    · simp [hyB]
  -- Pointwise on `B(c, R)`, compare `[b, T] f` with the constant `-a`.
  have hpt : ∀ᵐ z ∂μ.restrict (ball c R), ‖(b • T f - T (b • f)) z - -a‖ₑ ≤
      ‖b z - a₀‖ₑ * ‖T f z‖ₑ + ‖T g₁ z‖ₑ + A * J := by
    filter_upwards [ae_restrict_of_ae hh, hfar] with z h1 h2
    rw [h1]
    calc ‖(b z - a₀) • T f z - T g₁ z - T g₂ z - -a‖ₑ
        = ‖(b z - a₀) • T f z + -T g₁ z + -(T g₂ z - a)‖ₑ := by congr 1; abel
      _ ≤ ‖(b z - a₀) • T f z‖ₑ + ‖-T g₁ z‖ₑ + ‖-(T g₂ z - a)‖ₑ :=
          (enorm_add_le _ _).trans (by gcongr; exact enorm_add_le _ _)
      _ ≤ _ := by rw [enorm_smul, enorm_neg, enorm_neg]; gcongr
  -- The first term, by Hölder's inequality on `B(c, R)`.
  have h₁ : ⨍⁻ z in ball c R, ‖b z - a₀‖ₑ * ‖T f z‖ₑ ∂μ ≤ (1 + 2 ^ n) * M * MTf := by
    refine (setLAverage_enorm_sub_mul_le hqrs hs hbm.restrict (hb c R)
      (Lp.aestronglyMeasurable (T f)).enorm.restrict a₀).trans ?_
    have hdrift : ‖(⨍ z in ball c R, b z ∂μ) - a₀‖ₑ ≤ 2 ^ n * M := by
      rw [enorm_sub_rev]
      calc _ ≤ ((1 : ℕ) : ℝ≥0∞) * (2 ^ n * bmoSeminorm (⇑b) μ) := by
            simpa [a₀] using enorm_setAverage_ball_two_pow_mul_sub_le hbm c hR 1
        _ ≤ 2 ^ n * M := by
            rw [Nat.cast_one, one_mul]
            gcongr
            exact bmoSeminorm_le hM₁
    calc _ ≤ (M + 2 ^ n * M) * MTf := by
          gcongr
          refine ENNReal.rpow_le_rpow ?_ (by have := hqrs.symm.pos; positivity)
          simpa only [enorm_eq_self] using
            setLAverage_le_uncenteredMaximalFunction μ (fun y => ‖T f y‖ₑ ^ r) hx
      _ = _ := by ring
  -- The second term, by the `Lˢ` bound of `T` and Hölder's inequality on `B(c, 2R)`.
  have hx₂ : x ∈ ball c (2 * R) := ball_subset_ball (by linarith) hx
  have h₂ : ⨍⁻ z in ball c R, ‖T g₁ z‖ₑ ∂μ ≤ N * (2 ^ n) ^ (1 / s) * M * Mf := by
    have hs0 : 0 < s := one_pos.trans_le hs
    have hg₁s : ∀ᵐ y ∂μ, ‖g₁ y‖ₑ ^ s ≤
        (ball c (2 * R)).indicator (fun y => (‖b y - a₀‖ₑ * ‖f y‖ₑ) ^ s) y := by
      filter_upwards [hg₁] with y hy
      rw [hy]
      by_cases hyB : y ∈ ball c (2 * R)
      · simp [hyB, enorm_smul]
      · simp [hyB, ENNReal.zero_rpow_of_pos hs0]
    refine (setLAverage_enorm_apply_le T hs hTs hR hg₁s).trans ?_
    have hHolder : (⨍⁻ y in ball c (2 * R), (‖b y - a₀‖ₑ * ‖f y‖ₑ) ^ s ∂μ) ^ (1 / s) ≤
        M * Mf := by
      refine (laverage_Lp_mul_le_Lq_mul_Lr
        (hbm.sub (aestronglyMeasurable_const (b := a₀))).enorm.restrict
        (Lp.aestronglyMeasurable f).enorm.restrict hqrs).trans ?_
      gcongr
      · calc _ ≤ (M ^ q) ^ (1 / q) := ENNReal.rpow_le_rpow (hb c (2 * R))
              (by have := hqrs.pos; positivity)
          _ = M := by rw [one_div, ENNReal.rpow_rpow_inv hqrs.pos.ne']
      · refine ENNReal.rpow_le_rpow ?_ (by have := hqrs.symm.pos; positivity)
        simpa only [enorm_eq_self] using
          setLAverage_le_uncenteredMaximalFunction μ (fun y => ‖f y‖ₑ ^ r) hx₂
    calc _ ≤ N * (2 ^ n) ^ (1 / s) * (M * Mf) := by gcongr
      _ = _ := by ring
  -- The third term, by the kernel estimate on dyadic annuli.
  have h₃ : J ≤ 2 ^ n * μ (ball 0 1) * S * M * Mf :=
    setLIntegral_compl_ball_ofReal_mul_le hbm hqrs hs hb (Lp.aestronglyMeasurable f).enorm hδ hx
  have : IsFiniteMeasure (μ.restrict (ball c R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : IntegrableOn (⇑(b • T f - T (b • f))) (ball c R) μ :=
    ((Lp.memLp _).restrict _).integrable one_le_two
  calc ⨍⁻ z in ball c R, ‖(b • T f - T (b • f)) z -
        ⨍ w in ball c R, (b • T f - T (b • f)) w ∂μ‖ₑ ∂μ
      ≤ 2 * ⨍⁻ z in ball c R, ‖(b • T f - T (b • f)) z - -a‖ₑ ∂μ :=
        setLAverage_enorm_sub_setAverage_le hint (-a)
    _ ≤ 2 * ⨍⁻ z in ball c R, (‖b z - a₀‖ₑ * ‖T f z‖ₑ + ‖T g₁ z‖ₑ + A * J) ∂μ := by
        gcongr 2 * ?_
        exact laverage_mono_ae hpt
    _ = 2 * (⨍⁻ z in ball c R, ‖b z - a₀‖ₑ * ‖T f z‖ₑ ∂μ + ⨍⁻ z in ball c R, ‖T g₁ z‖ₑ ∂μ +
          A * J) := by
        rw [setLAverage_add_add_const (u := fun z => ‖b z - a₀‖ₑ * ‖T f z‖ₑ)
          (measure_ball_pos μ c hR).ne' measure_ball_lt_top.ne
          ((hbm.sub (aestronglyMeasurable_const (b := a₀))).enorm.mul
            (Lp.aestronglyMeasurable (T f)).enorm).restrict]
    _ ≤ 2 * ((1 + 2 ^ n) * M * MTf + N * (2 ^ n) ^ (1 / s) * M * Mf +
          A * (2 ^ n * μ (ball 0 1) * S * M * Mf)) := by
        gcongr
    _ = 2 * M * ((1 + 2 ^ n) * MTf + (N * (2 ^ n) ^ (1 / s) + A * (2 ^ n * μ (ball 0 1) * S)) *
          Mf) := by ring
    _ ≤ 2 * M * (K₀ * MTf + K₀ * Mf) := by
        gcongr
        · exact le_add_right (le_add_right le_rfl)
        · calc _ ≤ (1 + 2 ^ n) + (N * (2 ^ n) ^ (1 / s) + A * (2 ^ n * μ (ball 0 1) * S)) :=
                le_add_left le_rfl
            _ = K₀ := (add_assoc _ _ _).symm
    _ = 2 * K₀ * M * (MTf + Mf) := by ring

end Haar

section Euclidean

variable {ι E F : Type*} [Fintype ι] {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- **The sharp maximal function of a commutator with a function of bounded mean oscillation**
(Coifman–Rochberg–Weiss), on `ℝⁿ = EuclideanSpace ℝ ι` with an additive Haar measure `μ`. Let `T`
be a bounded linear operator on `L²(μ)` given, on any ball on which its argument vanishes, by a
kernel `K` with the standard smoothness estimate in the first variable,

`‖K x y - K x' y‖ ≤ A |x - x'| ^ δ |y - x'| ^ (-(n + δ))` whenever `2 |x - x'| < |y - x'|`,

with `δ > 0`, and bounded in the `Lˢ` norm on `L²`, `‖T g‖_s ≤ N ‖g‖_s`, for some `1 ≤ s`. Then
for every `r > s` there is a constant `C` such that for every bounded `b`, every `f ∈ L²` and every
point `x`,

`(b T f - T (b f))^# (x) ≤ C ‖b‖_{BMO} ((M |T f|^r)(x)^(1/r) + (M |f|^r)(x)^(1/r))`,

where `g^#` is the sharp maximal function and `M` the uncentred Hardy–Littlewood maximal
function. The constant depends only on `ι`, `μ`, `s`, `r`, `δ`, `A` and `N`. This is
`TauCeti.exists_sharpMaximalFunction_commutator_le` with the `q`-th mean oscillation of `b`,
`q⁻¹ = s⁻¹ - r⁻¹`, bounded by the `Lᵖ` form of the John–Nirenberg inequality
(`TauCeti.exists_setLAverage_enorm_sub_setAverage_rpow_le_mul_bmoSeminorm_rpow`). -/
theorem exists_sharpMaximalFunction_commutator_le_bmoSeminorm {r s δ : ℝ} (hs : 1 ≤ s)
    (hsr : s < r) (hδ : 0 < δ) (A N : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (T : Lp E 2 μ →L[ℝ] Lp F 2 μ)
      (K : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → E →L[ℝ] F),
      (∀ x, AEStronglyMeasurable (K x) μ) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖K x y - K x' y‖ ≤ A * (dist x x' ^ δ * dist y x' ^ (-((Fintype.card ι : ℝ) + δ)))) →
      (∀ (g : Lp E 2 μ) (y : EuclideanSpace ℝ ι) (ρ : ℝ), (∀ᵐ z ∂μ, z ∈ ball y ρ → g z = 0) →
        ∀ᵐ x ∂μ, x ∈ ball y ρ → T g x = ∫ z, K x z (g z) ∂μ) →
      (∀ g : Lp E 2 μ,
        eLpNorm (T g) (ENNReal.ofReal s) μ ≤ N * eLpNorm g (ENNReal.ofReal s) μ) →
      ∀ (b : Lp ℝ ∞ μ) (f : Lp E 2 μ) (x : EuclideanSpace ℝ ι),
        sharpMaximalFunction μ (⇑(b • T f - T (b • f))) x ≤
          C * bmoSeminorm (⇑b) μ *
            (uncenteredMaximalFunction μ (fun y => ‖T f y‖ₑ ^ r) x ^ (1 / r) +
              uncenteredMaximalFunction μ (fun y => ‖f y‖ₑ ^ r) x ^ (1 / r)) := by
  have hs0 : 0 < s := one_pos.trans_le hs
  have hr0 : 0 < r := hs0.trans hsr
  have hq0 : 0 < s⁻¹ - r⁻¹ := sub_pos.2 (inv_strictAnti₀ hs0 hsr)
  have hqrs : (s⁻¹ - r⁻¹)⁻¹.HolderTriple r s :=
    ⟨by rw [inv_inv, sub_add_cancel], inv_pos.2 hq0, hr0⟩
  set q := (s⁻¹ - r⁻¹)⁻¹
  have hq : 0 < q := inv_pos.2 hq0
  obtain ⟨C₀, hC₀⟩ := exists_setLAverage_enorm_sub_setAverage_rpow_le_mul_bmoSeminorm_rpow
    (ι := ι) hq
  obtain ⟨C, hC⟩ := exists_sharpMaximalFunction_commutator_le (μ := μ) (E := E) (F := F)
    hqrs hs hδ A N
  refine ⟨C * C₀ ^ (1 / q), fun T K hK hKs hrep hTs b f x => ?_⟩
  set M : ℝ≥0∞ := (C₀ : ℝ≥0∞) ^ (1 / q) * bmoSeminorm (⇑b) μ
  have hM : ∀ c ρ, ⨍⁻ y in ball c ρ, ‖b y - ⨍ z in ball c ρ, b z ∂μ‖ₑ ^ q ∂μ ≤ M ^ q := by
    intro c ρ
    refine (hC₀ ((Lp.memLp b).locallyIntegrable le_top) c ρ).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne',
      ENNReal.rpow_one]
  have hrank : (Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) = Fintype.card ι := by
    rw [finrank_euclideanSpace]
  refine (hC T K hK (by simpa only [hrank] using hKs) hrep hTs b M hM f x).trans (le_of_eq ?_)
  rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ (by positivity)]
  ring

end Euclidean

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import TauCeti.Analysis.Analytic.MultiIndex.TaylorCoeff
import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Normed.Ring.InfiniteSum

/-!
# Taylor coefficients of exponential monomials

For `τ : ι → ℕ` and `w ξ : ι → ℂ`, the exponential monomial
`f z = (∏ v, z v ^ τ v) * exp (∑ v, w v * z v)` on `ι → ℂ` factors over the coordinates, and
about `ξ` each factor `(ξ v + y) ^ τ v * exp (w v * (ξ v + y))` is a polynomial times an
exponential in one variable `y`. Multiplying the binomial expansion of `(ξ v + y) ^ τ v` by the
exponential series of `exp (w v * y)` gives the multi-index Taylor coefficient of `f` at `ξ` of
order `σ`,

  `exp (w · ξ) * ∏ v, ∑ j ≤ σ v, (τ v choose j) * ξ v ^ (τ v - j) * w v ^ (σ v - j) / (σ v - j)!`,

which is Waldschmidt's Lemma 4.9 in coefficient form: his `D^σ f (ξ)` is `σ!` times it. The
expansion of `f` about `ξ` converges normally on every polydisc, so `f` and every finite linear
combination of exponential monomials have power series on every polydisc about every point.
The Taylor coefficients of the auxiliary functions of the Schneider–Lang criterion at its
interpolation points are integer combinations of these, and their arithmetic is read off from
this formula.

The terms with `j > τ v` vanish, since then `(τ v).choose j = 0`; the truncated subtraction
`τ v - j` therefore never matters.

## Main results

* `TauCeti.hasSum_add_pow_mul_cexp` and `TauCeti.summable_norm_add_pow_mul_cexp`: the
  everywhere absolutely convergent expansion of `(a + t) ^ τ * exp (w * t)` in powers of `t`.
* `TauCeti.mvTaylorCoeff_prod_pow_mul_cexp`: the Taylor coefficients of an exponential monomial.
* `TauCeti.summable_norm_mvTaylorCoeff_prod_pow_mul_cexp` and
  `TauCeti.hasSum_mvTaylorCoeff_prod_pow_mul_cexp`: its expansion about any point converges
  normally on every polydisc.
* `TauCeti.mvTaylorCoeff_sum_mul_prod_pow_mul_cexp`,
  `TauCeti.summable_norm_mvTaylorCoeff_sum_mul_prod_pow_mul_cexp`,
  `TauCeti.hasSum_mvTaylorCoeff_sum_mul_prod_pow_mul_cexp`: the same for finite linear
  combinations of exponential monomials.
* `TauCeti.analyticAt_prod_pow_mul_cexp`: an exponential monomial is analytic everywhere.
* `TauCeti.exists_hasFPowerSeriesOnBall_sum_mul_prod_pow_mul_cexp`: a finite linear combination
  of exponential monomials has a power series on every polydisc about every point.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, Lemma 4.9, pp. 130–131.
* M. Karatarakis, formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`,
  commit `1d51891b5b`, `Mathlib/NumberTheory/Transcendental/Baker/ExpPoly.lean`, Apache 2.0),
  which states this formula as `taylorCoeff_expMonomial`.
-/

public section

open Finset Nat
open scoped NNReal

namespace TauCeti

/-! ### One variable -/

section OneVariable

/-- The `k`-th term of the Cauchy product of the binomial expansion of `(a + t) ^ τ` and the
exponential series of `exp (w * t)` is the `k`-th term of the expansion of their product. -/
private theorem sum_range_choose_mul_pow_mul_div_factorial (τ : ℕ) (a w t : ℂ) (k : ℕ) :
    ∑ j ∈ range (k + 1), ((τ.choose j : ℂ) * a ^ (τ - j) * t ^ j) *
        ((w * t) ^ (k - j) / (k - j)!) =
      (∑ j ∈ range (k + 1), (τ.choose j : ℂ) * a ^ (τ - j) * (w ^ (k - j) / (k - j)!)) *
        t ^ k := by
  rw [sum_mul]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [← pow_mul_pow_sub t (Nat.lt_succ_iff.1 (mem_range.1 hj)), mul_pow]
  ring

/-- The binomial expansion of `(a + t) ^ τ` as an absolutely summable series in `j`. -/
private theorem hasSum_choose_mul_pow (τ : ℕ) (a t : ℂ) :
    HasSum (fun j ↦ (τ.choose j : ℂ) * a ^ (τ - j) * t ^ j) ((a + t) ^ τ) ∧
      Summable fun j ↦ ‖(τ.choose j : ℂ) * a ^ (τ - j) * t ^ j‖ := by
  have h0 : ∀ j ∉ range (τ + 1), (τ.choose j : ℂ) * a ^ (τ - j) * t ^ j = 0 := fun j hj ↦ by
    rw [choose_eq_zero_of_lt (by simpa using hj)]
    simp
  have hsum : ∑ j ∈ range (τ + 1), (τ.choose j : ℂ) * a ^ (τ - j) * t ^ j = (a + t) ^ τ := by
    rw [add_comm a t, add_pow]
    exact sum_congr rfl fun j _ ↦ by ring
  exact ⟨hsum ▸ hasSum_sum_of_ne_finset_zero h0,
    summable_of_ne_finset_zero (s := range (τ + 1)) fun j hj ↦ by simp [h0 j hj]⟩

/-- **Expansion of a polynomial times an exponential in one variable**: for all `a w t : ℂ`,
`(a + t) ^ τ * exp (w * t)` is the sum over `k` of
`(∑ j ≤ k, (τ choose j) * a ^ (τ - j) * w ^ (k - j) / (k - j)!) * t ^ k`. -/
theorem hasSum_add_pow_mul_cexp (τ : ℕ) (a w t : ℂ) :
    HasSum (fun k ↦ (∑ j ∈ range (k + 1),
        (τ.choose j : ℂ) * a ^ (τ - j) * (w ^ (k - j) / (k - j)!)) * t ^ k)
      ((a + t) ^ τ * Complex.exp (w * t)) := by
  obtain ⟨hf, hfn⟩ := hasSum_choose_mul_pow τ a t
  have hg := NormedSpace.expSeries_div_hasSum_exp (w * t)
  rw [← Complex.exp_eq_exp_ℂ] at hg
  simpa only [sum_range_choose_mul_pow_mul_div_factorial, hf.tsum_eq, hg.tsum_eq] using
    hasSum_sum_range_mul_of_summable_norm hfn (NormedSpace.norm_expSeries_div_summable (w * t))

/-- The expansion of `(a + t) ^ τ * exp (w * t)` in powers of `t` converges absolutely for every
`t : ℂ`. -/
theorem summable_norm_add_pow_mul_cexp (τ : ℕ) (a w t : ℂ) :
    Summable fun k ↦ ‖(∑ j ∈ range (k + 1),
        (τ.choose j : ℂ) * a ^ (τ - j) * (w ^ (k - j) / (k - j)!)) * t ^ k‖ := by
  simpa only [sum_range_choose_mul_pow_mul_div_factorial] using
    summable_norm_sum_mul_range_of_summable_norm (hasSum_choose_mul_pow τ a t).2
      (NormedSpace.norm_expSeries_div_summable (w * t))

end OneVariable

/-! ### Exponential monomials -/

section Monomial

variable {ι : Type*} [Fintype ι]

/-- About `ξ`, the exponential monomial is `exp (w · ξ)` times a product over the coordinates of
one-variable functions of `y v`. -/
private theorem prod_pow_mul_cexp_add (τ : ι → ℕ) (w ξ y : ι → ℂ) :
    (∏ v, (ξ + y) v ^ τ v) * Complex.exp (∑ v, w v * (ξ + y) v) =
      Complex.exp (∑ v, w v * ξ v) * ∏ v, (ξ v + y v) ^ τ v * Complex.exp (w v * y v) := by
  simp only [Pi.add_apply, mul_add, sum_add_distrib, Complex.exp_add, Complex.exp_sum,
    prod_mul_distrib]
  ring

/-- The normally convergent expansion of an exponential monomial about `ξ`, with the explicit
coefficients. -/
private theorem hasSum_prod_pow_mul_cexp (τ : ι → ℕ) (w ξ y : ι → ℂ) :
    HasSum (fun σ : ι → ℕ ↦ (∏ v, y v ^ σ v) • (Complex.exp (∑ v, w v * ξ v) *
        ∏ v, ∑ j ∈ range (σ v + 1),
          ((τ v).choose j : ℂ) * ξ v ^ (τ v - j) * (w v ^ (σ v - j) / (σ v - j)!)))
      ((∏ v, (ξ + y) v ^ τ v) * Complex.exp (∑ v, w v * (ξ + y) v)) := by
  rw [prod_pow_mul_cexp_add]
  refine ((hasSum_prod_of_summable_norm (fun v ↦ hasSum_add_pow_mul_cexp (τ v) (ξ v) (w v) (y v))
    fun v ↦ summable_norm_add_pow_mul_cexp (τ v) (ξ v) (w v) (y v)).mul_left _).congr_fun
    fun σ ↦ ?_
  simp only [smul_eq_mul, prod_mul_distrib]
  ring

/-- The explicit coefficients of the expansion of an exponential monomial about `ξ` are normally
summable on every polydisc. -/
private theorem summable_norm_prod_pow_mul_cexp (τ : ι → ℕ) (w ξ : ι → ℂ) (ρ : ℝ≥0) :
    Summable fun σ : ι → ℕ ↦ ‖Complex.exp (∑ v, w v * ξ v) *
        ∏ v, ∑ j ∈ range (σ v + 1),
          ((τ v).choose j : ℂ) * ξ v ^ (τ v - j) * (w v ^ (σ v - j) / (σ v - j)!)‖ *
        (ρ : ℝ) ^ (∑ v, σ v) := by
  refine ((summable_norm_prod_of_summable_norm fun v ↦
    summable_norm_add_pow_mul_cexp (τ v) (ξ v) (w v) (ρ : ℂ)).mul_left
      ‖Complex.exp (∑ v, w v * ξ v)‖).congr fun σ ↦ ?_
  simp only [norm_mul, norm_prod, norm_pow, Complex.norm_real, NNReal.norm_eq, prod_mul_distrib,
    prod_pow_eq_pow_sum]
  ring

/-- **Taylor coefficients of an exponential monomial** (Waldschmidt, Lemma 4.9): at `ξ`, the
coefficient of order `σ` of `z ↦ (∏ v, z v ^ τ v) * exp (∑ v, w v * z v)` is
`exp (w · ξ) * ∏ v, ∑ j ≤ σ v, (τ v choose j) * ξ v ^ (τ v - j) * w v ^ (σ v - j) / (σ v - j)!`. -/
@[simp]
theorem mvTaylorCoeff_prod_pow_mul_cexp (τ σ : ι → ℕ) (w ξ : ι → ℂ) :
    mvTaylorCoeff (fun z : ι → ℂ ↦ (∏ v, z v ^ τ v) * Complex.exp (∑ v, w v * z v)) ξ σ =
      Complex.exp (∑ v, w v * ξ v) * ∏ v, ∑ j ∈ range (σ v + 1),
        ((τ v).choose j : ℂ) * ξ v ^ (τ v - j) * (w v ^ (σ v - j) / (σ v - j)!) := by
  refine mvTaylorCoeff_eq_of_hasSum one_pos (summable_norm_prod_pow_mul_cexp τ w ξ 1)
    (fun y _ ↦ ?_) σ
  exact hasSum_prod_pow_mul_cexp τ w ξ y

/-- An exponential monomial is analytic at every point. -/
theorem analyticAt_prod_pow_mul_cexp (τ : ι → ℕ) (w ξ : ι → ℂ) :
    AnalyticAt ℂ (fun z : ι → ℂ ↦ (∏ v, z v ^ τ v) * Complex.exp (∑ v, w v * z v)) ξ := by
  obtain ⟨p, hp, -⟩ := exists_hasFPowerSeriesOnBall_of_hasSum
    (f := fun z : ι → ℂ ↦ (∏ v, z v ^ τ v) * Complex.exp (∑ v, w v * z v)) one_pos
    (summable_norm_prod_pow_mul_cexp τ w ξ 1) fun y _ ↦ hasSum_prod_pow_mul_cexp τ w ξ y
  exact hp.analyticAt

/-- The Taylor coefficients of an exponential monomial at any point are normally summable on
every polydisc. -/
theorem summable_norm_mvTaylorCoeff_prod_pow_mul_cexp (τ : ι → ℕ) (w ξ : ι → ℂ) (ρ : ℝ≥0) :
    Summable fun σ : ι → ℕ ↦
      ‖mvTaylorCoeff (fun z : ι → ℂ ↦ (∏ v, z v ^ τ v) * Complex.exp (∑ v, w v * z v)) ξ σ‖ *
        (ρ : ℝ) ^ (∑ v, σ v) := by
  simpa only [mvTaylorCoeff_prod_pow_mul_cexp] using summable_norm_prod_pow_mul_cexp τ w ξ ρ

/-- An exponential monomial is the sum of its Taylor expansion about any point `ξ`, on all of
`ι → ℂ`. -/
theorem hasSum_mvTaylorCoeff_prod_pow_mul_cexp (τ : ι → ℕ) (w ξ y : ι → ℂ) :
    HasSum (fun σ : ι → ℕ ↦ (∏ v, y v ^ σ v) •
        mvTaylorCoeff (fun z : ι → ℂ ↦ (∏ v, z v ^ τ v) * Complex.exp (∑ v, w v * z v)) ξ σ)
      ((∏ v, (ξ + y) v ^ τ v) * Complex.exp (∑ v, w v * (ξ + y) v)) := by
  simpa only [mvTaylorCoeff_prod_pow_mul_cexp] using hasSum_prod_pow_mul_cexp τ w ξ y

end Monomial

/-! ### Finite linear combinations of exponential monomials -/

section LinearCombination

variable {ι κ : Type*} [Fintype ι]

/-- The Taylor coefficients of a finite linear combination of exponential monomials are the
corresponding combinations of the coefficients of `mvTaylorCoeff_prod_pow_mul_cexp`. -/
@[simp]
theorem mvTaylorCoeff_sum_mul_prod_pow_mul_cexp (s : Finset κ) (c : κ → ℂ) (τ : κ → ι → ℕ)
    (w : κ → ι → ℂ) (ξ : ι → ℂ) (σ : ι → ℕ) :
    mvTaylorCoeff (fun z : ι → ℂ ↦
        ∑ k ∈ s, c k * ((∏ v, z v ^ τ k v) * Complex.exp (∑ v, w k v * z v))) ξ σ =
      ∑ k ∈ s, c k * (Complex.exp (∑ v, w k v * ξ v) * ∏ v, ∑ j ∈ range (σ v + 1),
        ((τ k v).choose j : ℂ) * ξ v ^ (τ k v - j) * (w k v ^ (σ v - j) / (σ v - j)!)) := by
  rw [mvTaylorCoeff_fun_sum s
    (f := fun k z ↦ c k * ((∏ v, z v ^ τ k v) * Complex.exp (∑ v, w k v * z v)))
    fun k _ ↦ analyticAt_const.mul (analyticAt_prod_pow_mul_cexp (τ k) (w k) ξ)]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← mvTaylorCoeff_prod_pow_mul_cexp]
  simpa only [smul_eq_mul] using mvTaylorCoeff_fun_const_smul (c k)
    (fun z ↦ (∏ v, z v ^ τ k v) * Complex.exp (∑ v, w k v * z v)) ξ σ

/-- The Taylor coefficients of a finite linear combination of exponential monomials at any point
are normally summable on every polydisc. -/
theorem summable_norm_mvTaylorCoeff_sum_mul_prod_pow_mul_cexp (s : Finset κ) (c : κ → ℂ)
    (τ : κ → ι → ℕ) (w : κ → ι → ℂ) (ξ : ι → ℂ) (ρ : ℝ≥0) :
    Summable fun σ : ι → ℕ ↦
      ‖mvTaylorCoeff (fun z : ι → ℂ ↦
          ∑ k ∈ s, c k * ((∏ v, z v ^ τ k v) * Complex.exp (∑ v, w k v * z v))) ξ σ‖ *
        (ρ : ℝ) ^ (∑ v, σ v) := by
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun σ ↦ ?_)
    (summable_sum (s := s) fun k _ ↦
      (summable_norm_mvTaylorCoeff_prod_pow_mul_cexp (τ k) (w k) ξ ρ).mul_left ‖c k‖)
  rw [mvTaylorCoeff_sum_mul_prod_pow_mul_cexp]
  simp only [mvTaylorCoeff_prod_pow_mul_cexp, ← mul_assoc, ← norm_mul, ← sum_mul]
  gcongr
  exact norm_sum_le _ _

/-- A finite linear combination of exponential monomials is the sum of its Taylor expansion about
any point `ξ`, on all of `ι → ℂ`. -/
theorem hasSum_mvTaylorCoeff_sum_mul_prod_pow_mul_cexp (s : Finset κ) (c : κ → ℂ)
    (τ : κ → ι → ℕ) (w : κ → ι → ℂ) (ξ y : ι → ℂ) :
    HasSum (fun σ : ι → ℕ ↦ (∏ v, y v ^ σ v) •
        mvTaylorCoeff (fun z : ι → ℂ ↦
          ∑ k ∈ s, c k * ((∏ v, z v ^ τ k v) * Complex.exp (∑ v, w k v * z v))) ξ σ)
      (∑ k ∈ s, c k * ((∏ v, (ξ + y) v ^ τ k v) * Complex.exp (∑ v, w k v * (ξ + y) v))) := by
  simp only [mvTaylorCoeff_sum_mul_prod_pow_mul_cexp, smul_eq_mul, mul_sum]
  refine hasSum_sum fun k _ ↦ ?_
  simpa only [mvTaylorCoeff_prod_pow_mul_cexp, smul_eq_mul, mul_left_comm _ (c k)] using
    (hasSum_mvTaylorCoeff_prod_pow_mul_cexp (τ k) (w k) ξ y).mul_left (c k)

/-- **Exponential polynomials have power series on every polydisc**: a finite linear combination
of exponential monomials has, about every point `ξ` and for every radius `r > 0`, a formal
multilinear power series on the ball of radius `r`. Its multi-index coefficients are the Taylor
coefficients at `ξ`, by `HasFPowerSeriesOnBall.mvTaylorCoeff_eq`. -/
theorem exists_hasFPowerSeriesOnBall_sum_mul_prod_pow_mul_cexp (s : Finset κ) (c : κ → ℂ)
    (τ : κ → ι → ℕ) (w : κ → ι → ℂ) (ξ : ι → ℂ) {r : ℝ≥0} (hr : 0 < r) :
    ∃ p : FormalMultilinearSeries ℂ (ι → ℂ) ℂ,
      HasFPowerSeriesOnBall (fun z : ι → ℂ ↦
          ∑ k ∈ s, c k * ((∏ v, z v ^ τ k v) * Complex.exp (∑ v, w k v * z v))) p ξ r := by
  obtain ⟨p, hp, -⟩ := exists_hasFPowerSeriesOnBall_of_hasSum (f := fun z : ι → ℂ ↦
      ∑ k ∈ s, c k * ((∏ v, z v ^ τ k v) * Complex.exp (∑ v, w k v * z v))) hr
    (summable_norm_mvTaylorCoeff_sum_mul_prod_pow_mul_cexp s c τ w ξ r)
    fun y _ ↦ hasSum_mvTaylorCoeff_sum_mul_prod_pow_mul_cexp s c τ w ξ y
  exact ⟨p, hp⟩

end LinearCombination

end TauCeti

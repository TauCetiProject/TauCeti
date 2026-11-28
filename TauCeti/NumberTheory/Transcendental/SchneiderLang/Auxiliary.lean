/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.Analysis.Analytic.MultiIndex.TaylorCoeff
import TauCeti.Analysis.Complex.ExpPolynomial.Growth
import TauCeti.Analysis.Complex.ExpPolynomial.LinearIndependence
import TauCeti.Analysis.Complex.ExpPolynomial.TaylorCoeff
import TauCeti.NumberTheory.Transcendental.AuxiliaryFunction

/-!
# The Schneider–Lang auxiliary family

The auxiliary functions for the Schneider–Lang criterion on
`ℂ^d₀ × (ℂˣ)^d₁` have polynomial factors in the first `d₀` coordinates and frequencies
that are bounded natural combinations of a given family of `d₁` vectors. Their growth bound
keeps track of the common cutoff for both exponents and frequencies. When the bounded
frequencies are distinct, every nonzero coefficient vector gives a nonzero Taylor coefficient
at the origin. Rational linear independence of the generators ensures this distinctness.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren 326,
  Springer, 2000, §4.6.
* M. Karatarakis, `mkaratarakis/mathlib4`, branch `baker`, commit `1d51891b5b`,
  `Mathlib/NumberTheory/Transcendental/Baker/Criterion.lean` (Apache 2.0), for the auxiliary family.
-/

public section

open Finset Metric
open scoped Nat NNReal

namespace TauCeti.SchneiderLang

variable {n d₀ d₁ T : ℕ}

/-- The monomial exponents and frequency multipliers of an auxiliary term, all at most `T`. -/
abbrev AuxiliaryIndex (d₀ d₁ T : ℕ) :=
  (Fin d₀ → Fin (T + 1)) × (Fin d₁ → Fin (T + 1))

/-- The number of terms in the auxiliary family. -/
theorem card_auxiliaryIndex (d₀ d₁ T : ℕ) :
    Fintype.card (AuxiliaryIndex d₀ d₁ T) = (T + 1) ^ (d₀ + d₁) := by
  simp [AuxiliaryIndex, pow_add]

/-- The monomial exponents in the first `d₀` coordinates, extended by zero in the others. -/
noncomputable def auxiliaryExponent (h : d₀ ≤ n) (τ : Fin d₀ → Fin (T + 1)) : Fin n → ℕ :=
  Function.extend (Fin.castLEEmb h) (fun j ↦ (τ j : ℕ)) 0

theorem auxiliaryExponent_castLE (h : d₀ ≤ n) (τ : Fin d₀ → Fin (T + 1)) (j : Fin d₀) :
    auxiliaryExponent h τ (Fin.castLE h j) = τ j :=
  (Fin.castLEEmb h).injective.extend_apply _ _ _

@[simp]
theorem auxiliaryExponent_eq_zero_of_le (h : d₀ ≤ n) (τ : Fin d₀ → Fin (T + 1)) {v : Fin n}
    (hv : d₀ ≤ (v : ℕ)) : auxiliaryExponent h τ v = 0 := by
  refine Function.extend_apply' _ _ _ ?_
  rintro ⟨j, rfl⟩
  exact (not_le_of_gt j.isLt) hv

/-- Evaluate the auxiliary exponent at any coordinate of the ambient space. -/
theorem auxiliaryExponent_apply (h : d₀ ≤ n) (τ : Fin d₀ → Fin (T + 1)) (v : Fin n) :
    auxiliaryExponent h τ v = if hv : (v : ℕ) < d₀ then (τ ⟨v, hv⟩ : ℕ) else 0 := by
  by_cases hv : (v : ℕ) < d₀
  · have hcast : Fin.castLE h ⟨v, hv⟩ = v := Fin.ext rfl
    rw [dite_eq_left hv, ← auxiliaryExponent_castLE h τ, hcast]
  · rw [dite_eq_right hv, auxiliaryExponent_eq_zero_of_le h τ (Nat.le_of_not_gt hv)]

/-- In the first `d₀` coordinates the auxiliary exponent agrees with the original exponent. -/
@[simp]
theorem auxiliaryExponent_of_lt (h : d₀ ≤ n) (τ : Fin d₀ → Fin (T + 1)) {v : Fin n}
    (hv : (v : ℕ) < d₀) : auxiliaryExponent h τ v = τ ⟨v, hv⟩ := by
  rw [auxiliaryExponent_apply, dite_eq_left hv]

/-- The zero monomial exponent vector extends to zero in the ambient space. -/
@[simp]
theorem auxiliaryExponent_zero (h : d₀ ≤ n) :
    auxiliaryExponent h (0 : Fin d₀ → Fin (T + 1)) = 0 := by
  rw [auxiliaryExponent]
  exact Function.extend_const (Fin.castLEEmb h) (0 : ℕ)

/-- The total degree after extending a monomial's exponents by zero. -/
theorem sum_auxiliaryExponent (h : d₀ ≤ n) (τ : Fin d₀ → Fin (T + 1)) :
    ∑ v, auxiliaryExponent h τ v = ∑ j, (τ j : ℕ) :=
  sum_extend_zero_of_injective _ (Fin.castLEEmb h).injective (fun _ ↦ mem_univ _)

/-- The degree of an auxiliary monomial is at most `d₀ * T`. -/
theorem sum_auxiliaryExponent_le (h : d₀ ≤ n) (τ : Fin d₀ → Fin (T + 1)) :
    ∑ v, auxiliaryExponent h τ v ≤ d₀ * T := by
  rw [sum_auxiliaryExponent]
  simpa [nsmul_eq_mul] using
    (sum_le_card_nsmul univ (fun j ↦ (τ j : ℕ)) T fun j _ ↦ Nat.lt_succ_iff.1 (τ j).isLt)

/-- The frequency vector with multipliers `t`, namely `∑ i, t i • x i`. -/
noncomputable def auxiliaryFrequency (x : Fin d₁ → Fin n → ℂ) (t : Fin d₁ → Fin (T + 1)) :
    Fin n → ℂ :=
  ∑ i, (t i : ℕ) • x i

@[simp]
theorem auxiliaryFrequency_apply (x : Fin d₁ → Fin n → ℂ) (t : Fin d₁ → Fin (T + 1))
    (v : Fin n) : auxiliaryFrequency x t v = ∑ i, (t i : ℕ) * x i v := by
  simp only [auxiliaryFrequency, Finset.sum_apply, ← Nat.cast_smul_eq_nsmul ℂ, Pi.smul_apply,
    smul_eq_mul]

/-- The linear map from coefficient vectors to Schneider–Lang auxiliary functions. -/
noncomputable def auxiliaryFunction (h : d₀ ≤ n) (x : Fin d₁ → Fin n → ℂ) :
    (AuxiliaryIndex d₀ d₁ T → ℂ) →ₗ[ℂ] ((Fin n → ℂ) → ℂ) :=
  Fintype.linearCombination ℂ fun a z ↦
    (∏ v, z v ^ auxiliaryExponent h a.1 v) *
      Complex.exp (∑ v, auxiliaryFrequency x a.2 v * z v)

/-- Pointwise evaluation of the auxiliary family as a sum of exponential monomials. -/
theorem auxiliaryFunction_apply (h : d₀ ≤ n) (x : Fin d₁ → Fin n → ℂ)
    (p : AuxiliaryIndex d₀ d₁ T → ℂ) (z : Fin n → ℂ) :
    auxiliaryFunction h x p z =
      ∑ a, p a * ((∏ v, z v ^ auxiliaryExponent h a.1 v) *
        Complex.exp (∑ v, auxiliaryFrequency x a.2 v * z v)) := by
  simp only [auxiliaryFunction, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]

/-- A coefficient vector supported at one index gives a multiple of its exponential monomial. -/
@[simp]
theorem auxiliaryFunction_apply_single (h : d₀ ≤ n) (x : Fin d₁ → Fin n → ℂ)
    (a : AuxiliaryIndex d₀ d₁ T) (c : ℂ) (z : Fin n → ℂ) :
    auxiliaryFunction h x (Pi.single a c) z =
      c * ((∏ v, z v ^ auxiliaryExponent h a.1 v) *
        Complex.exp (∑ v, auxiliaryFrequency x a.2 v * z v)) := by
  rw [auxiliaryFunction, Fintype.linearCombination_apply_single, Pi.smul_apply, smul_eq_mul]

/-- Every auxiliary function has a power series about every point on every positive-radius
polydisc. -/
theorem exists_hasFPowerSeriesOnBall_auxiliaryFunction (h : d₀ ≤ n) (x : Fin d₁ → Fin n → ℂ)
    (p : AuxiliaryIndex d₀ d₁ T → ℂ) (ξ : Fin n → ℂ) {r : ℝ≥0} (hr : 0 < r) :
    ∃ q : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ,
      HasFPowerSeriesOnBall (auxiliaryFunction h x p) q ξ r := by
  simpa only [← auxiliaryFunction_apply] using
    exists_hasFPowerSeriesOnBall_sum_mul_prod_pow_mul_cexp univ p
      (fun a ↦ auxiliaryExponent h a.1) (fun a ↦ auxiliaryFrequency x a.2) ξ hr

/-- Every Schneider–Lang auxiliary function is entire. -/
theorem analyticOnNhd_auxiliaryFunction (h : d₀ ≤ n) (x : Fin d₁ → Fin n → ℂ)
    (p : AuxiliaryIndex d₀ d₁ T → ℂ) :
    AnalyticOnNhd ℂ (auxiliaryFunction h x p) Set.univ := by
  intro ξ _
  obtain ⟨q, hq⟩ := exists_hasFPowerSeriesOnBall_auxiliaryFunction h x p ξ zero_lt_one
  exact hq.analyticAt

/-- The Taylor coefficients of an auxiliary function are sums of the coefficients of its
exponential monomials, weighted by the auxiliary coefficient vector. -/
theorem mvTaylorCoeff_auxiliaryFunction (h : d₀ ≤ n) (x : Fin d₁ → Fin n → ℂ)
    (p : AuxiliaryIndex d₀ d₁ T → ℂ) (ξ : Fin n → ℂ) (σ : Fin n → ℕ) :
    mvTaylorCoeff (auxiliaryFunction h x p) ξ σ =
      ∑ a, p a * (Complex.exp (∑ v, auxiliaryFrequency x a.2 v * ξ v) *
        ∏ v, ∑ j ∈ range (σ v + 1), ((auxiliaryExponent h a.1 v).choose j : ℂ) *
          ξ v ^ (auxiliaryExponent h a.1 v - j) *
          (auxiliaryFrequency x a.2 v ^ (σ v - j) / (σ v - j)!)) := by
  simpa only [← auxiliaryFunction_apply] using
    mvTaylorCoeff_sum_mul_prod_pow_mul_cexp univ p
      (fun a ↦ auxiliaryExponent h a.1) (fun a ↦ auxiliaryFrequency x a.2) ξ σ

/-- The growth bound on the polydisc of radius `ρ`, with coefficient norms at most `exp N`
and sum of the generator coordinate norms at most `A`. -/
noncomputable def auxiliaryGrowth (d₀ d₁ T : ℕ) (N A ρ : ℝ) : ℝ :=
  ((T : ℝ) + 1) ^ (d₀ + d₁) * Real.exp N * (1 + ρ) ^ (d₀ * T) *
    Real.exp (T * A * ρ)

theorem auxiliaryGrowth_def (d₀ d₁ T : ℕ) (N A ρ : ℝ) :
    auxiliaryGrowth d₀ d₁ T N A ρ =
      ((T : ℝ) + 1) ^ (d₀ + d₁) * Real.exp N * (1 + ρ) ^ (d₀ * T) *
        Real.exp (T * A * ρ) := (rfl)

@[simp]
theorem auxiliaryGrowth_zero_cutoff (d₀ d₁ : ℕ) (N A ρ : ℝ) :
    auxiliaryGrowth d₀ d₁ 0 N A ρ = Real.exp N := by
  simp [auxiliaryGrowth_def]

/-- On nonnegative radii and generator bounds, the growth bound is nondecreasing in the cutoff,
coefficient exponent, generator bound and radius. -/
theorem auxiliaryGrowth_le_auxiliaryGrowth {T' : ℕ} {N N' A A' ρ ρ' : ℝ}
    (hT : T ≤ T') (hN : N ≤ N') (hA : A ≤ A') (hρ : ρ ≤ ρ') (hA₀ : 0 ≤ A) (hρ₀ : 0 ≤ ρ) :
    auxiliaryGrowth d₀ d₁ T N A ρ ≤ auxiliaryGrowth d₀ d₁ T' N' A' ρ' := by
  have hA' : 0 ≤ A' := hA₀.trans hA
  have hρ' : 0 ≤ ρ' := hρ₀.trans hρ
  rw [auxiliaryGrowth_def, auxiliaryGrowth_def]
  have hpow : (1 + ρ) ^ (d₀ * T) ≤ (1 + ρ') ^ (d₀ * T') := by
    calc
      (1 + ρ) ^ (d₀ * T) ≤ (1 + ρ') ^ (d₀ * T) := by gcongr
      _ ≤ (1 + ρ') ^ (d₀ * T') :=
        pow_le_pow_right₀ (le_add_of_nonneg_right hρ') (Nat.mul_le_mul_left _ hT)
  gcongr

/-- The growth bound is at least the coefficient bound for nonnegative radii and generator
bounds. -/
theorem exp_le_auxiliaryGrowth {N A ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ) :
    Real.exp N ≤ auxiliaryGrowth d₀ d₁ T N A ρ := by
  rw [← auxiliaryGrowth_zero_cutoff d₀ d₁ N A ρ]
  exact auxiliaryGrowth_le_auxiliaryGrowth (Nat.zero_le _) le_rfl le_rfl le_rfl hA hρ

/-- The sum of the coordinate norms of an auxiliary frequency is bounded by the cutoff times
the sum of the coordinate norms of the generators. -/
theorem sum_norm_auxiliaryFrequency_le (x : Fin d₁ → Fin n → ℂ)
    (t : Fin d₁ → Fin (T + 1)) :
    ∑ v, ‖auxiliaryFrequency x t v‖ ≤ (T : ℝ) * ∑ i, ∑ v, ‖x i v‖ := by
  calc
    ∑ v, ‖auxiliaryFrequency x t v‖ ≤ ∑ v, ∑ i, (T : ℝ) * ‖x i v‖ := by
      refine sum_le_sum fun v _ ↦ ?_
      rw [auxiliaryFrequency_apply]
      refine (norm_sum_le _ _).trans (sum_le_sum fun i _ ↦ ?_)
      rw [norm_mul, Complex.norm_natCast]
      gcongr
      exact_mod_cast Nat.lt_succ_iff.1 (t i).isLt
    _ = _ := by rw [sum_comm]; simp only [mul_sum]

/-- The auxiliary family on a closed polydisc is bounded by `auxiliaryGrowth`. -/
theorem norm_auxiliaryFunction_le (h : d₀ ≤ n) (x : Fin d₁ → Fin n → ℂ)
    (p : AuxiliaryIndex d₀ d₁ T → ℂ) {N ρ : ℝ} (hp : ‖p‖ ≤ Real.exp N)
    {z : Fin n → ℂ} (hz : ‖z‖ ≤ ρ) :
    ‖auxiliaryFunction h x p z‖ ≤ auxiliaryGrowth d₀ d₁ T N (∑ i, ∑ v, ‖x i v‖) ρ := by
  rw [auxiliaryFunction_apply, auxiliaryGrowth_def]
  simpa only [card_univ, card_auxiliaryIndex, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    norm_sum_mul_prod_pow_mul_cexp_le_of_le (s := univ) (c := p)
      (fun a _ ↦ (norm_le_pi_norm p a).trans hp)
      (fun a _ ↦ sum_auxiliaryExponent_le h a.1)
      (fun a _ ↦ sum_norm_auxiliaryFrequency_le x a.2) hz

/-- Rational linear independence of the generators makes the natural frequency
multipliers recoverable from the resulting vector. -/
theorem auxiliaryFrequency_injective {x : Fin d₁ → Fin n → ℂ}
    (hx : LinearIndependent ℚ x) :
    Function.Injective (auxiliaryFrequency (T := T) x) := by
  intro t u htu
  have heq := Fintype.linearIndependent_iffₛ.1 hx
    (fun i ↦ ((t i : ℕ) : ℚ)) (fun i ↦ ((u i : ℕ) : ℚ))
  simp only [Nat.cast_smul_eq_nsmul] at heq
  exact funext fun i ↦ Fin.ext (by exact_mod_cast heq htu i)

/-- Distinct auxiliary frequencies ensure that the function determines its coefficient vector. -/
theorem auxiliaryFunction_injective (h : d₀ ≤ n) {x : Fin d₁ → Fin n → ℂ}
    (hx : Function.Injective (auxiliaryFrequency (T := T) x)) :
    Function.Injective (auxiliaryFunction (T := T) h x) := by
  apply linearIndependent_iff_injective_fintypeLinearCombination.1
  exact linearIndependent_prod_pow_mul_cexp.comp
    (fun a : AuxiliaryIndex d₀ d₁ T ↦ (auxiliaryExponent h a.1, auxiliaryFrequency x a.2))
    (fun a b hab ↦ Prod.ext
      (funext fun j ↦ Fin.ext (by
        simpa only [Fin.castLEEmb_apply, auxiliaryExponent_castLE] using
          congrFun (congrArg Prod.fst hab) (Fin.castLEEmb h j)))
      (hx (congrArg Prod.snd hab)))

/-- A nonzero auxiliary coefficient vector yields a nonzero Taylor coefficient at the origin
when the bounded auxiliary frequencies are distinct. -/
theorem exists_mvTaylorCoeff_auxiliaryFunction_ne_zero (h : d₀ ≤ n)
    {x : Fin d₁ → Fin n → ℂ} (hx : Function.Injective (auxiliaryFrequency (T := T) x))
    {p : AuxiliaryIndex d₀ d₁ T → ℂ} (hp : p ≠ 0) :
    ∃ σ : Fin n → ℕ, mvTaylorCoeff (auxiliaryFunction h x p) 0 σ ≠ 0 := by
  by_contra! hσ
  apply hp (auxiliaryFunction_injective h hx ?_)
  rw [map_zero]
  funext z
  have hs := hasSum_mvTaylorCoeff_sum_mul_prod_pow_mul_cexp univ p
    (fun a ↦ auxiliaryExponent h a.1) (fun a ↦ auxiliaryFrequency x a.2) 0 z
  simp only [← auxiliaryFunction_apply, zero_add, hσ, smul_zero] at hs
  have hz : auxiliaryFunction h x p z = 0 := hs.unique hasSum_zero
  exact hz

/-- Waldschmidt's small-value construction applied to the Schneider–Lang auxiliary family.
The growth bound with `N = 0` controls the sum of the bounds for the individual terms. -/
theorem exists_ne_zero_int_norm_auxiliaryFunction_le (h : d₀ ≤ n) (hn : 0 < n)
    (x : Fin d₁ → Fin n → ℂ) {R : ℝ≥0} {N U V r : ℝ}
    (hU : auxiliaryGrowth d₀ d₁ T 0 (∑ i, ∑ v, ‖x i v‖) R ≤ Real.exp U)
    (hW : 12 ≤ N + U + V) (hRr : Real.exp 1 ≤ R / r) (hRr' : R / r ≤ Real.exp ((N + U + V) / 6))
    (hL : (2 * (N + U + V)) ^ (n + 1) ≤ ((T : ℝ) + 1) ^ (d₀ + d₁) * N *
      Real.log (R / r) ^ n) :
    ∃ p : AuxiliaryIndex d₀ d₁ T → ℤ, p ≠ 0 ∧ (∀ a, |(p a : ℝ)| ≤ Real.exp N) ∧
      ∀ z ∈ closedBall (0 : Fin n → ℂ) r,
        ‖auxiliaryFunction h x (fun a ↦ (p a : ℂ)) z‖ ≤ Real.exp (-V) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 hn
  have hR : 0 < R := by
    by_contra! hzero
    have hzero : R = 0 := le_antisymm hzero zero_le
    simp only [hzero, NNReal.coe_zero, zero_div] at hRr
    exact (Real.exp_pos 1).not_ge hRr
  have hφ (a : AuxiliaryIndex d₀ d₁ T) :=
    exists_hasFPowerSeriesOnBall_auxiliaryFunction h x (Pi.single a 1) 0 hR
  choose q hq using hφ
  let A : ℝ := ∑ i, ∑ v, ‖x i v‖
  let M : ℝ := (1 + (R : ℝ)) ^ (d₀ * T) * Real.exp (T * A * R)
  have hM (a : AuxiliaryIndex d₀ d₁ T) (z) (hz : z ∈ ball (0 : Fin n → ℂ) R) :
      ‖auxiliaryFunction h x (Pi.single a 1) z‖ ≤ M := by
    simp only [auxiliaryFunction_apply_single, one_mul]
    exact norm_prod_pow_mul_cexp_le_of_le (sum_auxiliaryExponent_le h a.1)
      (sum_norm_auxiliaryFrequency_le x a.2) (mem_ball_zero_iff.1 hz).le
  have hMU : ∑ _a : AuxiliaryIndex d₀ d₁ T, M ≤ Real.exp U := by
    simpa only [sum_const, nsmul_eq_mul, card_univ, card_auxiliaryIndex, Nat.cast_pow,
      Nat.cast_add, Nat.cast_one, M, A, auxiliaryGrowth_def, Real.exp_zero, mul_one,
      mul_assoc] using hU
  have hcount : (2 * (N + U + V)) ^ (Fintype.card (Fin n) + 1) ≤
      Fintype.card (AuxiliaryIndex d₀ d₁ T) * N * Real.log (R / r) ^ Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin, card_auxiliaryIndex, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one] using hL
  obtain ⟨p, hp, hpN, hsmall⟩ := exists_ne_zero_int_norm_sum_le hq hM hMU hW hRr hRr' hcount
  simp only [auxiliaryFunction_apply_single, one_mul] at hsmall
  exact ⟨p, hp, hpN, fun z hz ↦ by simpa only [auxiliaryFunction_apply] using hsmall z hz⟩

end TauCeti.SchneiderLang

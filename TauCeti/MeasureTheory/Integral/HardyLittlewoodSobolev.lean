/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.MaximalFunction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Hardy–Littlewood–Sobolev inequality

Let `E` be a real normed space of finite dimension `n ≥ 1` with an additive Haar measure `μ`. For
`0 < α < n` the **Riesz potential** of order `α` of a function `f` is

`I_α f (x) = ∫ ‖x - y‖ ^ (α - n) f(y) dy`,

up to the normalising constant, which plays no role here. Fractional integration gains `α`
derivatives in the scale of Lebesgue spaces: for `1 < p` and `q < ∞` with
`1 / p - 1 / q = α / n` there is `C` with

`‖I_α f‖_q ≤ C ‖f‖_p`

(`TauCeti.eLpNorm_lintegral_enorm_sub_rpow_mul_enorm_le`, for the potential of `‖f‖`, and
`TauCeti.eLpNorm_integral_norm_sub_rpow_smul_le`, for the Bochner integral of a function with
values in a real normed space). On the line this is the time integration behind the Strichartz
estimates, and in higher dimension it gives the Sobolev embeddings on the whole space. On a set
of finite measure, Young's inequality alone gives the bound for every `q` strictly below this
critical exponent (`TauCeti.eLpNorm_setLIntegral_enorm_sub_rpow_mul_le`); the critical exponent
needs the maximal function.

The proof is Hedberg's. Split the potential at a radius `R` about `x`. The dyadic shells
`R / 2 ^ (k + 1) < ‖x - y‖ ≤ R / 2 ^ k` inside the ball contribute at most a multiple of
`R ^ α M f (x)`, where `M f` is the Hardy–Littlewood maximal function, because each shell lies in a
ball about `x` of comparable radius. Outside the ball, Hölder's inequality with the exponent `q'`
conjugate to `p` bounds the potential by `‖f‖_p` times the `L^{q'}` norm of the kernel there, which
is a multiple of `R ^ (α - n / p)` because `(n - α) q' > n`; it is computed by summing over the
dyadic shells `2 ^ k R ≤ ‖x - y‖ < 2 ^ (k + 1) R`. Choosing `R = (‖f‖_p / M f (x)) ^ (p / n)`
balances the two terms and gives **Hedberg's inequality**

`I_α |f| (x) ≤ C (M f (x)) ^ (1 - α p / n) ‖f‖_p ^ (α p / n)`

(`TauCeti.lintegral_enorm_sub_rpow_mul_enorm_le`). Since `(1 - α p / n) q = p`, raising it to the
power `q` and integrating reduces the theorem to the strong-type `(p, p)` maximal inequality
`TauCeti.lintegral_rpow_maximalFunction_le`.

## Main declarations

* `TauCeti.lintegral_enorm_sub_rpow_mul_enorm_le`: Hedberg's pointwise inequality.
* `TauCeti.eLpNorm_lintegral_enorm_sub_rpow_mul_enorm_le`: the Hardy–Littlewood–Sobolev
  inequality for the potential of `‖f‖`.
* `TauCeti.eLpNorm_integral_norm_sub_rpow_smul_le`: the Hardy–Littlewood–Sobolev inequality for
  the vector-valued potential.

## References

* L. I. Hedberg, *On certain convolution inequalities*, Proc. Amer. Math. Soc. 36 (1972),
  505–510.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V,
  §1.2, Theorem 1.
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 1.2.1.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Module Set
open scoped ENNReal NNReal

section Shells

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (ν : Measure X)

/-- If `k` is dominated by a weighted sum of indicators of balls about `x`, then `∫ k g` is
dominated by the same weighted sum of the integrals of `g` over these balls. -/
private theorem lintegral_mul_le_tsum_mul_setLIntegral_ball {x : X} {k g : X → ℝ≥0∞}
    (hg : AEMeasurable g ν) (c : ℕ → ℝ≥0∞) (r : ℕ → ℝ)
    (hk : ∀ᵐ y ∂ν, k y ≤ ∑' i, (ball x (r i)).indicator (fun _ ↦ c i) y) :
    ∫⁻ y, k y * g y ∂ν ≤ ∑' i, c i * ∫⁻ y in ball x (r i), g y ∂ν := by
  calc ∫⁻ y, k y * g y ∂ν
      ≤ ∫⁻ y, ∑' i, (ball x (r i)).indicator (fun _ ↦ c i) y * g y ∂ν := by
        refine lintegral_mono_ae (hk.mono fun y hy => ?_)
        rw [ENNReal.tsum_mul_right]
        exact mul_le_mul_left hy _
    _ = ∑' i, ∫⁻ y, (ball x (r i)).indicator (fun _ ↦ c i) y * g y ∂ν :=
        lintegral_tsum fun i => (aemeasurable_const.indicator measurableSet_ball).mul hg
    _ = ∑' i, c i * ∫⁻ y in ball x (r i), g y ∂ν := by
        refine tsum_congr fun i => ?_
        rw [← lintegral_const_mul'' _ hg.restrict, ← lintegral_indicator measurableSet_ball]
        congr 1 with y
        by_cases hy : y ∈ ball x (r i) <;> simp [hy]

end Shells

section Kernel

variable {E : Type*} [NormedAddCommGroup E]

/-- Near `x`, the kernel `‖x - y‖ ^ γ`, `γ ≤ 0`, is dominated on each dyadic shell
`R / 2 ^ (i + 1) < ‖x - y‖ ≤ R / 2 ^ i` by its value at the inner radius. -/
private theorem indicator_closedBall_enorm_sub_rpow_le {x y : E} (hyx : y ≠ x) {R γ : ℝ}
    (hR : 0 < R) (hγ : γ ≤ 0) :
    (closedBall x R).indicator (fun y ↦ ‖x - y‖ₑ ^ γ) y ≤
      ∑' i : ℕ, (ball x (2 * R / 2 ^ i)).indicator
        (fun _ ↦ ENNReal.ofReal ((R / 2 ^ (i + 1)) ^ γ)) y := by
  by_cases hy : y ∈ closedBall x R
  swap
  · simp [hy]
  rw [indicator_of_mem hy]
  have ht : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx.symm)
  have htR : ‖x - y‖ ≤ R := by rwa [mem_closedBall, dist_comm, dist_eq_norm] at hy
  obtain ⟨i, hi₁, hi₂⟩ := exists_nat_pow_near ((one_le_div ht).2 htR) one_lt_two
  rw [le_div_iff₀ ht] at hi₁
  rw [div_lt_iff₀ ht] at hi₂
  refine le_trans ?_ (le_tsum _ i)
  have hmem : y ∈ ball x (2 * R / 2 ^ i) := by
    rw [mem_ball, dist_comm, dist_eq_norm, lt_div_iff₀ (by positivity)]
    nlinarith
  rw [indicator_of_mem hmem, ← ofReal_norm, ENNReal.ofReal_rpow_of_pos ht]
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hγ)
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- Away from `x`, the kernel `‖x - y‖ ^ γ`, `γ ≤ 0`, is dominated on each dyadic shell
`2 ^ i R ≤ ‖x - y‖ < 2 ^ (i + 1) R` by its value at the inner radius. -/
private theorem indicator_compl_closedBall_enorm_sub_rpow_le (x y : E) {R γ : ℝ}
    (hR : 0 < R) (hγ : γ ≤ 0) :
    (closedBall x R)ᶜ.indicator (fun y ↦ ‖x - y‖ₑ ^ γ) y ≤
      ∑' i : ℕ, (ball x (2 ^ (i + 1) * R)).indicator
        (fun _ ↦ ENNReal.ofReal ((2 ^ i * R) ^ γ)) y := by
  by_cases hy : y ∈ (closedBall x R)ᶜ
  swap
  · simp [hy]
  rw [indicator_of_mem hy]
  have htR : R < ‖x - y‖ := by
    rwa [mem_compl_iff, mem_closedBall, not_le, dist_comm, dist_eq_norm] at hy
  have ht : 0 < ‖x - y‖ := hR.trans htR
  obtain ⟨i, hi₁, hi₂⟩ := exists_nat_pow_near ((one_le_div hR).2 htR.le) one_lt_two
  rw [le_div_iff₀ hR] at hi₁
  rw [div_lt_iff₀ hR] at hi₂
  refine le_trans ?_ (le_tsum _ i)
  have hmem : y ∈ ball x (2 ^ (i + 1) * R) := by
    rwa [mem_ball, dist_comm, dist_eq_norm]
  rw [indicator_of_mem hmem, ← ofReal_norm, ENNReal.ofReal_rpow_of_pos ht]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) hi₁ hγ)

end Kernel

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  [TopologicalSpace F] [ENormedAddMonoid F]

/-- The part of the Riesz potential of order `α ≤ n = dim E` coming from the closed ball
`closedBall x R` is controlled by the maximal function at `x`. -/
private theorem setLIntegral_closedBall_enorm_sub_rpow_mul_le (x : E) {R α : ℝ} (hR : 0 < R)
    (hα : 0 < α) (hαn : α ≤ finrank ℝ E) {f : E → F} (hf : AEStronglyMeasurable f μ) :
    ∫⁻ y in closedBall x R, ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ ≤
      ENNReal.ofReal (4 ^ finrank ℝ E * R ^ α / (2 ^ α - 1)) * μ (ball 0 1) *
        maximalFunction μ f x := by
  set n := finrank ℝ E
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    have : (0 : ℝ) < n := hα.trans_le hαn
    exact_mod_cast this)
  set ρ : ℝ := (2 ^ α)⁻¹
  have h2α : 1 < (2 : ℝ) ^ α := Real.one_lt_rpow one_lt_two hα
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ h2α
  -- The `i`-th dyadic shell contributes `4ⁿ Rᵅ ρ ρⁱ` times `ωₙ M f(x)`.
  have hterm (i : ℕ) : (R / 2 ^ (i + 1)) ^ (α - n) * (2 * R / 2 ^ i) ^ n =
      4 ^ n * R ^ α * ρ * ρ ^ i := by
    have hu : 0 < R / 2 ^ (i + 1) := by positivity
    have h4 : 2 * R / 2 ^ i = 4 * (R / 2 ^ (i + 1)) := by
      rw [pow_succ]
      field_simp
      ring
    rw [h4, mul_pow, Real.rpow_sub hu, Real.rpow_natCast, Real.div_rpow hR.le (by positivity),
      ← Real.rpow_pow_comm (by norm_num)]
    simp only [ρ, inv_pow, pow_succ]
    field_simp
  rw [← lintegral_indicator measurableSet_closedBall]
  simp_rw [indicator_mul_left]
  calc ∫⁻ y, (closedBall x R).indicator (fun y ↦ ‖x - y‖ₑ ^ (α - n)) y * ‖f y‖ₑ ∂μ
      ≤ ∑' i : ℕ, ENNReal.ofReal ((R / 2 ^ (i + 1)) ^ (α - n)) *
          ∫⁻ y in ball x (2 * R / 2 ^ i), ‖f y‖ₑ ∂μ :=
        lintegral_mul_le_tsum_mul_setLIntegral_ball μ hf.enorm _ _
          ((Measure.ae_ne μ x).mono fun y hy =>
            indicator_closedBall_enorm_sub_rpow_le hy hR (by linarith))
    _ ≤ ∑' i : ℕ, ENNReal.ofReal ((R / 2 ^ (i + 1)) ^ (α - n)) *
          (μ (ball x (2 * R / 2 ^ i)) * maximalFunction μ f x) := by
        gcongr with i
        exact setLIntegral_ball_le_measure_mul_maximalFunction μ f x (by positivity)
          measure_ball_lt_top.ne
    _ = ∑' i : ℕ, ENNReal.ofReal (4 ^ n * R ^ α * ρ * ρ ^ i) *
          (μ (ball 0 1) * maximalFunction μ f x) := by
        refine tsum_congr fun i => ?_
        rw [Measure.addHaar_ball_of_pos μ _ (by positivity), ← mul_assoc, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), hterm, mul_assoc]
    _ = ENNReal.ofReal (4 ^ n * R ^ α / (2 ^ α - 1)) * μ (ball 0 1) *
          maximalFunction μ f x := by
        rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
          ((summable_geometric_of_lt_one hρ0 hρ1).mul_left _), tsum_mul_left,
          tsum_geometric_of_lt_one hρ0 hρ1, ← mul_assoc]
        congr 2
        simp only [ρ]
        field_simp

/-- Outside the closed ball `closedBall x R`, the kernel `‖x - y‖ ^ (-s)` with `s > n = dim E` has
integral at most a multiple of `R ^ (n - s)`. -/
private theorem setLIntegral_compl_closedBall_enorm_sub_rpow_le (x : E) {R s : ℝ} (hR : 0 < R)
    (hs : finrank ℝ E < s) :
    ∫⁻ y in (closedBall x R)ᶜ, ‖x - y‖ₑ ^ (-s) ∂μ ≤
      ENNReal.ofReal (2 ^ finrank ℝ E * R ^ (finrank ℝ E - s) * (1 - 2 ^ (finrank ℝ E - s))⁻¹) *
        μ (ball 0 1) := by
  set n := finrank ℝ E
  set τ : ℝ := 2 ^ (n - s)
  have hτ0 : 0 ≤ τ := by positivity
  have hτ1 : τ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  -- The `i`-th dyadic shell contributes `2ⁿ R^(n - s) τⁱ` times `ωₙ`.
  have hterm (i : ℕ) : (2 ^ i * R) ^ (-s) * (2 ^ (i + 1) * R) ^ n =
      2 ^ n * R ^ (n - s) * τ ^ i := by
    have hv : 0 < 2 ^ i * R := by positivity
    have h2 : (2 : ℝ) ^ (i + 1) * R = 2 * (2 ^ i * R) := by ring
    rw [h2, mul_pow, mul_left_comm, ← Real.rpow_natCast (2 ^ i * R) n, ← Real.rpow_add hv,
      neg_add_eq_sub, Real.mul_rpow (by positivity) hR.le, ← Real.rpow_pow_comm (by norm_num)]
    ring
  calc ∫⁻ y in (closedBall x R)ᶜ, ‖x - y‖ₑ ^ (-s) ∂μ
      = ∫⁻ y, (closedBall x R)ᶜ.indicator (fun y ↦ ‖x - y‖ₑ ^ (-s)) y * 1 ∂μ := by
        rw [← lintegral_indicator measurableSet_closedBall.compl]
        simp
    _ ≤ ∑' i : ℕ, ENNReal.ofReal ((2 ^ i * R) ^ (-s)) *
          ∫⁻ _ in ball x (2 ^ (i + 1) * R), 1 ∂μ :=
        lintegral_mul_le_tsum_mul_setLIntegral_ball μ aemeasurable_const _ _
          (.of_forall fun y => indicator_compl_closedBall_enorm_sub_rpow_le x y hR
            (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
    _ = ∑' i : ℕ, ENNReal.ofReal (2 ^ n * R ^ (n - s) * τ ^ i) * μ (ball 0 1) := by
        refine tsum_congr fun i => ?_
        rw [setLIntegral_one, Measure.addHaar_ball_of_pos μ _ (by positivity), ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), hterm]
    _ = ENNReal.ofReal (2 ^ n * R ^ (n - s) * (1 - τ)⁻¹) * μ (ball 0 1) := by
        rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
          ((summable_geometric_of_lt_one hτ0 hτ1).mul_left _), tsum_mul_left,
          tsum_geometric_of_lt_one hτ0 hτ1]

/-- Away from `x`, Hölder's inequality with conjugate exponents `p` and `q` bounds the part of the
Riesz potential of order `α` coming from the complement of `closedBall x R` by the `Lᵖ` norm of
`f`, provided `s = (n - α) q > n = dim E`. -/
private theorem setLIntegral_compl_closedBall_enorm_sub_rpow_mul_le (x : E) {R α p q : ℝ}
    (hR : 0 < R) (hpq : p.HolderConjugate q) (hs : finrank ℝ E < (finrank ℝ E - α) * q)
    {f : E → F} (hf : AEStronglyMeasurable f μ) :
    ∫⁻ y in (closedBall x R)ᶜ, ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ ≤
      (ENNReal.ofReal (2 ^ finrank ℝ E * R ^ (finrank ℝ E - (finrank ℝ E - α) * q) *
        (1 - 2 ^ (finrank ℝ E - (finrank ℝ E - α) * q))⁻¹) * μ (ball 0 1)) ^ (1 / q) *
        (∫⁻ y, ‖f y‖ₑ ^ p ∂μ) ^ (1 / p) := by
  set n := finrank ℝ E
  have hk : AEMeasurable (fun y ↦ ‖x - y‖ₑ ^ (α - n)) (μ.restrict (closedBall x R)ᶜ) := by
    fun_prop
  calc ∫⁻ y in (closedBall x R)ᶜ, ‖x - y‖ₑ ^ (α - n) * ‖f y‖ₑ ∂μ
      ≤ (∫⁻ y in (closedBall x R)ᶜ, (‖x - y‖ₑ ^ (α - n)) ^ q ∂μ) ^ (1 / q) *
          (∫⁻ y in (closedBall x R)ᶜ, ‖f y‖ₑ ^ p ∂μ) ^ (1 / p) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq.symm hk hf.enorm.restrict
    _ ≤ _ := by
        refine mul_le_mul' (ENNReal.rpow_le_rpow ?_ (by simpa using hpq.symm.nonneg))
          (ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _) (by simpa using hpq.nonneg))
        simp_rw [← ENNReal.rpow_mul, show (α - n) * q = -((n - α) * q) by ring]
        exact setLIntegral_compl_closedBall_enorm_sub_rpow_le μ x hR hs

/-- The two terms of Hedberg's splitting balance at the radius `R = (N / m) ^ (p / n)`: there,
`R ^ α m` and `R ^ ((n - s) / q) N` are both `m ^ (1 - θ) N ^ θ`, where `θ = α p / n`,
`s = (n - α) q` and `q` is the exponent conjugate to `p`. -/
private theorem rpow_mul_eq_and_rpow_rpow_mul_eq {n α p q m N : ℝ} (hn : 0 < n)
    (hpq : p.HolderConjugate q) (hm : 0 < m) (hN : 0 < N) :
    ((N / m) ^ (p / n)) ^ α * m = m ^ (1 - α * p / n) * N ^ (α * p / n) ∧
      (((N / m) ^ (p / n)) ^ (n - (n - α) * q)) ^ (1 / q) * N =
        m ^ (1 - α * p / n) * N ^ (α * p / n) := by
  have hNm : 0 ≤ N / m := by positivity
  have hq : q ≠ 0 := hpq.symm.ne_zero
  have hp : p ≠ 0 := hpq.ne_zero
  have hpq' : q⁻¹ = 1 - p⁻¹ := by linarith [hpq.inv_add_inv_eq_one]
  simp_rw [← Real.rpow_mul hNm]
  constructor
  · rw [show p / n * α = α * p / n by ring, Real.div_rpow hN.le hm.le,
      Real.rpow_sub hm, Real.rpow_one]
    field_simp
  · have he : p / n * (n - (n - α) * q) * (1 / q) = α * p / n - 1 := by
      rw [show p / n * (n - (n - α) * q) * (1 / q) = p / n * (n * q⁻¹ - (n - α)) by
        field_simp, hpq']
      field_simp
      ring
    rw [he, Real.div_rpow hN.le hm.le, Real.rpow_sub_one hN.ne', Real.rpow_sub_one hm.ne',
      Real.rpow_sub hm, Real.rpow_one]
    field_simp

/-- **Hedberg's inequality.** Let `n = dim E`, `0 < α`, `1 < p` and `α p < n`. There is a
constant `C`, depending only on `μ`, `α` and `p`, such that the Riesz potential of order `α` of
every `f` is bounded pointwise by its maximal function and its `Lᵖ` norm:

`∫ ‖x - y‖ ^ (α - n) ‖f y‖ dy ≤ C (M f x) ^ (1 - α p / n) ‖f‖_p ^ (α p / n)`. -/
theorem lintegral_enorm_sub_rpow_mul_enorm_le {α : ℝ} {p : ℝ≥0} (hα : 0 < α) (hp : 1 < p)
    (hαp : α * p < finrank ℝ E) :
    ∃ C : ℝ≥0, ∀ f : E → F, AEStronglyMeasurable f μ → ∀ x : E,
      ∫⁻ y, ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ ≤
        C * maximalFunction μ f x ^ (1 - α * p / finrank ℝ E) *
          eLpNorm f p μ ^ (α * p / finrank ℝ E) := by
  set n := finrank ℝ E
  have hp0 : (0 : ℝ) < p := by positivity
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hn : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hαp
  have hαn : α ≤ n := by nlinarith
  set q := (p : ℝ).conjExponent
  have hpq : (p : ℝ).HolderConjugate q := .conjExponent hp1
  have hs : (n : ℝ) < (n - α) * q := by
    have h := hpq.sub_one_mul_conj
    have hq0 : 0 < q := hpq.symm.pos
    nlinarith
  set θ := α * p / n
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := (div_lt_one hn).2 hαp
  set ω := μ (ball (0 : E) 1)
  have hω0 : ω ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hωtop : ω ≠ ∞ := measure_ball_lt_top.ne
  set A : ℝ := 4 ^ n / (2 ^ α - 1)
  set B : ℝ := 2 ^ n * (1 - 2 ^ (n - (n - α) * q))⁻¹
  have h2α : 0 < (2 : ℝ) ^ α - 1 := by linarith [Real.one_lt_rpow one_lt_two hα]
  have hA : 0 < A := div_pos (by positivity) h2α
  have hB : 0 ≤ B := mul_nonneg (by positivity) (inv_nonneg.2 (sub_nonneg.2
    (Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith))))
  set C : ℝ := A * ω.toReal + (B * ω.toReal) ^ (1 / q)
  have hC : 0 < C := add_pos_of_pos_of_nonneg (mul_pos hA (ENNReal.toReal_pos hω0 hωtop))
    (by positivity)
  refine ⟨C.toNNReal, fun f hf x => ?_⟩
  set M := maximalFunction μ f x
  set N := eLpNorm f p μ
  have hN : N = (∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) :=
    eLpNorm_nnreal_eq_lintegral (by positivity) hf
  -- If `f` vanishes almost everywhere, so does its potential.
  by_cases hf0 : ∀ᵐ y ∂μ, ‖f y‖ₑ = 0
  · calc ∫⁻ y, ‖x - y‖ₑ ^ (α - n) * ‖f y‖ₑ ∂μ = ∫⁻ _, 0 ∂μ :=
          lintegral_congr_ae (hf0.mono fun y hy => by simp [hy])
      _ ≤ _ := by simp
  have hM0 : M ≠ 0 := fun h => hf0 (ae_enorm_eq_zero_of_maximalFunction_eq_zero μ hf.enorm h)
  have hN0 : N ≠ 0 := fun h => hf0 <| by
    filter_upwards [(eLpNorm_eq_zero_iff (by positivity)).1 h] with y hy
    simp [hy]
  have hC0 : (C.toNNReal : ℝ≥0∞) ≠ 0 := by simpa using hC
  -- If `M f x` or `‖f‖_p` is infinite, so is the right-hand side.
  by_cases hMtop : M = ∞
  · rw [hMtop, ENNReal.top_rpow_of_pos (by linarith), ENNReal.mul_top hC0,
      ENNReal.top_mul (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hN0) hθ0.le).ne']
    exact le_top
  by_cases hNtop : N = ∞
  · rw [hNtop, ENNReal.top_rpow_of_pos hθ0, ENNReal.mul_top]
    · exact le_top
    · exact mul_ne_zero hC0 (ENNReal.rpow_pos (pos_iff_ne_zero.2 hM0) hMtop).ne'
  -- Otherwise split at the radius `R` that balances the two terms.
  set m := M.toReal
  set ν := N.toReal
  have hm : 0 < m := ENNReal.toReal_pos hM0 hMtop
  have hν : 0 < ν := ENNReal.toReal_pos hN0 hNtop
  obtain ⟨h₁, h₂⟩ := rpow_mul_eq_and_rpow_rpow_mul_eq hn hpq hm hν (α := α)
  set R := (ν / m) ^ ((p : ℝ) / n)
  have hR : 0 < R := by positivity
  set ω' := ω.toReal
  have hω' : 0 ≤ ω' := ENNReal.toReal_nonneg
  have hωeq : ω = ENNReal.ofReal ω' := (ENNReal.ofReal_toReal hωtop).symm
  have hMeq : M = ENNReal.ofReal m := (ENNReal.ofReal_toReal hMtop).symm
  have hNeq : N = ENNReal.ofReal ν := (ENNReal.ofReal_toReal hNtop).symm
  have hBR : 0 ≤ 2 ^ n * R ^ (n - (n - α) * q) * (1 - 2 ^ (n - (n - α) * q))⁻¹ := by
    rw [mul_right_comm]
    exact mul_nonneg hB (by positivity)
  have hq0 : 0 ≤ 1 / q := by simpa using hpq.symm.nonneg
  have e₁ : ENNReal.ofReal (4 ^ n * R ^ α / (2 ^ α - 1)) * ω * M =
      ENNReal.ofReal (A * ω' * (R ^ α * m)) := by
    rw [hωeq, hMeq, ← ENNReal.ofReal_mul (div_nonneg (by positivity) h2α.le),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [A]
    ring
  have e₂ : (ENNReal.ofReal (2 ^ n * R ^ (n - (n - α) * q) * (1 - 2 ^ (n - (n - α) * q))⁻¹) *
      ω) ^ (1 / q) * N =
      ENNReal.ofReal ((B * ω') ^ (1 / q) * ((R ^ (n - (n - α) * q)) ^ (1 / q) * ν)) := by
    rw [hωeq, hNeq, ← ENNReal.ofReal_mul hBR,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hBR hω') hq0, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← mul_assoc, ← Real.mul_rpow (mul_nonneg hB hω') (by positivity)]
    congr 2
    simp only [B]
    ring
  calc ∫⁻ y, ‖x - y‖ₑ ^ (α - n) * ‖f y‖ₑ ∂μ
      = ∫⁻ y in closedBall x R, ‖x - y‖ₑ ^ (α - n) * ‖f y‖ₑ ∂μ +
          ∫⁻ y in (closedBall x R)ᶜ, ‖x - y‖ₑ ^ (α - n) * ‖f y‖ₑ ∂μ :=
        (lintegral_add_compl _ measurableSet_closedBall).symm
    _ ≤ ENNReal.ofReal (4 ^ n * R ^ α / (2 ^ α - 1)) * ω * M +
          (ENNReal.ofReal (2 ^ n * R ^ (n - (n - α) * q) * (1 - 2 ^ (n - (n - α) * q))⁻¹) *
            ω) ^ (1 / q) * N := by
        rw [hN]
        exact add_le_add (setLIntegral_closedBall_enorm_sub_rpow_mul_le μ x hR hα hαn hf)
          (setLIntegral_compl_closedBall_enorm_sub_rpow_mul_le μ x hR hpq hs hf)
    _ = ENNReal.ofReal (C * (m ^ (1 - θ) * ν ^ θ)) := by
        rw [e₁, e₂, ← ENNReal.ofReal_add (by positivity) (by positivity), h₁, h₂]
        congr 1
        simp only [C, θ, ω']
        ring
    _ = C.toNNReal * M ^ (1 - θ) * N ^ θ := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_rpow_of_nonneg hm.le (by linarith),
          ← ENNReal.ofReal_rpow_of_nonneg hν.le hθ0.le, ← hMeq, ← hNeq, mul_assoc]
        rfl

/-- **The Hardy–Littlewood–Sobolev inequality.** Let `n = dim E`, `0 < α`, `1 < p` and let `q` be
given by `1 / p - 1 / q = α / n`, with `q < ∞`. Then the Riesz potential of order `α`,

`I_α f (x) = ∫ ‖x - y‖ ^ (α - n) ‖f y‖ dy`,

maps `Lᵖ` to `L^q`: there is `C`, depending only on `μ`, `α` and `p`, with
`‖I_α f‖_q ≤ C ‖f‖_p` for every `f`. -/
theorem eLpNorm_lintegral_enorm_sub_rpow_mul_enorm_le {α : ℝ} {p q : ℝ≥0} (hα : 0 < α)
    (hp : 1 < p) (hq : q ≠ 0) (hpq : (p : ℝ)⁻¹ - (q : ℝ)⁻¹ = α / finrank ℝ E) :
    ∃ C : ℝ≥0, ∀ f : E → F,
      eLpNorm (fun x ↦ ∫⁻ y, ‖x - y‖ₑ ^ (α - finrank ℝ E) * ‖f y‖ₑ ∂μ) q μ ≤
        C * eLpNorm f p μ := by
  set n := finrank ℝ E
  -- On the zero space the kernel `‖x - y‖ ^ α` vanishes identically.
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · have : Subsingleton E := Module.finrank_zero_iff.1 hn0
    have hk (x y : E) : ‖x - y‖ₑ ^ (α - n) = 0 := by
      rw [Subsingleton.elim x y, sub_self, enorm_zero, hn0, Nat.cast_zero, sub_zero,
        ENNReal.zero_rpow_of_pos hα]
    exact ⟨0, fun f => by simp [hk]⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast hn0
  have hp0 : (0 : ℝ) < p := by positivity
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hq0 : (0 : ℝ) < q := by positivity
  -- The exponent relation says `α p / n = 1 - p / q`.
  have hθ : α * p / n = 1 - p / q := by
    rw [mul_comm, mul_div_assoc, ← hpq]
    field_simp
  have hαp : α * p < n := by
    rw [← div_lt_one hn, hθ]
    linarith [div_pos hp0 hq0]
  obtain ⟨C₁, hC₁⟩ := lintegral_enorm_sub_rpow_mul_enorm_le μ (F := F) hα hp hαp
  set K : ℝ≥0∞ := ENNReal.ofReal (2 * p * 2 ^ ((p : ℝ) - 1) / (p - 1)) * 4 ^ n
  have hK : K ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
  set C : ℝ≥0∞ := (C₁ + 1 : ℝ≥0) * K ^ (1 / (q : ℝ))
  have hCtop : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hK)
  refine ⟨C.toNNReal, fun f => ?_⟩
  rw [ENNReal.coe_toNNReal hCtop]
  set N := eLpNorm f p μ
  -- A nonmeasurable `f`, or one of infinite norm, has `‖f‖_p = ∞`.
  have hK0 : K ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 (by
    have : (0 : ℝ) < p - 1 := by linarith
    positivity)).ne' (by simp)
  have hC0 : C ≠ 0 := mul_ne_zero (by simp) (ENNReal.rpow_pos (pos_iff_ne_zero.2 hK0) hK).ne'
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · rw [show N = ∞ from eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.mul_top hC0]
    exact le_top
  by_cases hNtop : N = ∞
  · rw [hNtop, ENNReal.mul_top hC0]
    exact le_top
  have hN : N = (∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) :=
    eLpNorm_nnreal_eq_lintegral (by positivity) hf
  have hNp : ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂μ = N ^ (p : ℝ) := by
    rw [hN, one_div, ENNReal.rpow_inv_rpow hp0.ne']
  -- The potential is measurable, as a partial integral of a measurable function on `E × E`.
  have hI : AEMeasurable (fun x ↦ ∫⁻ y, ‖x - y‖ₑ ^ (α - n) * ‖f y‖ₑ ∂μ) μ :=
    AEMeasurable.lintegral_prod_right' (f := fun z : E × E ↦ ‖z.1 - z.2‖ₑ ^ (α - n) * ‖f z.2‖ₑ)
      ((by fun_prop : Measurable fun z : E × E ↦ ‖z.1 - z.2‖ₑ ^ (α - n)).aemeasurable.mul
        hf.enorm.comp_snd)
  have hexp : (1 - α * p / n) * q = p := by
    rw [hθ]
    field_simp
    ring
  have hexp' : α * p / n * q + p = q := by
    rw [hθ]
    field_simp
    ring
  calc eLpNorm (fun x ↦ ∫⁻ y, ‖x - y‖ₑ ^ (α - n) * ‖f y‖ₑ ∂μ) q μ
      = (∫⁻ x, (∫⁻ y, ‖x - y‖ₑ ^ (α - n) * ‖f y‖ₑ ∂μ) ^ (q : ℝ) ∂μ) ^ (1 / (q : ℝ)) := by
        rw [eLpNorm_nnreal_eq_lintegral hq hI.aestronglyMeasurable]
        simp only [enorm_eq_self]
    _ ≤ (∫⁻ x, ((C₁ + 1 : ℝ≥0) * maximalFunction μ f x ^ (1 - α * p / n) *
          N ^ (α * p / n)) ^ (q : ℝ) ∂μ) ^ (1 / (q : ℝ)) := by
        gcongr with x
        refine (hC₁ f hf x).trans ?_
        gcongr
        exact le_self_add
    _ = ((C₁ + 1 : ℝ≥0) ^ (q : ℝ) * N ^ (α * p / n * q) *
          ∫⁻ x, maximalFunction μ f x ^ (p : ℝ) ∂μ) ^ (1 / (q : ℝ)) := by
        rw [← lintegral_const_mul _ ((measurable_maximalFunction μ f).pow_const _)]
        congr 2 with x
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hexp]
        ring
    _ ≤ ((C₁ + 1 : ℝ≥0) ^ (q : ℝ) * N ^ (α * p / n * q) * (K * N ^ (p : ℝ))) ^
          (1 / (q : ℝ)) := by
        gcongr
        rw [← hNp]
        exact lintegral_rpow_maximalFunction_le μ hf.enorm hp1
    _ = C * N := by
        rw [mul_left_comm, ← mul_assoc, ← mul_assoc, mul_assoc _ _ (N ^ (p : ℝ)),
          ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) hp0.le, hexp',
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), one_div,
          ENNReal.rpow_rpow_inv hq0.ne', ENNReal.rpow_rpow_inv hq0.ne']
        simp only [C, one_div]
        ring

/-- **The Hardy–Littlewood–Sobolev inequality** for the Riesz potential
`I_α f (x) = ∫ ‖x - y‖ ^ (α - n) f y dy` of a function with values in a real normed space. Let
`n = dim E`, `0 < α`, `1 < p` and `1 / p - 1 / q = α / n` with `q < ∞`. There is `C`, depending
only on `μ`, `α` and `p`, with `‖I_α f‖_q ≤ C ‖f‖_p` for every `f`. -/
theorem eLpNorm_integral_norm_sub_rpow_smul_le {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {α : ℝ} {p q : ℝ≥0} (hα : 0 < α) (hp : 1 < p) (hq : q ≠ 0)
    (hpq : (p : ℝ)⁻¹ - (q : ℝ)⁻¹ = α / finrank ℝ E) :
    ∃ C : ℝ≥0, ∀ f : E → G,
      eLpNorm (fun x ↦ ∫ y, ‖x - y‖ ^ (α - finrank ℝ E) • f y ∂μ) q μ ≤ C * eLpNorm f p μ := by
  set n := finrank ℝ E
  obtain ⟨C, hC⟩ := eLpNorm_lintegral_enorm_sub_rpow_mul_enorm_le μ (F := G) hα hp hq hpq
  refine ⟨C + 1, fun f => ?_⟩
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.mul_top (by simp)]
    exact le_top
  have hmeas : AEStronglyMeasurable (fun x ↦ ∫ y, ‖x - y‖ ^ (α - n) • f y ∂μ) μ :=
    AEStronglyMeasurable.integral_prod_right'
      (f := fun z : E × E ↦ ‖z.1 - z.2‖ ^ (α - n) • f z.2)
      ((by fun_prop : Measurable fun z : E × E ↦ ‖z.1 - z.2‖ ^ (α - n)).aestronglyMeasurable.smul
        hf.comp_snd)
  calc eLpNorm (fun x ↦ ∫ y, ‖x - y‖ ^ (α - n) • f y ∂μ) q μ
      ≤ eLpNorm (fun x ↦ ∫⁻ y, ‖x - y‖ₑ ^ (α - n) * ‖f y‖ₑ ∂μ) q μ := by
        refine eLpNorm_mono_enorm hmeas fun x => ?_
        rw [enorm_eq_self]
        refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
        rw [enorm_smul]
        gcongr
        -- The real kernel is the extended one, except at `y = x` for a negative exponent, where
        -- it is `0` instead of `∞`.
        rw [← enorm_norm (x - y)]
        rcases lt_or_ge (α - n) 0 with hγ | hγ
        · rcases (norm_nonneg (x - y)).eq_or_lt with h | h
          · rw [← h, enorm_zero, ENNReal.zero_rpow_of_neg hγ]
            exact le_top
          · rw [Real.enorm_of_nonneg (by positivity), Real.enorm_of_nonneg h.le,
              ENNReal.ofReal_rpow_of_pos h]
        · exact (Real.enorm_rpow_of_nonneg (norm_nonneg _) hγ).le
    _ ≤ C * eLpNorm f p μ := hC f
    _ ≤ (C + 1 : ℝ≥0) * eLpNorm f p μ := by
        gcongr
        exact le_self_add

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
public import Mathlib.Analysis.Calculus.DSlope
import TauCeti.Analysis.Complex.Taylor.DSlope
import TauCeti.Probability.Distributions.Gamma.MeanApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A quantitative Laplace Tauberian theorem

A Lipschitz function on the positive half-line decays faster than every inverse power if
its Laplace transform is a holomorphic divided difference with polynomial bounds on
regions extending to the left of the convergence line by an inverse logarithmic power.
The theorem estimates the function by a Gamma average concentrated at the evaluation
point, and uses the Cauchy estimate `TauCeti.Complex.norm_scaled_taylorCoeff_dslope_le_exp`
to bound that average.

The quantitative Taylor-coefficient method follows `New.eventually_abs_le_inv_pow_of_transform`
in `Lib/Analytic/PrimeNumberTheorem/Tauberian.lean` of lsernau/grh-lean (commit `72fead1`).
-/

public section

open Complex Filter MeasureTheory Metric Set
open scoped NNReal Nat Topology

namespace TauCeti

private theorem abs_le_norm_scaled_taylorCoeff_dslope_add {R : ℝ → ℝ} {F : ℂ → ℂ}
    {L : ℝ≥0} (hR : LipschitzOnWith L R (Ioi 0))
    (hF : ∀ s : ℂ, 2 < s.re → HasLaplace (fun u ↦ (R u : ℂ)) (s - 1) (dslope F 1 s))
    {H : ℝ} (hH : 1 < H) (k : ℕ) :
    |R ((k + 1 : ℕ) / H)| ≤
      ‖((1 + (H : ℂ) - 1) ^ (k + 1) / k !) • iteratedDeriv k (dslope F 1) (1 + H)‖ +
        L * (Real.sqrt (k + 1 : ℕ) / H) := by
  have ha : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hH₀ : 0 < H := zero_lt_one.trans hH
  have hLap : ∀ᶠ z in 𝓝 (H : ℂ), HasLaplace (fun u ↦ (R u : ℂ)) z
      (dslope F 1 (1 + z)) := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds
      (show (H : ℂ) ∈ {z : ℂ | 1 < z.re} by simpa using hH)] with z hz
    have hRe : 1 < z.re := hz
    simpa using hF (1 + z) (by simp only [add_re, one_re]; linarith only [hRe])
  obtain ⟨_, hterm⟩ := integrable_and_taylor_term_eq_integral hLap H k
  rw [iteratedDeriv_comp_const_add] at hterm
  let A := ∫ u, R u ∂ProbabilityTheory.gammaMeasure (k + 1 : ℕ) H
  have hA : A = H * ∫ u in Ioi 0, (H * u) ^ k / (k ! : ℝ) * (Real.exp (-H * u) * R u) := by
    dsimp only [A]
    rw [Probability.integral_gammaMeasure_eq_integral_Ioi ha hH₀, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
    push_cast
    rw [Real.rpow_add_one hH₀.ne', Real.rpow_natCast, add_sub_cancel_right,
      Real.rpow_natCast, Real.Gamma_nat_eq_factorial, smul_eq_mul, mul_pow, neg_mul]
    ring
  have hnA : |A| =
      ‖((1 + (H : ℂ) - 1) ^ (k + 1) / k !) • iteratedDeriv k (dslope F 1) (1 + H)‖ := by
    have he := congrArg (fun z : ℂ ↦ ‖z‖) (congrArg (fun z : ℂ ↦ (H : ℂ) * z) hterm)
    simpa [hA, smul_eq_mul, norm_mul, abs_mul, abs_of_pos hH₀, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc, pow_succ] using he.symm
  rw [← hnA]
  have herr := Probability.norm_integral_gammaMeasure_sub_le ha hH₀ hR
  have htriangle := abs_sub_le (R ((k + 1 : ℕ) / H)) A 0
  rw [sub_zero, sub_zero, abs_sub_comm] at htriangle
  exact htriangle.trans (by
    rw [add_comm]
    exact add_le_add_right (by simpa only [A, Real.norm_eq_abs] using herr) _)

private theorem norm_scaled_taylorCoeff_dslope_le_of_region {F : ℂ → ℂ} {H η M T : ℝ}
    (hH : 0 < H) (hη : 0 < η) (hηH : η ≤ H) (hT : 1 + 2 * H + η ≤ T)
    (hF : ∀ z : ℂ, 1 - η ≤ z.re → ‖z‖ ≤ T → DifferentiableAt ℂ F z ∧ ‖F z‖ ≤ M)
    (k : ℕ) :
    ‖((1 + (H : ℂ) - 1) ^ (k + 1) / k !) • iteratedDeriv k (dslope F 1) (1 + H)‖ ≤
      (4 * M * H / η) * Real.exp (-(((k + 1 : ℕ) : ℝ) / H) * η / 2) := by
  have hd : dist (1 : ℂ) (1 + (H : ℂ)) = H := by
    simp [dist_eq_norm, abs_of_pos hH]
  have hgeom (z : ℂ) (hz : z ∈ closedBall (1 + (H : ℂ)) (H + η)) :
      1 - η ≤ z.re ∧ ‖z‖ ≤ T := by
    have hdist := mem_closedBall.mp hz
    rw [dist_eq_norm] at hdist
    have hr := (Complex.abs_re_le_norm (z - (1 + H))).trans hdist
    have hnorm : ‖1 + (H : ℂ)‖ = 1 + H := by
      simpa only [ofReal_add, ofReal_one] using Complex.norm_of_nonneg (by positivity : 0 ≤ 1 + H)
    refine ⟨?_, ?_⟩
    · simp only [sub_re, add_re, one_re, ofReal_re] at hr
      linarith [(abs_le.mp hr).1]
    · linarith [norm_le_insert' z (1 + (H : ℂ))]
  have hAt (z : ℂ) (hz : z ∈ closedBall (1 + (H : ℂ)) (H + η)) :=
    hF z (hgeom z hz).1 (hgeom z hz).2
  have hM : 0 ≤ M := (norm_nonneg _).trans (hAt _ (mem_closedBall_self (by positivity))).2
  have h := TauCeti.Complex.norm_scaled_taylorCoeff_dslope_le_exp
    (a := 1) (c := 1 + (H : ℂ)) (R := H + η) (M := M)
    (by rw [mem_ball, hd]; linarith)
    ⟨fun z hz ↦ (hAt z (ball_subset_closedBall hz)).1.differentiableWithinAt,
      fun z hz ↦ (hAt z (closure_ball_subset_closedBall hz)).1.continuousAt.continuousWithinAt⟩
    (fun z hz ↦ (hAt z (sphere_subset_closedBall hz)).2) k
  have hgap : H + η - H = η := by ring
  rw [hd, hgap, add_sub_cancel_left] at h
  have hpref : 0 ≤ 4 * M * H / η := by positivity
  have hpref' : 2 * M * (H + η) / η ≤ 4 * M * H / η := by
    apply div_le_div_of_nonneg_right _ hη.le
    calc
      _ ≤ 2 * M * (2 * H) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  rw [add_sub_cancel_left]
  refine h.trans (mul_le_mul hpref' (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hpref)
  have hexp : -(↑(k + 1 : ℕ) / H) * η / 2 = -((k + 1 : ℝ) * (η / (2 * H))) := by
    push_cast
    ring
  rw [hexp]
  simp only [neg_mul, neg_le_neg_iff]
  gcongr
  linarith

private theorem eventually_log_scale_pow_le_sqrt (D : ℝ) (hD : 0 < D) (A : ℕ) :
    ∀ᶠ u : ℝ in atTop, (D * Real.log u) ^ A ≤ Real.sqrt u := by
  have h := isLittleO_log_rpow_rpow_atTop (A : ℝ) (s := 1 / 2) (by norm_num)
  have h' := h.def (c := (D ^ A)⁻¹) (by positivity)
  filter_upwards [h', eventually_ge_atTop (1 : ℝ)] with u hu hu₁
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu₁
  rw [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg hlog _),
    ← Real.sqrt_eq_rpow, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hu
  rwa [mul_pow, ← le_inv_mul_iff₀ (by positivity : 0 < D ^ A)]

private theorem eventually_pow_mul_exp_neg_sqrt_le (n : ℕ) :
    ∀ᶠ u : ℝ in atTop, 12 * u ^ n * Real.exp (-(Real.sqrt u) / 2) ≤ 1 / 2 := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * n : ℕ) (1 / 2)
    (by norm_num)).comp Real.tendsto_sqrt_atTop
  have hlim : Tendsto (fun u : ℝ ↦ 12 * (Real.sqrt u ^ ((2 * n : ℕ) : ℝ) *
      Real.exp (-(1 / 2) * Real.sqrt u))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using h.const_mul 12
  have h' := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [h', eventually_ge_atTop (0 : ℝ)] with u hu hu₀
  have hpow : (Real.sqrt u) ^ (2 * n) = u ^ n := by
    rw [pow_mul, Real.sq_sqrt hu₀]
  have harg : -(1 / 2 : ℝ) * Real.sqrt u = -Real.sqrt u / 2 := by ring
  simpa only [Real.rpow_natCast, hpow, ← mul_assoc, harg] using hu.le

private theorem abs_le_of_hasLaplace_dslope_on_region {R : ℝ → ℝ} {F : ℂ → ℂ}
    {L : ℝ≥0} (hR : LipschitzOnWith L R (Ioi 0))
    (hLap : ∀ s : ℂ, 2 < s.re → HasLaplace (fun u ↦ (R u : ℂ)) (s - 1) (dslope F 1 s))
    {u H η M T : ℝ} (hH : 1 < H) (hη : 0 < η) (hηH : η ≤ H) (hT : 1 + 2 * H + η ≤ T)
    (hF : ∀ s : ℂ, 1 - η ≤ s.re → ‖s‖ ≤ T → DifferentiableAt ℂ F s ∧ ‖F s‖ ≤ M)
    (k : ℕ) (hu : ((k + 1 : ℕ) : ℝ) / H = u) :
    |R u| ≤ (4 * M * H / η) * Real.exp (-u * η / 2) + L * (u / Real.sqrt (k + 1 : ℕ)) := by
  have hc := norm_scaled_taylorCoeff_dslope_le_of_region (zero_lt_one.trans hH) hη hηH hT hF k
  have hg := abs_le_norm_scaled_taylorCoeff_dslope_add hR hLap hH k
  have hspread : Real.sqrt (k + 1 : ℕ) / H = u / Real.sqrt (k + 1 : ℕ) := by
    rw [← hu]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
  rw [hu] at hc
  rw [hu, hspread] at hg
  exact hg.trans (add_le_add_left hc _)

private theorem gamma_error_le_half_inv_pow {u : ℝ} {L : ℝ≥0} {B k : ℕ}
    (hu : 0 < u) (hL : 2 * (L : ℝ) ≤ u) (hk : u ^ (2 * (B + 2)) ≤ (k : ℝ)) :
    (L : ℝ) * (u / Real.sqrt (k + 1 : ℕ)) ≤ (1 / 2 : ℝ) / u ^ B := by
  have hs : u ^ (B + 2) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    rw [← pow_mul, mul_comm (B + 2)]
    exact hk.trans (by simp)
  rw [← mul_div_assoc]
  calc
    _ ≤ (L : ℝ) * u / u ^ (B + 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hs
    _ ≤ (1 / 2 : ℝ) / u ^ B := by
      rw [pow_add, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (show 0 ≤ u * u ^ B by positivity) (show 0 ≤ u / 2 - L by linarith)]

private theorem scaled_exp_le_half_inv_pow {u M H : ℝ} {B D : ℕ}
    (hu : 0 < u) (hM : 0 < M) (hMu : M ≤ Real.sqrt u) (hH : H ≤ 3 * u ^ D)
    (hexp : 12 * u ^ (D + 1 + B) * Real.exp (-Real.sqrt u / 2) ≤ 1 / 2) :
    4 * M * H / (1 / M) * Real.exp (-u * (1 / M) / 2) ≤ (1 / 2 : ℝ) / u ^ B := by
  have hs : Real.sqrt u ≤ u * (1 / M) := by
    rw [mul_one_div, le_div_iff₀ hM]
    exact (mul_le_mul_of_nonneg_left hMu (Real.sqrt_nonneg _)).trans_eq
      (Real.mul_self_sqrt hu.le)
  have hM₂ : M ^ 2 ≤ u := (pow_le_pow_left₀ hM.le hMu 2).trans_eq (Real.sq_sqrt hu.le)
  have hP : 4 * M * H / (1 / M) ≤ 12 * u ^ (D + 1) := calc
    _ = 4 * M ^ 2 * H := by rw [div_div_eq_mul_div, div_one]; ring
    _ ≤ 4 * M ^ 2 * (3 * u ^ D) := mul_le_mul_of_nonneg_left hH (by positivity)
    _ ≤ 4 * u * (3 * u ^ D) := by gcongr
    _ = _ := by rw [pow_succ]; ring
  have he : Real.exp (-u * (1 / M) / 2) ≤ Real.exp (-Real.sqrt u / 2) :=
    Real.exp_le_exp.mpr (by rw [neg_mul]; linarith)
  refine (mul_le_mul hP he (Real.exp_pos _).le
    (by positivity : 0 ≤ 12 * u ^ (D + 1))).trans ?_
  rw [le_div_iff₀ (by positivity)]
  simpa only [pow_add u (D + 1) B, mul_assoc, mul_comm (u ^ B)] using hexp

/-- A quantitative Tauberian criterion for a real input with Laplace transform
`(F(s) - F(1)) / (s - 1)` at `s - 1`. Polynomial growth of `F` on the expanding regions
`Re s ≥ 1 - l⁻ᴬ`, `‖s‖ ≤ exp l`, with `F` holomorphic there, forces the input to decay
faster than every inverse power. Only the positive half-line of the input is used. -/
theorem eventually_abs_le_inv_pow_of_laplace_transform {R : ℝ → ℝ} {F : ℂ → ℂ}
    {L : ℝ≥0} (hR : LipschitzOnWith L R (Ioi 0))
    (hLap : ∀ s : ℂ, 2 < s.re → HasLaplace (fun u ↦ (R u : ℂ)) (s - 1) (dslope F 1 s))
    {A : ℕ} (hF : ∀ᶠ l : ℝ in atTop, ∀ s : ℂ, 1 - 1 / l ^ A ≤ s.re → ‖s‖ ≤ Real.exp l →
      DifferentiableAt ℂ F s ∧ ‖F s‖ ≤ l ^ A) (B : ℕ) :
    ∀ᶠ u : ℝ in atTop, |R u| ≤ (u ^ B)⁻¹ := by
  -- Choose the Gamma shape on a polynomial scale so that its width is at most `u⁻ᴮ⁻¹`.
  let D : ℕ := 2 * (B + 2)
  have hlog : Tendsto (fun u : ℝ ↦ (D + 2 : ℕ) * Real.log u) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (by positivity)
  filter_upwards [eventually_ge_atTop (8 : ℝ), eventually_ge_atTop (2 * (L : ℝ)),
    hlog.eventually hF, hlog.eventually (eventually_ge_atTop 1),
    eventually_log_scale_pow_le_sqrt (D + 2 : ℕ) (by positivity) A,
    eventually_pow_mul_exp_neg_sqrt_le (D + 1 + B)] with u hu huL hregion hl hlpow hexp
  let k := ⌈u ^ D⌉₊
  let H : ℝ := (k + 1 : ℕ) / u
  let l : ℝ := (D + 2 : ℕ) * Real.log u
  let η : ℝ := 1 / l ^ A
  have hu₀ : 0 < u := by linarith
  have hk : u ^ D ≤ (k : ℝ) := Nat.le_ceil _
  have hk' : ((k + 1 : ℕ) : ℝ) ≤ 3 * u ^ D := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ u ^ D)
    have hp : 1 ≤ u ^ D := one_le_pow₀ (by linarith)
    push_cast
    linarith
  have hH : 1 < H := by
    have hp : u ≤ u ^ D := le_self_pow₀ (by linarith) (by dsimp [D]; omega)
    dsimp [H]
    rw [lt_div_iff₀ hu₀, one_mul, Nat.cast_succ]
    linarith
  have hH' : H ≤ 3 * u ^ D := (div_le_self (by positivity) (by linarith)).trans hk'
  have hcenter : ((k + 1 : ℕ) : ℝ) / H = u := by
    dsimp [H]
    field_simp
  have hη : 0 < η := by positivity
  have hη₁ : η ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hl)
  -- The same polynomial scale bounds the radius of the Cauchy disc.
  have hT : 1 + 2 * H + η ≤ Real.exp l := by
    have hexpl : Real.exp l = u ^ (D + 2) := by
      rw [Real.exp_natCast_mul, Real.exp_log hu₀]
    rw [hexpl, pow_add]
    nlinarith [one_le_pow₀ (by linarith : 1 ≤ u) (n := D), sq_nonneg (u - 8)]
  have hRbound := abs_le_of_hasLaplace_dslope_on_region hR hLap hH hη (hη₁.trans hH.le)
    hT hregion k hcenter
  have hc : (4 * l ^ A * H / η) * Real.exp (-u * η / 2) ≤ (1 / 2 : ℝ) / u ^ B :=
    scaled_exp_le_half_inv_pow hu₀ (by positivity) hlpow hH' hexp
  exact hRbound.trans ((add_le_add hc (gamma_error_le_half_inv_pow hu₀ huL hk)).trans_eq (by ring))

end TauCeti

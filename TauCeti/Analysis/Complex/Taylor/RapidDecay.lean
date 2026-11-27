/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rapid decay of normalized Taylor coefficients in a logarithmic region

A holomorphic function with polylogarithmic growth just to the left of the line `Re z = 1`
has small normalized Taylor coefficients of its divided difference at `1`, when the degree
and center are chosen as in the Post–Widder method. The estimate supplies the analytic half
of a quantitative Laplace Tauberian argument: the normalization is the one for which the
coefficients of a Laplace transform are Gamma averages.

The target estimate is `New.norm_taylorCoeff_dslope_le_inv_pow` in lsernau/grh-lean,
`grh/src/Lib/Analytic/PrimeNumberTheorem/Tauberian.lean` at revision `72fead1`. We use a disc
extending `1 / √u` to the left of `1`, independent of the logarithmic exponent.
-/

open Filter Metric Asymptotics

namespace TauCeti

private theorem eventually_on_postWidder_disc {F : ℂ → ℂ} {A P : ℕ}
    (hF : ∀ᶠ l : ℝ in atTop, ∀ z : ℂ, 1 - 1 / l ^ A ≤ z.re → ‖z‖ ≤ Real.exp l →
      DifferentiableAt ℂ F z ∧ ‖F z‖ ≤ l ^ A) :
    ∀ᶠ u : ℝ in atTop, ∀ H : ℝ, H ≤ u ^ (P + 1) →
      ∀ z ∈ closedBall (1 + (H : ℂ)) (H + 1 / √u),
        DifferentiableAt ℂ F z ∧ ‖F z‖ ≤ √u := by
  have hlog : Tendsto (fun u : ℝ ↦ ↑(P + 2) * Real.log u) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (by positivity)
  have hsmall := IsLittleO.const_mul_left
    (isLittleO_log_rpow_rpow_atTop (A : ℝ) (by norm_num : 0 < (1 / 2 : ℝ)))
    ((↑(P + 2) : ℝ) ^ A)
  filter_upwards [hlog.eventually hF, hsmall.eventuallyLE,
    eventually_ge_atTop (4 : ℝ)] with u hF hu h₄ H hHu z hz
  have hl : 0 < Real.log u := Real.log_pos (by linarith)
  rw [Real.rpow_natCast, ← mul_pow, ← Real.sqrt_eq_rpow, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hu
  let c : ℂ := 1 + (H : ℂ)
  let η : ℝ := 1 / √u
  have hu₀ : 0 < u := by linarith
  have hs : 0 < √u := Real.sqrt_pos.2 hu₀
  have hη₁ : η ≤ 1 := (div_le_iff₀ hs).2 (by simpa using Real.sqrt_le_sqrt (by linarith : 1 ≤ u))
  have hz' : ‖z - c‖ ≤ H + η := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hre := Complex.re_le_norm (c - z)
  rw [norm_sub_rev] at hre
  have hleft : 1 - η ≤ z.re := by simp [c] at hre; linarith
  have hnorm : ‖z‖ ≤ u ^ (P + 2) := calc
    ‖z‖ ≤ ‖z - c‖ + ‖c‖ := norm_le_norm_sub_add z c
    _ ≤ (H + η) + (1 + H) := by
      have hnonneg : 0 ≤ 1 + H := by linarith [norm_nonneg (z - c)]
      have hc : ‖c‖ = 1 + H := by
        simp only [c, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
          Real.norm_of_nonneg hnonneg]
      rw [hc]
      gcongr
    _ ≤ u ^ (P + 2) := by
      have hp : 1 ≤ u ^ (P + 1) := one_le_pow₀ (by linarith : 1 ≤ u)
      rw [pow_succ]
      nlinarith
  have h := hF z (le_trans (by dsimp [η]; gcongr) hleft) (by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
    exact hnorm)
  exact ⟨h.1, h.2.trans hu⟩

private theorem norm_iteratedDeriv_dslope_le_on_log_scale {F : ℂ → ℂ} {A P : ℕ}
    (hF : ∀ᶠ l : ℝ in atTop, ∀ z : ℂ, 1 - 1 / l ^ A ≤ z.re → ‖z‖ ≤ Real.exp l →
      DifferentiableAt ℂ F z ∧ ‖F z‖ ≤ l ^ A) :
    ∀ᶠ u : ℝ in atTop, ∀ H : ℝ, 0 ≤ H → H ≤ u ^ (P + 1) → ∀ k : ℕ,
      ‖iteratedDeriv k (dslope F 1) (1 + (H : ℂ))‖ ≤
        (k.factorial : ℝ) * (2 * u) / (H + 1 / √u) ^ k := by
  filter_upwards [eventually_on_postWidder_disc (P := P) hF, eventually_gt_atTop (0 : ℝ)]
    with u hdisc hu H hH hHu k
  let c : ℂ := 1 + (H : ℂ)
  let η : ℝ := 1 / √u
  have hη : 0 < η := by positivity
  have hball := hdisc H hHu
  have hc : ‖(1 : ℂ) - c‖ = H := by
    simp [c, abs_of_nonneg hH]
  have h₁ : (1 : ℂ) ∈ ball c (H + η) := by
    rw [mem_ball, dist_eq_norm, hc]; linarith
  have hd : DifferentiableOn ℂ (dslope F 1) (closedBall c (H + η)) :=
    (Complex.differentiableOn_dslope (mem_of_superset (isOpen_ball.mem_nhds h₁)
      ball_subset_closedBall)).2 (fun z hz ↦ (hball z hz).1.differentiableWithinAt)
  refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by linarith)
    ⟨hd.mono ball_subset_closedBall, hd.continuousOn.mono closure_ball_subset_closedBall⟩ ?_
  intro z hz
  have hden : η ≤ ‖z - 1‖ := by
    -- The circle stays at least its radius minus the distance of the anchor from its center.
    have h := dist_triangle z (1 : ℂ) c
    rw [mem_sphere] at hz
    rw [hz, dist_eq_norm z 1, dist_eq_norm 1 c, hc] at h
    linarith
  have hne : z ≠ 1 := by intro he; simp [he] at hden; linarith
  rw [dslope_of_ne _ hne, slope_def_field, norm_div]
  calc
    ‖F z - F 1‖ / ‖z - 1‖ ≤ (√u + √u) / η := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add (hball z (sphere_subset_closedBall hz)).2
        (hball 1 (ball_subset_closedBall h₁)).2)
    _ = 2 * u := by
      simp only [η, div_div_eq_mul_div, div_one]
      nlinarith [Real.sq_sqrt hu.le]

private theorem normalized_coeff_geometric_le {u H : ℝ} {k : ℕ}
    (hηH : 1 / √u ≤ H) (hk : 1 ≤ k) (hku : (k : ℝ) + 1 = H * u) :
    (H / (H + 1 / √u)) ^ k ≤ Real.exp (-(1 / 4) * √u) := by
  let η := 1 / √u
  have hu : 0 < u := by
    by_contra! h
    have hH : 0 ≤ H := by simpa [Real.sqrt_eq_zero_of_nonpos h] using hηH
    linarith [mul_nonpos_of_nonneg_of_nonpos hH h, Nat.cast_nonneg (α := ℝ) k]
  have hs : 0 < √u := Real.sqrt_pos.2 hu
  have hη : 0 < η := by positivity
  have hH : 0 < H := hη.trans_le hηH
  have hR : 0 < H + η := by linarith
  have hrat : H / (H + η) ≤ Real.exp (-(η / (H + η))) := by
    convert Real.add_one_le_exp (-(η / (H + η))) using 1
    field_simp
    ring
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hgain : √u / 4 ≤ (k : ℝ) * (η / (H + η)) := by
    have hle : H * u ≤ 2 * k := by linarith
    have hsq := Real.sq_sqrt (by linarith : 0 ≤ u)
    have haux : √u * (H + η) ≤ 4 * k * η := by
      apply (mul_le_mul_iff_left₀ hs).1 ?_
      have he : η * √u = 1 := by dsimp [η]; field_simp
      calc
        √u * (H + η) * √u = u * (H + η) := by nlinarith
        _ ≤ u * (2 * H) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        _ ≤ 4 * k := by linarith only [hle]
        _ = 4 * k * η * √u := by rw [mul_assoc, he, mul_one]
    rw [← mul_div_assoc, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hR]
    linarith
  calc
    (H / (H + η)) ^ k ≤ Real.exp (-(η / (H + η))) ^ k := by gcongr
    _ ≤ Real.exp (-(1 / 4) * √u) := by
      rw [← Real.exp_natCast_mul]
      exact Real.exp_le_exp.mpr (by linarith)

/-- For a holomorphic continuation with polylogarithmic growth, the normalized Taylor
coefficient of `dslope F 1` at `1 + H` has rapid decay as `u → ∞`. Here the degree is
`k = ⌊u ^ (P + 1)⌋₊` and the rate is `H = (k + 1) / u`; the sign of the normalization
is chosen for use with Laplace derivatives. -/
public theorem eventually_norm_normalized_iteratedDeriv_dslope_le_inv_pow {F : ℂ → ℂ} {A : ℕ}
    (hF : ∀ᶠ l : ℝ in atTop, ∀ z : ℂ, 1 - 1 / l ^ A ≤ z.re → ‖z‖ ≤ Real.exp l →
      DifferentiableAt ℂ F z ∧ ‖F z‖ ≤ l ^ A) (P B : ℕ) :
    ∀ᶠ u : ℝ in atTop,
      let k := ⌊u ^ (P + 1)⌋₊
      let H : ℝ := (k + 1 : ℝ) / u
      ‖((-(H : ℂ)) ^ k * H / k.factorial) • iteratedDeriv k (dslope F 1) (1 + (H : ℂ))‖ ≤
        (u ^ B)⁻¹ := by
  have hdecay := (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : 0 < (1 / 4 : ℝ))
    (-(↑(2 * (P + 2 + B)) : ℝ))).const_mul_left 2
  filter_upwards [norm_iteratedDeriv_dslope_le_on_log_scale (P := P) hF,
    Real.tendsto_sqrt_atTop.eventually hdecay.eventuallyLE,
    eventually_ge_atTop (2 : ℝ)] with u hC hexp hu
  dsimp only
  set k := ⌊u ^ (P + 1)⌋₊
  set H : ℝ := (k + 1 : ℝ) / u
  have hu₀ : 0 < u := by linarith
  have hup : u ≤ u ^ (P + 1) := le_self_pow₀ (by linarith) (Nat.succ_ne_zero P)
  have hk : 1 ≤ k := (Nat.one_le_floor_iff _).2 (by linarith)
  have hku : (k : ℝ) + 1 = H * u := (div_mul_cancel₀ _ hu₀.ne').symm
  have hH : 1 ≤ H := (one_le_div₀ hu₀).2 (hup.trans (Nat.lt_floor_add_one _).le)
  have hHu : H ≤ u ^ (P + 1) := by
    have hfloor : (k : ℝ) ≤ u ^ (P + 1) := Nat.floor_le (by positivity)
    rw [div_le_iff₀ hu₀]
    nlinarith
  have hH₀ : 0 ≤ H := by linarith
  have hc := hC H hH₀ hHu k
  have hη : 1 / √u ≤ H := calc
    1 / √u ≤ 1 := (div_le_one (Real.sqrt_pos.2 hu₀)).2 (by
      simpa using Real.sqrt_le_sqrt (by linarith : 1 ≤ u))
    _ ≤ H := hH
  have hg := normalized_coeff_geometric_le hη hk hku
  rw [Real.rpow_neg (Real.sqrt_nonneg u), Real.rpow_natCast, pow_mul, Real.sq_sqrt hu₀.le,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hexp
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  simp only [norm_smul, norm_div, norm_mul, norm_pow, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg hH₀, Complex.norm_natCast]
  calc
    H ^ k * H / ↑k.factorial * ‖iteratedDeriv k (dslope F 1) (1 + (H : ℂ))‖ ≤
        H ^ k * H / ↑k.factorial * (↑k.factorial * (2 * u) / (H + 1 / √u) ^ k) := by gcongr
    _ = H * (2 * u) * (H / (H + 1 / √u)) ^ k := by
      have hnum : (H ^ k * H) * (↑k.factorial * (2 * u)) =
          ↑k.factorial * (H * (2 * u) * H ^ k) := by ring
      rw [div_mul_div_comm, hnum, mul_div_mul_left _ _ hf.ne', div_pow H (H + 1 / √u) k,
        ← mul_div_assoc]
    _ ≤ u ^ (P + 2) * (2 * Real.exp (-(1 / 4) * √u)) := by
      calc
        _ ≤ (u ^ (P + 1) * (2 * u)) * Real.exp (-(1 / 4) * √u) := by gcongr
        _ = _ := by rw [pow_succ]; ring
    _ ≤ (u ^ B)⁻¹ := by
      refine (mul_le_mul_of_nonneg_left hexp (by positivity)).trans_eq ?_
      rw [pow_add u (P + 2) B, mul_inv_rev, mul_comm ((u ^ B)⁻¹)]
      exact mul_inv_cancel_left₀ (pow_ne_zero _ hu₀.ne') _

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Laurent.Expansion
public import TauCeti.Analysis.Complex.PowerSeries.FourierCoeff
import TauCeti.Analysis.Fourier.RiemannLebesgue

/-!
# Darboux's method

Let `f` be holomorphic in the punctured disc `0 < |z - c| < r`, with Laurent coefficients
`fₙ = TauCeti.circleLaurentCoeff f c ρ n` for any `ρ ∈ (0, r)`. Darboux's method reads off the
growth of `fₙ` as `n → ±∞` from the singularities of `f` on the circle `|z - c| = r`: one chooses a
comparison function `g`, holomorphic in the same punctured disc and with explicitly known
coefficients `gₙ`, that carries those singularities, so that `f - g` is better behaved on the
circle. Then (DLMF 2.10.29)

* if `f - g` extends continuously to `0 < |z - c| ≤ r`, then `fₙ = gₙ + o(r⁻ⁿ)` as `n → ±∞`
  (`TauCeti.tendsto_circleLaurentCoeff_sub`);

and, more generally (DLMF 2.10.31),

* if the `m`-th derivative of `f - g` extends continuously to `0 < |z - c| ≤ r`, then
  `fₙ = gₙ + o(r⁻ⁿ |n|⁻ᵐ)` as `n → ±∞`
  (`TauCeti.tendsto_circleLaurentCoeff_sub_of_iteratedDeriv`).

Both are stated along the cofinite filter on `ℤ`, as the vanishing of `rⁿ (fₙ - gₙ)` and of
`nᵐ rⁿ (fₙ - gₙ)` respectively. The continuous extension is a function `H`, continuous on the
closed punctured disc and equal to `f - g` (respectively to `f⁽ᵐ⁾ - g⁽ᵐ⁾`) on the open one; the
values of `f` and `g` on the circle itself play no role.

The proof moves the circle of integration out to the boundary circle `|z - c| = r`, where the
coefficients of `H` are `r⁻ⁿ` times the Fourier coefficients of `θ ↦ H(c + r e^{iθ})`
(`TauCeti.circleLaurentCoeff_eq_zpow_smul_fourierCoeffOn`); these tend to `0` by the
Riemann--Lebesgue lemma (`TauCeti.tendsto_zpow_smul_circleLaurentCoeff`). For the derivative form,
the coefficients of `f⁽ᵐ⁾` are those of `f` multiplied by falling factorials
(`TauCeti.circleLaurentCoeff_iteratedDeriv`), which grow like `|n|ᵐ`.

The typical comparison functions are built from `(a - z)⁻¹` with `|a - c| = r`, whose
coefficients `(a - c)⁻ⁿ⁻¹` for `n ≥ 0` and `0` for `n < 0` are computed on every circle of radius
less than `|a - c|` (`TauCeti.circleLaurentCoeff_inv_sub`).

## Main results

* `TauCeti.tendsto_zpow_smul_circleLaurentCoeff`: the Laurent coefficients of any function on a
  circle of radius `R` are `o(R⁻ⁿ)` as `n → ±∞`.
* `TauCeti.tendsto_circleLaurentCoeff_sub`: Darboux's comparison theorem, DLMF 2.10.29.
* `TauCeti.tendsto_circleLaurentCoeff_sub_of_iteratedDeriv`: its refinement for continuous
  `m`-th derivatives, DLMF 2.10.31.
* `TauCeti.circleLaurentCoeff_inv_sub`: the Laurent coefficients of `(a - z)⁻¹`.

## References

* NIST Digital Library of Mathematical Functions, §2.10(iv), equations (2.10.25)–(2.10.32),
  <https://dlmf.nist.gov/2.10.iv>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997, Chapter 8, §9.
-/

public section

open Complex Filter Metric Polynomial Set
open scoped Real Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Riemann--Lebesgue for Laurent coefficients**: the coefficients of any function extracted by
a circle of radius `R` satisfy `Rⁿ fₙ → 0` as `n → ±∞`. -/
theorem tendsto_zpow_smul_circleLaurentCoeff (f : ℂ → E) (c : ℂ) (R : ℝ) :
    Tendsto (fun n : ℤ ↦ (R : ℂ) ^ n • circleLaurentCoeff f c R n) cofinite (𝓝 0) := by
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp [circleLaurentCoeff_def, circleIntegral.integral_radius_zero]
  refine (tendsto_fourierCoeffOn Real.two_pi_pos
    (fun θ ↦ f (circleMap c R θ))).congr fun n ↦ ?_
  rw [circleLaurentCoeff_eq_zpow_smul_fourierCoeffOn f c hR, smul_smul, ← zpow_add₀ (by simpa),
    add_neg_cancel, zpow_zero, one_smul]

/-- **Darboux's method** (DLMF 2.10.29). Let `f` and `g` be holomorphic in the punctured disc
`0 < |z - c| < r`, and let `f - g` extend to a function `H` continuous on `0 < |z - c| ≤ r`. Then
the Laurent coefficients satisfy `fₙ = gₙ + o(r⁻ⁿ)` as `n → ±∞`: `rⁿ (fₙ - gₙ) → 0` along the
cofinite filter on `ℤ`, the coefficients being extracted on any circle of radius `ρ ∈ (0, r)`. -/
theorem tendsto_circleLaurentCoeff_sub {f g H : ℂ → E} {c : ℂ} {r ρ : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r)
    (hf : DifferentiableOn ℂ f (ball c r \ {c})) (hg : DifferentiableOn ℂ g (ball c r \ {c}))
    (hH : ContinuousOn H (closedBall c r \ {c})) (hHfg : EqOn H (f - g) (ball c r \ {c})) :
    Tendsto (fun n : ℤ ↦ (r : ℂ) ^ n • (circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n))
      cofinite (𝓝 0) := by
  have hopen : IsOpen (ball c r \ {c}) := isOpen_ball.sdiff isClosed_singleton
  have hsphere : sphere c ρ ⊆ ball c r \ {c} := fun z hz ↦
    ⟨mem_ball.2 ((mem_sphere.1 hz).trans_lt hρr),
      fun h ↦ hρ.ne' (by rw [← mem_sphere.1 hz, h, dist_self])⟩
  have hannulus : ball c r \ closedBall c ρ ⊆ ball c r \ {c} :=
    sdiff_subset_sdiff_right (singleton_subset_iff.2 (mem_closedBall_self hρ.le))
  -- The coefficients of `f - g` on the circle of radius `ρ` are those of `H` on the circle of
  -- radius `r`, by Cauchy's theorem on the closed annulus between them.
  have hcoeff (n : ℤ) : circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n =
      circleLaurentCoeff H c r n := by
    rw [← circleLaurentCoeff_sub ((hf.continuousOn.mono hsphere).circleIntegrable hρ.le)
      ((hg.continuousOn.mono hsphere).circleIntegrable hρ.le),
      circleLaurentCoeff_congr (f := fun z ↦ f z - g z) (g := H) hρ.le
        (fun z hz ↦ (hHfg (hsphere hz)).symm)]
    refine (circleLaurentCoeff_eq_of_differentiable_on_annulus_off_countable hρ hρr.le
      countable_empty (hH.mono ?_) (fun z hz ↦ ?_) n).symm
    · exact sdiff_subset_sdiff_right (singleton_subset_iff.2 (mem_ball_self hρ))
    · have hz' := hannulus hz.1
      exact (((hf z hz').sub (hg z hz')).differentiableAt
        (hopen.mem_nhds hz')).congr_of_eventuallyEq (eventually_of_mem (hopen.mem_nhds hz') hHfg)
  simpa only [hcoeff] using tendsto_zpow_smul_circleLaurentCoeff H c r

/-- The falling factorial `n (n - 1) ⋯ (n - m + 1)` is at least `|n|ᵐ / 2ᵐ` once `|n| ≥ 2m`. -/
private theorem norm_pow_le_two_pow_mul_norm_descPochhammer_eval {m : ℕ} {n : ℤ}
    (hn : 2 * (m : ℝ) ≤ |(n : ℝ)|) :
    ‖(n : ℂ)‖ ^ m ≤ 2 ^ m * ‖(descPochhammer ℂ m).eval (n : ℂ)‖ := by
  calc ‖(n : ℂ)‖ ^ m = ∏ _j ∈ Finset.range m, ‖(n : ℂ)‖ := by simp
    _ ≤ ∏ j ∈ Finset.range m, 2 * ‖(n : ℂ) - j‖ := by
      refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun j hj ↦ ?_
      have hj : (j : ℝ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.1 hj
      have h := norm_sub_norm_le (n : ℂ) (j : ℂ)
      rw [norm_intCast] at h ⊢
      rw [Complex.norm_natCast] at h
      linarith
    _ = 2 ^ m * ‖(descPochhammer ℂ m).eval (n : ℂ)‖ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        descPochhammer_eval_eq_prod_range, norm_prod]

/-- **Darboux's method with derivatives** (DLMF 2.10.31). Let `f` and `g` be holomorphic in the
punctured disc `0 < |z - c| < r`, and let `f⁽ᵐ⁾ - g⁽ᵐ⁾` extend to a function `H` continuous on
`0 < |z - c| ≤ r`. Then the Laurent coefficients satisfy `fₙ = gₙ + o(r⁻ⁿ |n|⁻ᵐ)` as `n → ±∞`:
`nᵐ rⁿ (fₙ - gₙ) → 0` along the cofinite filter on `ℤ`, the coefficients being extracted on any
circle of radius `ρ ∈ (0, r)`. For `m = 0` this is `tendsto_circleLaurentCoeff_sub`. -/
theorem tendsto_circleLaurentCoeff_sub_of_iteratedDeriv [CompleteSpace E] {f g H : ℂ → E}
    {c : ℂ} {r ρ : ℝ} (m : ℕ) (hρ : 0 < ρ) (hρr : ρ < r)
    (hf : DifferentiableOn ℂ f (ball c r \ {c})) (hg : DifferentiableOn ℂ g (ball c r \ {c}))
    (hH : ContinuousOn H (closedBall c r \ {c}))
    (hHfg : EqOn H (iteratedDeriv m f - iteratedDeriv m g) (ball c r \ {c})) :
    Tendsto (fun n : ℤ ↦ ((n : ℂ) ^ m * (r : ℂ) ^ n) •
      (circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n)) cofinite (𝓝 0) := by
  have hr : 0 < r := hρ.trans hρr
  have hopen : IsOpen (ball c r \ {c}) := isOpen_ball.sdiff isClosed_singleton
  have hD {φ : ℂ → E} (hφ : DifferentiableOn ℂ φ (ball c r \ {c})) :
      DifferentiableOn ℂ (iteratedDeriv m φ) (ball c r \ {c}) := by
    simpa only [iteratedDeriv_eq_iterate] using
      ((hφ.analyticOnNhd hopen).iterated_deriv m).differentiableOn
  have hdom : ball c r \ {c} = eball c (ENNReal.ofReal r) \ closedBall c 0 := by
    rw [eball_ofReal, closedBall_zero]
  have hρR : ENNReal.ofReal ρ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hr).2 hρr
  -- Darboux's theorem for the `m`-th derivatives, read at the shifted degree `n - m`.
  have hT := (tendsto_circleLaurentCoeff_sub hρ hρr (hD hf) (hD hg) hH hHfg).comp
    (sub_left_injective (b := (m : ℤ))).tendsto_cofinite
  have hbound : Tendsto (fun n : ℤ ↦ (2 * r) ^ m *
      ‖(r : ℂ) ^ (n - m) • (circleLaurentCoeff (iteratedDeriv m f) c ρ (n - m) -
        circleLaurentCoeff (iteratedDeriv m g) c ρ (n - m))‖) cofinite (𝓝 0) := by
    simpa using hT.norm.const_mul ((2 * r) ^ m)
  refine squeeze_zero_norm' ?_ hbound
  have hfin : ∀ᶠ n : ℤ in cofinite, 2 * (m : ℝ) ≤ |(n : ℝ)| := by
    refine eventually_cofinite.2 ((Set.finite_Ioo (-(2 * (m : ℤ))) (2 * m)).subset fun n hn ↦ ?_)
    have hn := abs_lt.1 (not_le.1 hn)
    refine ⟨?_, ?_⟩
    · have : ((-(2 * (m : ℤ)) : ℤ) : ℝ) < n := by push_cast; linarith
      exact_mod_cast this
    · have : (n : ℝ) < ((2 * (m : ℤ) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  -- For `|n| ≥ 2m`, the coefficients of the derivatives are the falling factorial, of size at
  -- least `|n|ᵐ / 2ᵐ`, times those of `f - g`.
  filter_upwards [hfin] with n hn
  have hcoeff : circleLaurentCoeff (iteratedDeriv m f) c ρ (n - m) -
      circleLaurentCoeff (iteratedDeriv m g) c ρ (n - m) =
        (descPochhammer ℂ m).eval (n : ℂ) •
          (circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n) := by
    rw [hdom] at hf hg
    rw [circleLaurentCoeff_iteratedDeriv hf le_rfl hρ hρR,
      circleLaurentCoeff_iteratedDeriv hg le_rfl hρ hρR, smul_sub]
  have hpow : r ^ (n - m) * r ^ m = r ^ n := by
    rw [← zpow_natCast, ← zpow_add₀ hr.ne', sub_add_cancel]
  rw [hcoeff, norm_smul, norm_smul, norm_smul, norm_mul, norm_pow, norm_zpow, norm_zpow,
    norm_real, Real.norm_of_nonneg hr.le, mul_pow, ← hpow]
  calc ‖(n : ℂ)‖ ^ m * (r ^ (n - m) * r ^ m) * ‖circleLaurentCoeff f c ρ n -
        circleLaurentCoeff g c ρ n‖
      ≤ 2 ^ m * ‖(descPochhammer ℂ m).eval (n : ℂ)‖ * (r ^ (n - m) * r ^ m) *
          ‖circleLaurentCoeff f c ρ n - circleLaurentCoeff g c ρ n‖ := by
        gcongr
        exact norm_pow_le_two_pow_mul_norm_descPochhammer_eval hn
    _ = _ := by ring

/-- The Laurent coefficients of `(a - z)⁻¹` about `c`, on any circle of radius less than
`|a - c|`, are `(a - c)⁻ⁿ⁻¹` in degrees `n ≥ 0` and `0` in negative degrees: on the disc
`|z - c| < |a - c|` the function is the geometric series `∑ (z - c)ⁿ (a - c)⁻ⁿ⁻¹`. -/
theorem circleLaurentCoeff_inv_sub {a c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρa : ρ < ‖a - c‖) (n : ℤ) :
    circleLaurentCoeff (fun z ↦ (a - z)⁻¹) c ρ n = if 0 ≤ n then (a - c) ^ (-n - 1) else 0 := by
  have hac : a - c ≠ 0 := norm_pos_iff.1 (hρ.trans hρa)
  have hpow (k : ℕ) : (a - c) ^ (-(k : ℤ) - 1) = (a - c)⁻¹ * ((a - c) ^ k)⁻¹ := by
    rw [show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
      pow_succ, mul_inv, mul_comm]
  refine circleLaurentCoeff_eq_of_hasSum_sphere (E := ℂ)
    (a := fun k : ℤ ↦ if 0 ≤ k then (a - c) ^ (-k - 1) else 0) hρ (fun z hz ↦ ?_) ?_ n
  · have hw : ‖(z - c) / (a - c)‖ < 1 := by
      rw [norm_div, mem_sphere_iff_norm.1 hz, div_lt_one (hρ.trans hρa)]
      exact hρa
    have hnat : HasSum (fun k : ℕ ↦ (z - c) ^ (k : ℤ) •
        (if 0 ≤ (k : ℤ) then (a - c) ^ (-(k : ℤ) - 1) else 0)) (a - z)⁻¹ := by
      have h := (hasSum_geometric_of_norm_lt_one hw).mul_left (a - c)⁻¹
      convert h using 1
      · funext k
        simp only [Nat.cast_nonneg, ite_true, zpow_natCast, smul_eq_mul, hpow, div_pow]
        field_simp
      · rw [← mul_inv, mul_sub, mul_one, mul_div_cancel₀ _ hac, sub_sub_sub_cancel_right]
    simpa using hnat.of_nat_of_neg_add_one (m' := 0) (hasSum_zero.congr_fun fun k ↦ by
      simp only [ite_eq_right (show ¬ (0 ≤ -((k : ℤ) + 1)) by omega)])
  · refine Summable.of_nat_of_neg_add_one ?_ (summable_zero.congr fun k ↦ by
      simp only [ite_eq_right (show ¬ (0 ≤ -((k : ℤ) + 1)) by omega), norm_zero, zero_mul])
    have hq : ρ / ‖a - c‖ < 1 := (div_lt_one (hρ.trans hρa)).2 hρa
    refine ((summable_geometric_of_lt_one (by positivity) hq).mul_left ‖a - c‖⁻¹).congr
      fun k ↦ ?_
    simp only [Nat.cast_nonneg, ite_true, hpow, norm_mul, norm_inv, norm_pow, zpow_natCast,
      div_pow]
    field_simp

/-! ### Checks

On every circle of radius `ρ ∈ (0, 1)`, the coefficients of `1 / (1 - z)` are `1` in degrees
`n ≥ 0` and `0` in negative degrees. For `f(z) = 1 / (1 - z) + 1 / (2 - z)` and the comparison
function `g(z) = 1 / (1 - z)`, the difference `f - g = 1 / (2 - z)` is continuous on `|z| ≤ 1`,
and Darboux's theorem with `r = 1` gives `fₙ - gₙ → 0`; indeed `fₙ - gₙ = 2⁻ⁿ⁻¹` for `n ≥ 0`. -/

example {ρ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ < 1) (n : ℤ) :
    circleLaurentCoeff (fun z : ℂ ↦ (1 - z)⁻¹) 0 ρ n = if 0 ≤ n then 1 else 0 := by
  rw [circleLaurentCoeff_inv_sub hρ (by simpa using hρ₁)]
  simp

example {ρ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ < 1) :
    Tendsto (fun n : ℤ ↦ circleLaurentCoeff (fun z : ℂ ↦ (1 - z)⁻¹ + (2 - z)⁻¹) 0 ρ n -
      circleLaurentCoeff (fun z : ℂ ↦ (1 - z)⁻¹) 0 ρ n) cofinite (𝓝 0) := by
  have hne {a z : ℂ} (h : ‖z‖ < ‖a‖) : a - z ≠ 0 := sub_ne_zero.2 fun h' ↦ (h' ▸ h).false
  have hd (a : ℂ) (ha : 1 ≤ ‖a‖) : DifferentiableOn ℂ (fun z : ℂ ↦ (a - z)⁻¹) (ball 0 1 \ {0}) :=
    fun z hz ↦ (DifferentiableAt.inv (by fun_prop)
      (hne ((mem_ball_zero_iff.1 hz.1).trans_le ha))).differentiableWithinAt
  have hc : ContinuousOn (fun z : ℂ ↦ (2 - z)⁻¹) (closedBall 0 1 \ {0}) := fun z hz ↦
    (ContinuousAt.inv₀ (by fun_prop) (hne ((mem_closedBall_zero_iff.1 hz.1).trans_lt
      (by norm_num)))).continuousWithinAt
  have h := tendsto_circleLaurentCoeff_sub (f := fun z : ℂ ↦ (1 - z)⁻¹ + (2 - z)⁻¹)
    (g := fun z : ℂ ↦ (1 - z)⁻¹) hρ hρ₁ ((hd 1 (by simp)).add (hd 2 (by norm_num)))
    (hd 1 (by simp)) hc (fun z _ ↦ by simp)
  simpa only [ofReal_one, one_zpow, one_smul] using h

example {ρ : ℝ} (hρ : 0 < ρ) (hρ₁ : ρ < 1) (n : ℕ) :
    circleLaurentCoeff (fun z : ℂ ↦ (1 - z)⁻¹ + (2 - z)⁻¹) 0 ρ n -
      circleLaurentCoeff (fun z : ℂ ↦ (1 - z)⁻¹) 0 ρ n = (2 : ℂ) ^ (-(n : ℤ) - 1) := by
  have hi (a : ℂ) (ha : ρ < ‖a‖) : CircleIntegrable (fun z : ℂ ↦ (a - z)⁻¹) 0 ρ :=
    ContinuousOn.circleIntegrable hρ.le fun z hz ↦ (ContinuousAt.inv₀ (by fun_prop)
      (sub_ne_zero.2 fun h ↦ by rw [h, mem_sphere_zero_iff_norm.1 hz] at ha; exact ha.false))
      |>.continuousWithinAt
  rw [circleLaurentCoeff_add (hi 1 (by simpa using hρ₁)) (hi 2 (by norm_num; linarith)),
    add_sub_cancel_left, circleLaurentCoeff_inv_sub hρ (by norm_num; linarith)]
  simp

end TauCeti

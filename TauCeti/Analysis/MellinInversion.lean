/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Polynomial.Basic
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Mellin inversion and the continuous first-order cutoff

Mathlib's `mellinInv σ f y` is `(1 / 2π) ∫ y^{-(σ + i t)} • f(σ + i t) dt`. This file records that
the integrand is integrable whenever `f` is integrable on the vertical line `Re s = σ` and
`y > 0`, since `t ↦ y^{-(σ + i t)}` is continuous of constant norm `y^{-σ}`.

## Main results

* `Complex.VerticalIntegrable.integrable_cpow_smul`: the integrand of the Mellin inversion
  integral of a vertically integrable function is integrable.
* `TauCeti.verticalIntegrable_inv_mul_add_one`: `1 / (s(s+1))` is integrable on lines avoiding
  `Re s = 0, -1`, including negative lines.
* `TauCeti.mellinInv_inv_mul_add_one`: its inverse Mellin transform is `max (1 - x) 0` for
  positive `x`, on every line `Re s = c > 0`.
* `TauCeti.integrable_cpow_div_mul_add_one`: absolute convergence of `x^s / (s(s+1))` for
  `x ≥ 0` on every line avoiding the two poles.
* `TauCeti.isTheta_cpow_div_ascPochhammer`: the all-order Perron kernel decays as
  `|t|⁻(j+1)` uniformly on every bounded set of real parts.
* `TauCeti.integral_cpow_div_mul_add_one`: its integral is `2π * max (1 - 1/x) 0` for
  positive `x` and `c`. At the cutoff `x = 1` this value is zero.

The kernel is used for sums smoothed by `1 - n/x`. The migration motivating this computation
is the Prime Number Theorem and more project by Alex Kontorovich, Terence Tao and contributors,
`PrimeNumberTheoremAnd/PerronFormula.lean` (`Perron.formulaLtOne`, `Perron.formulaGtOne`). The proof
here composes Mathlib's interval-power Mellin transforms and Mellin inversion, independently of
that project's contour argument.

The all-order height profile generalizes the first-order uniform estimates in the same PNT+
file, which credits Lawrence Wu for its uniform little-o arguments. Here the denominator uses
Mathlib's Pochhammer polynomial and its leading-monomial asymptotics. The profile supplies the
horizontal-tail estimates for Landau's iterated Perron formula (ExplicitZetaBounds §6.1a).
-/

public section

open Real MeasureTheory Filter Asymptotics
open scoped Topology
open Complex hiding exp continuous_exp

namespace Complex

/-- If `f` is integrable on the vertical line `Re s = σ`, then so is the integrand
`t ↦ y^{-(σ + i t)} • f(σ + i t)` of the Mellin inversion integral `mellinInv σ f y`, for
`y > 0`. -/
theorem VerticalIntegrable.integrable_cpow_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {σ : ℝ} (hf : VerticalIntegrable f σ) {y : ℝ} (hy : 0 < y) :
    Integrable fun t : ℝ ↦ (y : ℂ) ^ (-(σ + t * I)) • f (σ + t * I) := by
  -- `t ↦ y^{-(σ + i t)}` is continuous of constant norm `y^{-σ}`
  refine hf.bdd_smul (y ^ (-σ)) ?_ (Eventually.of_forall fun t ↦ ?_)
  · exact (Continuous.const_cpow (by fun_prop)
      (Or.inl (ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable
  · rw [norm_cpow_eq_rpow_re_of_pos hy]
    simp

end Complex

namespace TauCeti

/-- The kernel `1 / (s(s+1))` is integrable on each vertical line avoiding its two poles. -/
theorem verticalIntegrable_inv_mul_add_one {c : ℝ} (hc : c ≠ 0) (hc1 : c ≠ -1) :
    VerticalIntegrable (fun s : ℂ ↦ (s * (s + 1))⁻¹) c := by
  let d := min |c| |c + 1|
  have h1 : c + 1 ≠ 0 := by simpa using sub_ne_zero.mpr hc1
  have hd : 0 < d := lt_min (abs_pos.mpr hc) (abs_pos.mpr h1)
  have hmajor : Integrable (fun t : ℝ ↦ (d ^ 2 + t ^ 2)⁻¹) := by
    simpa only [add_comm] using (integrable_inv_sq_add_sq hd.ne')
  refine hmajor.mono' (by fun_prop) (Filter.Eventually.of_forall fun t ↦ ?_)
  rw [norm_inv, norm_mul]
  have hnorm (a : ℝ) (ha : d ≤ |a|) :
      Real.sqrt (d ^ 2 + t ^ 2) ≤ ‖(a : ℂ) + t * I‖ := by
    apply (Real.sqrt_le_left (norm_nonneg _)).mpr
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    nlinarith only [ha, hd.le, sq_abs a]
  have hshift : (c : ℂ) + t * I + 1 = ((c + 1 : ℝ) : ℂ) + t * I := by
    push_cast
    ring
  apply inv_anti₀ (by positivity)
  calc
    d ^ 2 + t ^ 2 = (Real.sqrt (d ^ 2 + t ^ 2)) ^ 2 :=
      (Real.sq_sqrt (by positivity)).symm
    _ ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖ := by
      rw [sq, hshift]
      exact mul_le_mul (hnorm c (min_le_left _ _)) (hnorm (c + 1) (min_le_right _ _))
        (Real.sqrt_nonneg _) (norm_nonneg _)

/-- The inverse Mellin transform of `1 / (s(s+1))` is the continuous first-order cutoff. -/
theorem mellinInv_inv_mul_add_one {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    mellinInv c (fun s : ℂ ↦ (s * (s + 1))⁻¹) x = (max (1 - x) 0 : ℝ) := by
  have hm (t : ℝ) : mellin (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ)) ((c : ℂ) + t * I) =
      ((((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))⁻¹) :=
    (hasMellin_max_one_sub_zero (by simpa using hc)).2
  have hv : VerticalIntegrable (mellin (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ))) c := by
    simpa only [VerticalIntegrable, hm] using
      verticalIntegrable_inv_mul_add_one hc.ne' (by linarith)
  have h := mellinInv_mellin_eq c (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ)) hx
    (hasMellin_max_one_sub_zero (by simpa using hc)).1 hv (by fun_prop)
  rw [mellinInv] at h ⊢
  simpa only [hm] using h

private lemma riesz_integrand_eq {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    ((x⁻¹ : ℝ) : ℂ) ^ (-s) • (s * (s + 1))⁻¹ = (x : ℂ) ^ s / (s * (s + 1)) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hx, Complex.cpow_neg, inv_inv,
    smul_eq_mul, ← div_eq_mul_inv]

/-- The first-order Perron kernel is absolutely integrable for `x ≥ 0` on every line away from
`Re s = 0, -1`. At `x = 0` the integrand vanishes. -/
theorem integrable_cpow_div_mul_add_one {c x : ℝ} (hc : c ≠ 0) (hc1 : c ≠ -1) (hx : 0 ≤ x) :
    Integrable (fun t : ℝ ↦ (x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) := by
  rcases hx.eq_or_lt with rfl | hx
  · have hz (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
      intro h
      apply hc
      simpa using congrArg Complex.re h
    apply (integrable_zero ℝ ℂ volume).congr
    exact Filter.Eventually.of_forall fun t ↦ by
      simp only [Pi.zero_apply, Complex.ofReal_zero, Complex.zero_cpow (hz t), zero_div]
  · simpa only [riesz_integrand_eq hx.le] using
      (verticalIntegrable_inv_mul_add_one hc hc1).integrable_cpow_smul (inv_pos.mpr hx)

/-- The integral of `x^s / (s(s+1))` on a positive vertical line is the continuous cutoff
weight times `2π`. In particular, its value at `x = 1` is zero. -/
theorem integral_cpow_div_mul_add_one {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (∫ t : ℝ, (x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) =
      ((2 * π : ℝ) : ℂ) * (max (1 - x⁻¹) 0 : ℝ) := by
  have h := mellinInv_inv_mul_add_one hc (inv_pos.mpr hx)
  simp only [mellinInv, riesz_integrand_eq hx.le] at h
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero pi_ne_zero
  apply (inv_mul_eq_iff_eq_mul₀ hπ).mp
  simpa only [Complex.real_smul, one_div, Complex.ofReal_inv] using h

/-- The order-`j` Perron kernel has size `|t|⁻ᵈ`, where `d = j + 1`, uniformly when its real
part ranges over a bounded set. The Pochhammer denominator is `s(s + 1)⋯(s + j)`.

Empty and nonclosed sets of real parts are allowed, including real parts through the poles.
The estimate holds in both height directions. At `j = 0` it gives decay of order `|t|⁻¹`,
which does not imply absolute convergence of the vertical integral. -/
theorem isTheta_cpow_div_ascPochhammer (j : ℕ) {x : ℝ} (hx : 0 < x)
    {K : Set ℝ} (hK : Bornology.IsBounded K) :
    (fun q : ℝ × ℝ ↦ (x : ℂ) ^ ((q.1 : ℂ) + q.2 * I) /
      (ascPochhammer ℂ (j + 1)).eval ((q.1 : ℂ) + q.2 * I))
      =Θ[𝓟 K ×ˢ (atBot ⊔ atTop)] ((fun t : ℝ ↦ 1 / t ^ (j + 1)) ∘ Prod.snd) := by
  set l : Filter (ℝ × ℝ) := 𝓟 (closure K) ×ˢ (atBot ⊔ atTop) with hl
  have hc : ∀ c : ℂ, (fun _ : ℝ × ℝ ↦ c) =o[l] Prod.snd := by
    intro c
    rw [hl, Filter.prod_sup, isLittleO_sup]
    exact ⟨(isLittleO_const_id_atBot c).comp_tendsto tendsto_snd,
      (isLittleO_const_id_atTop c).comp_tendsto tendsto_snd⟩
  have hs : (fun q : ℝ × ℝ ↦ (q.1 : ℂ) + q.2 * I) =Θ[l] Prod.snd := by
    refine IsLittleO.add_isTheta ?_ (IsTheta.of_norm_eventuallyEq_norm (by simp))
    exact ((continuous_ofReal.continuousOn.isBigO_principal hK.isCompact_closure
      (by norm_num : ‖(1 : ℂ)‖ ≠ 0)).comp_tendsto tendsto_fst).trans_isLittleO (hc 1)
  have hesc : Tendsto (fun q : ℝ × ℝ ↦ (q.1 : ℂ) + q.2 * I) l
      (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    apply hs.tendsto_norm_atTop_iff.mpr
    rw [hl, Filter.prod_sup, tendsto_sup]
    exact ⟨tendsto_abs_atBot_atTop.comp tendsto_snd,
      tendsto_abs_atTop_atTop.comp tendsto_snd⟩
  have hp := ((ascPochhammer ℂ (j + 1)).isEquivalent_cobounded_leading_monomial
    |>.comp_tendsto hesc).isTheta
  simp only [(monic_ascPochhammer ℂ (j + 1)).leadingCoeff, ascPochhammer_natDegree,
    one_mul, Function.comp_def] at hp
  have hn : (fun q : ℝ × ℝ ↦ (x : ℂ) ^ ((q.1 : ℂ) + q.2 * I)) =Θ[l]
      (fun _ ↦ (1 : ℝ)) := by
    apply isTheta_norm_left.mp
    have hcont : ContinuousOn (fun σ : ℝ ↦ |x| ^ σ) (closure K) :=
      continuousOn_const.rpow continuousOn_id fun _ _ ↦ Or.inl (ne_of_gt (abs_pos.mpr hx.ne'))
    simpa [norm_cpow_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), arg_ofReal_of_nonneg hx.le] using!
      (hcont.isTheta_principal hK.isCompact_closure (by norm_num : ‖(1 : ℝ)‖ ≠ 0)
        (fun _ _ ↦ ne_of_gt (rpow_pos_of_pos (abs_pos.mpr hx.ne') _))).comp_tendsto
          tendsto_fst
  exact (hn.div (hp.trans (hs.pow (j + 1)))).mono
    (Filter.prod_mono (Filter.principal_mono.mpr subset_closure) le_rfl)

end TauCeti

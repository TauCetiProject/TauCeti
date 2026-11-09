/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Grönwall-type estimates

Mathlib's Grönwall inequality (`le_gronwallBound_of_liminf_deriv_right_le`) bounds a function by
a bound on its derivative. Energy estimates for evolution equations instead produce a bound on a
function by an integral of itself: a continuous `φ` with `φ t ≤ c + K ∫ₐᵗ φ` on `[a, b]`, for
some `K ≥ 0`. This file proves that such a `φ` satisfies `φ t ≤ c exp (K (t - a))`
(`TauCeti.le_mul_exp_of_le_add_mul_integral`).

The hypothesis `K ≥ 0` cannot be dropped: a very negative stretch of `φ` makes `c + K ∫ₐᵗ φ`
large when `K < 0`.

For a monotone `g` the differential form needs neither continuity nor differentiability: if
`k g ≤ g'` at almost every point of `[s, t]` and `g s ≥ 0`, then `g s exp (∫ₛᵗ k) ≤ g t`
(`TauCeti.mul_exp_integral_le_of_mul_le_deriv`), because the derivative of the monotone function
`log g` integrates to at most its increment.

It also writes Mathlib's `gronwallBound` with a negative rate `-λ` in terms of the exponential
integral `E_λ(T) = ∫₀ᵀ e^{λr} dr` (`TauCeti.exp_mul_gronwallBound_neg`), and records that
`E_λ(T) > 0` for `T > 0` (`TauCeti.integral_exp_mul_pos`), that `z ↦ E_λ(z - t)` has derivative `1`
at `t` (`TauCeti.hasDerivAt_integral_exp_mul_sub`), and `E_λ(T) ≤ T e^{|λ|T}`
(`TauCeti.integral_exp_mul_le`).

Finally, it specializes Mathlib's inequality to exponential decay: a function whose derivative
satisfies `g' ≤ -λ g` on `[T, ∞)` is bounded by `g T exp (-λ (t - T))` there
(`TauCeti.le_mul_exp_of_hasDerivAt_le_neg_mul`), hence by `C exp (-λ t)` for large `t`
(`TauCeti.exists_le_mul_exp_atTop_of_hasDerivAt_le_neg_mul`).

Mathlib's uniqueness statement `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` propagates
the vanishing of a function with `‖f'‖ ≤ K ‖f‖` forward from the left endpoint of an interval.
Reversing time gives the two-sided version: on `[a, b]` such a function vanishes identically as
soon as it vanishes at one point (`TauCeti.eq_zero_of_norm_deriv_le_mul_norm_self_of_mem_Icc`).
This is the uniqueness argument for linear differential equations by energy estimates.

## References

* T. H. Gronwall, *Note on the derivatives with respect to a parameter of the solutions of a
  system of differential equations*, Ann. of Math. **20** (1919), 292–296.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix B.2.
-/

public section

open Set Filter Real MeasureTheory
open scoped Topology

namespace TauCeti

/-- **Grönwall's inequality, integral form.** If `φ` is continuous on `[a, b]`, `0 ≤ K` and
`φ t ≤ c + K ∫ₐᵗ φ` for every `t ∈ [a, b]`, then `φ t ≤ c exp (K (t - a))` on `[a, b]`. -/
theorem le_mul_exp_of_le_add_mul_integral {φ : ℝ → ℝ} {a b c K : ℝ}
    (hφ : ContinuousOn φ (Icc a b)) (hK : 0 ≤ K)
    (h : ∀ t ∈ Icc a b, φ t ≤ c + K * ∫ s in a..t, φ s) :
    ∀ t ∈ Icc a b, φ t ≤ c * exp (K * (t - a)) := by
  -- Apply the differential form to the primitive `Ψ t = ∫ₐᵗ φ`, whose derivative `φ` is at most
  -- `c + K Ψ`, then use `K ≥ 0` to pass from the bound on `Ψ` back to `φ`.
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  have hint : IntegrableOn φ (Icc a b) := hφ.integrableOn_Icc
  -- The primitive `Ψ` satisfies `Ψ a = 0` and `Ψ' = φ ≤ c + K Ψ` from the right on `[a, b)`.
  have hΨ : ContinuousOn (fun t ↦ ∫ s in a..t, φ s) (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (by rwa [uIcc_of_le hab] : IntegrableOn φ (uIcc a b))
    rwa [uIcc_of_le hab] at this
  have hderiv (x : ℝ) (hx : x ∈ Ico a b) :
      HasDerivWithinAt (fun t ↦ ∫ s in a..t, φ s) (φ x) (Ici x) x := by
    have hmem : Icc a b ∈ 𝓝[>] x := Icc_mem_nhdsGT_of_mem hx
    have hsub : uIcc a x ⊆ Icc a b := by
      rw [uIcc_of_le hx.1]
      exact Icc_subset_Icc_right hx.2.le
    refine intervalIntegral.integral_hasDerivWithinAt_right (hint.mono_set hsub).intervalIntegrable
      ?_ ((hφ x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin hmem)
    exact (hφ.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x).filter_mono
      (nhdsWithin_le_of_mem hmem)
  have hgr := le_gronwallBound_of_liminf_deriv_right_le (δ := 0) (K := K) (ε := c) hΨ
    (fun x hx r hr ↦ (hderiv x hx).liminf_right_slope_le hr) (by simp)
    (fun x hx ↦ by linarith [h x (Ico_subset_Icc_self hx)]) t ht
  -- Hence `φ t ≤ c + K Ψ t ≤ c + K gronwallBound 0 K c (t - a) = c exp (K (t - a))`.
  calc φ t ≤ c + K * ∫ s in a..t, φ s := h t ht
    _ ≤ c + K * gronwallBound 0 K c (t - a) := by gcongr
    _ = c * exp (K * (t - a)) := by
        rcases hK.eq_or_lt with rfl | hK
        · simp
        · rw [gronwallBound_of_K_ne_0 hK.ne']
          field_simp
          ring

/-- **Grönwall's inequality for monotone functions, almost-everywhere form.** Let `g` be monotone
on `[s, t]` with `g s ≥ 0`. If `k g ≤ g'` at almost every point of `(s, t)`, for an interval
integrable `k`, then `g s · exp (∫ₛᵗ k) ≤ g t`. No continuity of `g` is needed. -/
theorem mul_exp_integral_le_of_mul_le_deriv {g k : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hg : MonotoneOn g (Icc s t)) (hgs : 0 ≤ g s) (hk : IntervalIntegrable k volume s t)
    (h : ∀ᵐ σ, σ ∈ Ioo s t → k σ * g σ ≤ deriv g σ) :
    g s * Real.exp (∫ σ in s..t, k σ) ≤ g t := by
  have hgst : g s ≤ g t := hg ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  rcases hgs.eq_or_lt with hgs0 | hgs0
  · rw [← hgs0, zero_mul]
    exact hgs.trans hgst
  have hpos (σ : ℝ) (hσ : σ ∈ Icc s t) : 0 < g σ := hgs0.trans_le (hg ⟨le_rfl, hst⟩ hσ hσ.1)
  set L : ℝ → ℝ := fun σ => Real.log (g σ)
  have hL : MonotoneOn L (uIcc s t) := by
    rw [uIcc_of_le hst]
    exact fun x hx y hy hxy => Real.log_le_log (hpos x hx) (hg hx hy hxy)
  -- `k ≤ (log g)' = g' / g` at almost every point of `[s, t]`.
  have hlow : k ≤ᵐ[volume.restrict (Icc s t)] deriv L := by
    rw [Filter.EventuallyLE, Measure.restrict_congr_set Ioo_ae_eq_Icc.symm,
      ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [h, (hg.mono Ioo_subset_Icc_self).ae_differentiableWithinAt_of_mem]
      with σ hσ hd hσI
    have hgσ := hpos σ (Ioo_subset_Icc_self hσI)
    have hd' := (hd hσI).differentiableAt (Ioo_mem_nhds hσI.1 hσI.2)
    rw [(hd'.hasDerivAt.log hgσ.ne').deriv, le_div_iff₀ hgσ]
    exact hσ hσI
  -- Integrating, `∫ₛᵗ k ≤ ∫ₛᵗ (log g)' ≤ log (g t) - log (g s)`.
  have hint := intervalIntegral.integral_mono_ae_restrict hst hk hL.intervalIntegrable_deriv hlow
  have hup := hL.intervalIntegral_deriv_mem_uIcc
  rw [uIcc_of_le (sub_nonneg.2 (Real.log_le_log hgs0 hgst))] at hup
  calc g s * Real.exp (∫ σ in s..t, k σ) ≤ g s * Real.exp (L t - L s) := by
        gcongr
        exact hint.trans hup.2
    _ = g t := by
        rw [Real.exp_sub, Real.exp_log (hpos s ⟨le_rfl, hst⟩),
          Real.exp_log (hpos t ⟨hst, le_rfl⟩)]
        field_simp

/-- The closed form of `e^{λT}` times the Grönwall bound with rate `-λ`:
`e^{λT} gronwallBound δ (-λ) c T = δ + E_λ(T) c`, where `E_λ(T) = ∫₀ᵀ e^{λr} dr`. -/
theorem exp_mul_gronwallBound_neg (δ lam c T : ℝ) :
    exp (lam * T) * gronwallBound δ (-lam) c T = δ + (∫ r in 0..T, exp (lam * r)) * c := by
  rcases eq_or_ne lam 0 with rfl | hlam
  · simp [gronwallBound_K0]
    ring
  · rw [intervalIntegral.integral_comp_mul_left (fun r ↦ exp r) hlam, integral_exp]
    simp only [gronwallBound_of_K_ne_0 (neg_ne_zero.2 hlam), neg_mul, exp_neg, mul_zero, exp_zero,
      smul_eq_mul]
    have := (exp_pos (lam * T)).ne'
    field_simp
    ring

/-- The function `E_λ(T) = ∫₀ᵀ e^{λr} dr` is positive for `T > 0`. -/
theorem integral_exp_mul_pos (lam : ℝ) {T : ℝ} (hT : 0 < T) :
    0 < ∫ r in 0..T, exp (lam * r) :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous fun r ↦ exp (lam * r)).intervalIntegrable _ _)
    (fun _ _ ↦ exp_pos _) hT

/-- The map `z ↦ ∫ r in 0..(z - t), exp (lam * r)` has derivative `1` at `t`. -/
theorem hasDerivAt_integral_exp_mul_sub (lam t : ℝ) :
    HasDerivAt (fun z ↦ ∫ r in 0..(z - t), exp (lam * r)) 1 t := by
  have hsub : HasDerivAt (fun z : ℝ ↦ z - t) 1 t := (hasDerivAt_id t).sub_const t
  simpa [Function.comp_def] using ((by fun_prop : Continuous fun r ↦
    exp (lam * r)).integral_hasStrictDerivAt 0 (t - t)).hasDerivAt.comp (h := fun z ↦ z - t) t
      hsub

/-- The function `E_λ(T) = ∫₀ᵀ e^{λr} dr` satisfies `E_λ(T) ≤ T e^{|λ|T}`. -/
theorem integral_exp_mul_le (lam T : ℝ) :
    ∫ r in 0..T, exp (lam * r) ≤ T * exp (|lam| * T) := by
  have hc : Continuous fun r ↦ exp (lam * r) := by fun_prop
  rcases le_total 0 T with hT | hT
  · have := intervalIntegral.integral_mono_on (g := fun _ ↦ exp (|lam| * T)) hT
      (hc.intervalIntegrable _ _) (intervalIntegrable_const (μ := volume))
      fun r hr ↦ exp_le_exp.2 <| by
        nlinarith [le_abs_self lam, abs_nonneg lam, hr.1, hr.2]
    simpa using this
  · rw [intervalIntegral.integral_symm]
    have := intervalIntegral.integral_mono_on (f := fun _ ↦ exp (|lam| * T)) hT
      (intervalIntegrable_const (μ := volume)) (hc.intervalIntegrable _ _)
      fun r hr ↦ exp_le_exp.2 <| by
        rcases le_total 0 lam with h | h
        · rw [abs_of_nonneg h]; nlinarith [hr.1, hr.2]
        · rw [abs_of_nonpos h]; nlinarith [hr.1, hr.2]
    simp only [intervalIntegral.integral_const, smul_eq_mul, zero_sub] at this
    linarith

/-- **Exponential decay from a differential inequality.** If `g' ≤ -lam * g` on `[T, ∞)`, then
`g t ≤ g T * exp (-(lam * (t - T)))` for every `t ≥ T`. -/
theorem le_mul_exp_of_hasDerivAt_le_neg_mul {g g' : ℝ → ℝ} {T lam : ℝ}
    (hg : ∀ s ∈ Ici T, HasDerivAt g (g' s) s) (hle : ∀ s ∈ Ici T, g' s ≤ -lam * g s)
    {t : ℝ} (ht : T ≤ t) :
    g t ≤ g T * exp (-(lam * (t - T))) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le (f := g) (f' := g') (δ := g T) (K := -lam)
    (ε := 0) (a := T) (b := t) (fun s hs ↦ (hg s hs.1).continuousAt.continuousWithinAt)
    (fun s hs r hr ↦ (hg s hs.1).hasDerivWithinAt.liminf_right_slope_le hr) le_rfl
    (fun s hs ↦ by linarith [hle s hs.1]) t ⟨ht, le_rfl⟩
  simpa only [gronwallBound_ε0, neg_mul] using h

/-- **Exponential decay from a differential inequality, eventual form.** If `g' ≤ -lam * g` on
`[T, ∞)`, then `g t ≤ C * exp (-(lam * t))` for some `C > 0` and all large `t`. -/
theorem exists_le_mul_exp_atTop_of_hasDerivAt_le_neg_mul {g g' : ℝ → ℝ} {T lam : ℝ}
    (hg : ∀ s ∈ Ici T, HasDerivAt g (g' s) s) (hle : ∀ s ∈ Ici T, g' s ≤ -lam * g s) :
    ∃ C > 0, ∀ᶠ t in atTop, g t ≤ C * exp (-(lam * t)) := by
  refine ⟨(|g T| + 1) * exp (lam * T), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop T] with t ht
  calc g t ≤ g T * exp (-(lam * (t - T))) := le_mul_exp_of_hasDerivAt_le_neg_mul hg hle ht
    _ ≤ (|g T| + 1) * exp (-(lam * (t - T))) := by
        gcongr
        linarith [le_abs_self (g T)]
    _ = (|g T| + 1) * exp (lam * T) * exp (-(lam * t)) := by
        rw [mul_assoc, ← exp_add]
        congr 2
        ring

/-- **Two-sided uniqueness from a Grönwall bound.** If `f` is differentiable within `[a, b]`,
satisfies `‖f'‖ ≤ K ‖f‖` there and vanishes at one point of `[a, b]`, then it vanishes on
`[a, b]`. Mathlib's `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` is the case where
the point is `a`. -/
theorem eq_zero_of_norm_deriv_le_mul_norm_self_of_mem_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f f' : ℝ → E} {K a b c : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (bound : ∀ x ∈ Icc a b, ‖f' x‖ ≤ K * ‖f x‖) (hc : c ∈ Icc a b) (hfc : f c = 0) :
    ∀ x ∈ Icc a b, f x = 0 := by
  intro x hx
  rcases le_total c x with hcx | hxc
  · have hsub : Icc c b ⊆ Icc a b := Icc_subset_Icc_left hc.1
    exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (fun y hy ↦ (hf y (hsub hy)).continuousWithinAt.mono hsub)
      (fun y hy ↦ (hf y (hsub (Ico_subset_Icc_self hy))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨hc.1.trans hy.1, hy.2⟩))
      hfc (fun y hy ↦ bound y (hsub (Ico_subset_Icc_self hy))) x ⟨hcx, hx.2⟩
  · -- Reverse time and run the forward argument on `[-c, -a]`.
    have hsub : Icc (-c) (-a) ⊆ -Icc a b := fun y hy ↦
      ⟨by linarith [hy.2], by linarith [hy.1, hc.2]⟩
    have key := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f := fun y ↦ f (-y)) (f' := fun y ↦ -f' (-y)) (K := K) (a := -c) (b := -a)
      (fun y hy ↦ (hf (-y) (hsub hy)).continuousWithinAt.comp continuous_neg.continuousWithinAt
        fun z hz ↦ hsub hz)
      (fun y hy ↦ by
        have h := ((hf (-y) (hsub (Ico_subset_Icc_self hy))).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem ⟨by linarith [hy.2], by linarith [hy.1, hc.2]⟩)).scomp y
          (hasDerivWithinAt_neg y (Ici y)) fun z hz ↦ neg_le_neg_iff.2 hz
        simpa [Function.comp_def] using h)
      (by simpa using hfc) (fun y hy ↦ by simpa using bound (-y) (hsub (Ico_subset_Icc_self hy)))
      (-x) ⟨by linarith, by linarith [hx.1]⟩
    simpa using key

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.ODE.Gronwall.Interior
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Grönwall-type estimates

Mathlib's Grönwall inequality (`le_gronwallBound_of_liminf_deriv_right_le`) bounds a function by
a bound on its derivative. The integral form, which bounds a function by an integral of itself, is
in `TauCeti.Analysis.ODE.Gronwall.Integrable`.

For a monotone `g` the differential form needs neither continuity nor differentiability: if
`k g ≤ g'` at almost every point of `[s, t]` and `g s ≥ 0`, then `g s exp (∫ₛᵗ k) ≤ g t`
(`TauCeti.mul_exp_integral_le_of_mul_le_deriv`), because the derivative of the monotone function
`log g` integrates to at most its increment.

It also writes Mathlib's `gronwallBound` with a negative rate `-λ` in terms of the exponential
integral `E_λ(T) = ∫₀ᵀ e^{λr} dr` (`TauCeti.exp_mul_gronwallBound_neg`). Elementary bounds on
`E_λ` live beside `TauCeti.integral_exp_mul` in `TauCeti.Analysis.SpecialFunctions.Integrals.Basic`.

Finally, it specializes Mathlib's inequality to exponential decay: a function whose derivative
satisfies `g' ≤ -λ g` on `[T, ∞)` is bounded by `g T exp (-λ (t - T))` there
(`TauCeti.le_mul_exp_of_hasDerivAt_le_neg_mul`), hence by `C exp (-λ t)` for large `t`
(`TauCeti.exists_le_mul_exp_atTop_of_hasDerivAt_le_neg_mul`).

Mathlib's uniqueness statement `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` propagates
the vanishing of a function with `‖f'‖ ≤ K ‖f‖` forward from the left endpoint of an interval.
Reversing time gives the two-sided version: on `[a, b]` such a function vanishes identically as
soon as it vanishes at one point (`TauCeti.eq_zero_of_norm_deriv_le_mul_norm_self_of_mem_Icc`).
The general closed-interval bound is supplied by
`TauCeti.norm_le_gronwallBound_of_norm_derivWithin_le`; its interior-derivative variant is
`TauCeti.norm_le_gronwallBound_of_norm_deriv_le`. This is the uniqueness argument for linear
differential equations by energy estimates.
Averaging the two-sided Grönwall bound over `[s, s + 1]` bounds a function `u` with
`‖u'‖ ≤ K ‖u‖` on `[s, s + 1]` (derivatives taken within `[s, s + 1]`) by its local `L²` norm:
`‖u s‖² ≤ exp (2 K) ∫_{[s, s + 1]} ‖u‖²` (`TauCeti.norm_sq_le_exp_mul_setIntegral_norm_sq`).
Hence a function that is differentiable on all of `ℝ`, satisfies `‖u'‖ ≤ K ‖u‖` at every point
of `ℝ` and is square integrable on `ℝ` obeys `‖u s‖² ≤ exp (2 K) ∫ ‖u‖²` for every `s`
(`TauCeti.norm_sq_le_exp_mul_integral_norm_sq`).

## References

* T. H. Gronwall, *Note on the derivatives with respect to a parameter of the solutions of a
  system of differential equations*, Ann. of Math. **20** (1919), 292–296.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix B.2.
-/

public section

open Set Filter Real MeasureTheory
open scoped Topology

namespace TauCeti

/-- **Grönwall's inequality for monotone functions, almost-everywhere form.** Let `g` be monotone
on `[s, t]` with `g s ≥ 0`. If `k g ≤ g'` at almost every point of `(s, t)`, then
`g s · exp (∫ₛᵗ k) ≤ g t`. No continuity of `g` is needed. If `k` is not interval integrable, the
integral is the junk value `0` and the bound is just monotonicity. -/
theorem mul_exp_integral_le_of_mul_le_deriv {g k : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hg : MonotoneOn g (Icc s t)) (hgs : 0 ≤ g s)
    (h : ∀ᵐ σ, σ ∈ Ioo s t → k σ * g σ ≤ deriv g σ) :
    g s * Real.exp (∫ σ in s..t, k σ) ≤ g t := by
  have hgst : g s ≤ g t := hg ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  by_cases hk : IntervalIntegrable k volume s t
  swap
  · rw [intervalIntegral.integral_undef hk, Real.exp_zero, mul_one]
    exact hgst
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
  have h := norm_le_gronwallBound_of_norm_derivWithin_le hc hf
    (δ := 0) (ε := 0) (by simp only [hfc, norm_zero, le_refl])
    (fun y hy ↦ by simpa only [add_zero] using bound y hy) x hx
  simpa only [gronwallBound_ε0_δ0, norm_le_zero_iff] using h

/-- **A path with derivative controlled by its norm is bounded by its local `L²` norm.** If `u`
has derivative `u'` within `[s, s + 1]` at every point of `[s, s + 1]` and `‖u'‖ ≤ K ‖u‖` there,
then `‖u s‖² ≤ exp (2 K) ∫_{[s, s + 1]} ‖u‖²`. (For `K < 0` the hypothesis at `s` forces
`u s = 0`.) -/
theorem norm_sq_le_exp_mul_setIntegral_norm_sq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u u' : ℝ → F} {K s : ℝ}
    (hu : ∀ t ∈ Icc s (s + 1), HasDerivWithinAt u (u' t) (Icc s (s + 1)) t)
    (hu' : ∀ t ∈ Icc s (s + 1), ‖u' t‖ ≤ K * ‖u t‖) :
    ‖u s‖ ^ 2 ≤ Real.exp (2 * K) * ∫ t in Icc s (s + 1), ‖u t‖ ^ 2 := by
  have hs : s ∈ Icc s (s + 1) := left_mem_Icc.2 (by linarith)
  -- For `K < 0`, `0 ≤ ‖u' s‖ ≤ K ‖u s‖` forces `u s = 0`.
  rcases lt_or_ge K 0 with hK | hK
  · have hus : ‖u s‖ = 0 :=
      (nonpos_of_mul_nonneg_right ((norm_nonneg _).trans (hu' s hs)) hK).antisymm (norm_nonneg _)
    rw [hus, zero_pow two_ne_zero]
    exact mul_nonneg (Real.exp_pos _).le (setIntegral_nonneg measurableSet_Icc fun _ _ ↦ by
      positivity)
  -- Grönwall on `[s, s + 1]` from the point `t`: `‖u s‖ ≤ exp K ‖u t‖` for `t ∈ [s, s + 1]`.
  have hback (t : ℝ) (ht : t ∈ Icc s (s + 1)) :
      ‖u s‖ ^ 2 ≤ Real.exp (2 * K) * ‖u t‖ ^ 2 := by
    have hg := norm_le_gronwallBound_of_norm_derivWithin_le ht hu le_rfl
      (fun r hr ↦ (hu' r hr).trans_eq (add_zero _).symm) s hs
    rw [gronwallBound_ε0] at hg
    have hst : |s - t| ≤ 1 := by
      simpa [abs_sub_comm s t] using abs_sub_left_of_mem_uIcc (Icc_subset_uIcc ht)
    have hle : ‖u s‖ ≤ ‖u t‖ * Real.exp K :=
      hg.trans (by gcongr; exact mul_le_of_le_one_right hK hst)
    calc ‖u s‖ ^ 2 ≤ (‖u t‖ * Real.exp K) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = Real.exp (2 * K) * ‖u t‖ ^ 2 := by
        rw [mul_pow, ← Real.exp_natCast_mul, Nat.cast_ofNat, mul_comm]
  -- Average the pointwise bound over `[s, s + 1]`; `‖u‖²` is continuous on `[s, s + 1]`.
  have hcont : ContinuousOn u (Icc s (s + 1)) := fun t ht ↦ (hu t ht).continuousWithinAt
  have hint : IntegrableOn (fun t ↦ ‖u t‖ ^ 2) (Icc s (s + 1)) :=
    (hcont.norm.pow 2).integrableOn_Icc
  calc ‖u s‖ ^ 2 = ∫ _ in Icc s (s + 1), ‖u s‖ ^ 2 := by simp
    _ ≤ ∫ t in Icc s (s + 1), Real.exp (2 * K) * ‖u t‖ ^ 2 :=
      setIntegral_mono_on (by simp) (hint.const_mul _) measurableSet_Icc hback
    _ = Real.exp (2 * K) * ∫ t in Icc s (s + 1), ‖u t‖ ^ 2 := integral_const_mul _ _

/-- **A square-integrable path with derivative controlled by its norm is bounded.** If `u` is
differentiable on all of `ℝ`, `‖u'‖ ≤ K ‖u‖` at every point of `ℝ` and `u` is square integrable
on `ℝ`, then `‖u s‖² ≤ exp (2 K) ∫ ‖u‖²` for every `s`. (For `K < 0` the hypothesis forces
`u = 0`.) -/
theorem norm_sq_le_exp_mul_integral_norm_sq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u u' : ℝ → F} {K : ℝ}
    (hu : ∀ s, HasDerivAt u (u' s) s) (hu' : ∀ s, ‖u' s‖ ≤ K * ‖u s‖) (hu2 : MemLp u 2)
    (s : ℝ) : ‖u s‖ ^ 2 ≤ Real.exp (2 * K) * ∫ t, ‖u t‖ ^ 2 :=
  (norm_sq_le_exp_mul_setIntegral_norm_sq (fun t _ ↦ (hu t).hasDerivWithinAt)
    fun t _ ↦ hu' t).trans <| mul_le_mul_of_nonneg_left
      (setIntegral_le_integral ((memLp_two_iff_integrable_sq_norm hu2.aestronglyMeasurable).1 hu2)
        (.of_forall fun _ ↦ by positivity)) (Real.exp_pos _).le

end TauCeti

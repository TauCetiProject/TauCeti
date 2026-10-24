/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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

It also writes Mathlib's `gronwallBound` with a negative rate `-λ` in terms of the exponential
integral `E_λ(T) = ∫₀ᵀ e^{λr} dr` (`TauCeti.exp_mul_gronwallBound_neg`), and records that
`E_λ(T) > 0` for `T > 0` (`TauCeti.integral_exp_mul_pos`) and `E_λ(T) ≤ T e^{|λ|T}` for `T ≥ 0`
(`TauCeti.integral_exp_mul_le`).

Finally, it specializes Mathlib's inequality to exponential decay: a function whose derivative
satisfies `g' ≤ -λ g` on `[T, ∞)` is bounded by `g T exp (-λ (t - T))` there
(`TauCeti.le_mul_exp_of_hasDerivAt_le_neg_mul`), hence by `C exp (-λ t)` for large `t`
(`TauCeti.exists_le_mul_exp_atTop_of_hasDerivAt_le_neg_mul`).

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

/-- The function `E_λ(T) = ∫₀ᵀ e^{λr} dr` satisfies `E_λ(T) ≤ T e^{|λ|T}` for `T ≥ 0`. -/
theorem integral_exp_mul_le (lam : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ r in 0..T, exp (lam * r) ≤ T * exp (|lam| * T) := by
  have := intervalIntegral.integral_mono_on (g := fun _ ↦ exp (|lam| * T)) hT
    ((by fun_prop : Continuous fun r ↦ exp (lam * r)).intervalIntegrable _ _)
    (intervalIntegrable_const (μ := volume)) fun r hr ↦ exp_le_exp.2 <| by
      nlinarith [le_abs_self lam, abs_nonneg lam, hr.1, hr.2]
  simpa using this

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

end TauCeti

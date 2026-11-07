/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PathIntegral
public import TauCeti.Geometry.Manifold.DifferentialForm.LogDeriv
-- Private: the endpoint-ratio identity of winding numbers is used only inside proofs.
import TauCeti.Analysis.Contour.Winding.EndpointRatio

/-!
# Periods of logarithmic derivatives

The logarithmic derivative `dlog u = u⁻¹ du` of a complex function `u` on a manifold
(`TauCeti.mlogDeriv`, in `TauCeti.Geometry.Manifold.DifferentialForm.LogDeriv`) integrates along
a `C¹` curve avoiding the zeros of `u` to a number whose exponential is the ratio of the endpoint
values,

`exp (∫_γ dlog u) = u (γ b) / u (γ a)`

(`TauCeti.exp_pathIntegral_mlogDeriv`). This is the endpoint-ratio identity for the winding number
of the plane curve `u ∘ γ` about the origin. Hence the periods of `dlog u` lie in `2πiℤ`
(`TauCeti.exists_pathIntegral_mlogDeriv_eq_int_mul`).

Conversely, on a connected manifold a closed `1`-form `φ` whose integrals along smooth loops at a
base point `x₀` lie in `2πiℤ` is the logarithmic derivative of a nowhere-vanishing function `u`
with `u x₀ = 1` (`TauCeti.exists_mlogDeriv_eq_of_forall_pathIntegral_eq_int_mul`). The function is
`u y = exp (∫_γ φ)` along any smooth curve `γ` from `x₀` to `y`. Two such curves give integrals
that differ by a period, so `u` is well defined. Near each point `u` is a constant multiple of
`exp g` for a local primitive `g` of `φ`, so `u` is smooth with `dlog u = φ`. The construction is
the multiplicative form of the line-integral primitive of
`TauCeti.exists_mextDeriv_eq_of_forall_pathIntegral_eq_zero`.

Together with `TauCeti.re_mlogDeriv_apply_eq_zero` and
`TauCeti.norm_eq_of_re_mlogDeriv_apply_eq_zero` (in
`TauCeti.Geometry.Manifold.DifferentialForm.LogDeriv`), imaginary closed `1`-forms with periods
in `2πiℤ` are exactly the logarithmic derivatives of circle-valued functions.

## Main declarations

* `TauCeti.exp_pathIntegral_mlogDeriv`, `TauCeti.exists_pathIntegral_mlogDeriv_eq_int_mul`: the
  periods of `dlog u` lie in `2πiℤ`.
* `TauCeti.exists_mlogDeriv_eq_of_forall_pathIntegral_eq_int_mul`: a closed `1`-form with periods
  in `2πiℤ` is the logarithmic derivative of a nowhere-vanishing function.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section *Conservative
  Covector Fields*.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996 (the gauge group of
  circle-valued maps and its logarithmic derivatives).
-/
public section

noncomputable section

open Set Filter Complex MeasureTheory
open scoped Manifold ContDiff Topology Real

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Periods -/

/-- **The integral of `dlog u` along a curve exponentiates to the endpoint ratio.** Along a `C¹`
curve `γ` on which the `C¹` function `u` does not vanish,
`exp (∫_γ dlog u) = u (γ b) / u (γ a)`. -/
theorem exp_pathIntegral_mlogDeriv {u : M → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) 1 u) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {a b : ℝ} (hu₀ : ∀ t ∈ uIcc a b, u (γ t) ≠ 0) :
    exp (pathIntegral (mlogDeriv I u) γ a b) = u (γ b) / u (γ a) := by
  have hc : ContDiff ℝ 1 (u ∘ γ) := contMDiff_iff_contDiff.mp (hu.comp hγ)
  have hd (t : ℝ) : HasDerivAt (u ∘ γ)
      (mvfderiv I u (γ t) (Manifold.curveVelocity I γ t)) t :=
    Manifold.hasDerivAt_comp_curve ((hu (γ t)).mdifferentiableAt one_ne_zero)
      (Manifold.hasMFDerivAt_curveVelocity ((hγ t).mdifferentiableAt one_ne_zero))
  -- The line integral is the winding-number integral of the plane curve `u ∘ γ`.
  have hint : pathIntegral (mlogDeriv I u) γ a b =
      ∫ t in a..b, ((u ∘ γ) t - 0)⁻¹ * deriv (u ∘ γ) t := by
    rw [pathIntegral_def]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    rw [mlogDeriv_apply, (hd t).deriv, sub_zero, Function.comp_apply]
  have hcont : ContinuousOn (u ∘ γ) (uIcc a b) := hc.continuous.continuousOn
  have hii := Contour.intervalIntegrable_inv_sub_mul_deriv hcont hu₀
    (hc.continuous_deriv_one.intervalIntegrable a b)
  have he := Contour.exp_two_pi_I_mul_windingNumber_of_avoidance countable_empty hcont
    (fun t _ ↦ hc.differentiable one_ne_zero t) hu₀ hii
  rw [Contour.windingNumber_eq_integral_of_avoidance hcont hu₀, ← mul_assoc,
    mul_inv_cancel₀ two_pi_I_ne_zero, one_mul] at he
  rw [hint, he, sub_zero, sub_zero, Function.comp_apply, Function.comp_apply]

/-- **The periods of `dlog u` lie in `2πiℤ`.** The integral of the logarithmic derivative of a
`C¹` function `u` around a closed `C¹` curve on which `u` does not vanish is an integer multiple
of `2πi`. -/
theorem exists_pathIntegral_mlogDeriv_eq_int_mul {u : M → ℂ} (hu : ContMDiff I 𝓘(ℝ, ℂ) 1 u)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {a b : ℝ} (hu₀ : ∀ t ∈ uIcc a b, u (γ t) ≠ 0)
    (hab : γ a = γ b) : ∃ n : ℤ, pathIntegral (mlogDeriv I u) γ a b = n * (2 * π * Complex.I) := by
  rw [← exp_eq_one_iff, exp_pathIntegral_mlogDeriv hu hγ hu₀, hab,
    div_self (hu₀ b right_mem_uIcc)]

/-! ### Closed forms with periods in `2πiℤ` -/

/-- If the integrals of `φ` along smooth loops at `x₀` lie in `2πiℤ`, then two smooth curves from
`x₀` to `y`, constant on `(-∞, 0]` and on `[1, ∞)`, have line integrals with the same
exponential. -/
private theorem exp_pathIntegral_eq_of_forall_pathIntegral_eq_int_mul [IsManifold I 1 M]
    {φ : RoughForm I M ℂ 1} (hφ : IsSmoothForm I 0 φ) {x₀ y : M}
    (h : ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ → γ 0 = x₀ → γ 1 = x₀ →
      ∃ n : ℤ, pathIntegral φ γ 0 1 = n * (2 * π * Complex.I))
    {γ γ' : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hγ₀ : ∀ t ≤ 0, γ t = x₀)
    (hγ₁ : ∀ t, 1 ≤ t → γ t = y) (hγ' : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ')
    (hγ'₀ : ∀ t ≤ 0, γ' t = x₀) (hγ'₁ : ∀ t, 1 ≤ t → γ' t = y) :
    exp (pathIntegral φ γ 0 1) = exp (pathIntegral φ γ' 0 1) := by
  obtain ⟨ℓ, hℓ, hℓ₀, hℓ₁, hℓφ⟩ :=
    exists_contMDiff_loop_pathIntegral_eq_sub hφ hγ hγ₀ hγ₁ hγ' hγ'₀ hγ'₁
  obtain ⟨n, hn⟩ := h ℓ hℓ hℓ₀ hℓ₁
  exact exp_eq_exp_iff_exists_int.mpr ⟨n, by rw [← hn, hℓφ]; ring⟩

/-- **Closed forms with periods in `2πiℤ` are logarithmic derivatives.** On a connected manifold,
a closed `C^r` complex `1`-form `φ` (`1 ≤ r`) whose integral along every smooth loop at a base
point `x₀` is an integer multiple of `2πi` is the logarithmic derivative of a nowhere-vanishing
`C^r` function `u` with `u x₀ = 1`. The function is `u y = exp (∫_γ φ)` along smooth curves `γ`
from `x₀` to `y`. -/
theorem exists_mlogDeriv_eq_of_forall_pathIntegral_eq_int_mul [FiniteDimensional ℝ E]
    [T2Space M] [IsManifold I ∞ M] [PreconnectedSpace M] {r : ℕ∞} (hr : 1 ≤ r)
    {φ : RoughForm I M ℂ 1} (hφ : IsSmoothForm I r φ) (hclosed : mextDeriv φ = 0) (x₀ : M)
    (h : ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ γ → γ 0 = x₀ → γ 1 = x₀ →
      ∃ n : ℤ, pathIntegral φ γ 0 1 = n * (2 * π * Complex.I)) :
    ∃ u : M → ℂ, ContMDiff I 𝓘(ℝ, ℂ) r u ∧ (∀ x, u x ≠ 0) ∧ u x₀ = 1 ∧ mlogDeriv I u = φ := by
  have hφ₀ : IsSmoothForm I 0 φ := hφ.of_le (by simp)
  -- The exponent `f` is the integral along chosen smooth curves from `x₀`.
  choose γ hγ hγ₀ hγ₁ using fun y : M ↦ exists_contMDiff_curve (I := I) (n := ⊤) x₀ y
  set f : M → ℂ := fun y ↦ pathIntegral φ (γ y) 0 1 with hf_def
  -- Near each point `x`, `exp ∘ f` is a constant multiple of `exp g` for a local primitive `g`.
  have hloc (x : M) : ∃ g : M → ℂ, ContMDiffAt I 𝓘(ℝ, ℂ) r g x ∧
      (∀ᶠ y in 𝓝 x, exp (f y) = exp (f x - g x) * exp (g y)) ∧
      mextDeriv (RoughForm.ofFunction I g) x = φ x := by
    obtain ⟨g, hg, hdg, hδ⟩ := exists_local_primitive_pathIntegral_eq_add_sub hr hφ
      (Eventually.of_forall fun y ↦ congrFun hclosed y) (hγ x) (hγ₀ x) (hγ₁ x)
    refine ⟨g, hg, ?_, hdg⟩
    filter_upwards [hδ] with y ⟨δ, hδ, hδ₀, hδ₁, hδφ⟩
    rw [hf_def, exp_pathIntegral_eq_of_forall_pathIntegral_eq_int_mul hφ₀ h (hγ y) (hγ₀ y)
      (hγ₁ y) hδ hδ₀ hδ₁, hδφ, ← exp_add]
    congr 1
    ring
  refine ⟨fun y ↦ exp (f y), fun x ↦ ?_, fun x ↦ exp_ne_zero _, ?_, funext fun x ↦ ?_⟩
  · obtain ⟨g, hg, hfg, -⟩ := hloc x
    exact ((contDiff_const.mul Complex.contDiff_exp).contDiffAt.comp_contMDiffAt hg)
      |>.congr_of_eventuallyEq hfg
  · obtain ⟨n, hn⟩ := h _ (hγ x₀) (hγ₀ x₀ 0 le_rfl) (hγ₁ x₀ 1 le_rfl)
    exact exp_eq_one_iff.mpr ⟨n, hn⟩
  · obtain ⟨g, hg, hfg, hdg⟩ := hloc x
    rw [mlogDeriv_eq_of_eventuallyEq_mul_exp (exp_ne_zero _)
      ((hg.of_le (by exact_mod_cast hr)).mdifferentiableAt one_ne_zero) hfg, hdg]

end TauCeti

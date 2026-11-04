/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Equicontinuity
public import TauCeti.Analysis.Calculus.BumpFunction.SmoothApprox
public import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.WholeSpace

/-!
# Attainment of uniformly continuous initial values

On the slab `Q = [0, T] × ℝⁿ`, with `ℝⁿ = EuclideanSpace ℝ ι`, consider the parabolic operator
in non-divergence form

`P u = ∂ₜu - ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

with degenerate elliptic `a` and bounded coefficients: `|aⁱʲ| ≤ Λ`, `‖b‖ ≤ β` and `|c| ≤ γ`,
as in `TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.WholeSpace`. Let `u` be a bounded
classical solution, continuous on `Q`, `C²` in space and differentiable in time for `0 < t < T`,
with `|P u| ≤ F` and `|u(·, 0)| ≤ G`. This file proves that `u(·, t)` approaches its initial
value at a rate given by the modulus of continuity of `u(·, 0)` alone: there is a constant `C`,
depending only on `n`, `T`, `Λ`, `β` and `γ`, such that

`|u(t, x) - u(0, x)| ≤ C (ω(√t) + t (G + F))`

whenever `|u(0, x) - u(0, y)| ≤ ω(‖x - y‖)` with `ω` nondecreasing
(`TauCeti.PDE.exists_abs_sub_le_mul_add_of_abs_sub_le_comp_dist`). The constant does not depend
on `u`, `ω`, `G` or `F`. Consequently, for a uniformly bounded family of solutions whose initial
values are uniformly equicontinuous, `u(·, t) → u(·, 0)` uniformly over the whole family as
`t → 0` (`TauCeti.PDE.tendstoUniformly_nhdsWithin_zero_of_uniformEquicontinuous`). This is the
estimate by which solutions with bounded uniformly continuous initial data are shown to attain
their initial values, uniformly over data with a common modulus of continuity.

## The argument

Fix `t > 0` and smooth `u(·, 0)` at the parabolic scale `ε = √t`
(`TauCeti.exists_forall_exists_contDiff_dist_le_and_norm_iteratedFDeriv_le`): the smoothing `h`
satisfies `|h - u(·, 0)| ≤ ω(ε)`, `‖Dh‖ ≤ K₁ ω(ε) / ε` and `‖D²h‖ ≤ K₂ ω(ε) / ε²`. As `h` does
not depend on time, `v = u - h` satisfies `|P v| ≤ F + n² Λ ‖D²h‖ + β ‖Dh‖ + γ |h|` and
`|v(·, 0)| ≤ ω(ε)`, so the a priori bound of the whole-space comparison principle
(`abs_le_exp_mul_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le`)
gives `|v(t, x)| ≤ exp (γ t) (ω(ε) + t sup |P v|)`. At time `t = ε²` the derivative terms
contribute `t ‖D²h‖ ≤ K₂ ω(ε)` and `t ‖Dh‖ ≤ K₁ √T ω(ε)`, which yields the estimate.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004),
  Chapter 4.
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2, Section 4.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Filter Matrix Metric Set Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {a : ℝ → EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : ℝ → EuclideanSpace ℝ ι → ℝ}
  {u : ℝ → EuclideanSpace ℝ ι → ℝ} {T Λ β γ F : ℝ}

/-- **Comparison with a stationary function.** If `h` is `C²` with `|h| ≤ M₀`, `‖Dh‖ ≤ M₁` and
`‖D²h‖ ≤ M₂`, and `|u(·, 0) - h| ≤ w`, then
`|u(t, x) - h(x)| ≤ exp (γ t) (w + t (F + n² Λ M₂ + β M₁ + γ M₀))`. -/
private theorem abs_sub_le_of_abs_initial_sub_le
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a t x).toQuadraticForm' ξ)
    (hΛ : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x i j, |a t x i j| ≤ Λ)
    (hb : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b t x‖ ≤ β)
    (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |c t x| ≤ γ) (hΛ0 : 0 ≤ Λ) (hβ0 : 0 ≤ β) (hγ0 : 0 ≤ γ)
    (hcont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hbdd : Bornology.IsBounded (Function.uncurry u '' Icc 0 T ×ˢ univ))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hP : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |deriv (fun s ↦ u s x) t -
      (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x)| ≤ F)
    {h : EuclideanSpace ℝ ι → ℝ} (hh : ContDiff ℝ 2 h) {w M₀ M₁ M₂ : ℝ}
    (hh0 : ∀ x, |h x| ≤ M₀) (hh1 : ∀ x, ‖fderiv ℝ h x‖ ≤ M₁)
    (hh2 : ∀ x, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M₂) (hw : ∀ x, |u 0 x - h x| ≤ w) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, |u t x - h x| ≤
      Real.exp (γ * t) * (w + t * (F + Fintype.card ι ^ 2 * Λ * M₂ + β * M₁ + γ * M₀)) := by
  set v : ℝ → EuclideanSpace ℝ ι → ℝ := fun t ↦ u t + (-1 : ℝ) • h
  have hv : ∀ t x, v t x = u t x - h x := fun t x ↦ by
    simp only [v, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  have hvR : ∀ p ∈ Icc 0 T ×ˢ univ, |Function.uncurry v p| ≤ R + M₀ := fun p hp ↦ by
    have h1 : |u p.1 p.2| ≤ R := by simpa [Function.uncurry_def] using hR _ ⟨p, hp, rfl⟩
    rw [Function.uncurry_apply_pair, hv]
    exact (abs_sub _ _).trans (add_le_add h1 (hh0 p.2))
  have key :=
    abs_le_exp_mul_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le (u := v)
    (Lam := Fintype.card ι * Λ) (β := β) (γ := γ) (M := w)
    (F := F + Fintype.card ι ^ 2 * Λ * M₂ + β * M₁ + γ * M₀) ha
    (fun t ht x ↦ by
      have htr : (a t x).trace ≤ Fintype.card ι * Λ :=
        calc (a t x).trace ≤ ∑ _i : ι, Λ :=
              Finset.sum_le_sum fun i _ ↦ (le_abs_self _).trans (hΛ ht x i i)
          _ = Fintype.card ι * Λ := by simp
      exact htr.trans (le_mul_of_one_le_right (by positivity) (by nlinarith [norm_nonneg x])))
    (fun t ht x ↦ (hb ht x).trans (le_mul_of_one_le_right hβ0 (by linarith [norm_nonneg x])))
    (fun t ht x ↦ (le_abs_self _).trans (hc ht x)) hγ0
    ((hcont.sub (hh.continuous.comp continuous_snd).continuousOn).congr fun p _ ↦ hv p.1 p.2)
    ⟨R + M₀, by
      rintro _ ⟨p, hp, rfl⟩
      exact (le_abs_self _).trans (hvR p hp)⟩
    ⟨-(R + M₀), by
      rintro _ ⟨p, hp, rfl⟩
      exact neg_le_of_abs_le (hvR p hp)⟩
    (fun t ht x ↦ (hcd ht x).add (hh.contDiffAt.const_smul (-1 : ℝ)))
    (fun t ht x ↦ by
      simp only [hv]
      exact (hdiff ht x).sub_const _)
    (fun t ht x ↦ by
      -- As `h` does not depend on time, `P v = P u + (∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼh + bⁱ ∂ᵢh + c h)`.
      have hderiv : deriv (fun s ↦ v s x) t = deriv (fun s ↦ u s x) t := by
        simp only [hv]
        exact deriv_sub_const _
      have hop := sum_mul_fderiv_fderiv_add_fderiv_add_smul (A := a t x) (hcd ht x) hh.contDiffAt
        (-1) (b t x)
      rw [hderiv, hop, hv, abs_le]
      have h2 := (abs_sum_mul_fderiv_fderiv_le (hΛ ht x) h x).trans
        (mul_le_mul_of_nonneg_left (hh2 x) (by positivity))
      have h1 : |fderiv ℝ h x (b t x)| ≤ M₁ * β := by
        rw [← Real.norm_eq_abs]
        exact ((fderiv ℝ h x).le_opNorm _).trans
          (mul_le_mul (hh1 x) (hb ht x) (norm_nonneg _) ((norm_nonneg _).trans (hh1 x)))
      have h0 : |c t x * h x| ≤ γ * M₀ := by
        rw [abs_mul]
        exact mul_le_mul (hc ht x) (hh0 x) (abs_nonneg _) hγ0
      obtain ⟨hP₁, hP₂⟩ := abs_le.mp (hP ht x)
      obtain ⟨h2₁, h2₂⟩ := abs_le.mp h2
      obtain ⟨h1₁, h1₂⟩ := abs_le.mp h1
      obtain ⟨h0₁, h0₂⟩ := abs_le.mp h0
      constructor <;> linarith)
    (fun x ↦ by rw [hv]; exact hw x)
  intro t ht x
  simpa only [hv] using key ht x

/-- **The approach to the initial value at the parabolic scale.** There is a constant `C ≥ 0`,
depending only on `n`, `T`, `Λ`, `β` and `γ`, with the following property. Let `a` be degenerate
elliptic with `|aⁱʲ| ≤ Λ`, `‖b‖ ≤ β` and `|c| ≤ γ` for `0 < t < T`, and let `u` be continuous and
bounded on `[0, T] × ℝⁿ`, `C²` in space and differentiable in time for `0 < t < T`, with
`|P u| ≤ F` there and `|u(·, 0)| ≤ G`. If `0 < t ≤ T` and `u(·, 0)` oscillates by at most `w` at
distances below `√t`, then `|u(t, x) - u(0, x)| ≤ C (w + t (G + F))` for every `x`. -/
theorem exists_abs_sub_le_mul_add_of_forall_dist_lt_sqrt (T Λ β γ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃a : ℝ → EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
      ⦃b : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι⦄ ⦃c : ℝ → EuclideanSpace ℝ ι → ℝ⦄
      ⦃u : ℝ → EuclideanSpace ℝ ι → ℝ⦄ ⦃G F : ℝ⦄,
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a t x).toQuadraticForm' ξ) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x i j, |a t x i j| ≤ Λ) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b t x‖ ≤ β) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |c t x| ≤ γ) →
      ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ) →
      Bornology.IsBounded (Function.uncurry u '' Icc 0 T ×ˢ univ) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |deriv (fun s ↦ u s x) t -
        (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x)| ≤ F) →
      (∀ x, |u 0 x| ≤ G) →
      ∀ ⦃t w : ℝ⦄, t ∈ Ioc 0 T → (∀ x y, dist x y < √t → |u 0 x - u 0 y| ≤ w) →
      ∀ x, |u t x - u 0 x| ≤ C * (w + t * (G + F)) := by
  obtain ⟨K, hK0, hK⟩ := exists_forall_exists_contDiff_dist_le_and_norm_iteratedFDeriv_le
    (E := EuclideanSpace ℝ ι) (F := ℝ) (μ := MeasureTheory.volume)
  set Λ' := max Λ 0
  set β' := max β 0
  set γ' := max γ 0
  set T' := max T 0
  set n : ℝ := (Fintype.card ι : ℝ)
  have hΛ' : 0 ≤ Λ' := le_max_right _ _
  have hβ' : 0 ≤ β' := le_max_right _ _
  have hγ' : 0 ≤ γ' := le_max_right _ _
  have hT' : 0 ≤ T' := le_max_right _ _
  set E := Real.exp (γ' * T')
  have hE : 0 ≤ E := (Real.exp_pos _).le
  set A := n ^ 2 * Λ' * K 2 + β' * K 1 * √T'
  have hA : 0 ≤ A := by have := hK0 1; have := hK0 2; positivity
  refine ⟨E * (2 + γ' + γ' * T' + A) + 1, by positivity, ?_⟩
  intro a b c u G F ha hΛ hb hc hcont hbdd hcd hdiff hP hG t w ht hw x
  set C := E * (2 + γ' + γ' * T' + A) + 1
  have ht0 : 0 < t := ht.1
  have htT' : t ≤ T' := ht.2.trans (le_max_left _ _)
  have hε : 0 < √t := Real.sqrt_pos.2 ht0
  have hw0 : 0 ≤ w := (abs_nonneg _).trans (hw x x (by simpa using hε))
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG x)
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hP ⟨half_pos ht0, by linarith [ht.2]⟩ x)
  -- Smooth the initial value at the parabolic scale `√t`.
  have hu0 : Continuous (u 0) := by
    simpa [Function.comp_def] using hcont.comp_continuous (continuous_const.prodMk continuous_id)
      fun y ↦ ⟨⟨le_rfl, ht0.le.trans ht.2⟩, mem_univ y⟩
  obtain ⟨h, hhc, hh⟩ := hK hε (hu0.locallyIntegrable (μ := MeasureTheory.volume))
  have hosc (y : EuclideanSpace ℝ ι) : ∀ z ∈ ball y √t, dist (u 0 z) (u 0 y) ≤ w :=
    fun z hz ↦ by rw [Real.dist_eq]; exact hw z y hz
  have h0 (y : EuclideanSpace ℝ ι) : |u 0 y - h y| ≤ w := by
    rw [abs_sub_comm, ← Real.dist_eq]; exact (hh y w (hosc y)).1
  have h1 (y : EuclideanSpace ℝ ι) : ‖fderiv ℝ h y‖ ≤ K 1 * w / √t := by
    simpa [norm_iteratedFDeriv_one] using (hh y w (hosc y)).2 1 one_ne_zero
  have h2 (y : EuclideanSpace ℝ ι) : ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ K 2 * w / t := by
    have h2eq : ‖iteratedFDeriv ℝ 2 h y‖ = ‖fderiv ℝ (fderiv ℝ h) y‖ := by
      rw [← norm_iteratedFDeriv_one (f := fderiv ℝ h), norm_iteratedFDeriv_fderiv]
    simpa [h2eq, Real.sq_sqrt ht0.le] using (hh y w (hosc y)).2 2 two_ne_zero
  have hM (y : EuclideanSpace ℝ ι) : |h y| ≤ G + w := by
    have := abs_sub_abs_le_abs_sub (h y) (u 0 y)
    rw [abs_sub_comm] at this
    linarith [h0 y, hG y]
  have key := abs_sub_le_of_abs_initial_sub_le ha
    (fun s hs y i j ↦ (hΛ hs y i j).trans (le_max_left _ _))
    (fun s hs y ↦ (hb hs y).trans (le_max_left _ _))
    (fun s hs y ↦ (hc hs y).trans (le_max_left _ _)) hΛ' hβ' hγ' hcont hbdd hcd hdiff hP
    (by simpa using contDiff_infty.mp hhc 2) hM h1 h2 h0 ⟨ht0.le, ht.2⟩ x
  -- At time `t = (√t)²` the derivative bounds contribute only multiples of `w`.
  have hinner : t * (F + n ^ 2 * Λ' * (K 2 * w / t) + β' * (K 1 * w / √t) + γ' * (G + w)) ≤
      A * w + γ' * T' * w + (1 + γ') * (t * (G + F)) := by
    have e2 : t * (K 2 * w / t) = K 2 * w := by field_simp
    have e1 : t * (K 1 * w / √t) = K 1 * w * √t :=
      calc t * (K 1 * w / √t) = √t * √t * (K 1 * w / √t) := by rw [Real.mul_self_sqrt ht0.le]
        _ = K 1 * w * √t := by field_simp
    have hs : K 1 * w * √t ≤ K 1 * w * √T' := by
      have := hK0 1; gcongr
    have hγt : γ' * t * w ≤ γ' * T' * w := by gcongr
    have hγG : γ' * t * G ≤ γ' * (t * (G + F)) := by nlinarith [mul_nonneg ht0.le hF0]
    calc _ = t * F + n ^ 2 * Λ' * (t * (K 2 * w / t)) + β' * (t * (K 1 * w / √t)) +
          γ' * t * G + γ' * t * w := by ring
      _ ≤ t * F + n ^ 2 * Λ' * (K 2 * w) + β' * (K 1 * w * √T') + γ' * (t * (G + F)) +
          γ' * T' * w := by
        rw [e2, e1]; gcongr
      _ ≤ _ := by
        simp only [A]
        nlinarith [mul_nonneg ht0.le hG0]
  have hexp : Real.exp (γ' * t) ≤ E := Real.exp_le_exp.mpr (by gcongr)
  have htGF : 0 ≤ t * (G + F) := by positivity
  have htri : |u t x - u 0 x| ≤ |u t x - h x| + |u 0 x - h x| := by
    have := abs_sub_le (u t x) (h x) (u 0 x)
    rwa [abs_sub_comm (h x)] at this
  calc |u t x - u 0 x| ≤ |u t x - h x| + |u 0 x - h x| := htri
    _ ≤ E * (w + (A * w + γ' * T' * w + (1 + γ') * (t * (G + F)))) + w := by
        refine add_le_add ?_ (h0 x)
        refine key.trans (mul_le_mul hexp (add_le_add le_rfl hinner) ?_ hE)
        have := hK0 1; have := hK0 2
        positivity
    _ = (E * (1 + γ' * T' + A) + 1) * w + E * (1 + γ') * (t * (G + F)) := by ring
    _ ≤ C * w + C * (t * (G + F)) := by
        gcongr ?_ * _ + ?_ * _
        · nlinarith
        · nlinarith [mul_nonneg hE (add_nonneg (mul_nonneg hγ' hT') hA)]
    _ = _ := by ring

/-- **The approach to the initial value, with a modulus of continuity.** There is a constant
`C ≥ 0`, depending only on `n`, `T`, `Λ`, `β` and `γ`, with the following property. Let `a` be
degenerate elliptic with `|aⁱʲ| ≤ Λ`, `‖b‖ ≤ β` and `|c| ≤ γ` for `0 < t < T`, and let `u` be
continuous and bounded on `[0, T] × ℝⁿ`, `C²` in space and differentiable in time for
`0 < t < T`, with `|P u| ≤ F` there and `|u(·, 0)| ≤ G`. If `ω` is nondecreasing on `[0, ∞)` and
`|u(0, x) - u(0, y)| ≤ ω(‖x - y‖)`, then `|u(t, x) - u(0, x)| ≤ C (ω(√t) + t (G + F))` on
`[0, T] × ℝⁿ`. -/
theorem exists_abs_sub_le_mul_add_of_abs_sub_le_comp_dist (T Λ β γ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃a : ℝ → EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
      ⦃b : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι⦄ ⦃c : ℝ → EuclideanSpace ℝ ι → ℝ⦄
      ⦃u : ℝ → EuclideanSpace ℝ ι → ℝ⦄ ⦃G F : ℝ⦄ ⦃ω : ℝ → ℝ⦄,
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a t x).toQuadraticForm' ξ) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x i j, |a t x i j| ≤ Λ) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b t x‖ ≤ β) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |c t x| ≤ γ) →
      ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ) →
      Bornology.IsBounded (Function.uncurry u '' Icc 0 T ×ˢ univ) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |deriv (fun s ↦ u s x) t -
        (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x)| ≤ F) →
      (∀ x, |u 0 x| ≤ G) → (∀ x y, |u 0 x - u 0 y| ≤ ω (dist x y)) → MonotoneOn ω (Ici 0) →
      ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, |u t x - u 0 x| ≤ C * (ω √t + t * (G + F)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_sub_le_mul_add_of_forall_dist_lt_sqrt (ι := ι) T Λ β γ
  refine ⟨C, hC0, fun a b c u G F ω ha hΛ hb hc hcont hbdd hcd hdiff hP hG hω hωm t ht x ↦ ?_⟩
  rcases ht.1.eq_or_lt with rfl | ht0
  · have hω0 : 0 ≤ ω 0 := by simpa using hω x x
    simpa using mul_nonneg hC0 hω0
  refine hC ha hΛ hb hc hcont hbdd hcd hdiff hP hG ⟨ht0, ht.2⟩ (fun y z hyz ↦ ?_) x
  exact (hω y z).trans (hωm dist_nonneg (Real.sqrt_nonneg t) hyz.le)

/-- **Uniform attainment of equicontinuous initial values.** Let `a` be degenerate elliptic with
`|aⁱʲ| ≤ Λ`, `‖b‖ ≤ β` and `|c| ≤ γ` for `0 < t < T`, and let `uᵢ` be a family of functions,
each continuous and bounded on `[0, T] × ℝⁿ`, `C²` in space and differentiable in time for
`0 < t < T`, with `|P uᵢ| ≤ F` there and `|uᵢ(·, 0)| ≤ G`. If the initial values `uᵢ(·, 0)` are
uniformly equicontinuous, then `uᵢ(·, t) → uᵢ(·, 0)` as `t → 0` within `[0, T]`, uniformly in
both `i` and the spatial variable. -/
theorem tendstoUniformly_nhdsWithin_zero_of_uniformEquicontinuous {κ : Type*}
    {u : κ → ℝ → EuclideanSpace ℝ ι → ℝ} {G : ℝ}
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a t x).toQuadraticForm' ξ)
    (hΛ : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x i j, |a t x i j| ≤ Λ)
    (hb : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b t x‖ ≤ β)
    (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |c t x| ≤ γ)
    (hcont : ∀ k, ContinuousOn (Function.uncurry (u k)) (Icc 0 T ×ˢ univ))
    (hbdd : ∀ k, Bornology.IsBounded (Function.uncurry (u k) '' Icc 0 T ×ˢ univ))
    (hcd : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u k t) x)
    (hdiff : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u k s x) t)
    (hP : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |deriv (fun s ↦ u k s x) t -
      (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u k t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u k t) x (b t x) + c t x * u k t x)| ≤ F)
    (hG : ∀ k x, |u k 0 x| ≤ G) (hequi : UniformEquicontinuous fun k ↦ u k 0) :
    TendstoUniformly (fun t (p : κ × EuclideanSpace ℝ ι) ↦ u p.1 t p.2)
      (fun p ↦ u p.1 0 p.2) (𝓝[Icc 0 T] 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_sub_le_mul_add_of_forall_dist_lt_sqrt (ι := ι) T Λ β γ
  rw [Metric.tendstoUniformly_iff]
  intro η hη
  -- Choose the oscillation `w` with `C w < η / 2`, then `t` so small that `√t` is below the
  -- equicontinuity radius for `w` and `C t (G + F) < η / 2`.
  set w := η / (2 * (C + 1))
  have hw : 0 < w := by positivity
  obtain ⟨r, hr, hr'⟩ := Metric.uniformEquicontinuous_iff.mp hequi w hw
  set δ := min (r ^ 2) (η / (2 * (C * (|G| + |F|) + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds hδ)] with t ht htδ
  rintro ⟨k, x⟩
  rw [Real.dist_eq, abs_sub_comm]
  rcases ht.1.eq_or_lt with rfl | ht0
  · simpa using hη
  have hsqrt : √t < r := by
    rw [show r = √(r ^ 2) by rw [Real.sqrt_sq hr.le]]
    exact Real.sqrt_lt_sqrt ht0.le (htδ.trans_le (min_le_left _ _))
  have hest := hC ha hΛ hb hc (hcont k) (hbdd k) (hcd k) (hdiff k) (hP k) (hG k) ⟨ht0, ht.2⟩
    (fun y z hyz ↦ by simpa [Real.dist_eq] using (hr' y z (hyz.trans hsqrt) k).le) x
  have htη : t * (C * (|G| + |F|) + 1) < η / 2 := by
    have := htδ.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have hCw : C * w < η / 2 := by
    simp only [w]
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith
  have hGF : C * (t * (G + F)) ≤ t * (C * (|G| + |F|)) := by
    have : G + F ≤ |G| + |F| := add_le_add (le_abs_self G) (le_abs_self F)
    nlinarith [mul_nonneg hC0 ht0.le]
  nlinarith

end PDE

end TauCeti

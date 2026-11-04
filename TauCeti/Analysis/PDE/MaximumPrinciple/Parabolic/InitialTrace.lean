/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.WholeSpace
public import Mathlib.Topology.UniformSpace.UniformConvergence
import TauCeti.Analysis.Calculus.BumpFunction.Oscillation
import TauCeti.Analysis.Matrix.Contraction

/-!
# Uniform attainment of the initial data by a modulus of continuity

On the slab `Q = [0, T] × ℝⁿ`, with `ℝⁿ = EuclideanSpace ℝ ι`, consider the parabolic operator

`P u = ∂ₜu - ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

with coefficients that, for `0 < t < T`, satisfy `0 ≤ ξᵀ a(t, x) ξ`, `|aⁱʲ(t, x)| ≤ Λ`,
`‖b(t, x)‖ ≤ β` and `|c(t, x)| ≤ γ`. No regularity of the coefficients is needed. This file proves
that a bounded classical solution approaches its initial data `g = u(0, ·)` at a rate governed by
a modulus of continuity `ω` of `g` alone: there is a constant `C`, depending only on `ι`, `T`, `Λ`,
`β` and `γ`, such that

`|u(t, x) - g(x)| ≤ C (ω(√t) + t (sup |g| + sup |P u|))`

for `0 < t ≤ T`. Here `ω` is nondecreasing on `[0, ∞)` and `|g(x) - g(y)| ≤ ω(‖x - y‖)`. Since `C`
does not depend on the solution, a family of solutions whose data share one modulus `ω` with
`ω(r) → 0` as `r → 0⁺`, and whose data and forcing are uniformly bounded, attains its initial
data uniformly over the whole family. This is the estimate behind the construction of solutions
with bounded uniformly continuous initial data as limits of solutions with smooth data.

## The argument

Mollify `g` at scale `ε = √t₀`: this gives a smooth `h` with `|h - g| ≤ ω(ε)`,
`‖Dh‖ ≤ C₀ ω(ε) / ε` and `‖D²h‖ ≤ C₀ ω(ε) / ε²`
(`TauCeti.exists_contDiff_norm_sub_le_and_norm_fderiv_le`). The difference `v = u - h` is a
classical solution of `P v = P u + ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼh + bⁱ ∂ᵢh + c h`, whose right side is at most
`sup |P u| + C (ω(ε) / ε² + ω(ε) / ε + sup |g| + ω(ε))`, and `|v(0, ·)| ≤ ω(ε)`. The two-sided a
priori bound of the comparison principle on `[0, t₀] × ℝⁿ`
(`abs_le_exp_mul_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le`)
gives `|v(t₀, ·)| ≤ exp (|γ| t₀) (ω(ε) + t₀ sup |P v|)`, and `t₀ / ε² = 1` turns the size
`ω(ε) / ε²` of `P h` into `ω(ε)`.

## Main declarations

All declarations are in the `TauCeti.PDE` namespace.

* `abs_sub_le_exp_mul_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le`:
  a classical solution stays close to a time-independent `C²` function `h` that is close to its
  initial data, with an explicit bound in terms of the first two derivatives of `h`.
* `exists_abs_sub_le_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le`:
  **the modulus estimate** `|u(t, ·) - g| ≤ C (ω(√t) + t (sup |g| + sup |P u|))`.
* `tendstoUniformly_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le`: a family of
  solutions with a common modulus attains its initial data uniformly.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004),
  Chapter 4 (the Cauchy problem with uniformly continuous initial data).
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2, Section 4
  (the maximum principle on the whole space).
-/

public section

noncomputable section

open Set Filter Function Topology Matrix

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {a : ℝ → EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : ℝ → EuclideanSpace ℝ ι → ℝ}
  {u : ℝ → EuclideanSpace ℝ ι → ℝ} {T Lam β γ : ℝ}

/-- **Comparison of a solution with a time-independent function.** Let the coefficients satisfy,
for `0 < t < T`, `0 ≤ ξᵀ a(t, x) ξ`, `|aⁱʲ(t, x)| ≤ Λ`, `‖b(t, x)‖ ≤ β` and `|c(t, x)| ≤ γ`. Let
`u` be continuous and bounded on `[0, T] × ℝⁿ`, `C²` in space and differentiable in time for
`0 < t < T`, with `|P u| ≤ F` there. Let `h` be a `C²` function with `|h| ≤ N`, `‖Dh‖ ≤ D₁`,
`‖D²h‖ ≤ D₂` and `|u(0, ·) - h| ≤ w`. Then for `0 < t₀ ≤ T`,

`|u(t₀, x) - h(x)| ≤ exp (|γ| t₀) (w + t₀ (F + (card ι)² Λ D₂ + β D₁ + |γ| N))`. -/
theorem abs_sub_le_exp_mul_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le
    (ha : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a t x).toQuadraticForm' ξ)
    (haLam : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x i j, |a t x i j| ≤ Lam)
    (hb : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b t x‖ ≤ β)
    (hc : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |c t x| ≤ γ) {F : ℝ}
    (hcont : ContinuousOn (uncurry u) (Icc 0 T ×ˢ univ))
    (hbdd : Bornology.IsBounded (uncurry u '' Icc 0 T ×ˢ univ))
    (hcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x)
    (hdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hP : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |deriv (fun s ↦ u s x) t -
      (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x)| ≤ F)
    {h : EuclideanSpace ℝ ι → ℝ} {N D₁ D₂ w : ℝ} (hh : ContDiff ℝ 2 h) (hhN : ∀ x, |h x| ≤ N)
    (hD₁ : ∀ x, ‖fderiv ℝ h x‖ ≤ D₁) (hD₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ D₂)
    (hw : ∀ x, |u 0 x - h x| ≤ w) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioc 0 T) (x : EuclideanSpace ℝ ι) :
    |u t₀ x - h x| ≤
      Real.exp (|γ| * t₀) * (w + t₀ * (F + Fintype.card ι ^ 2 * Lam * D₂ + β * D₁ + |γ| * N)) := by
  have hsub : Ioo 0 t₀ ⊆ Ioo 0 T := Ioo_subset_Ioo_right ht₀.2
  -- `v = u - h`, written so that the linearity of the spatial operator applies directly.
  set v : ℝ → EuclideanSpace ℝ ι → ℝ := fun t ↦ u t + (-1 : ℝ) • h
  have hv : ∀ t y, v t y = u t y - h y := fun t y ↦ by
    simp only [v, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcd' : ∀ ⦃t⦄, t ∈ Ioo 0 t₀ → ∀ y, ContDiffAt ℝ 2 (v t) y := fun t ht y ↦
    (hcd (hsub ht) y).add (hh.contDiffAt.const_smul (-1 : ℝ))
  have hdiff' : ∀ ⦃t⦄, t ∈ Ioo 0 t₀ → ∀ y, DifferentiableAt ℝ (fun s ↦ v s y) t := fun t ht y ↦ by
    simp only [hv]
    exact (hdiff (hsub ht) y).sub_const _
  -- `v` is bounded because `u` and `h` are.
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hbdd
  have hvR : ∀ t ∈ Icc 0 t₀, ∀ y, |v t y| ≤ R + N := fun t ht y ↦ by
    have hu := hR _ ⟨(t, y), ⟨⟨ht.1, ht.2.trans ht₀.2⟩, mem_univ y⟩, rfl⟩
    rw [Real.norm_eq_abs, uncurry_apply_pair] at hu
    rw [hv]
    linarith [abs_sub (u t y) (h y), hhN y]
  have hvbdd : Bornology.IsBounded (uncurry v '' Icc 0 t₀ ×ˢ univ) := by
    refine isBounded_iff_forall_norm_le.2 ⟨R + N, ?_⟩
    rintro _ ⟨⟨t, y⟩, ⟨ht, -⟩, rfl⟩
    exact hvR t ht y
  rw [isBounded_iff_bddBelow_bddAbove] at hvbdd
  have hvcont : ContinuousOn (uncurry v) (Icc 0 t₀ ×ˢ univ) := by
    refine ContinuousOn.congr ?_ fun p _ ↦ hv p.1 p.2
    exact (hcont.mono (prod_mono (Icc_subset_Icc_right ht₀.2) subset_rfl)).sub
      (hh.continuous.comp continuous_snd).continuousOn
  have : 0 ≤ D₂ := (ContinuousLinearMap.opNorm_nonneg _).trans (hD₂ 0)
  have hD₁0 : 0 ≤ D₁ := (norm_nonneg _).trans (hD₁ 0)
  -- The equation for `v`, with the forcing enlarged by the size of `P h`.
  have hPv : ∀ ⦃t⦄, t ∈ Ioo 0 t₀ → ∀ y, |deriv (fun s ↦ v s y) t -
      (∑ i, ∑ j, a t y i j * fderiv ℝ (fderiv ℝ (v t)) y (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (v t) y (b t y) + c t y * v t y)| ≤
      F + Fintype.card ι ^ 2 * Lam * D₂ + β * D₁ + |γ| * N := fun t ht y ↦ by
    have htT := hsub ht
    have hderiv : deriv (fun s ↦ v s y) t = deriv (fun s ↦ u s y) t := by
      simp only [hv]
      exact deriv_sub_const (h y)
    rw [hderiv, sum_mul_fderiv_fderiv_add_fderiv_add_smul (hcd htT y) hh.contDiffAt, hv]
    have h2 := Matrix.abs_sum_sum_mul_apply_single_single_le (haLam htT y)
      (fderiv ℝ (fderiv ℝ h) y)
    have h1 : |fderiv ℝ h y (b t y)| ≤ D₁ * β := by
      simpa only [Real.norm_eq_abs] using
        (fderiv ℝ h y).le_of_opNorm_le (hD₁ y) (b t y) |>.trans
          (mul_le_mul_of_nonneg_left (hb htT y) hD₁0)
    have h0 : |c t y * h y| ≤ |γ| * N := by
      rw [abs_mul]
      exact mul_le_mul ((hc htT y).trans (le_abs_self γ)) (hhN y) (abs_nonneg _) (abs_nonneg _)
    have hLam : Fintype.card ι ^ 2 * Lam * ‖fderiv ℝ (fderiv ℝ h) y‖ ≤
        Fintype.card ι ^ 2 * Lam * D₂ := by
      have hLam0 : 0 ≤ Fintype.card ι ^ 2 * Lam := by
        rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
        · simp
        · exact mul_nonneg (by positivity) ((abs_nonneg _).trans (haLam htT y i i))
      exact mul_le_mul_of_nonneg_left (hD₂ y) hLam0
    have hPu := hP htT y
    rw [abs_le] at h2 h1 h0 hPu ⊢
    constructor <;> nlinarith
  have hb' : ∀ ⦃t⦄, t ∈ Ioo 0 t₀ → ∀ y, ‖b t y‖ ≤ |β| * (1 + ‖y‖) := fun t ht y ↦
    (hb (hsub ht) y).trans ((le_abs_self β).trans (le_mul_of_one_le_right (abs_nonneg β)
      (le_add_of_nonneg_right (norm_nonneg y))))
  have htr : ∀ ⦃t⦄, t ∈ Ioo 0 t₀ → ∀ y,
      (a t y).trace ≤ (Fintype.card ι * |Lam|) * (1 + ‖y‖ ^ 2) := fun t ht y ↦ by
    have htrace : (a t y).trace ≤ Fintype.card ι * |Lam| := by
      rw [Matrix.trace]
      refine (Finset.sum_le_sum fun i _ ↦ (le_abs_self _).trans
        ((haLam (hsub ht) y i i).trans (le_abs_self Lam))).trans_eq ?_
      simp
    exact htrace.trans (le_mul_of_one_le_right (by positivity)
      (le_add_of_nonneg_right (by positivity)))
  have hbound :=
    abs_le_exp_mul_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le
    (T := t₀) (u := v) (γ := |γ|) (fun t ht ↦ ha (hsub ht)) htr hb'
    (fun t ht y ↦ (le_abs_self _).trans ((hc (hsub ht) y).trans (le_abs_self γ)))
    (abs_nonneg γ) hvcont hvbdd.2
    hvbdd.1 hcd' hdiff' hPv (fun y ↦ by rw [hv]; exact hw y) ⟨ht₀.1.le, le_rfl⟩ x
  rwa [hv] at hbound

/-- **Uniform attainment of the initial data by a modulus of continuity.** There is a constant
`C`, depending only on `ι`, `T`, `Λ`, `β` and `γ`, with the following property. Let the
coefficients satisfy, for `0 < t < T`, `0 ≤ ξᵀ a(t, x) ξ`, `|aⁱʲ(t, x)| ≤ Λ`, `‖b(t, x)‖ ≤ β` and
`|c(t, x)| ≤ γ`. Let `u` be continuous and bounded on `[0, T] × ℝⁿ`, `C²` in space and
differentiable in time for `0 < t < T`, with `|P u| ≤ F` there and `|u(0, ·)| ≤ M`. Let `ω` be
nondecreasing on `[0, ∞)` with `|u(0, x) - u(0, y)| ≤ ω(‖x - y‖)`. Then for `0 < t ≤ T`,

`|u(t, x) - u(0, x)| ≤ C (ω(√t) + t (M + F))`. -/
theorem exists_abs_sub_le_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le
    (T Lam β γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ → EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {b : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : ℝ → EuclideanSpace ℝ ι → ℝ}
      {u : ℝ → EuclideanSpace ℝ ι → ℝ} {ω : ℝ → ℝ} {M F : ℝ},
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a t x).toQuadraticForm' ξ) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x i j, |a t x i j| ≤ Lam) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b t x‖ ≤ β) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |c t x| ≤ γ) →
      ContinuousOn (uncurry u) (Icc 0 T ×ˢ univ) →
      Bornology.IsBounded (uncurry u '' Icc 0 T ×ˢ univ) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |deriv (fun s ↦ u s x) t -
        (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x)| ≤ F) →
      (∀ x, |u 0 x| ≤ M) → MonotoneOn ω (Ici 0) →
      (∀ x y, |u 0 x - u 0 y| ≤ ω (dist x y)) →
      ∀ ⦃t⦄, t ∈ Ioc 0 T → ∀ x, |u t x - u 0 x| ≤ C * (ω (√t) + t * (M + F)) := by
  obtain ⟨C₀, hC₀, hmoll⟩ :=
    exists_contDiff_norm_sub_le_and_norm_fderiv_le (E := EuclideanSpace ℝ ι) (F := ℝ)
  set K : ℝ := Fintype.card ι ^ 2 * |Lam| * C₀ + |β| * C₀ * √T + |γ| * |T|
  have hK : 0 ≤ K := by positivity
  set C : ℝ := Real.exp (|γ| * T) * (2 + K + |γ|) + 1
  refine ⟨C, by positivity, fun {a b c u ω M F} ha haLam hb hc hcont hbdd hcd hdiff hP hM hωm hω
    t₀ ht₀ x ↦ ?_⟩
  -- Mollify the initial data at scale `√t₀`.
  set ε := √t₀
  have hε : 0 < ε := Real.sqrt_pos.2 ht₀.1
  have hεsq : ε ^ 2 = t₀ := Real.sq_sqrt ht₀.1.le
  set w := ω ε
  have hosc : ∀ x y, dist x y < ε → ‖u 0 x - u 0 y‖ ≤ w := fun x y hxy ↦
    (hω x y).trans (hωm dist_nonneg hε.le hxy.le)
  have hw0 : 0 ≤ w := by simpa using hosc 0 0 (by simpa using hε)
  have hu0 : Continuous (u 0) := by
    have := hcont.comp_continuous (Continuous.prodMk_right (0 : ℝ))
      fun y ↦ ⟨⟨le_rfl, ht₀.1.le.trans ht₀.2⟩, mem_univ y⟩
    simpa [Function.comp_def] using this
  obtain ⟨h, hh, hhg, hD₁, hD₂⟩ := hmoll hε (u 0) w hu0 hosc
  simp only [Real.norm_eq_abs] at hhg
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hF0 : 0 ≤ F := (abs_nonneg _).trans
    (hP ⟨half_pos ht₀.1, by linarith [ht₀.2, ht₀.1]⟩ 0)
  -- Compare `u` with `h` on `[0, t₀]`.
  have hcmp :=
    abs_sub_le_exp_mul_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le
    (N := M + w) ha haLam hb hc hcont hbdd hcd hdiff hP (hh.of_le (by simp))
    (fun y ↦ by linarith [abs_sub_abs_le_abs_sub (h y) (u 0 y), hhg y, hM y])
    hD₁ hD₂ (fun y ↦ by rw [abs_sub_comm]; exact hhg y) ht₀ x
  -- Absorb the powers of `ε` into `t₀ = ε²`.
  have hLam0 : Fintype.card ι ^ 2 * Lam ≤ Fintype.card ι ^ 2 * |Lam| :=
    mul_le_mul_of_nonneg_left (le_abs_self Lam) (by positivity)
  have hT : t₀ ≤ T := ht₀.2
  have hsqrt : ε ≤ √T := Real.sqrt_le_sqrt hT
  have hexp : Real.exp (|γ| * t₀) ≤ Real.exp (|γ| * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT (abs_nonneg γ))
  have h2 : t₀ * (Fintype.card ι ^ 2 * Lam * (C₀ * w / ε ^ 2)) ≤
      Fintype.card ι ^ 2 * |Lam| * C₀ * w := by
    have : t₀ * (Fintype.card ι ^ 2 * Lam * (C₀ * w / ε ^ 2)) =
        Fintype.card ι ^ 2 * Lam * (C₀ * w) := by
      rw [hεsq]
      field_simp [ht₀.1.ne']
    rw [this, mul_assoc _ C₀]
    exact mul_le_mul_of_nonneg_right hLam0 (mul_nonneg hC₀ hw0)
  have h1 : t₀ * (β * (C₀ * w / ε)) ≤ |β| * C₀ * √T * w := by
    have : t₀ * (β * (C₀ * w / ε)) = ε * β * C₀ * w := by
      rw [← hεsq]
      field_simp
    rw [this]
    have hβ : ε * β ≤ √T * |β| :=
      (mul_le_mul_of_nonneg_left (le_abs_self β) hε.le).trans
        (mul_le_mul_of_nonneg_right hsqrt (abs_nonneg β))
    nlinarith [mul_nonneg hC₀ hw0]
  have h0 : t₀ * (|γ| * (M + w)) ≤ |γ| * |T| * w + |γ| * (t₀ * (M + F)) := by
    have htT : t₀ ≤ |T| := hT.trans (le_abs_self T)
    nlinarith [mul_le_mul_of_nonneg_left htT (mul_nonneg (abs_nonneg γ) hw0),
      mul_nonneg (mul_nonneg (abs_nonneg γ) ht₀.1.le) hF0]
  have hinner : w + t₀ * (F + Fintype.card ι ^ 2 * Lam * (C₀ * w / ε ^ 2) + β * (C₀ * w / ε) +
      |γ| * (M + w)) ≤ (1 + K) * w + (1 + |γ|) * (t₀ * (M + F)) := by
    simp only [K]
    nlinarith [mul_nonneg ht₀.1.le hM0]
  have hinner0 : 0 ≤ (1 + K) * w + (1 + |γ|) * (t₀ * (M + F)) := by
    have := ht₀.1.le
    positivity
  calc |u t₀ x - u 0 x| ≤ |u t₀ x - h x| + |h x - u 0 x| := abs_sub_le _ _ _
    _ ≤ Real.exp (|γ| * T) * ((1 + K) * w + (1 + |γ|) * (t₀ * (M + F))) + w := by
      gcongr
      · exact hcmp.trans ((mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le).trans
          (mul_le_mul_of_nonneg_right hexp hinner0))
      · exact hhg x
    _ ≤ C * (w + t₀ * (M + F)) := by
      have hE := Real.exp_pos (|γ| * T)
      have htMF : 0 ≤ t₀ * (M + F) := mul_nonneg ht₀.1.le (add_nonneg hM0 hF0)
      simp only [C]
      nlinarith [mul_nonneg hE.le hw0, mul_nonneg hE.le htMF, mul_nonneg hE.le hK,
        mul_nonneg (mul_nonneg hE.le hK) hw0, mul_nonneg (mul_nonneg hE.le (abs_nonneg γ)) htMF,
        mul_nonneg (mul_nonneg hE.le (abs_nonneg γ)) hw0]

/-- **A family of solutions attains its initial data uniformly.** Let `u k`, for `k : κ`, be
classical solutions on `[0, T] × ℝⁿ`, `0 < T`, as in
`exists_abs_sub_le_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le`, with
coefficients `a k`, `b k`, `c k` obeying common bounds `Λ`, `β`, `γ`, with `|P (u k)| ≤ F` and
`|u k (0, ·)| ≤ M`. If the initial data share a modulus of continuity `ω`, nondecreasing on
`[0, ∞)` with `ω(r) → 0` as `r → 0⁺`, then `u k (t, x) → u k (0, x)` as `t → 0⁺`, uniformly in
`k` and `x`. -/
theorem tendstoUniformly_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le
    {κ : Type*} {a : κ → ℝ → EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : κ → ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : κ → ℝ → EuclideanSpace ℝ ι → ℝ}
    {u : κ → ℝ → EuclideanSpace ℝ ι → ℝ} {ω : ℝ → ℝ} {M F : ℝ} (hT : 0 < T)
    (ha : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a k t x).toQuadraticForm' ξ)
    (haLam : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x i j, |a k t x i j| ≤ Lam)
    (hb : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b k t x‖ ≤ β)
    (hc : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |c k t x| ≤ γ)
    (hcont : ∀ k, ContinuousOn (uncurry (u k)) (Icc 0 T ×ˢ univ))
    (hbdd : ∀ k, Bornology.IsBounded (uncurry (u k) '' Icc 0 T ×ˢ univ))
    (hcd : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u k t) x)
    (hdiff : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u k s x) t)
    (hP : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |deriv (fun s ↦ u k s x) t -
      (∑ i, ∑ j, a k t x i j * fderiv ℝ (fderiv ℝ (u k t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u k t) x (b k t x) + c k t x * u k t x)| ≤ F)
    (hM : ∀ k x, |u k 0 x| ≤ M) (hωm : MonotoneOn ω (Ici 0))
    (hω : ∀ k x y, |u k 0 x - u k 0 y| ≤ ω (dist x y)) (hω0 : Tendsto ω (𝓝[>] 0) (𝓝 0)) :
    TendstoUniformly (fun t (q : κ × EuclideanSpace ℝ ι) ↦ u q.1 t q.2)
      (fun q ↦ u q.1 0 q.2) (𝓝[>] 0) := by
  obtain ⟨C, _, hest⟩ :=
    exists_abs_sub_le_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le
      (ι := ι) T Lam β γ
  -- The bound `C (ω(√t) + t (M + F))` tends to zero as `t → 0⁺`.
  have hsqrt : Tendsto (fun t : ℝ ↦ √t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht ↦
      Real.sqrt_pos.2 ht⟩
    simpa using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun t : ℝ ↦ C * (ω (√t) + t * (M + F))) (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using ((hω0.comp hsqrt).add (ht.mul_const (M + F))).const_mul C
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  filter_upwards [hlim.eventually (gt_mem_nhds hδ), Ioo_mem_nhdsGT hT] with t ht htT
  rintro ⟨k, x⟩
  rw [Real.dist_eq, abs_sub_comm]
  exact (hest (ha k) (haLam k) (hb k) (hc k) (hcont k) (hbdd k) (hcd k) (hdiff k) (hP k) (hM k) hωm
    (hω k) ⟨htT.1, htT.2.le⟩ x).trans_lt ht

end PDE

end TauCeti

end

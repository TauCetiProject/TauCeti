/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Divergence
public import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Algebra.Module.LinearMap.DivisionRing
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Normed.Module.LipschitzHyperplane

/-!
# Test vector fields vanishing normally on a hyperplane

A test vector field whose normal component `f ∘ χ` vanishes on a hyperplane `{f = a}` has normal
component `O (|f - a|)`: `StrongDual.exists_abs_apply_le_mul_abs_sub`.

Given a hyperplane `{f = c}`, a test vector field `φ` extends its normal component off the
hyperplane in a fixed direction `w` with `f w = 1`, by a smooth cutoff
(`StrongDual.exists_coe_eq_cutoff_normal_field`); the extension is divergence-free above the
hyperplane up to the cutoff (`StrongDual.divergenceCLM_cutoff_normal_field`). Two admissible test
vector fields are interpolated across the hyperplane by the smooth transition
(`StrongDual.exists_interpolation_divergence`), with an error term which is uniformly bounded when
the normal component of their difference vanishes on the hyperplane
(`StrongDual.exists_abs_deriv_smoothTransition_mul_le_indicator`).
-/

public section

open Filter Set TauCeti TopologicalSpace TestFunction
open scoped Distributions Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A test vector field whose normal component `f ∘ χ` vanishes on the hyperplane `{f = a}` has
normal component `O (|f - a|)`. -/
theorem StrongDual.exists_abs_apply_le_mul_abs_sub (f : StrongDual ℝ E) (a : ℝ) {Ω : Opens E}
    {χ : 𝓓(Ω, E)} (hχ : ∀ x, f x = a → f (χ x) = 0) : ∃ C, ∀ x, |f (χ x)| ≤ C * |f x - a| := by
  by_cases hf : f = 0
  · exact ⟨0, fun x => by simp [hf]⟩
  obtain ⟨v, hv⟩ : ∃ v, f v = 1 :=
    LinearMap.surjective_iff_ne_zero.mpr (fun h => hf (ContinuousLinearMap.coe_injective
      (by simpa using h))) 1
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (χ.hasCompactSupport.comp_left (g := f) f.map_zero)
    (f.contDiff.comp (χ.contDiff.of_le (by simp))) one_ne_zero
  exact ⟨L * ‖v‖, fun x => by
    simpa using hL.norm_le_mul_abs_sub_of_eq_zero (f := f) hv hχ x⟩

/-- The cutoff field `x ↦ η (f x) · f (φ (x - (f x - c) • w)) • w` used to extend the normal
component of `φ` off the hyperplane `{f = c}` is a test vector field, where `w` is any vector
and `η` is a smooth cutoff equal to one on `[c, c + n]`. -/
theorem StrongDual.exists_coe_eq_cutoff_normal_field
    (f : StrongDual ℝ E) (c : ℝ) (w : E)
    (φ : 𝓓(⊤, E)) (n : ℕ) : ∃ ψ : 𝓓(⊤, E), ⇑ψ = fun x =>
      ((Real.smoothTransition (f x - c + 1) * (1 - Real.smoothTransition (f x - (c + n)))) *
        f (φ (x - (f x - c) • w))) • w := by
  refine ⟨⟨_, ContDiff.smul (by have := φ.contDiff; fun_prop) contDiff_const,
    HasCompactSupport.intro
      ((φ.hasCompactSupport.isCompact.prod (isCompact_Icc (a := (-1 : ℝ)) (b := n + 1))).image
        (f := fun p : E × ℝ => p.1 + p.2 • w) (by fun_prop)) fun x hx => ?_, by simp⟩, rfl⟩
  by_contra h
  refine hx ⟨(x - (f x - c) • w, f x - c), ⟨subset_tsupport _ fun h' => h ?_, ?_⟩, by simp⟩
  · simp [h']
  have h₁ : Real.smoothTransition (f x - c + 1) ≠ 0 := fun h' => h (by simp [h'])
  have h₂ : Real.smoothTransition (f x - (c + n)) ≠ 1 := fun h' => h (by simp [h'])
  rw [Ne, Real.smoothTransition.zero_iff_nonpos] at h₁
  rw [Ne, Real.smoothTransition.eq_one_iff_one_le] at h₂
  constructor <;> linarith


variable [FiniteDimensional ℝ E] in
/-- Above the hyperplane `{f = c}`, the divergence of the cutoff field of
`StrongDual.exists_coe_eq_cutoff_normal_field` only sees the upper cutoff. -/
theorem StrongDual.divergenceCLM_cutoff_normal_field
    (f : StrongDual ℝ E) (c : ℝ) {w : E}
    (hw : f w = 1) (φ : 𝓓(⊤, E)) (n : ℕ) {ψ : 𝓓(⊤, E)} (hψ : ⇑ψ = fun x =>
      ((Real.smoothTransition (f x - c + 1) * (1 - Real.smoothTransition (f x - (c + n)))) *
        f (φ (x - (f x - c) • w))) • w) {x : E} (hx : c < f x) :
    divergenceCLM ψ x =
      -(deriv Real.smoothTransition (f x - (c + n)) * f (φ (x - (f x - c) • w))) := by
  have hP (t : ℝ) : x + t • w - (f (x + t • w) - c) • w = x - (f x - c) • w := by
    simp only [map_add, map_smul, hw, smul_eq_mul, mul_one]
    module
  set h : E → ℝ := fun y => (1 - Real.smoothTransition (f y - (c + n))) *
    f (φ (y - (f y - c) • w))
  have hloc : (ψ : E → E) =ᶠ[𝓝 x] fun y => h y • w := by
    filter_upwards [(isOpen_lt continuous_const f.continuous).mem_nhds hx] with y hy
    have hcut : 1 ≤ f y - c + 1 := by have : c < f y := hy; linarith
    simp [hψ, h, Real.smoothTransition.one_of_one_le hcut]
  have hhd : DifferentiableAt ℝ h x := by
    have := φ.contDiff.differentiable (by simp)
    fun_prop
  have hline : (fun t : ℝ => h (x + t • w)) =
      fun t => (1 - Real.smoothTransition (f x + t - (c + n))) *
        f (φ (x - (f x - c) • w)) := by
    ext t
    simp only [h, hP]
    simp [hw]
  have hd : HasDerivAt (fun t : ℝ => (1 - Real.smoothTransition (f x + t - (c + n))) *
      f (φ (x - (f x - c) • w)))
      (-(deriv Real.smoothTransition (f x - (c + n)) * f (φ (x - (f x - c) • w)))) 0 := by
    have := (((((hasDerivAt_id (0 : ℝ)).const_add (f x)).sub_const (c + n)).smoothTransition
      ).const_sub 1).mul_const (f (φ (x - (f x - c) • w)))
    simpa using this
  rw [divergenceCLM_apply, hloc.fderiv_eq, trace_fderiv_smul_const hhd,
    ← hhd.lineDeriv_eq_fderiv, lineDeriv, hline, hd.deriv]

/-- The error term `ψ₀' ((n + 1) (f - a)) (n + 1) f (χ)` of the interpolation of two test vector
fields is dominated, uniformly in `n`, by a constant on the support of `χ`, when the normal
component of `χ` vanishes on the hyperplane `{f = a}`. -/
theorem StrongDual.exists_abs_deriv_smoothTransition_mul_le_indicator
    (f : StrongDual ℝ E) (a : ℝ)
    {Ω : Opens E} {χ : 𝓓(Ω, E)} (hχ : ∀ x, f x = a → f (χ x) = 0) :
    ∃ K : ℝ, ∀ (n : ℕ) (x : E),
      |deriv Real.smoothTransition ((n + 1) * (f x - a)) * ((n + 1) * f (χ x))| ≤
        (tsupport χ).indicator (fun _ => K) x := by
  obtain ⟨C, hC⟩ := StrongDual.exists_abs_apply_le_mul_abs_sub f a hχ
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support
    ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl)
    Real.smoothTransition.hasCompactSupport_deriv
  refine ⟨M * max C 0, fun n x => ?_⟩
  by_cases hx : x ∈ tsupport χ
  · rw [indicator_of_mem hx]
    exact Real.smoothTransition.abs_deriv_mul_mul_le hM (le_max_right _ _)
      ((hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
  · simp [image_eq_zero_of_notMem_tsupport hx, hx]

variable [FiniteDimensional ℝ E] in
/-- Interpolating two admissible test vector fields `φ` and `ψ` across the hyperplane `{f = a}` by
`Φₙ = φ + σₙ (ψ - φ)`, where `σₙ = ψ₀ ((n + 1) (f - a))` for the smooth transition `ψ₀`, gives
admissible test vector fields, with divergence `div φ + σₙ div (ψ - φ) + σₙ' f (ψ - φ)`. -/
theorem StrongDual.exists_interpolation_divergence
    (f : StrongDual ℝ E) (a : ℝ) {Ω : Opens E}
    {φ ψ : 𝓓(Ω, E)} (hφ : ∀ x, ‖φ x‖ ≤ 1) (hψ : ∀ x, ‖ψ x‖ ≤ 1) :
    ∃ Φ : ℕ → 𝓓(Ω, E), (∀ n x, ‖Φ n x‖ ≤ 1) ∧ ∀ (n : ℕ) (x : E),
      divergenceCLM (Φ n) x = divergenceCLM φ x +
        Real.smoothTransition ((n + 1) * (f x - a)) * divergenceCLM (ψ - φ) x +
          deriv Real.smoothTransition ((n + 1) * (f x - a)) * ((n + 1) * f ((ψ - φ) x)) := by
  set χ : 𝓓(Ω, E) := ψ - φ
  set σ : ℕ → E → ℝ := fun n x => Real.smoothTransition ((n + 1) * (f x - a))
  have hσ (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (σ n) := by fun_prop
  have hσd (n : ℕ) (x : E) : HasFDerivAt (σ n)
      (deriv Real.smoothTransition ((n + 1) * (f x - a)) • (((n : ℝ) + 1) • f)) x := by
    refine HasFDerivAt.smoothTransition ?_
    have := ((f.hasFDerivAt (x := x)).sub_const a).const_mul ((n : ℝ) + 1)
    simpa using this
  choose θ hθ using fun n => exists_coe_eq_smul_of_contDiffOn (hσ n).contDiffOn χ
  refine ⟨fun n => φ + θ n, fun n x => ?_, fun n x => ?_⟩
  · have h0 : 0 ≤ σ n x := Real.smoothTransition.nonneg _
    have h1 : 0 ≤ 1 - σ n x := sub_nonneg.2 (Real.smoothTransition.le_one _)
    have : (φ + θ n) x = (1 - σ n x) • φ x + σ n x • ψ x := by
      simp only [χ, add_apply, hθ, sub_apply]
      module
    rw [this, ← mem_closedBall_zero_iff]
    exact convex_closedBall (0 : E) 1 (mem_closedBall_zero_iff.2 (hφ x))
      (mem_closedBall_zero_iff.2 (hψ x)) h1 h0 (by ring)
  · have hχd : DifferentiableAt ℝ χ x := χ.contDiff.differentiable (by simp) x
    simp only [map_add, add_apply]
    rw [add_assoc, divergenceCLM_apply (θ n), hθ, trace_fderiv_smul (hσd n x).differentiableAt hχd,
      ← divergenceCLM_apply, (hσd n x).fderiv]
    simp [σ, smul_eq_mul]

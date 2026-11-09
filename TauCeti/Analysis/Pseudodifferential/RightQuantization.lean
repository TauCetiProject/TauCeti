/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Sobolev
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# The left symbol of a right quantization

The right quantization of a coefficient `c(y, ξ)` depending on the input variable `y` is
`(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) c(y, ξ) u(y) dy dξ`. Formal adjoints of left (Kohn–Nirenberg)
quantizations are of this form, so to stay in the calculus one rewrites a right quantization as a
left one. For a symbol `c` of order `m` with compact spatial support this file constructs the left
symbol

`b(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + 2πθ) dθ`,

where `ĉ(θ, ξ)` is Mathlib's Fourier transform of the position slice `z ↦ c(z, ξ)`, and proves
that it is a symbol of order `m` whose quantization is the right quantization of `c`.

## Main declarations

* `TauCeti.Symbol.ofRight`: the left symbol `b` of the right quantization of `c`, a symbol of
  order `m` with estimates uniform in the position (`TauCeti.Symbol.isUniform_ofRight`), whose
  position and frequency derivatives are the left symbols of the derivatives of `c`
  (`TauCeti.Symbol.spatialDeriv_ofRight`, `TauCeti.Symbol.frequencyDeriv_ofRight`).
* `TauCeti.Symbol.quantizeSchwartzValue_ofRight`: `Op(b) v (x)` is the right quantization
  `∫ exp(2πi ⟪ζ, x⟫) 𝓕 (y ↦ c(y, 2πζ) v(y)) (ζ) dζ` of `c`.

## The estimates

Since `c` has compact spatial support, `ĉ(θ, ξ)` decays faster than every power of `θ`, with
`‖ĉ(θ, ξ)‖ ≤ C_N (1 + ‖θ‖) ^ (-N) ⟨ξ⟩ ^ m`
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_one_add_norm_pow_mul_norm_fourier_le`). Peetre's
inequality `⟨ξ + 2πθ⟩ ^ m ≤ 2 ^ (|m| / 2) ⟨ξ⟩ ^ m ⟨2πθ⟩ ^ |m|` then bounds the integrand of `b`
by `C ⟨ξ⟩ ^ m (1 + ‖θ‖) ^ (-(n + 1))`, which is integrable in `θ`. To differentiate under the
integral sign the integrand is written as the position integral
`∫ exp(-2πi ⟪y, θ⟫) c(x + y, ξ + 2πθ) dy`, in which `(x, ξ)` only enters through the argument of
`c`. So every derivative of `b` is the left symbol of the corresponding derivative of `c`, and the
estimates of all mixed derivatives follow from the bound above by induction.

## Implementation notes

Integrals of the derivatives are linear maps on `ℝⁿ × ℝⁿ` with values in `V →L[ℂ] W`. Instance
synthesis for integrability on this concrete space fails, so the lemmas that need it are stated
for an abstract complex Banach space `F` and only then applied to `F = V →L[ℂ] W`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Module
open scoped RealInnerProductSpace SchwartzMap ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### The integrand and its decay -/

section Right

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-- The integrand `exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + 2πθ)` of the left symbol of the right quantization of
`c`, where `ĉ(θ, ξ)` is the Fourier transform of the position slice `z ↦ c(z, ξ)`. -/
private def rightIntegrand (c : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (p : CoordinateSpace n × CoordinateSpace n) (θ : CoordinateSpace n) : V →L[ℂ] W :=
  (𝐞 ⟪θ, p.1⟫ : ℂ) • 𝓕 (fun z ↦ c (z, p.2 + (2 * π) • θ)) θ

/-- The left symbol `∫ exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + 2πθ) dθ` of the right quantization of `c`. -/
private def rightCoeff (c : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (p : CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] W :=
  ∫ θ, rightIntegrand c p θ

variable {c : Symbol n V W m}

/-- The Fourier transform `ĉ(θ, ξ)` of the position slices of a symbol with compact spatial support
decays faster than `(1 + ‖θ‖) ^ (-(n + 1 + |m|))`. -/
private theorem HasCompactSpatialSupport.exists_norm_fourier_le (hc : c.HasCompactSpatialSupport) :
    ∃ C, 0 ≤ C ∧ ∀ θ ξ : CoordinateSpace n, ‖𝓕 (fun z ↦ c.coefficient (z, ξ)) θ‖ ≤
      C * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_one_add_norm_pow_mul_norm_fourier_le (n + 1 + ⌈|m|⌉₊)
  refine ⟨C, hC0, fun θ ξ ↦ ?_⟩
  have h1 : 1 ≤ 1 + ‖θ‖ := le_add_of_nonneg_right (norm_nonneg θ)
  have hexp : (n : ℝ) + 1 + |m| ≤ ((n + 1 + ⌈|m|⌉₊ : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil |m|]
  have hle : 1 ≤ (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * (1 + ‖θ‖) ^ (n + 1 + ⌈|m|⌉₊) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
    exact Real.one_le_rpow h1 (by linarith)
  calc ‖𝓕 (fun z ↦ c.coefficient (z, ξ)) θ‖
      ≤ (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * (1 + ‖θ‖) ^ (n + 1 + ⌈|m|⌉₊) *
          ‖𝓕 (fun z ↦ c.coefficient (z, ξ)) θ‖ := le_mul_of_one_le_left (norm_nonneg _) hle
    _ = (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) *
          ((1 + ‖θ‖) ^ (n + 1 + ⌈|m|⌉₊) * ‖𝓕 (fun z ↦ c.coefficient (z, ξ)) θ‖) := by ring
    _ ≤ (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :=
        mul_le_mul_of_nonneg_left (hC θ ξ) (by positivity)
    _ = C * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by ring

/-- Rescaling the frequency by `2π` changes the weight `⟨ξ⟩ ^ s` by at most `(2π) ^ |s|`. -/
private theorem weight_two_pi_smul_le (s : ℝ) (ξ : CoordinateSpace n) :
    (1 + ‖(2 * π) • ξ‖ ^ 2) ^ (s / 2) ≤ (2 * π) ^ |s| * (1 + ‖ξ‖ ^ 2) ^ (s / 2) :=
  one_add_norm_sq_rpow_le_of_norm_eq_mul (by linarith [Real.two_le_pi]) s
    (by rw [norm_smul, Real.norm_of_nonneg Real.two_pi_pos.le])

/-- The weight `⟨θ⟩ ^ |m|` lost to Peetre's inequality is absorbed by the decay of `ĉ`. -/
private theorem weight_mul_decay_le (θ : CoordinateSpace n) :
    (1 + ‖θ‖ ^ 2) ^ (|m| / 2) * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) ≤
      (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
  have hsplit : (1 + ‖θ‖) ^ |m| * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) =
      (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  have hθ : (1 + ‖θ‖ ^ 2) ^ (|m| / 2) ≤ (1 + ‖θ‖) ^ |m| := by
    rw [show (|m| / 2) = (1 / 2 : ℝ) * |m| by ring, Real.rpow_mul (by positivity),
      ← Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow (by positivity) (sqrt_one_add_norm_sq_le θ) (abs_nonneg m)
  rw [← hsplit]
  gcongr

/-- The weight `⟨2πθ⟩ ^ |m|` lost to Peetre's inequality is absorbed by the decay of `ĉ`. -/
private theorem weight_two_pi_mul_le (θ : CoordinateSpace n) :
    (1 + ‖(2 * π) • θ‖ ^ 2) ^ (|m| / 2) * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) ≤
      (2 * π) ^ |m| * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
  have hscale := weight_two_pi_smul_le |m| θ
  rw [abs_abs] at hscale
  calc (1 + ‖(2 * π) • θ‖ ^ 2) ^ (|m| / 2) * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|))
      ≤ (2 * π) ^ |m| * (1 + ‖θ‖ ^ 2) ^ (|m| / 2) * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) := by
        gcongr
    _ ≤ (2 * π) ^ |m| * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
        rw [mul_assoc]
        gcongr
        exact weight_mul_decay_le θ

/-- **The integrand decays in `θ`.**
`‖exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + 2πθ)‖ ≤ C ⟨ξ⟩ ^ m (1 + ‖θ‖) ^ (-(n + 1))`, uniformly in the position
`x`. -/
private theorem HasCompactSpatialSupport.exists_norm_rightIntegrand_le
    (hc : c.HasCompactSpatialSupport) :
    ∃ C, 0 ≤ C ∧ ∀ p θ, ‖rightIntegrand c.coefficient p θ‖ ≤
      C * (1 + ‖p.2‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_fourier_le
  refine ⟨C * 2 ^ (|m| / 2) * (2 * π) ^ |m|, by positivity, fun p θ ↦ ?_⟩
  have hpeetre := one_add_norm_add_sq_rpow_le_mul m p.2 ((2 * π) • θ)
  have hw := weight_two_pi_mul_le (m := m) θ
  rw [rightIntegrand, norm_smul, Circle.norm_coe, one_mul]
  calc ‖𝓕 (fun z ↦ c.coefficient (z, p.2 + (2 * π) • θ)) θ‖
      ≤ C * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * (1 + ‖p.2 + (2 * π) • θ‖ ^ 2) ^ (m / 2) :=
        hC θ _
    _ ≤ C * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * (2 ^ (|m| / 2) * (1 + ‖p.2‖ ^ 2) ^ (m / 2) *
          (1 + ‖(2 * π) • θ‖ ^ 2) ^ (|m| / 2)) := by gcongr
    _ = C * 2 ^ (|m| / 2) * (1 + ‖p.2‖ ^ 2) ^ (m / 2) * ((1 + ‖(2 * π) • θ‖ ^ 2) ^ (|m| / 2) *
          (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|))) := by ring
    _ ≤ C * 2 ^ (|m| / 2) * (1 + ‖p.2‖ ^ 2) ^ (m / 2) *
          ((2 * π) ^ |m| * (1 + ‖θ‖) ^ (-((n : ℝ) + 1))) := by gcongr
    _ = C * 2 ^ (|m| / 2) * (2 * π) ^ |m| * (1 + ‖p.2‖ ^ 2) ^ (m / 2) *
          (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by ring

/-- The decay weight `(1 + ‖θ‖) ^ (-(n + 1))` is integrable on `ℝⁿ`. -/
private theorem integrable_decay :
    Integrable fun θ : CoordinateSpace n ↦ (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) :=
  integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; linarith)

/-- The Fourier transform `ĉ(θ, ξ)` of the position slices is jointly continuous. -/
private theorem HasCompactSpatialSupport.continuous_fourier (hc : c.HasCompactSpatialSupport) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun z ↦ c.coefficient (z, q.2)) q.1 := by
  obtain ⟨K, hK, hKc⟩ := hasCompactSpatialSupport_iff.mp hc
  have h : (fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun z ↦ c.coefficient (z, q.2)) q.1) =
        fun q ↦ ∫ z in K, (𝐞 (-⟪z, q.1⟫) : ℂ) • c.coefficient (z, q.2) := by
    funext q
    rw [Real.fourier_eq, setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
      simp [hKc z hz]]
    simp only [Circle.smul_def]
  rw [h]
  refine continuous_parametric_integral_of_continuous ?_ hK
  exact (by fun_prop : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) ×
      CoordinateSpace n ↦ (𝐞 (-⟪q.2, q.1.1⟫) : ℂ)).smul
    (c.contDiff_coefficient.continuous.comp (by fun_prop))

/-- The integrand is jointly continuous in the point and the frequency `θ`. -/
private theorem HasCompactSpatialSupport.continuous_rightIntegrand
    (hc : c.HasCompactSpatialSupport) :
    Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      rightIntegrand c.coefficient q.1 q.2 := by
  have h₁ : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      (𝐞 ⟪q.2, q.1.1⟫ : ℂ) := by fun_prop
  have hg : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      ((q.2, q.1.2 + (2 * π) • q.2) : CoordinateSpace n × CoordinateSpace n) := by fun_prop
  have h₂ := hc.continuous_fourier.comp hg
  simp only [Function.comp_def] at h₂
  exact h₁.smul h₂

/-- The integrand is integrable in `θ`. -/
private theorem HasCompactSpatialSupport.integrable_rightIntegrand
    (hc : c.HasCompactSpatialSupport) (p : CoordinateSpace n × CoordinateSpace n) :
    Integrable (rightIntegrand c.coefficient p) := by
  obtain ⟨C, -, hC⟩ := hc.exists_norm_rightIntegrand_le
  exact (integrable_decay.const_mul (C * (1 + ‖p.2‖ ^ 2) ^ (m / 2))).mono'
    (hc.continuous_rightIntegrand.comp
      (by fun_prop : Continuous fun θ ↦ (p, θ))).aestronglyMeasurable
    (.of_forall fun θ ↦ (hC p θ).trans_eq (by ring))

/-- **The symbol bound.** `‖∫ exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + 2πθ) dθ‖ ≤ C ⟨ξ⟩ ^ m`, uniformly in `x`. -/
private theorem HasCompactSpatialSupport.exists_norm_rightCoeff_le
    (hc : c.HasCompactSpatialSupport) :
    ∃ C, 0 ≤ C ∧ ∀ p, ‖rightCoeff c.coefficient p‖ ≤ C * (1 + ‖p.2‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_rightIntegrand_le
  have hI : 0 ≤ ∫ θ : CoordinateSpace n, (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) :=
    integral_nonneg fun θ ↦ by positivity
  refine ⟨C * ∫ θ : CoordinateSpace n, (1 + ‖θ‖) ^ (-((n : ℝ) + 1)), by positivity, fun p ↦ ?_⟩
  calc ‖rightCoeff c.coefficient p‖
      ≤ ∫ θ, C * (1 + ‖p.2‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) :=
        norm_integral_le_of_norm_le (integrable_decay.const_mul _) (.of_forall (hC p))
    _ = C * (∫ θ : CoordinateSpace n, (1 + ‖θ‖) ^ (-((n : ℝ) + 1))) *
          (1 + ‖p.2‖ ^ 2) ^ (m / 2) := by
        rw [integral_const_mul]
        ring

/-- The integrand as an integral over positions:
`exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + 2πθ) = ∫ exp(-2πi ⟪y, θ⟫) c(x + y, ξ + 2πθ) dy`. In this form the point
`(x, ξ)` only enters through the argument of `c`. -/
private theorem rightIntegrand_eq_integral (c : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (p : CoordinateSpace n × CoordinateSpace n) (θ : CoordinateSpace n) :
    rightIntegrand c p θ = ∫ y, (𝐞 (-⟪y, θ⟫) : ℂ) • c (p + (y, (2 * π) • θ)) := by
  set g : CoordinateSpace n → V →L[ℂ] W := fun z ↦
    (𝐞 (-⟪z - p.1, θ⟫) : ℂ) • c (z, p.2 + (2 * π) • θ)
  have hshift : (∫ y, (𝐞 (-⟪y, θ⟫) : ℂ) • c (p + (y, (2 * π) • θ))) = ∫ y, g (p.1 + y) := by
    congr 1 with y
    simp only [g, add_sub_cancel_left]
    rfl
  rw [hshift, integral_add_left_eq_self g p.1, rightIntegrand, Real.fourier_eq, ← integral_smul]
  congr 1 with z
  simp only [g, Circle.smul_def, smul_smul, inner_sub_left]
  congr 1
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, real_inner_comm p.1 θ,
    show -(⟪z, θ⟫ - ⟪p.1, θ⟫) = ⟪p.1, θ⟫ + -⟪z, θ⟫ by ring]

end Right

/-! ### Differentiation under the integral sign -/

section Shift

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A function vanishing at all positions outside a closed set `K` has vanishing derivative at
every point whose position lies outside `K`. -/
private theorem fderiv_eq_zero_of_fst_notMem {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : CoordinateSpace n × CoordinateSpace n → G} {K : Set (CoordinateSpace n)}
    (hK : IsClosed K) (hfK : ∀ z ∉ K, ∀ ξ, f (z, ξ) = 0) {q : CoordinateSpace n × CoordinateSpace n}
    (hq : q.1 ∉ K) : fderiv ℝ f q = 0 := by
  have h : f =ᶠ[nhds q] fun _ ↦ 0 := by
    filter_upwards [(hK.isOpen_compl.preimage continuous_fst).mem_nhds hq] with r hr
    exact hfK r.1 hr r.2
  rw [h.fderiv_eq, fderiv_const_apply]

/-- The positions `y` at which `f(p + (y, ·))` can be nonzero, for `p` near `p₀`. -/
private theorem mem_image_sub_of_add_mem {K : Set (CoordinateSpace n)} {x₀ x y : CoordinateSpace n}
    (hx : dist x x₀ ≤ 1) (hy : x + y ∈ K) :
    y ∈ (fun q : CoordinateSpace n × CoordinateSpace n ↦ q.1 - q.2) ''
      (K ×ˢ Metric.closedBall x₀ 1) :=
  ⟨(x + y, x), ⟨hy, hx⟩, add_sub_cancel_left x y⟩

/-- The shifted position integrand `y ↦ exp(-2πi ⟪y, θ⟫) f(p + (y, 2πθ))` of a continuous function
vanishing for positions outside a compact set is integrable. -/
private theorem integrable_shift {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {f : CoordinateSpace n × CoordinateSpace n → G} (hf : Continuous f)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (hfK : ∀ z ∉ K, ∀ ξ, f (z, ξ) = 0)
    (p : CoordinateSpace n × CoordinateSpace n) (θ : CoordinateSpace n) :
    Integrable fun y ↦ (𝐞 (-⟪y, θ⟫) : ℂ) • f (p + (y, (2 * π) • θ)) := by
  have hS : IsCompact ((fun q : CoordinateSpace n × CoordinateSpace n ↦ q.1 - q.2) ''
      (K ×ˢ Metric.closedBall p.1 1)) := (hK.prod (isCompact_closedBall _ _)).image (by fun_prop)
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.intro hS ?_)
  intro y hy
  have hK' : p.1 + y ∉ K := fun h ↦ hy (mem_image_sub_of_add_mem (by simp) h)
  simp [show f (p + (y, (2 * π) • θ)) = 0 from hfK _ hK' _]

/-- **Differentiation under the position integral.** For a `C¹` function `f` vanishing for
positions outside a compact set, `p ↦ ∫ exp(-2πi ⟪y, θ⟫) f(p + (y, 2πθ)) dy` has the derivative
`∫ exp(-2πi ⟪y, θ⟫) Df(p + (y, 2πθ)) dy`. -/
private theorem hasFDerivAt_integral_shift {f : CoordinateSpace n × CoordinateSpace n → F}
    (hf : ContDiff ℝ 1 f) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (hfK : ∀ z ∉ K, ∀ ξ, f (z, ξ) = 0) (θ : CoordinateSpace n)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (fun p ↦ ∫ y, (𝐞 (-⟪y, θ⟫) : ℂ) • f (p + (y, (2 * π) • θ)))
      (∫ y, (𝐞 (-⟪y, θ⟫) : ℂ) • fderiv ℝ f (p₀ + (y, (2 * π) • θ))) p₀ := by
  set S := (fun q : CoordinateSpace n × CoordinateSpace n ↦ q.1 - q.2) ''
    (K ×ˢ Metric.closedBall p₀.1 1)
  have hS : IsCompact S := (hK.prod (isCompact_closedBall _ _)).image (by fun_prop)
  have hT : IsCompact (K ×ˢ Metric.closedBall (p₀.2 + (2 * π) • θ) 1) :=
    hK.prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hT.exists_bound_of_continuousOn (hf.continuous_fderiv one_ne_zero).continuousOn
  have hbound : ∀ y, ∀ p ∈ Metric.ball p₀ 1,
      ‖(𝐞 (-⟪y, θ⟫) : ℂ) • fderiv ℝ f (p + (y, (2 * π) • θ))‖ ≤
        S.indicator (fun _ ↦ max M 0) y := by
    intro y p hp
    rw [norm_smul, Circle.norm_coe, one_mul]
    have hp' : max (dist p.1 p₀.1) (dist p.2 p₀.2) < 1 := by
      rw [← Prod.dist_eq]
      exact hp
    have h₁ : dist p.1 p₀.1 ≤ 1 := (le_max_left _ _).trans hp'.le
    have h₂ : dist (p.2 + (2 * π) • θ) (p₀.2 + (2 * π) • θ) ≤ 1 := by
      rw [dist_add_right]
      exact (le_max_right _ _).trans hp'.le
    by_cases hy : p.1 + y ∈ K
    · rw [Set.indicator_of_mem (mem_image_sub_of_add_mem h₁ hy)]
      have hmem : p + (y, (2 * π) • θ) ∈ K ×ˢ Metric.closedBall (p₀.2 + (2 * π) • θ) 1 :=
        ⟨by simpa using hy, by simpa using h₂⟩
      exact (hM _ hmem).trans (le_max_left _ _)
    · have hnot : (p + (y, (2 * π) • θ)).1 ∉ K := by simpa using hy
      rw [fderiv_eq_zero_of_fst_notMem hK.isClosed hfK hnot, norm_zero]
      exact Set.indicator_nonneg (fun _ _ ↦ le_max_right _ _) y
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds p₀ one_pos)
    (.of_forall fun p ↦ (integrable_shift hf.continuous hK hfK p θ).aestronglyMeasurable)
    (integrable_shift hf.continuous hK hfK p₀ θ)
    ((by fun_prop : Continuous fun y : CoordinateSpace n ↦ (𝐞 (-⟪y, θ⟫) : ℂ)).smul
      ((hf.continuous_fderiv one_ne_zero).comp
        (by fun_prop : Continuous fun y : CoordinateSpace n ↦ p₀ + (y, (2 * π) • θ)))
      ).aestronglyMeasurable
    (.of_forall hbound) ?_ (.of_forall fun y p _ ↦ ?_)
  · exact (integrable_indicator_iff hS.measurableSet).2 (integrableOn_const hS.measure_lt_top.ne)
  · have h := (hf.differentiable one_ne_zero (p + (y, (2 * π) • θ))).hasFDerivAt.comp p
      ((hasFDerivAt_id p).add_const (y, (2 * π) • θ))
    rw [ContinuousLinearMap.comp_id] at h
    exact h.const_smul _

/-- Evaluating the integrated derivative in a direction `v` commutes with the position
integral. -/
private theorem integral_shift_fderiv_apply {f : CoordinateSpace n × CoordinateSpace n → F}
    (hf : ContDiff ℝ 1 f) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (hfK : ∀ z ∉ K, ∀ ξ, f (z, ξ) = 0) (θ : CoordinateSpace n)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    (∫ y, (𝐞 (-⟪y, θ⟫) : ℂ) • fderiv ℝ f (p + (y, (2 * π) • θ))) v =
      ∫ y, (𝐞 (-⟪y, θ⟫) : ℂ) • fderiv ℝ f (p + (y, (2 * π) • θ)) v :=
  ContinuousLinearMap.integral_apply (integrable_shift (hf.continuous_fderiv one_ne_zero) hK
    (fun _ hz _ ↦ fderiv_eq_zero_of_fst_notMem hK.isClosed hfK hz) p θ) v

/-- A continuous family of linear maps is a.e. strongly measurable.

This instance of `Continuous.aestronglyMeasurable` is stated over an abstract codomain `F`:
applied directly to the concrete codomain `_ →L[ℝ] V →L[ℂ] W` below, the search for its
`PseudoMetrizableSpace` instance exceeds the default typeclass heartbeat limit. -/
private theorem aestronglyMeasurable_of_continuous_clm {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {φ : CoordinateSpace n → H →L[ℝ] F} (hφ : Continuous φ) :
    AEStronglyMeasurable φ :=
  hφ.aestronglyMeasurable

end Shift

/-! ### Smoothness of the left symbol -/

section Smooth

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {c : Symbol n V W m}

/-- The derivative of a symbol in the direction `v` through its first-order coordinate
derivatives. -/
private theorem fderiv_coefficient_apply (c : Symbol n V W m)
    (q v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ c.coefficient q v = ∑ j, v.1 j • (Symbol.spatialDeriv j c).coefficient q +
      ∑ j, v.2 j • (Symbol.frequencyDeriv j c).coefficient q := by
  obtain ⟨x, ξ⟩ := q
  have hd : DifferentiableAt ℝ c.coefficient (x, ξ) :=
    c.contDiff_coefficient.differentiable (by simp) _
  have h₁ (y : CoordinateSpace n) :
      fderiv ℝ c.coefficient (x, ξ) (y, 0) = fderiv ℝ (fun y ↦ c.coefficient (y, ξ)) x y := by
    have h := hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x ξ)
    rw [Function.comp_def] at h
    simp [h.fderiv]
  have h₂ (η : CoordinateSpace n) :
      fderiv ℝ c.coefficient (x, ξ) (0, η) = fderiv ℝ (fun η ↦ c.coefficient (x, η)) ξ η := by
    have h := hd.hasFDerivAt.comp ξ (hasFDerivAt_prodMk_right (𝕜 := ℝ) x ξ)
    rw [Function.comp_def] at h
    simp [h.fderiv]
  have hsum (w : CoordinateSpace n) : w = ∑ j, w j • EuclideanSpace.single j (1 : ℝ) := by
    simpa using ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w).symm
  have hexp (L : CoordinateSpace n →L[ℝ] V →L[ℂ] W) (w : CoordinateSpace n) :
      L w = ∑ j, w j • L (EuclideanSpace.single j 1) := by
    conv_lhs => rw [hsum w]
    rw [map_sum]
    simp only [map_smul]
  calc fderiv ℝ c.coefficient (x, ξ) v = fderiv ℝ c.coefficient (x, ξ) ((v.1, 0) + (0, v.2)) := by
        congr 1
        exact Prod.ext (by simp) (by simp)
    _ = fderiv ℝ (fun y ↦ c.coefficient (y, ξ)) x v.1 +
          fderiv ℝ (fun η ↦ c.coefficient (x, η)) ξ v.2 := by rw [map_add, h₁, h₂]
    _ = _ := by
        rw [hexp _ v.1, hexp _ v.2]
        congr 1
        · refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [fderiv_coefficient_single]
        · refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [coefficient_frequencyDeriv, coordinateDeriv_cons, coordinateDeriv_nil]

/-- The shifted position integrand of a symbol with compact spatial support is integrable. -/
private theorem HasCompactSpatialSupport.integrable_shift (hc : c.HasCompactSpatialSupport)
    (p : CoordinateSpace n × CoordinateSpace n) (θ : CoordinateSpace n) :
    Integrable fun y ↦ (𝐞 (-⟪y, θ⟫) : ℂ) • c.coefficient (p + (y, (2 * π) • θ)) := by
  obtain ⟨K, hK, hKc⟩ := hasCompactSpatialSupport_iff.mp hc
  exact Symbol.integrable_shift c.contDiff_coefficient.continuous hK hKc p θ

/-- The derivative in the point `p` of the integrand, as an integral over positions. -/
private def rightDeriv (c : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n)
    (θ : CoordinateSpace n) : CoordinateSpace n × CoordinateSpace n →L[ℝ] V →L[ℂ] W :=
  ∫ y, (𝐞 (-⟪y, θ⟫) : ℂ) • fderiv ℝ c.coefficient (p + (y, (2 * π) • θ))

/-- The derivative of the integrand in the direction `v`, through the integrands of the first-order
derivatives of the symbol. -/
private theorem HasCompactSpatialSupport.rightDeriv_apply (hc : c.HasCompactSpatialSupport)
    (p : CoordinateSpace n × CoordinateSpace n) (θ : CoordinateSpace n)
    (v : CoordinateSpace n × CoordinateSpace n) :
    rightDeriv c p θ v = ∑ j, v.1 j • rightIntegrand (Symbol.spatialDeriv j c).coefficient p θ +
      ∑ j, v.2 j • rightIntegrand (Symbol.frequencyDeriv j c).coefficient p θ := by
  obtain ⟨K, hK, hKc⟩ := hasCompactSpatialSupport_iff.mp hc
  have hx (j : Fin n) := (hc.spatialDeriv j).integrable_shift p θ
  have hξ (j : Fin n) := (hc.frequencyDeriv j).integrable_shift p θ
  rw [rightDeriv, integral_shift_fderiv_apply (c.contDiff_coefficient.of_le (by simp)) hK hKc]
  have hx' (j : Fin n) : Integrable fun y ↦ v.1 j •
      (𝐞 (-⟪y, θ⟫) : ℂ) • (Symbol.spatialDeriv j c).coefficient (p + (y, (2 * π) • θ)) :=
    (hx j).smul (v.1 j)
  have hξ' (j : Fin n) : Integrable fun y ↦ v.2 j •
      (𝐞 (-⟪y, θ⟫) : ℂ) • (Symbol.frequencyDeriv j c).coefficient (p + (y, (2 * π) • θ)) :=
    (hξ j).smul (v.2 j)
  simp_rw [rightIntegrand_eq_integral, ← integral_smul]
  rw [← integral_finsetSum _ fun j _ ↦ hx' j, ← integral_finsetSum _ fun j _ ↦ hξ' j,
    ← integral_add (integrable_finsetSum _ fun j _ ↦ hx' j)
      (integrable_finsetSum _ fun j _ ↦ hξ' j)]
  congr 1
  funext y
  rw [fderiv_coefficient_apply, smul_add, Finset.smul_sum, Finset.smul_sum]
  exact congrArg₂ (· + ·)
    (Finset.sum_congr rfl fun j _ ↦ smul_comm (𝐞 (-⟪y, θ⟫) : ℂ) (v.1 j : ℝ)
      ((Symbol.spatialDeriv j c).coefficient (p + (y, (2 * π) • θ))))
    (Finset.sum_congr rfl fun j _ ↦ smul_comm (𝐞 (-⟪y, θ⟫) : ℂ) (v.2 j : ℝ)
      ((Symbol.frequencyDeriv j c).coefficient (p + (y, (2 * π) • θ))))

/-- Near a point `p₀`, the integrand is bounded by a multiple of `(1 + ‖θ‖) ^ (-(n + 1))`. -/
private theorem HasCompactSpatialSupport.exists_norm_rightIntegrand_le_of_mem_ball
    (hc : c.HasCompactSpatialSupport) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    ∃ B, 0 ≤ B ∧ ∀ p ∈ Metric.ball p₀ 1, ∀ θ,
      ‖rightIntegrand c.coefficient p θ‖ ≤ B * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_rightIntegrand_le
  have hcont : Continuous fun p : CoordinateSpace n × CoordinateSpace n ↦
      (1 + ‖p.2‖ ^ 2) ^ (m / 2) :=
    (by fun_prop : Continuous fun p : CoordinateSpace n × CoordinateSpace n ↦
      1 + ‖p.2‖ ^ 2).rpow_const fun _ ↦ Or.inl (by positivity)
  obtain ⟨D, hD⟩ := (isCompact_closedBall p₀ 1).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C * max D 0, by positivity, fun p hp θ ↦ (hC p θ).trans ?_⟩
  have hDp : (1 + ‖p.2‖ ^ 2) ^ (m / 2) ≤ max D 0 := by
    have h := hD p (Metric.ball_subset_closedBall hp)
    rw [Real.norm_of_nonneg (by positivity)] at h
    exact h.trans (le_max_left _ _)
  gcongr

/-- Near a point `p₀`, the derivative of the integrand is bounded by a multiple of
`(1 + ‖θ‖) ^ (-(n + 1))`. -/
private theorem HasCompactSpatialSupport.exists_norm_rightDeriv_le
    (hc : c.HasCompactSpatialSupport) (p₀ : CoordinateSpace n × CoordinateSpace n) :
    ∃ B, 0 ≤ B ∧ ∀ p ∈ Metric.ball p₀ 1, ∀ θ,
      ‖rightDeriv c p θ‖ ≤ B * (1 + ‖θ‖) ^ (-((n : ℝ) + 1)) := by
  choose Bx hBx0 hBx using fun j ↦ (hc.spatialDeriv j).exists_norm_rightIntegrand_le_of_mem_ball p₀
  choose Bξ hBξ0 hBξ using fun j ↦
    (hc.frequencyDeriv j).exists_norm_rightIntegrand_le_of_mem_ball p₀
  have hB : 0 ≤ ∑ j, Bx j + ∑ j, Bξ j :=
    add_nonneg (Finset.sum_nonneg fun j _ ↦ hBx0 j) (Finset.sum_nonneg fun j _ ↦ hBξ0 j)
  refine ⟨∑ j, Bx j + ∑ j, Bξ j, hB, fun p hp θ ↦ ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  have hv₁ (j : Fin n) : ‖v.1 j‖ ≤ ‖v‖ := (PiLp.norm_apply_le v.1 j).trans (norm_fst_le v)
  have hv₂ (j : Fin n) : ‖v.2 j‖ ≤ ‖v‖ := (PiLp.norm_apply_le v.2 j).trans (norm_snd_le v)
  rw [hc.rightDeriv_apply]
  set w := (1 + ‖θ‖) ^ (-((n : ℝ) + 1))
  calc ‖∑ j, v.1 j • rightIntegrand (Symbol.spatialDeriv j c).coefficient p θ +
        ∑ j, v.2 j • rightIntegrand (Symbol.frequencyDeriv j c).coefficient p θ‖
      ≤ ∑ j, ‖v.1 j • rightIntegrand (Symbol.spatialDeriv j c).coefficient p θ‖ +
          ∑ j, ‖v.2 j • rightIntegrand (Symbol.frequencyDeriv j c).coefficient p θ‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))
    _ ≤ ∑ j, ‖v‖ * (Bx j * w) + ∑ j, ‖v‖ * (Bξ j * w) := by
        gcongr with j _ j _
        · rw [norm_smul]
          exact mul_le_mul (hv₁ j) (hBx j p hp θ) (norm_nonneg _) (norm_nonneg _)
        · rw [norm_smul]
          exact mul_le_mul (hv₂ j) (hBξ j p hp θ) (norm_nonneg _) (norm_nonneg _)
    _ = (∑ j, Bx j + ∑ j, Bξ j) * w * ‖v‖ := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
        ring

/-- The derivative of the integrand is continuous in `θ`. -/
private theorem HasCompactSpatialSupport.continuous_rightDeriv (hc : c.HasCompactSpatialSupport)
    (p : CoordinateSpace n × CoordinateSpace n) : Continuous (rightDeriv c p) := by
  refine continuous_clm_apply.2 fun v ↦ ?_
  simp_rw [hc.rightDeriv_apply]
  refine (continuous_finsetSum _ fun j _ ↦ ?_).add (continuous_finsetSum _ fun j _ ↦ ?_)
  · exact ((hc.spatialDeriv j).continuous_rightIntegrand.comp
      (by fun_prop : Continuous fun θ : CoordinateSpace n ↦ (p, θ))).const_smul (v.1 j)
  · exact ((hc.frequencyDeriv j).continuous_rightIntegrand.comp
      (by fun_prop : Continuous fun θ : CoordinateSpace n ↦ (p, θ))).const_smul (v.2 j)

/-- **Differentiation under the frequency integral.** -/
private theorem HasCompactSpatialSupport.hasFDerivAt_rightCoeff (hc : c.HasCompactSpatialSupport)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    HasFDerivAt (rightCoeff c.coefficient) (∫ θ, rightDeriv c p₀ θ) p₀ := by
  obtain ⟨K, hK, hKc⟩ := hasCompactSpatialSupport_iff.mp hc
  obtain ⟨B, -, hB⟩ := hc.exists_norm_rightDeriv_le p₀
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds p₀ one_pos)
    (.of_forall fun p ↦ (hc.integrable_rightIntegrand p).aestronglyMeasurable)
    (hc.integrable_rightIntegrand p₀) (aestronglyMeasurable_of_continuous_clm
      (hc.continuous_rightDeriv p₀))
    (.of_forall fun θ p hp ↦ hB p hp θ) (integrable_decay.const_mul B)
    (.of_forall fun θ p _ ↦ ?_)
  have h : (fun p ↦ rightIntegrand c.coefficient p θ) =
      fun p ↦ ∫ y, (𝐞 (-⟪y, θ⟫) : ℂ) • c.coefficient (p + (y, (2 * π) • θ)) :=
    funext fun p ↦ rightIntegrand_eq_integral _ p θ
  rw [h]
  exact hasFDerivAt_integral_shift (c.contDiff_coefficient.of_le (by simp)) hK hKc θ p

/-- The derivative of the left symbol in the direction `v`, through the left symbols of the
first-order derivatives of `c`. -/
private theorem HasCompactSpatialSupport.fderiv_rightCoeff_apply (hc : c.HasCompactSpatialSupport)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (rightCoeff c.coefficient) p v =
      ∑ j, v.1 j • rightCoeff (Symbol.spatialDeriv j c).coefficient p +
        ∑ j, v.2 j • rightCoeff (Symbol.frequencyDeriv j c).coefficient p := by
  have hx (j : Fin n) : Integrable fun θ ↦
      v.1 j • rightIntegrand (Symbol.spatialDeriv j c).coefficient p θ :=
    ((hc.spatialDeriv j).integrable_rightIntegrand p).smul (v.1 j)
  have hξ (j : Fin n) : Integrable fun θ ↦
      v.2 j • rightIntegrand (Symbol.frequencyDeriv j c).coefficient p θ :=
    ((hc.frequencyDeriv j).integrable_rightIntegrand p).smul (v.2 j)
  obtain ⟨B, -, hB⟩ := hc.exists_norm_rightDeriv_le p
  rw [(hc.hasFDerivAt_rightCoeff p).fderiv, ContinuousLinearMap.integral_apply
    ((integrable_decay.const_mul B).mono'
      (aestronglyMeasurable_of_continuous_clm (hc.continuous_rightDeriv p))
      (.of_forall (hB p (Metric.mem_ball_self one_pos)))) v]
  simp_rw [hc.rightDeriv_apply]
  rw [integral_add (integrable_finsetSum _ fun j _ ↦ hx j) (integrable_finsetSum _ fun j _ ↦ hξ j),
    integral_finsetSum _ fun j _ ↦ hx j, integral_finsetSum _ fun j _ ↦ hξ j]
  simp_rw [integral_smul, rightCoeff]

/-- The left symbol is `C^k` for every `k`. -/
private theorem HasCompactSpatialSupport.contDiff_rightCoeff (k : ℕ) :
    ∀ {m : ℝ} {c : Symbol n V W m}, c.HasCompactSpatialSupport →
      ContDiff ℝ k (rightCoeff c.coefficient) := by
  induction k with
  | zero =>
    intro m c hc
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun p ↦
      (hc.hasFDerivAt_rightCoeff p).continuousAt)
  | succ k ih =>
    intro m c hc
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_fderiv_apply.2 ⟨fun p ↦ (hc.hasFDerivAt_rightCoeff p).differentiableAt,
      by simp, fun v ↦ ?_⟩
    simp_rw [hc.fderiv_rightCoeff_apply]
    exact (ContDiff.sum fun j _ ↦ (ih (hc.spatialDeriv j)).const_smul _).add
      (ContDiff.sum fun j _ ↦ (ih (hc.frequencyDeriv j)).const_smul _)

/-- A frequency derivative of the left symbol is the left symbol of the frequency derivative. -/
private theorem HasCompactSpatialSupport.coordinateDeriv_snd_rightCoeff
    (hc : c.HasCompactSpatialSupport) (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun η ↦ rightCoeff c.coefficient (x, η)) ξ =
      rightCoeff (Symbol.frequencyDeriv j c).coefficient (x, ξ) := by
  have h := (hc.hasFDerivAt_rightCoeff (x, ξ)).differentiableAt.hasFDerivAt.comp ξ
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x ξ)
  rw [Function.comp_def] at h
  rw [coordinateDeriv_cons, coordinateDeriv_nil, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    hc.fderiv_rightCoeff_apply, PiLp.zero_apply, zero_smul, Finset.sum_const_zero, zero_add,
    PiLp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- A position derivative of the left symbol is the left symbol of the position derivative. -/
private theorem HasCompactSpatialSupport.coordinateDeriv_fst_rightCoeff
    (hc : c.HasCompactSpatialSupport) (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun y ↦ rightCoeff c.coefficient (y, ξ)) x =
      rightCoeff (Symbol.spatialDeriv j c).coefficient (x, ξ) := by
  have h := (hc.hasFDerivAt_rightCoeff (x, ξ)).differentiableAt.hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x ξ)
  rw [Function.comp_def] at h
  rw [coordinateDeriv_cons, coordinateDeriv_nil, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    hc.fderiv_rightCoeff_apply, PiLp.zero_apply, zero_smul, Finset.sum_const_zero, add_zero,
    PiLp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Iterated frequency derivatives of the left symbol are left symbols of iterated frequency
derivatives of `c`. -/
private theorem HasCompactSpatialSupport.exists_coordinateDeriv_snd_rightCoeff
    (hc : c.HasCompactSpatialSupport) (β : List (Fin n)) :
    ∃ c' : Symbol n V W (m - β.length), c'.HasCompactSpatialSupport ∧ ∀ x ξ,
      coordinateDeriv β (fun η ↦ rightCoeff c.coefficient (x, η)) ξ =
        rightCoeff c'.coefficient (x, ξ) := by
  induction β with
  | nil => exact ⟨Symbol.inclusion (by simp) c, hc.inclusion _, fun x ξ ↦ by simp⟩
  | cons j β ih =>
    obtain ⟨c', hc', h⟩ := ih
    refine ⟨Symbol.inclusion (le_of_eq (by rw [List.length_cons, Nat.cast_succ]; ring))
      (Symbol.frequencyDeriv j c'),
      (hc'.frequencyDeriv j).inclusion _, fun x ξ ↦ ?_⟩
    rw [coordinateDeriv_cons, show coordinateDeriv β (fun η ↦ rightCoeff c.coefficient (x, η)) =
      fun η ↦ rightCoeff c'.coefficient (x, η) from funext (h x), coefficient_inclusion,
      ← hc'.coordinateDeriv_snd_rightCoeff j x ξ, coordinateDeriv_cons, coordinateDeriv_nil]

/-- Iterated position derivatives of the left symbol are left symbols of iterated position
derivatives of `c`. -/
private theorem HasCompactSpatialSupport.exists_coordinateDeriv_fst_rightCoeff
    (α : List (Fin n)) : ∀ {m : ℝ} {c : Symbol n V W m}, c.HasCompactSpatialSupport →
      ∃ c' : Symbol n V W m, c'.HasCompactSpatialSupport ∧ ∀ x ξ,
        coordinateDeriv α (fun y ↦ rightCoeff c.coefficient (y, ξ)) x =
          rightCoeff c'.coefficient (x, ξ) := by
  induction α with
  | nil => exact fun hc ↦ ⟨_, hc, fun _ _ ↦ by simp⟩
  | cons j α ih =>
    intro m c hc
    obtain ⟨c', hc', h⟩ := ih hc
    refine ⟨Symbol.spatialDeriv j c', hc'.spatialDeriv j, fun x ξ ↦ ?_⟩
    rw [coordinateDeriv_cons, show coordinateDeriv α (fun y ↦ rightCoeff c.coefficient (y, ξ)) =
      fun y ↦ rightCoeff c'.coefficient (y, ξ) from funext fun y ↦ h y ξ,
      ← hc'.coordinateDeriv_fst_rightCoeff j x ξ, coordinateDeriv_cons, coordinateDeriv_nil]

/-- Every mixed derivative of the left symbol is the left symbol of a symbol of order
`m - |β|` with compact spatial support. -/
private theorem HasCompactSpatialSupport.exists_mixedDeriv_rightCoeff
    (hc : c.HasCompactSpatialSupport) (α β : List (Fin n)) :
    ∃ c' : Symbol n V W (m - β.length), c'.HasCompactSpatialSupport ∧ ∀ x ξ,
      mixedDeriv α β (rightCoeff c.coefficient) x ξ = rightCoeff c'.coefficient (x, ξ) := by
  obtain ⟨c₁, hc₁, h₁⟩ := hc.exists_coordinateDeriv_snd_rightCoeff β
  obtain ⟨c₂, hc₂, h₂⟩ := HasCompactSpatialSupport.exists_coordinateDeriv_fst_rightCoeff α hc₁
  refine ⟨c₂, hc₂, fun x ξ ↦ ?_⟩
  rw [mixedDeriv_def, show (fun y ↦ coordinateDeriv β (fun η ↦ rightCoeff c.coefficient (y, η)) ξ) =
    fun y ↦ rightCoeff c₁.coefficient (y, ξ) from funext fun y ↦ h₁ y ξ, h₂]

/-- The mixed derivatives of the left symbol satisfy the estimates of order `m`, uniformly in the
position. -/
private theorem HasCompactSpatialSupport.exists_norm_mixedDeriv_rightCoeff_le
    (hc : c.HasCompactSpatialSupport) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ξ, ‖mixedDeriv α β (rightCoeff c.coefficient) x ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨c', hc', h⟩ := hc.exists_mixedDeriv_rightCoeff α β
  obtain ⟨C, hC0, hC⟩ := hc'.exists_norm_rightCoeff_le
  exact ⟨C, hC0, fun x ξ ↦ by rw [h]; exact hC (x, ξ)⟩

end Smooth

/-! ### The left symbol of the right quantization -/

section OfRight

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {c : Symbol n V W m}

/-- **The left symbol of the right quantization.** For a symbol `c` of order `m` with compact
spatial support, the symbol
`b(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) ĉ(θ, ξ + 2πθ) dθ`, where `ĉ(θ, ξ)` is the Fourier transform of the
position slice `z ↦ c(z, ξ)`. Its left quantization is the right quantization
`(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) c(y, ξ) u(y) dy dξ` of `c`
(`TauCeti.Symbol.quantizeSchwartzValue_ofRight`). It is again a symbol of order `m`, with
estimates uniform in the position (`TauCeti.Symbol.isUniform_ofRight`), but in general it does not
have compact spatial support. -/
def ofRight (c : Symbol n V W m) (hc : c.HasCompactSpatialSupport) : Symbol n V W m where
  coefficient := rightCoeff c.coefficient
  contDiff_coefficient := contDiff_infty.2 fun k ↦ hc.contDiff_rightCoeff k
  exists_bound _ _ α β := by
    obtain ⟨C, hC0, hC⟩ := hc.exists_norm_mixedDeriv_rightCoeff_le α β
    exact ⟨C, hC0, fun x _ ξ ↦ hC x ξ⟩

@[simp]
theorem coefficient_ofRight (hc : c.HasCompactSpatialSupport) (x ξ : CoordinateSpace n) :
    (c.ofRight hc).coefficient (x, ξ) =
      ∫ θ, (𝐞 ⟪θ, x⟫ : ℂ) • 𝓕 (fun z ↦ c.coefficient (z, ξ + (2 * π) • θ)) θ :=
  (rfl)

/-- The coefficient of `ofRight` is the private integral `rightCoeff` of this file. -/
private theorem coefficient_ofRight_eq_rightCoeff (hc : c.HasCompactSpatialSupport) :
    (c.ofRight hc).coefficient = rightCoeff c.coefficient :=
  (rfl)

/-- The left symbol of a right quantization satisfies its estimates uniformly in the position. -/
theorem isUniform_ofRight (hc : c.HasCompactSpatialSupport) : (c.ofRight hc).IsUniform :=
  isUniform_iff.2 fun α β ↦ hc.exists_norm_mixedDeriv_rightCoeff_le α β

/-- Position derivatives commute with passing to the left symbol. -/
theorem spatialDeriv_ofRight (hc : c.HasCompactSpatialSupport) (j : Fin n) :
    spatialDeriv j (c.ofRight hc) = (spatialDeriv j c).ofRight (hc.spatialDeriv j) :=
  Symbol.ext (funext fun ⟨x, ξ⟩ ↦ by
    rw [coefficient_spatialDeriv]
    exact hc.coordinateDeriv_fst_rightCoeff j x ξ)

/-- Frequency derivatives commute with passing to the left symbol. -/
theorem frequencyDeriv_ofRight (hc : c.HasCompactSpatialSupport) (j : Fin n) :
    frequencyDeriv j (c.ofRight hc) = (frequencyDeriv j c).ofRight (hc.frequencyDeriv j) :=
  Symbol.ext (funext fun ⟨x, ξ⟩ ↦ by
    rw [coefficient_frequencyDeriv]
    exact hc.coordinateDeriv_snd_rightCoeff j x ξ)

end OfRight

/-! ### The quantization of the left symbol -/

section Quantization

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {c : Symbol n V W m}

omit [CompleteSpace V] [CompleteSpace W] in
/-- The integrand `(y, η) ↦ exp(-2πi ⟪y, ζ - η⟫) c(y, ξ) v̂(η)` of the Fourier transform of
`y ↦ c(y, ξ) v(y)`, after Fourier inversion of `v`, is integrable. -/
private theorem HasCompactSpatialSupport.integrable_fourierChar_smul_apply_fourier
    (hc : c.HasCompactSpatialSupport) (v : 𝓢(CoordinateSpace n, V)) (ξ ζ : CoordinateSpace n) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 (-⟪q.1, ζ - q.2⟫) : ℂ) • c.coefficient (q.1, ξ) (𝓕 v q.2)) (volume.prod volume) := by
  obtain ⟨K, hK, hKc⟩ := hasCompactSpatialSupport_iff.mp hc
  obtain ⟨C, hC0, hC⟩ := c.exists_bound_coefficient K hK
  have hcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 (-⟪q.1, ζ - q.2⟫) : ℂ) • c.coefficient (q.1, ξ) (𝓕 v q.2) :=
    (by fun_prop : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 (-⟪q.1, ζ - q.2⟫) : ℂ)).smul (((c.contDiff_coefficient_slice ξ).continuous.comp
        continuous_fst).clm_apply ((𝓕 v).continuous.comp continuous_snd))
  have hK1 : Integrable (K.indicator fun _ ↦ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  refine (hK1.mul_prod (𝓕 v).integrable.norm).mono' hcont.aestronglyMeasurable
    (.of_forall fun q ↦ ?_)
  rw [norm_smul, Circle.norm_coe, one_mul]
  by_cases hq : q.1 ∈ K
  · rw [Set.indicator_of_mem hq]
    exact ((c.coefficient _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hC q.1 hq ξ) (norm_nonneg _))
  · simp only [hKc q.1 hq, zero_apply, norm_zero]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ ↦ by positivity) _) (norm_nonneg _)

/-- **The Fourier transform of a product.** The Fourier transform of `y ↦ c(y, ξ) v(y)` is the
convolution `∫ ĉ(θ, ξ) v̂(ζ - θ) dθ` of the Fourier transforms. -/
private theorem HasCompactSpatialSupport.fourier_apply_eq_integral
    (hc : c.HasCompactSpatialSupport) (v : 𝓢(CoordinateSpace n, V)) (ξ ζ : CoordinateSpace n) :
    𝓕 (fun y ↦ c.coefficient (y, ξ) (v y)) ζ =
      ∫ θ, 𝓕 (fun z ↦ c.coefficient (z, ξ)) θ (𝓕 v (ζ - θ)) := by
  obtain ⟨K, hK, hKc⟩ := hasCompactSpatialSupport_iff.mp hc
  have hslice : Continuous fun z ↦ c.coefficient (z, ξ) :=
    (c.contDiff_coefficient_slice ξ).continuous
  set F : CoordinateSpace n × CoordinateSpace n → W := fun q ↦
    (𝐞 (-⟪q.1, ζ - q.2⟫) : ℂ) • c.coefficient (q.1, ξ) (𝓕 v q.2) with hF
  have hFint : Integrable F (volume.prod volume) :=
    hc.integrable_fourierChar_smul_apply_fourier v ξ ζ
  have hv (y : CoordinateSpace n) : v y = ∫ η, 𝐞 ⟪η, y⟫ • 𝓕 v η := by
    rw [← Real.fourierInv_eq, ← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq]
  have hvint (y : CoordinateSpace n) : Integrable fun η ↦ 𝐞 ⟪η, y⟫ • 𝓕 v η :=
    (𝓕 v).integrable.norm.mono' ((by fun_prop : Continuous fun η : CoordinateSpace n ↦
      (𝐞 ⟪η, y⟫ : ℂ)).smul (𝓕 v).continuous).aestronglyMeasurable
      (.of_forall fun η ↦ (Circle.norm_smul _ _).le)
  calc 𝓕 (fun y ↦ c.coefficient (y, ξ) (v y)) ζ = ∫ y, ∫ η, F (y, η) := by
        rw [Real.fourier_eq]
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        dsimp only
        rw [hv y, ← (c.coefficient (y, ξ)).integral_comp_comm (hvint y), Circle.smul_def,
          ← integral_smul]
        refine integral_congr_ae (.of_forall fun η ↦ ?_)
        simp only [hF, Circle.smul_def, map_smul, smul_smul, ← Circle.coe_mul,
          ← AddChar.map_add_eq_mul, inner_sub_right, real_inner_comm y η]
        congr 3
        ring
    _ = ∫ η, ∫ y, F (y, η) := integral_integral_swap hFint
    _ = ∫ η, 𝓕 (fun z ↦ c.coefficient (z, ξ)) (ζ - η) (𝓕 v η) := by
        refine integral_congr_ae (.of_forall fun η ↦ ?_)
        have hint : Integrable fun z ↦ 𝐞 (-⟪z, ζ - η⟫) • c.coefficient (z, ξ) :=
          (((by fun_prop : Continuous fun z : CoordinateSpace n ↦ (𝐞 (-⟪z, ζ - η⟫) : ℂ)).smul
            hslice).integrable_of_hasCompactSupport
              (HasCompactSupport.intro hK fun z hz ↦ by simp [hKc z hz]))
        dsimp only
        rw [Real.fourier_eq, ContinuousLinearMap.integral_apply hint]
        simp only [hF, Circle.smul_def, smul_apply]
    _ = ∫ θ, 𝓕 (fun z ↦ c.coefficient (z, ξ)) θ (𝓕 v (ζ - θ)) := by
        rw [← integral_sub_left_eq_self _ volume ζ]
        simp only [sub_sub_cancel]

omit [CompleteSpace V] [CompleteSpace W] in
/-- The convolution integrand `(ζ, θ) ↦ ĉ(θ, 2πζ) v̂(ζ - θ)` is integrable. -/
private theorem HasCompactSpatialSupport.integrable_fourier_apply_sub
    (hc : c.HasCompactSpatialSupport) (v : 𝓢(CoordinateSpace n, V)) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun z ↦ c.coefficient (z, (2 * π) • q.1)) q.2 (𝓕 v (q.1 - q.2)))
        (volume.prod volume) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_fourier_le
  have hg : Integrable fun η : CoordinateSpace n ↦ (1 + ‖η‖ ^ 2) ^ (m / 2) * ‖𝓕 v η‖ :=
    (𝓕 v).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)
  have hconv := (integrable_decay (n := n)).convolution_integrand
    (ContinuousLinearMap.mul ℝ ℝ) hg (μ := volume) (ν := volume)
  have hcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun z ↦ c.coefficient (z, (2 * π) • q.1)) q.2 (𝓕 v (q.1 - q.2)) := by
    have h₁ := hc.continuous_fourier.comp (by fun_prop : Continuous
      fun q : CoordinateSpace n × CoordinateSpace n ↦
        ((q.2, (2 * π) • q.1) : CoordinateSpace n × CoordinateSpace n))
    simp only [Function.comp_def] at h₁
    exact h₁.clm_apply ((𝓕 v).continuous.comp (by fun_prop))
  refine (hconv.const_mul (C * (2 * π) ^ |m| * 2 ^ (|m| / 2))).mono' hcont.aestronglyMeasurable
    (.of_forall fun q ↦ ?_)
  obtain ⟨ζ, θ⟩ := q
  dsimp only
  simp only [ContinuousLinearMap.mul_apply']
  have hpeetre := one_add_norm_sq_rpow_le_mul_sub m ζ (ζ - θ)
  rw [sub_sub_cancel] at hpeetre
  have hw := weight_mul_decay_le (m := m) θ
  calc ‖𝓕 (fun z ↦ c.coefficient (z, (2 * π) • ζ)) θ (𝓕 v (ζ - θ))‖
      ≤ ‖𝓕 (fun z ↦ c.coefficient (z, (2 * π) • ζ)) θ‖ * ‖𝓕 v (ζ - θ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|)) * ((2 * π) ^ |m| *
          (2 ^ (|m| / 2) * (1 + ‖θ‖ ^ 2) ^ (|m| / 2) * (1 + ‖ζ - θ‖ ^ 2) ^ (m / 2))) *
          ‖𝓕 v (ζ - θ)‖ := by
        gcongr
        exact (hC θ _).trans (by gcongr; exact (weight_two_pi_smul_le m ζ).trans (by gcongr))
    _ = C * (2 * π) ^ |m| * 2 ^ (|m| / 2) * (((1 + ‖θ‖ ^ 2) ^ (|m| / 2) *
          (1 + ‖θ‖) ^ (-((n : ℝ) + 1 + |m|))) *
          ((1 + ‖ζ - θ‖ ^ 2) ^ (m / 2) * ‖𝓕 v (ζ - θ)‖)) := by ring
    _ ≤ C * (2 * π) ^ |m| * 2 ^ (|m| / 2) * ((1 + ‖θ‖) ^ (-((n : ℝ) + 1)) *
          ((1 + ‖ζ - θ‖ ^ 2) ^ (m / 2) * ‖𝓕 v (ζ - θ)‖)) := by gcongr

omit [CompleteSpace V] [CompleteSpace W] in
/-- The integrand `(η, θ) ↦ exp(2πi ⟪η, x⟫) (exp(2πi ⟪θ, x⟫) ĉ(θ, 2πη + 2πθ)) v̂(η)` of the
quantization of the left symbol is integrable. -/
private theorem HasCompactSpatialSupport.integrable_fourierChar_smul_rightIntegrand_apply
    (hc : c.HasCompactSpatialSupport) (v : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪q.1, x⟫ : ℂ) • rightIntegrand c.coefficient (x, (2 * π) • q.1) q.2 (𝓕 v q.1))
        (volume.prod volume) := by
  obtain ⟨C, hC0, hC⟩ := hc.exists_norm_rightIntegrand_le
  have hcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪q.1, x⟫ : ℂ) • rightIntegrand c.coefficient (x, (2 * π) • q.1) q.2 (𝓕 v q.1) := by
    have h₁ := hc.continuous_rightIntegrand.comp (by fun_prop : Continuous
      fun q : CoordinateSpace n × CoordinateSpace n ↦
        (((x, (2 * π) • q.1), q.2) : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n))
    simp only [Function.comp_def] at h₁
    exact (by fun_prop : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪q.1, x⟫ : ℂ)).smul (h₁.clm_apply ((𝓕 v).continuous.comp continuous_fst))
  have hf : Integrable fun η : CoordinateSpace n ↦
      C * (2 * π) ^ |m| * ((1 + ‖η‖ ^ 2) ^ (m / 2) * ‖𝓕 v η‖) :=
    ((𝓕 v).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)).const_mul _
  refine (hf.mul_prod integrable_decay).mono' hcont.aestronglyMeasurable
    (.of_forall fun q ↦ ?_)
  rw [norm_smul, Circle.norm_coe, one_mul]
  calc ‖rightIntegrand c.coefficient (x, (2 * π) • q.1) q.2 (𝓕 v q.1)‖
      ≤ ‖rightIntegrand c.coefficient (x, (2 * π) • q.1) q.2‖ * ‖𝓕 v q.1‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ((2 * π) ^ |m| * (1 + ‖q.1‖ ^ 2) ^ (m / 2)) * (1 + ‖q.2‖) ^ (-((n : ℝ) + 1)) *
          ‖𝓕 v q.1‖ := by
        gcongr
        exact (hC _ q.2).trans (by gcongr; exact weight_two_pi_smul_le m q.1)
    _ = C * (2 * π) ^ |m| * ((1 + ‖q.1‖ ^ 2) ^ (m / 2) * ‖𝓕 v q.1‖) *
          (1 + ‖q.2‖) ^ (-((n : ℝ) + 1)) := by ring

omit [CompleteSpace V] [CompleteSpace W] in
/-- The quantization of the left symbol as an iterated integral of the convolution
integrand. -/
private theorem HasCompactSpatialSupport.quantizeSchwartzValue_ofRight_eq
    (hc : c.HasCompactSpatialSupport) (v : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (c.ofRight hc).coefficient v x =
      ∫ ζ, 𝐞 ⟪ζ, x⟫ • ∫ θ, 𝓕 (fun z ↦ c.coefficient (z, (2 * π) • ζ)) θ (𝓕 v (ζ - θ)) := by
  set Φ : CoordinateSpace n × CoordinateSpace n → W := fun q ↦
    (𝐞 ⟪q.1, x⟫ : ℂ) • rightIntegrand c.coefficient (x, (2 * π) • q.1) q.2 (𝓕 v q.1) with hΦ
  have hΦint : Integrable Φ (volume.prod volume) :=
    hc.integrable_fourierChar_smul_rightIntegrand_apply v x
  have hΨ := hc.integrable_fourier_apply_sub v
  have hΨ' : Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦ (𝐞 ⟪q.1, x⟫ : ℂ) •
      𝓕 (fun z ↦ c.coefficient (z, (2 * π) • q.1)) q.2 (𝓕 v (q.1 - q.2)))
        (volume.prod volume) :=
    hΨ.norm.mono' ((by fun_prop : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪q.1, x⟫ : ℂ)).aestronglyMeasurable.smul hΨ.aestronglyMeasurable)
      (.of_forall fun q ↦ by rw [norm_smul, Circle.norm_coe, one_mul])
  calc quantizeSchwartzValue (c.ofRight hc).coefficient v x = ∫ η, ∫ θ, Φ (η, θ) := by
        rw [quantizeSchwartzValue_def]
        refine integral_congr_ae (.of_forall fun η ↦ ?_)
        dsimp only
        rw [coefficient_ofRight_eq_rightCoeff, rightCoeff,
          ContinuousLinearMap.integral_apply (hc.integrable_rightIntegrand _), Circle.smul_def,
          ← integral_smul]
    _ = ∫ θ, ∫ η, Φ (η, θ) := integral_integral_swap hΦint
    _ = ∫ θ, ∫ ζ, (𝐞 ⟪ζ, x⟫ : ℂ) •
          𝓕 (fun z ↦ c.coefficient (z, (2 * π) • ζ)) θ (𝓕 v (ζ - θ)) := by
        refine integral_congr_ae (.of_forall fun θ ↦ ?_)
        dsimp only
        rw [← integral_sub_right_eq_self _ θ]
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        simp only [hΦ, rightIntegrand, smul_apply, smul_smul, ← Circle.coe_mul,
          ← AddChar.map_add_eq_mul, ← smul_add, sub_add_cancel, inner_sub_left]
    _ = ∫ ζ, ∫ θ, (𝐞 ⟪ζ, x⟫ : ℂ) •
          𝓕 (fun z ↦ c.coefficient (z, (2 * π) • ζ)) θ (𝓕 v (ζ - θ)) :=
        (integral_integral_swap hΨ').symm
    _ = _ := by
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        dsimp only
        rw [Circle.smul_def, integral_smul]

/-- **The quantization of the left symbol is the right quantization.** For a symbol `c` with
compact spatial support and a Schwartz function `v`,
`Op(c.ofRight hc) v (x) = ∫ exp(2πi ⟪ζ, x⟫) 𝓕 (y ↦ c(y, 2πζ) v(y)) (ζ) dζ`, which in angular
frequency is the right quantization `(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) c(y, ξ) v(y) dy dξ`. -/
theorem quantizeSchwartzValue_ofRight (hc : c.HasCompactSpatialSupport)
    (v : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (c.ofRight hc).coefficient v x =
      ∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (fun y ↦ c.coefficient (y, (2 * π) • ζ) (v y)) ζ := by
  rw [hc.quantizeSchwartzValue_ofRight_eq]
  simp_rw [hc.fourier_apply_eq_integral]

/-- The frequency profile `ζ ↦ 𝓕 (y ↦ c(y, 2πζ) v(y)) (ζ)` of the right quantization of a symbol
with compact spatial support is integrable. -/
theorem HasCompactSpatialSupport.integrable_fourier_coefficient_apply
    (hc : c.HasCompactSpatialSupport) (v : 𝓢(CoordinateSpace n, V)) :
    Integrable fun ζ : CoordinateSpace n ↦
      𝓕 (fun y ↦ c.coefficient (y, (2 * π) • ζ) (v y)) ζ := by
  simp_rw [hc.fourier_apply_eq_integral]
  exact (hc.integrable_fourier_apply_sub v).integral_prod_left

end Quantization

end Symbol

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.RepresentationTheory.Continuous.Basic
public import TauCeti.Geometry.Lie.Exponential.Basic
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Geometry.Lie.Basic
import TauCeti.Geometry.Lie.Exponential.Smoothness
import TauCeti.MeasureTheory.Function.L1Space.Star

/-!
# Quantization of symbols on the Lie algebra of a Lie group

Let `G` be a Lie group modeled on its Lie algebra `E`, a finite-dimensional real inner-product
space, and let `π` be a representation of `G` on a complex normed space. A symbol `a` on the
imaginary dual of `E` acts on the representation by

`Op(a, χ) v = ∫ x, χ x a^∨(x) π (exp x) v dx`,

where `a^∨` is the inverse Fourier transform of `a` and `χ` is a cutoff near `0` (see
`TauCeti.IsQuantizationCutoff`). Writing a functional on `E` with values in `iℝ` as
`2πi⟪η, ·⟫` with `η ∈ E`, the symbol becomes a function `b : E → ℂ` and `a^∨` becomes Mathlib's
Fourier transform `𝓕 b`; in this coordinate the operator is `ContRepresentation.quantize π χ b`.
For a parameter `h > 0` the rescaled operator `Op_h(a, χ)` is the quantization of the dilated
symbol `fun η ↦ b (h • η)`.

This file records the basic properties of the quantization map: it is linear in the vector and in
the symbol, it vanishes on non-integrable symbols, it is bounded on a unitary representation by the
`L¹` norm of `χ 𝓕 b`, the rescaled operator is
`Op_h(a, χ) v = ∫ x, χ (h • x) 𝓕 b x π (exp (h • x)) v dx`, and for an even real cutoff the adjoint
of the quantization of `b` is the quantization of its complex conjugate `star b`.

## Main definitions

* `ContRepresentation.quantize π χ b v`: the quantization `∫ x, (χ x * 𝓕 b x) • π (exp x) v`.

## Main statements

* `ContRepresentation.integrable_quantize_integrand`: for an integrable symbol, a strongly
  continuous representation and a continuous compactly supported cutoff, the defining integrand is
  integrable.
* `ContRepresentation.quantize_add_left`, `ContRepresentation.quantize_smul_left`: linearity in the
  symbol; `ContRepresentation.quantize_add_right`, `ContRepresentation.quantize_smul_right`:
  linearity in the vector.
* `ContRepresentation.norm_quantize_le`: `‖Op(b, χ) v‖ ≤ (∫ x, |χ x| ‖𝓕 b x‖) ‖v‖` for a unitary
  representation.
* `ContRepresentation.quantize_comp_smul`: the change of variables for the rescaled operator.
* `ContRepresentation.inner_quantize_left`: `⟪Op(b, χ) v, w⟫ = ⟪v, Op(star b, χ) w⟫` for a
  strongly continuous unitary representation and an even continuous compactly supported cutoff.

## References

* P. D. Nelson, A. Venkatesh, *The orbit method and analysis of automorphic forms*, Acta Math.
  226 (2021), §§2.1–2.5 and Lemma 8.8.
-/

public section

open MeasureTheory
open scoped ComplexConjugate ContDiff FourierTransform InnerProductSpace Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

namespace ContRepresentation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
  [T2Space G]

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (π : ContRepresentation ℂ G V) (χ : E → ℝ)

/-- The **quantization** of a symbol `b : E → ℂ` against the cutoff `χ` (Nelson–Venkatesh (2.1)):
`π.quantize χ b v = ∫ x, (χ x * 𝓕 b x) • π (exp x) v`, the integral over the Lie algebra `E` with
its inner-product Lebesgue measure and `exp` the exponential map `mulInvariantExp` of `G`. The
symbol is written in the coordinate `ξ = 2πi⟪η, ·⟫` of the imaginary dual, in which the inverse
Fourier transform of the symbol is Mathlib's Fourier transform `𝓕 b`. The rescaled operator
`Op_h(b, χ)` is `π.quantize χ (fun η ↦ b (h • η))`. -/
noncomputable def quantize (b : E → ℂ) (v : V) : V :=
  ∫ x : E, ((χ x : ℂ) * 𝓕 b x) • π (mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) x) v

/-- Unfolding the quantization into its defining integral. -/
theorem quantize_def (b : E → ℂ) (v : V) :
    π.quantize χ b v =
      ∫ x : E, ((χ x : ℂ) * 𝓕 b x) • π (mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) x) v :=
  (rfl)

/-- The integrand of the quantization of an integrable symbol is integrable, for a strongly
continuous representation and a continuous compactly supported cutoff. -/
theorem integrable_quantize_integrand (hπ : ∀ v, Continuous fun g ↦ π g v)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) {b : E → ℂ} (hb : Integrable b) (v : V) :
    Integrable fun x : E ↦
      ((χ x : ℂ) * 𝓕 b x) • π (mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) x) v := by
  have hexp : Continuous fun x : E ↦ mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) x :=
    (contMDiff_mulInvariantExp (I := 𝓘(ℝ, E)) (G := G)).continuous
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact ((Complex.continuous_ofReal.comp hχ).mul hb.continuous_fourier).smul ((hπ v).comp hexp)
  · exact ((hχc.comp_left Complex.ofReal_zero).mul_right).smul_right

/-- The quantization of a non-integrable symbol vanishes, since its Fourier transform does. -/
theorem quantize_of_not_integrable {b : E → ℂ} (hb : ¬Integrable b) (v : V) :
    π.quantize χ b v = 0 := by
  simp [quantize_def, Real.fourier_eq_zero_of_not_integrable hb]

/-- The quantization of the zero symbol vanishes. -/
@[simp]
theorem quantize_zero_left (v : V) : π.quantize χ 0 v = 0 := by
  simp [quantize_def, Real.fourier_eq]

/-- The quantization of a symbol vanishes on the zero vector. -/
@[simp]
theorem quantize_zero_right (b : E → ℂ) : π.quantize χ b 0 = 0 := by
  simp [quantize_def]

/-- The quantization is homogeneous in the symbol. -/
theorem quantize_smul_left (c : ℂ) (b : E → ℂ) (v : V) :
    π.quantize χ (c • b) v = c • π.quantize χ b v := by
  simp only [quantize_def, Real.fourier_const_smul, Pi.smul_apply, smul_eq_mul, ← integral_smul,
    mul_left_comm _ c, mul_smul]

/-- The quantization is homogeneous in the vector. -/
theorem quantize_smul_right (b : E → ℂ) (c : ℂ) (v : V) :
    π.quantize χ b (c • v) = c • π.quantize χ b v := by
  simp only [quantize_def, map_smul, ← integral_smul, smul_comm c]

/-- The quantization is additive in the symbol, for integrable symbols, a strongly continuous
representation and a continuous compactly supported cutoff. -/
theorem quantize_add_left (hπ : ∀ v, Continuous fun g ↦ π g v) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) {b₁ b₂ : E → ℂ} (hb₁ : Integrable b₁) (hb₂ : Integrable b₂)
    (v : V) : π.quantize χ (b₁ + b₂) v = π.quantize χ b₁ v + π.quantize χ b₂ v := by
  simp only [quantize_def, hb₁.fourier_add hb₂]
  rw [← integral_add (π.integrable_quantize_integrand χ hπ hχ hχc hb₁ v)
    (π.integrable_quantize_integrand χ hπ hχ hχc hb₂ v)]
  simp only [Pi.add_apply, mul_add, add_smul]

/-- The quantization is additive in the vector, for a strongly continuous representation and a
continuous compactly supported cutoff. -/
theorem quantize_add_right (hπ : ∀ v, Continuous fun g ↦ π g v) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (b : E → ℂ) (v w : V) :
    π.quantize χ b (v + w) = π.quantize χ b v + π.quantize χ b w := by
  by_cases hb : Integrable b
  · simp only [quantize_def, map_add, smul_add]
    exact integral_add (π.integrable_quantize_integrand χ hπ hχ hχc hb v)
      (π.integrable_quantize_integrand χ hπ hχ hχc hb w)
  · simp [π.quantize_of_not_integrable χ hb]

/-- **The rescaled quantization**: for `h ≠ 0`, the quantization of the dilated symbol
`fun η ↦ b (h • η)` is `∫ x, (χ (h • x) * 𝓕 b x) • π (exp (h • x)) v`. This is the formula
`Op_h(a, χ) = ∫ χ(hx) a^∨(x) π(exp(hx)) dx` of Nelson–Venkatesh (2.2). -/
theorem quantize_comp_smul (b : E → ℂ) {h : ℝ} (hh : h ≠ 0) (v : V) :
    π.quantize χ (fun η ↦ b (h • η)) v =
      ∫ x : E, ((χ (h • x) : ℂ) * 𝓕 b x) •
        π (mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) (h • x)) v := by
  -- Change variables `y = h • x` in the integral of `(χ y * 𝓕 b (h⁻¹ • y)) • π (exp y) v`.
  have hcv := Measure.integral_comp_smul (volume : Measure E) (fun y : E ↦
    ((χ y : ℂ) * 𝓕 b (h⁻¹ • y)) • π (mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) y) v) h
  simp only [inv_smul_smul₀ hh, abs_inv] at hcv
  simp only [quantize_def, TauCeti.fourier_comp_smul b h]
  rw [hcv, ← integral_smul]
  simp only [mul_smul_comm, smul_assoc]

end NormedSpace

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (π : ContRepresentation ℂ G V) (χ : E → ℝ)

/-- **The `L¹` bound** (Nelson–Venkatesh, Lemma 8.8): on a unitary representation,
`‖Op(b, χ) v‖ ≤ (∫ x, |χ x| ‖𝓕 b x‖) ‖v‖`. -/
theorem norm_quantize_le (hπ : π.IsUnitary) (b : E → ℂ) (v : V) :
    ‖π.quantize χ b v‖ ≤ (∫ x : E, |χ x| * ‖𝓕 b x‖) * ‖v‖ := by
  rw [← integral_mul_const, quantize_def]
  refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (.of_forall fun x ↦ ?_))
  simp [norm_smul, hπ.norm_map]

/-- **The adjoint of a quantization** (Nelson–Venkatesh, §2.3): for a strongly continuous unitary
representation and an even continuous compactly supported cutoff, the adjoint of the quantization
of `b` is the quantization of its complex conjugate,
`⟪π.quantize χ b v, w⟫ = ⟪v, π.quantize χ (star b) w⟫`. In particular a real symbol quantizes to a
symmetric operator. -/
theorem inner_quantize_left [CompleteSpace V] (hπ : π.IsUnitary)
    (hπc : ∀ v, Continuous fun g ↦ π g v) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hχe : χ.Even) (b : E → ℂ) (v w : V) :
    ⟪π.quantize χ b v, w⟫_ℂ = ⟪v, π.quantize χ (star b) w⟫_ℂ := by
  by_cases hb : Integrable b
  · have hb' : Integrable (star b) := integrable_star_iff.2 hb
    rw [quantize_def, quantize_def, ← inner_conj_symm,
      ← integral_inner (π.integrable_quantize_integrand χ hπc hχ hχc hb v),
      ← integral_inner (π.integrable_quantize_integrand χ hπc hχ hχc hb' w), ← integral_conj,
      ← integral_neg_eq_self]
    congr 1 with x
    -- The substitution `x ↦ -x` uses the negation of `E`; restate the inverse law of the
    -- exponential for it.
    have hneg : mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) (-x : E) =
        (mulInvariantExp (I := 𝓘(ℝ, E)) (G := G) x)⁻¹ :=
      mulInvariantExp_neg _
    simp only [inner_smul_right, map_mul, inner_conj_symm, hπ.inner_map_left, hχe x, hneg, inv_inv,
      Real.fourier_star_apply, Complex.conj_ofReal]
  · have hb' : ¬Integrable (star b) := integrable_star_iff.not.2 hb
    simp [π.quantize_of_not_integrable χ hb, π.quantize_of_not_integrable χ hb']

end InnerProductSpace

end ContRepresentation

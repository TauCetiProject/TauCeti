/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.RightQuantization
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Instances.RealVectorSpace
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Adjoint symbols

The formal adjoint of the left (Kohn–Nirenberg) quantization
`Op(a) u (x) = (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) a(x, ξ) u(y) dy dξ` of a symbol `a` with values in
operators between complex Hilbert spaces `V` and `W` is the right quantization of the pointwise
Hilbert space adjoint `a(y, ξ)†`. For `a` of order `m` with compact spatial support, its left
symbol (`TauCeti.Symbol.ofRight`) is the adjoint symbol

`a*(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) b̂(θ, ξ + 2πθ) dθ`,

where `b̂(θ, ξ)` is the Fourier transform of the position slice `z ↦ a(z, ξ)†`. It is a symbol of
order `m` with estimates uniform in the position, and `Op(a)* = Op(a*)` on Schwartz functions.

## Main declarations

* `TauCeti.Symbol.adjoint`: the adjoint symbol `a*`, with its formula
  `TauCeti.Symbol.coefficient_adjoint`.
* `TauCeti.Symbol.integral_inner_quantizeSchwartzValue_adjoint`:
  `∫ ⟪Op(a) u (x), v(x)⟫ dx = ∫ ⟪u(x), Op(a*) v (x)⟫ dx` for Schwartz functions `u` and `v`.

Both pairings are computed on the Fourier side, where they become `∫ ⟪û(ζ), ĝ(ζ)⟫ dζ` for the
Fourier transform `ĝ(ζ)` of `y ↦ a(y, 2πζ)† v(y)` at `ζ`.

The asymptotic expansion `a* ∼ ∑_α (1/α!) ∂_ξ^α D_x^α a†` of the adjoint symbol is not developed
here.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1,
  Theorem 18.1.7.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped RealInnerProductSpace SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### The adjoint symbol -/

section Adjoint

open scoped InnerProduct InnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The Hilbert space adjoint `A ↦ A†`, which is conjugate-linear over `ℂ`, as a real-linear
map. -/
private def adjointCLM : (V →L[ℂ] W) →L[ℝ] (W →L[ℂ] V) :=
  AddMonoidHom.toRealLinearMap
    (ContinuousLinearMap.adjoint : (V →L[ℂ] W) ≃ₗᵢ⋆[ℂ] (W →L[ℂ] V)).toLinearEquiv.toAddMonoidHom
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := V) (F := W)).continuous

private theorem adjointCLM_apply (A : V →L[ℂ] W) : adjointCLM A = A† :=
  (rfl)

/-- **The adjoint symbol.** For a symbol `a` of order `m` with compact spatial support and values
in operators between complex Hilbert spaces, the symbol
`a*(x, ξ) = ∫ exp(2πi ⟪θ, x⟫) b̂(θ, ξ + 2πθ) dθ`, where `b̂(θ, ξ)` is the Fourier transform of
the position slice `z ↦ a(z, ξ)†` of the pointwise Hilbert space adjoint. It is the left symbol of
the right quantization of `a†` (`TauCeti.Symbol.ofRight`), a symbol of order `m` with estimates
uniform in the position, and its quantization is the formal adjoint of the quantization of `a`
(`TauCeti.Symbol.integral_inner_quantizeSchwartzValue_adjoint`). -/
def adjoint (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) : Symbol n W V m :=
  (a.map adjointCLM).ofRight (ha.map _)

variable {a : Symbol n V W m}

@[simp]
theorem coefficient_adjoint (ha : a.HasCompactSpatialSupport) (x ξ : CoordinateSpace n) :
    (a.adjoint ha).coefficient (x, ξ) =
      ∫ θ, (𝐞 ⟪θ, x⟫ : ℂ) • 𝓕 (fun z ↦ (a.coefficient (z, ξ + (2 * π) • θ))†) θ := by
  simp only [adjoint, coefficient_ofRight, coefficient_map, adjointCLM_apply]

/-- The adjoint symbol satisfies its estimates uniformly in the position. -/
theorem isUniform_adjoint (ha : a.HasCompactSpatialSupport) : (a.adjoint ha).IsUniform :=
  isUniform_ofRight _

/-- The integrand `(x, ζ) ↦ ⟪û(ζ), exp(-2πi ⟪x, ζ⟫) a(x, 2πζ)† v(x)⟫` of the pairing
`∫ ⟪Op(a) u, v⟫` is integrable. -/
private theorem HasCompactSpatialSupport.integrable_inner_fourierChar_smul_adjoint_apply
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      ⟪𝓕 u q.2, (𝐞 (-⟪q.1, q.2⟫) : ℂ) • ((a.coefficient (q.1, (2 * π) • q.2))†) (v q.1)⟫_ℂ)
        (volume.prod volume) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  obtain ⟨C, hC0, hC⟩ := a.exists_bound_coefficient K hK
  have hK1 : Integrable (K.indicator fun _ ↦ C * SchwartzMap.seminorm ℂ 0 0 v) :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  have hf : Integrable fun ζ : CoordinateSpace n ↦
      (2 * π) ^ |m| * ((1 + ‖ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖) :=
    ((𝓕 u).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)).const_mul _
  have hcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      ⟪𝓕 u q.2, (𝐞 (-⟪q.1, q.2⟫) : ℂ) • ((a.coefficient (q.1, (2 * π) • q.2))†) (v q.1)⟫_ℂ := by
    have h₁ : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
        (a.map adjointCLM).coefficient (q.1, (2 * π) • q.2) :=
      (a.map adjointCLM).contDiff_coefficient.continuous.comp (by fun_prop)
    simp only [coefficient_map, adjointCLM_apply] at h₁
    exact ((𝓕 u).continuous.comp continuous_snd).inner ((by fun_prop : Continuous
      fun q : CoordinateSpace n × CoordinateSpace n ↦ (𝐞 (-⟪q.1, q.2⟫) : ℂ)).smul
        (h₁.clm_apply (v.continuous.comp continuous_fst)))
  refine (hK1.mul_prod hf).mono' hcont.aestronglyMeasurable (.of_forall fun q ↦ ?_)
  obtain ⟨x, ζ⟩ := q
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [norm_smul, Circle.norm_coe, one_mul]
    have hcx : ‖(a.coefficient (x, (2 * π) • ζ))†‖ ≤
        C * ((2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) := by
      rw [LinearIsometryEquiv.norm_map]
      exact (hC x hx _).trans (by
        gcongr
        exact one_add_norm_sq_rpow_le_of_norm_eq_mul (by linarith [Real.two_le_pi]) m
          (by rw [norm_smul, Real.norm_of_nonneg Real.two_pi_pos.le]))
    calc ‖𝓕 u ζ‖ * ‖((a.coefficient (x, (2 * π) • ζ))†) (v x)‖
        ≤ ‖𝓕 u ζ‖ * (‖(a.coefficient (x, (2 * π) • ζ))†‖ * ‖v x‖) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖𝓕 u ζ‖ * (C * ((2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) *
            SchwartzMap.seminorm ℂ 0 0 v) := by
          gcongr
          exact SchwartzMap.norm_le_seminorm ℂ v x
      _ = C * SchwartzMap.seminorm ℂ 0 0 v *
            ((2 * π) ^ |m| * ((1 + ‖ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖)) := by ring
  · simp only [hKa x hx, map_zero, zero_apply, smul_zero, inner_zero_right, norm_zero]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ ↦ by positivity) _) (by positivity)

/-- The pairing `∫ ⟪Op(a) u, v⟫` on the Fourier side: it is `∫ ⟪û(ζ), ĝ(ζ)⟫ dζ` for the Fourier
transform `ĝ(ζ)` of `y ↦ a(y, 2πζ)† v(y)` at `ζ`. -/
private theorem HasCompactSpatialSupport.integral_inner_quantizeSchwartzValue
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, ⟪quantizeSchwartzValue a.coefficient u x, v x⟫_ℂ =
      ∫ ζ, ⟪𝓕 u ζ, 𝓕 (fun y ↦ ((a.coefficient (y, (2 * π) • ζ))†) (v y)) ζ⟫_ℂ := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  have hint (x : CoordinateSpace n) :
      Integrable fun ζ ↦ 𝐞 ⟪ζ, x⟫ • a.coefficient (x, (2 * π) • ζ) (𝓕 u ζ) := by
    obtain ⟨C, -, hC⟩ := isUniform_iff.mp ha.isUniform [] []
    exact integrable_quantizeSchwartzValue_integrand
      (a.continuous_coefficient_slice x).aestronglyMeasurable
      (fun ξ ↦ by simpa using hC x ξ) (𝓕 u)
  calc ∫ x, ⟪quantizeSchwartzValue a.coefficient u x, v x⟫_ℂ
      = ∫ x, ∫ ζ, ⟪𝓕 u ζ, (𝐞 (-⟪x, ζ⟫) : ℂ) •
          ((a.coefficient (x, (2 * π) • ζ))†) (v x)⟫_ℂ := by
        -- Move the adjoint and the conjugate character to the right slot.
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        rw [quantizeSchwartzValue_def, ← integral_inner_left (hint x)]
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        simp only [Circle.smul_def, inner_smul_left, inner_smul_right,
          ContinuousLinearMap.adjoint_inner_right, ← Circle.coe_inv_eq_conj,
          ← AddChar.map_neg_eq_inv, real_inner_comm]
      _ = ∫ ζ, ∫ x, ⟪𝓕 u ζ, (𝐞 (-⟪x, ζ⟫) : ℂ) •
          ((a.coefficient (x, (2 * π) • ζ))†) (v x)⟫_ℂ :=
        integral_integral_swap (ha.integrable_inner_fourierChar_smul_adjoint_apply u v)
      _ = _ := by
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        have hcv : Integrable fun x ↦
            (𝐞 (-⟪x, ζ⟫) : ℂ) • ((a.coefficient (x, (2 * π) • ζ))†) (v x) := by
          have h₁ := ((a.map adjointCLM).contDiff_coefficient_slice ((2 * π) • ζ)).continuous
          simp only [coefficient_map, adjointCLM_apply] at h₁
          refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK
            fun x hx ↦ by simp [hKa x hx])
          exact (by fun_prop : Continuous fun x : CoordinateSpace n ↦ (𝐞 (-⟪x, ζ⟫) : ℂ)).smul
            (h₁.clm_apply v.continuous)
        dsimp only
        rw [integral_inner hcv, Real.fourier_eq]
        simp only [Circle.smul_def]

/-- The pairing `∫ ⟪u, Op(c.ofRight hc) v⟫` on the Fourier side: it is `∫ ⟪û(ζ), ĝ(ζ)⟫ dζ` for
the Fourier transform `ĝ(ζ)` of `y ↦ c(y, 2πζ) v(y)` at `ζ`. -/
private theorem HasCompactSpatialSupport.integral_inner_quantizeSchwartzValue_ofRight
    {c : Symbol n W V m} (hc : c.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, ⟪u x, quantizeSchwartzValue (c.ofRight hc).coefficient v x⟫_ℂ =
      ∫ ζ, ⟪𝓕 u ζ, 𝓕 (fun y ↦ c.coefficient (y, (2 * π) • ζ) (v y)) ζ⟫_ℂ := by
  set g : CoordinateSpace n → V := fun ζ ↦
    𝓕 (fun y ↦ c.coefficient (y, (2 * π) • ζ) (v y)) ζ with hg_def
  have hg : Integrable g := hc.integrable_fourier_coefficient_apply v
  have hgx (x : CoordinateSpace n) : Integrable fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ) • g ζ :=
    hg.norm.mono' ((by fun_prop : Continuous fun ζ : CoordinateSpace n ↦
      (𝐞 ⟪ζ, x⟫ : ℂ)).aestronglyMeasurable.smul hg.aestronglyMeasurable)
      (.of_forall fun ζ ↦ by rw [norm_smul, Circle.norm_coe, one_mul])
  have hGint : Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      ⟪u q.1, (𝐞 ⟪q.2, q.1⟫ : ℂ) • g q.2⟫_ℂ) (volume.prod volume) := by
    refine (u.integrable.norm.mul_prod hg.norm).mono' ?_ (.of_forall fun q ↦ ?_)
    · exact (u.continuous.comp continuous_fst).aestronglyMeasurable.inner
        ((by fun_prop : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
          (𝐞 ⟪q.2, q.1⟫ : ℂ)).aestronglyMeasurable.smul hg.aestronglyMeasurable.comp_snd)
    · refine (norm_inner_le_norm _ _).trans ?_
      rw [norm_smul, Circle.norm_coe, one_mul]
  calc ∫ x, ⟪u x, quantizeSchwartzValue (c.ofRight hc).coefficient v x⟫_ℂ
      = ∫ x, ∫ ζ, ⟪u x, (𝐞 ⟪ζ, x⟫ : ℂ) • g ζ⟫_ℂ := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        rw [quantizeSchwartzValue_ofRight, integral_inner (hgx x)]
        simp only [hg_def, Circle.smul_def]
    _ = ∫ ζ, ∫ x, ⟪u x, (𝐞 ⟪ζ, x⟫ : ℂ) • g ζ⟫_ℂ := integral_integral_swap hGint
    _ = ∫ ζ, ⟪𝓕 u ζ, g ζ⟫_ℂ := by
        -- The `x`-integral is the Fourier transform of `u`, paired with `g ζ`.
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        have hu : Integrable fun x ↦ (𝐞 (-⟪x, ζ⟫) : ℂ) • u x :=
          u.integrable.norm.mono' ((by fun_prop : Continuous fun x : CoordinateSpace n ↦
            (𝐞 (-⟪x, ζ⟫) : ℂ)).smul u.continuous).aestronglyMeasurable
            (.of_forall fun x ↦ by rw [norm_smul, Circle.norm_coe, one_mul])
        dsimp only
        rw [SchwartzMap.fourier_coe, Real.fourier_eq]
        simp_rw [Circle.smul_def]
        rw [← integral_inner_left hu]
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        rw [inner_smul_left, inner_smul_right, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv,
          neg_neg, real_inner_comm]

/-- **The quantization of the adjoint symbol is the formal adjoint.** For a symbol `a` with
compact spatial support between complex Hilbert spaces `V` and `W`, and Schwartz functions `u` and
`v`, `∫ ⟪Op(a) u (x), v(x)⟫ dx = ∫ ⟪u(x), Op(a*) v (x)⟫ dx`. -/
theorem integral_inner_quantizeSchwartzValue_adjoint (ha : a.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, ⟪quantizeSchwartzValue a.coefficient u x, v x⟫_ℂ =
      ∫ x, ⟪u x, quantizeSchwartzValue (a.adjoint ha).coefficient v x⟫_ℂ := by
  rw [ha.integral_inner_quantizeSchwartzValue, adjoint,
    (ha.map adjointCLM).integral_inner_quantizeSchwartzValue_ofRight]
  simp only [coefficient_map, adjointCLM_apply]

end Adjoint

end Symbol

end TauCeti

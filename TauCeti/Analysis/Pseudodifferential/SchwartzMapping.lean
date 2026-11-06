/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Quantizations of uniform symbols map Schwartz space to itself

For a symbol `a ∈ S^m_{1,0}` whose estimates `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α β} ⟨ξ⟩^(m - |β|)` hold
uniformly in the position `x` (`TauCeti.Symbol.IsUniform`), the Kohn–Nirenberg quantization
`Op(a) u (x) = ∫ exp(2πi ⟪x, ζ⟫) a(x, 2πζ) (𝓕 u ζ) dζ` sends Schwartz functions to Schwartz
functions, continuously (`TauCeti.Symbol.quantizeUniformCLM`). Quantizations of uniform symbols
can therefore be composed as operators on Schwartz space, which is the setting of the uniform
symbol calculus.

The proof rests on two commutator formulas. A derivative of `Op(a) u` falls either on the input or
on the position variable of the symbol, `∂_j (Op(a) u) = Op(a) (∂_j u) + Op(∂_{x_j} a) u`
(`TauCeti.Symbol.coordinateDeriv_quantizeSchwartzValue`). Dually, multiplying by a coordinate
function falls either on the input or on the frequency variable of the symbol:

`x_j Op(a) u = Op(a) (x_j u) + i Op(∂_{ξ_j} a) u`

(`TauCeti.Symbol.ofLp_smul_quantizeSchwartzValue`). It comes from an integration by parts in the
frequency, since `x_j exp(2πi ⟪x, ζ⟫)` is a frequency derivative of `exp(2πi ⟪x, ζ⟫)` and
multiplication by `x_j` is a frequency derivative on the Fourier side. The general form, for a
direction `v` and a coefficient differentiable in the frequency, is
`TauCeti.inner_smul_quantizeSchwartzValue`.

Both formulas keep the class of uniform symbols, with spatial derivatives keeping the order and
frequency derivatives lowering it. Iterating them writes every `x^γ ∂^α (Op(a) u)` as a finite sum
of terms `Op(b) (L u)`, with `b` a uniform symbol and `L` a continuous operator on Schwartz space,
and each such term is bounded by a continuous seminorm of `u`
(`TauCeti.quantizeSchwartzCLM`).

## Main results

* `TauCeti.inner_smul_quantizeSchwartzValue`: `⟪x, v⟫ Op(a) u (x) = Op(a) (⟪·, v⟫ u) (x) +
  i Op(∂_{ξ, v} a) u (x)`.
* `TauCeti.Symbol.quantizeUniformCLM`: the quantization of a uniform symbol as a continuous linear
  map `𝓢(ℝⁿ, V) →L[ℂ] 𝓢(ℝⁿ, W)`.
* `TauCeti.Symbol.lineDerivOp_quantizeUniformCLM`,
  `TauCeti.Symbol.smulLeftCLM_quantizeUniformCLM`: the two commutator formulas in Schwartz space.
* `TauCeti.Symbol.quantizeUniformCLM_const`: a constant symbol `T` quantizes to the composition
  with `T`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.6.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace LineDeriv ContDiff
open MeasureTheory Real FourierTransform

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

section Weight

/-! ### Multiplication by a linear function -/

variable {a : E × E → V →L[ℂ] W} {x : E} {C C' m m' : ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The line derivative of the phase `ζ ↦ exp(2πi ⟪ζ, x⟫)` in the direction `v`. -/
private lemma hasLineDerivAt_fourierChar_inner (x v ζ : E) :
    HasLineDerivAt ℝ (fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ))
      ((2 * π * Complex.I * ⟪v, x⟫) * 𝐞 ⟪ζ, x⟫) ζ v := by
  have h : HasDerivAt (fun t : ℝ ↦ ⟪ζ, x⟫ + t * ⟪v, x⟫) ⟪v, x⟫ 0 := by
    simpa using (hasDerivAt_mul_const ⟪v, x⟫).const_add ⟪ζ, x⟫
  have h' := (Real.hasDerivAt_fourierChar (⟪ζ, x⟫ + 0 * ⟪v, x⟫)).scomp 0 h
  simp only [zero_mul, add_zero] at h'
  unfold HasLineDerivAt
  convert h' using 1
  · funext t
    simp [inner_add_left, inner_smul_left]
  · rw [Complex.real_smul]
    ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The line derivative in the direction `v` of the frequency-side integrand
`ζ ↦ a(x, 2πζ) (f ζ)`. -/
private lemma hasLineDerivAt_apply (ha : ContDiff ℝ 1 fun ξ ↦ a (x, ξ)) (f : 𝓢(E, V)) (v ζ : E) :
    HasLineDerivAt ℝ (fun ζ ↦ a (x, (2 * π) • ζ) (f ζ))
      ((2 * π) • fderiv ℝ (fun ξ ↦ a (x, ξ)) ((2 * π) • ζ) v (f ζ) +
        a (x, (2 * π) • ζ) (∂_{v} f ζ)) ζ v := by
  have hA : HasFDerivAt (fun ζ : E ↦ a (x, (2 * π) • ζ))
      ((fderiv ℝ (fun ξ ↦ a (x, ξ)) ((2 * π) • ζ)).comp ((2 * π) • ContinuousLinearMap.id ℝ E))
      ζ :=
    ((ha.differentiable one_ne_zero _).hasFDerivAt).comp ζ
      ((hasFDerivAt_id ζ).const_smul (2 * π))
  have hf : HasFDerivAt (fun ζ ↦ f ζ) (fderiv ℝ f ζ) ζ :=
    (f.differentiableAt).hasFDerivAt
  have hA' := ((ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ).hasFDerivAt).comp ζ hA
  convert (hA'.clm_apply hf).hasLineDerivAt v using 1
  · simp
  · simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, add_comm]

/-- The integration by parts behind `inner_smul_quantizeSchwartzValue`, before dividing by
`-2πi`. -/
private lemma integral_by_parts_quantizeSchwartzValue (ha : ContDiff ℝ 1 fun ξ ↦ a (x, ξ))
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (v : E)
    (hC' : ∀ ξ, ‖fderiv ℝ (fun η ↦ a (x, η)) ξ v‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    (u : 𝓢(E, V)) :
    (2 * π : ℂ) • quantizeSchwartzValue (fun p ↦ fderiv ℝ (fun η ↦ a (p.1, η)) p.2 v) u x +
      (-(2 * π * Complex.I)) • quantizeSchwartzValue a (SchwartzMap.smulLeftCLM V (⟪·, v⟫) u) x =
      -((2 * π * Complex.I * ⟪v, x⟫) • quantizeSchwartzValue a u x) := by
  set a' : E × E → V →L[ℂ] W := fun p ↦ fderiv ℝ (fun η ↦ a (p.1, η)) p.2 v
  have hmeas : AEStronglyMeasurable (fun ξ ↦ a (x, ξ)) := ha.continuous.aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun ξ ↦ a' (x, ξ)) :=
    ((ha.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
  have hint := integrable_quantizeSchwartzValue_integrand hmeas hC (𝓕 u)
  have hint₁ := integrable_quantizeSchwartzValue_integrand (a := a') hmeas' hC' (𝓕 u)
  have hint₂ := integrable_quantizeSchwartzValue_integrand hmeas hC (∂_{v} (𝓕 u))
  -- integrate by parts in the frequency, moving the derivative from the phase to the rest
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.lsmul ℝ ℂ (E := W))
    (f := fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ)) (f' := fun ζ ↦ (2 * π * Complex.I * ⟪v, x⟫) * 𝐞 ⟪ζ, x⟫)
    (g := fun ζ ↦ a (x, (2 * π) • ζ) (𝓕 u ζ))
    (g' := fun ζ ↦ (2 * π) • a' (x, (2 * π) • ζ) (𝓕 u ζ) +
      a (x, (2 * π) • ζ) (∂_{v} (𝓕 u) ζ))
    ((hint.smul (2 * π * Complex.I * ⟪v, x⟫ : ℂ)).congr (ae_of_all _ fun ζ ↦ by
      simp [Circle.smul_def, mul_smul]))
    (((hint₁.smul (2 * π)).add hint₂).congr (ae_of_all _ fun ζ ↦ by
      simp [Circle.smul_def, smul_add, smul_comm (2 * π)]))
    (hint.congr (ae_of_all _ fun ζ ↦ by simp [Circle.smul_def]))
    (fun ζ _ ↦ hasLineDerivAt_fourierChar_inner x v ζ)
    (fun ζ _ ↦ hasLineDerivAt_apply ha (𝓕 u) v ζ)
  have h₁ : ∫ ζ, ContinuousLinearMap.lsmul ℝ ℂ (𝐞 ⟪ζ, x⟫ : ℂ)
      ((2 * π) • a' (x, (2 * π) • ζ) (𝓕 u ζ) + a (x, (2 * π) • ζ) (∂_{v} (𝓕 u) ζ)) =
      (2 * π : ℂ) • (∫ ζ, 𝐞 ⟪ζ, x⟫ • a' (x, (2 * π) • ζ) (𝓕 u ζ)) +
        ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (∂_{v} (𝓕 u) ζ) := by
    calc _ = ∫ ζ, (2 * π : ℂ) • (𝐞 ⟪ζ, x⟫ • a' (x, (2 * π) • ζ) (𝓕 u ζ)) +
          𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (∂_{v} (𝓕 u) ζ) :=
          integral_congr_ae (ae_of_all _ fun ζ ↦ by
            simp [Circle.smul_def, smul_add, smul_comm (2 * π : ℂ), ← Complex.coe_smul])
      _ = _ := by
        have hint₁' : Integrable fun ζ ↦ (2 * π : ℂ) • (𝐞 ⟪ζ, x⟫ • a' (x, (2 * π) • ζ) (𝓕 u ζ)) :=
          hint₁.smul _
        rw [integral_add hint₁' hint₂, integral_smul]
  have h₂ : ∫ ζ, ContinuousLinearMap.lsmul ℝ ℂ ((2 * π * Complex.I * ⟪v, x⟫) * 𝐞 ⟪ζ, x⟫)
      (a (x, (2 * π) • ζ) (𝓕 u ζ)) =
      (2 * π * Complex.I * ⟪v, x⟫) • ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (𝓕 u ζ) := by
    rw [← integral_smul]
    exact integral_congr_ae (ae_of_all _ fun ζ ↦ by simp [Circle.smul_def, mul_smul])
  rw [h₁, h₂] at hibp
  rw [← quantizeSchwartzValue_smul_right (-(2 * π * Complex.I) : ℂ), quantizeSchwartzValue_def,
    quantizeSchwartzValue_def, quantizeSchwartzValue_def, ← SchwartzMap.lineDerivOp_fourier_eq]
  exact hibp

/-- **Multiplication by a linear function.** If `ξ ↦ a(x, ξ)` is `C¹`, and it and its frequency
derivative in the direction `v` have polynomial growth, then

`⟪x, v⟫ Op(a) u (x) = Op(a) (⟪·, v⟫ u) (x) + i Op(∂_{ξ, v} a) u (x)`,

where `∂_{ξ, v} a (x, ξ) = D_ξ a (x, ξ) v` is the derivative of the coefficient in the frequency.
This is an integration by parts in the frequency: `⟪x, v⟫ exp(2πi ⟪ζ, x⟫)` is a multiple of the
derivative of the phase in the direction `v`, and multiplication of the input by `⟪·, v⟫`
corresponds to the derivative of its Fourier transform in the direction `v`. -/
theorem inner_smul_quantizeSchwartzValue (ha : ContDiff ℝ 1 fun ξ ↦ a (x, ξ))
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (v : E)
    (hC' : ∀ ξ, ‖fderiv ℝ (fun η ↦ a (x, η)) ξ v‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    (u : 𝓢(E, V)) :
    ⟪x, v⟫ • quantizeSchwartzValue a u x =
      quantizeSchwartzValue a (SchwartzMap.smulLeftCLM V (⟪·, v⟫) u) x +
        Complex.I • quantizeSchwartzValue (fun p ↦ fderiv ℝ (fun η ↦ a (p.1, η)) p.2 v) u x := by
  have key := integral_by_parts_quantizeSchwartzValue ha hC v hC' u
  set a' : E × E → V →L[ℂ] W := fun p ↦ fderiv ℝ (fun η ↦ a (p.1, η)) p.2 v
  -- divide `key` by `-2πi`
  have h2πI : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hII : 2 * π * Complex.I * Complex.I = -(2 * π : ℂ) := by
    rw [mul_assoc, Complex.I_mul_I]
    ring
  refine smul_right_injective W h2πI ?_
  beta_reduce
  calc (2 * π * Complex.I) • ⟪x, v⟫ • quantizeSchwartzValue a u x =
        (2 * π * Complex.I * ⟪v, x⟫) • quantizeSchwartzValue a u x := by
        rw [real_inner_comm, ← Complex.coe_smul, smul_smul]
    _ = (2 * π * Complex.I) • quantizeSchwartzValue a (SchwartzMap.smulLeftCLM V (⟪·, v⟫) u) x +
        (2 * π * Complex.I * Complex.I) • quantizeSchwartzValue a' u x := by
        rw [hII]
        linear_combination (norm := module) key
    _ = _ := by rw [smul_add, smul_smul]

end Weight

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-- **Multiplication by a coordinate function.** For a symbol `a`, the coordinate function `x_j`
times `Op(a) u` is `Op(a) (x_j u) + i Op(∂_{ξ_j} a) u`. -/
theorem ofLp_smul_quantizeSchwartzValue (a : Symbol n V W m) (j : Fin n)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    x j • quantizeSchwartzValue a.coefficient u x =
      quantizeSchwartzValue a.coefficient
          (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ y j) u) x +
        Complex.I • quantizeSchwartzValue (frequencyDeriv j a).coefficient u x := by
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient {x} isCompact_singleton
  obtain ⟨C', -, hC'⟩ := (frequencyDeriv j a).exists_bound_coefficient {x} isCompact_singleton
  have hcoef : (fun p : CoordinateSpace n × CoordinateSpace n ↦
      fderiv ℝ (fun η ↦ a.coefficient (p.1, η)) p.2 (EuclideanSpace.single j 1)) =
        (frequencyDeriv j a).coefficient := by
    funext p
    rw [← Prod.mk.eta (p := p), coefficient_frequencyDeriv, coordinateDeriv_cons,
      coordinateDeriv_nil]
  have h := inner_smul_quantizeSchwartzValue (a := a.coefficient) (x := x)
    ((a.contDiff_coefficient.comp (contDiff_prodMk_right x)).of_le (by simp))
    (fun ξ ↦ hC x rfl ξ) (EuclideanSpace.single j 1)
    (fun ξ ↦ (congrFun hcoef (x, ξ)).symm ▸ hC' x rfl ξ) u
  rw [hcoef] at h
  simpa [EuclideanSpace.inner_single_right] using h

/-! ### Seminorm bounds -/

/-- A family `Φ u x` of reals, indexed by Schwartz functions `u` and points `x`, is bounded by a
continuous seminorm of `u`, uniformly in `x`. -/
private def IsControlled (Φ : 𝓢(CoordinateSpace n, V) → CoordinateSpace n → ℝ) : Prop :=
  ∃ q : Seminorm ℂ 𝓢(CoordinateSpace n, V), Continuous q ∧ ∀ u x, Φ u x ≤ q u

variable {Φ Ψ : 𝓢(CoordinateSpace n, V) → CoordinateSpace n → ℝ}

private lemma IsControlled.mono (h : IsControlled Ψ) (hle : ∀ u x, Φ u x ≤ Ψ u x) :
    IsControlled Φ :=
  let ⟨q, hq, hΨ⟩ := h
  ⟨q, hq, fun u x ↦ (hle u x).trans (hΨ u x)⟩

private lemma IsControlled.add (hΦ : IsControlled Φ) (hΨ : IsControlled Ψ) :
    IsControlled fun u x ↦ Φ u x + Ψ u x :=
  let ⟨q, hq, hqΦ⟩ := hΦ
  let ⟨q', hq', hqΨ⟩ := hΨ
  ⟨q + q', hq.add hq', fun u x ↦ add_le_add (hqΦ u x) (hqΨ u x)⟩

private lemma IsControlled.sum {ι : Type*} (s : Finset ι)
    {Φ : ι → 𝓢(CoordinateSpace n, V) → CoordinateSpace n → ℝ}
    (h : ∀ i ∈ s, IsControlled (Φ i)) :
    IsControlled fun u x ↦ ∑ i ∈ s, Φ i u x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, continuous_const, fun u x ↦ by simp⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun i' hi' ↦ h i' (Finset.mem_insert_of_mem hi'))

private lemma IsControlled.comp (h : IsControlled Φ)
    (L : 𝓢(CoordinateSpace n, V) →L[ℂ] 𝓢(CoordinateSpace n, V)) :
    IsControlled fun u x ↦ Φ (L u) x :=
  let ⟨q, hq, hqΦ⟩ := h
  ⟨q.comp L.toLinearMap, hq.comp L.continuous, fun u x ↦ hqΦ (L u) x⟩

/-- The quantization of a uniform symbol is bounded by a continuous seminorm of the input. -/
private lemma isControlled_norm_quantizeSchwartzValue {a : Symbol n V W m} (ha : a.IsUniform) :
    IsControlled fun u x ↦ ‖quantizeSchwartzValue a.coefficient u x‖ := by
  obtain ⟨C, -, hC⟩ := isUniform_iff.1 ha [] []
  let L := quantizeSchwartzCLM a.contDiff_coefficient.continuous
    ⟨C, m, fun x ξ ↦ by simpa [mixedDeriv_nil_nil] using hC x ξ⟩
  exact ⟨(normSeminorm ℂ _).comp L.toLinearMap, continuous_norm.comp L.continuous,
    fun u x ↦ by simpa [L] using (L u).norm_coe_le_norm x⟩

/-- Multiplication by the coordinate function `x_j`, as a complex-linear operator on Schwartz
space. -/
private lemma smulLeftCLM_ofLp_complex (j : Fin n) (u : 𝓢(CoordinateSpace n, V)) :
    SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ (y j : ℂ)) u =
      SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ y j) u := by
  have h : (fun y : CoordinateSpace n ↦ y j).HasTemperateGrowth :=
    (EuclideanSpace.proj j).hasTemperateGrowth
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), SchwartzMap.smulLeftCLM_apply_apply h,
    Complex.coe_smul]

/-- **The main estimate.** For a uniform symbol `a`, a word `w` of coordinate indices and an
order `N`, `|∏ᵢ x_{w i}| ‖D^N (Op(a) u) (x)‖` is bounded by a continuous seminorm of `u`. -/
private lemma isControlled_prod_mul_norm_iteratedFDeriv (N : ℕ) :
    ∀ (k : ℕ) (w : Fin k → Fin n) {m : ℝ} {a : Symbol n V W m}, a.IsUniform →
      IsControlled fun u x ↦
        |∏ i, x (w i)| * ‖iteratedFDeriv ℝ N (quantizeSchwartzValue a.coefficient u) x‖ := by
  induction N with
  | zero =>
    intro k
    induction k with
    | zero =>
      intro w m a ha
      simpa using isControlled_norm_quantizeSchwartzValue ha
    | succ k ih =>
      -- move one coordinate factor inside, using the commutator with `x_{w 0}`
      intro w m a ha
      refine (((ih (w ∘ Fin.succ) ha).comp (SchwartzMap.smulLeftCLM V
        (fun y : CoordinateSpace n ↦ (y (w 0) : ℂ)))).add
        (ih (w ∘ Fin.succ) (ha.frequencyDeriv (w 0)))).mono fun u x ↦ ?_
      simp only [norm_iteratedFDeriv_zero, Fin.prod_univ_succ, abs_mul, Function.comp_apply,
        smulLeftCLM_ofLp_complex]
      rw [mul_comm |x (w 0)|, mul_assoc, ← Real.norm_eq_abs (x (w 0)), ← norm_smul,
        ofLp_smul_quantizeSchwartzValue, ← mul_add]
      refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (abs_nonneg _)
      rw [norm_smul, Complex.norm_I, one_mul]
  | succ N ih =>
    -- differentiate once, using the commutator with `∂_j`
    intro k w m a ha
    refine (IsControlled.sum Finset.univ fun j _ ↦
      ((ih k w ha).comp (LineDeriv.lineDerivOpCLM ℂ 𝓢(CoordinateSpace n, V)
        (EuclideanSpace.single j (1 : ℝ)))).add (ih k w (ha.spatialDeriv j))).mono fun u x ↦ ?_
    simp only [LineDeriv.lineDerivOpCLM_apply, ← mul_add, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left
      ((norm_iteratedFDeriv_succ_le_sum_coordinateDeriv
        ((a.contDiff_quantizeSchwartzValue u).of_le (by exact_mod_cast le_top)) x).trans
        (Finset.sum_le_sum fun j _ ↦ ?_)) (abs_nonneg _)
    rw [a.coordinateDeriv_quantizeSchwartzValue j u, iteratedFDeriv_add_apply
      ((a.contDiff_quantizeSchwartzValue _).contDiffAt.of_le (by exact_mod_cast le_top))
      (((spatialDeriv j a).contDiff_quantizeSchwartzValue _).contDiffAt.of_le
        (by exact_mod_cast le_top))]
    exact norm_add_le _ _

/-- The Schwartz seminorm estimates for the quantization of a uniform symbol. -/
private lemma exists_bound_quantizeSchwartzValue {a : Symbol n V W m} (ha : a.IsUniform)
    (k N : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (u : 𝓢(CoordinateSpace n, V)) x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (quantizeSchwartzValue a.coefficient u) x‖ ≤
        C * s.sup (schwartzSeminormFamily ℂ (CoordinateSpace n) V) u := by
  obtain ⟨q, hq, hle⟩ := IsControlled.sum (Finset.univ : Finset (Fin k → Fin n))
    fun w _ ↦ isControlled_prod_mul_norm_iteratedFDeriv N k w ha
  obtain ⟨s, C, -, hqC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ _ _) q hq
  refine ⟨s, C, C.2, fun u x ↦ ?_⟩
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ N (quantizeSchwartzValue a.coefficient u) x‖ ≤
        (∑ j, |x j|) ^ k * ‖iteratedFDeriv ℝ N (quantizeSchwartzValue a.coefficient u) x‖ := by
        gcongr
        -- expand `x` in the standard basis
        set b := EuclideanSpace.basisFun (Fin n) ℝ
        calc ‖x‖ = ‖∑ j, x j • b j‖ := by
              congr 1
              exact (b.sum_repr x).symm
          _ ≤ ∑ j, ‖x j • b j‖ := norm_sum_le _ _
          _ = ∑ j, |x j| := by simp [norm_smul, b.orthonormal.1]
    _ = ∑ w : Fin k → Fin n,
          |∏ i, x (w i)| * ‖iteratedFDeriv ℝ N (quantizeSchwartzValue a.coefficient u) x‖ := by
        simp [Fintype.sum_pow, Finset.sum_mul, Finset.abs_prod]
    _ ≤ q u := hle u x
    _ ≤ C * s.sup (schwartzSeminormFamily ℂ (CoordinateSpace n) V) u := hqC u

/-! ### The quantization as an operator on Schwartz space -/

/-- **Schwartz mapping.** The Kohn–Nirenberg quantization `u ↦ Op(a) u` of a symbol `a` whose
estimates are uniform in the position, as a continuous linear map from Schwartz space to Schwartz
space. -/
def quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform) :
    𝓢(CoordinateSpace n, V) →L[ℂ] 𝓢(CoordinateSpace n, W) :=
  SchwartzMap.mkCLM (fun u ↦ quantizeSchwartzValue a.coefficient u)
    (fun u v x ↦ by
      obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient {x} isCompact_singleton
      exact quantizeSchwartzValue_add_right
        (a.contDiff_coefficient.continuous.comp (continuous_const.prodMk continuous_id)
          ).aestronglyMeasurable (hC x rfl) u v)
    (fun c u _ ↦ quantizeSchwartzValue_smul_right c u)
    (fun u ↦ a.contDiff_quantizeSchwartzValue u)
    (fun p ↦ exists_bound_quantizeSchwartzValue ha p.1 p.2)

theorem coe_quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) :
    ⇑(quantizeUniformCLM a ha u) = quantizeSchwartzValue a.coefficient u :=
  (rfl)

@[simp]
theorem quantizeUniformCLM_apply (a : Symbol n V W m) (ha : a.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeUniformCLM a ha u x = quantizeSchwartzValue a.coefficient u x :=
  (rfl)

/-- **Commutator with a derivative.** `∂_j (Op(a) u) = Op(a) (∂_j u) + Op(∂_{x_j} a) u` in
Schwartz space. -/
theorem lineDerivOp_quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform) (j : Fin n)
    (u : 𝓢(CoordinateSpace n, V)) :
    ∂_{EuclideanSpace.single j (1 : ℝ)} (quantizeUniformCLM a ha u) =
      quantizeUniformCLM a ha (∂_{EuclideanSpace.single j (1 : ℝ)} u) +
        quantizeUniformCLM (spatialDeriv j a) (ha.spatialDeriv j) u := by
  ext x
  have h := congrFun (a.coordinateDeriv_quantizeSchwartzValue j u) x
  rw [coordinateDeriv_cons, coordinateDeriv_nil, ← coe_quantizeUniformCLM a ha] at h
  simpa [SchwartzMap.lineDerivOp_apply_eq_fderiv] using h

/-- **Commutator with a coordinate function.** `x_j Op(a) u = Op(a) (x_j u) + i Op(∂_{ξ_j} a) u` in
Schwartz space. -/
theorem smulLeftCLM_quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform) (j : Fin n)
    (u : 𝓢(CoordinateSpace n, V)) :
    SchwartzMap.smulLeftCLM W (fun y : CoordinateSpace n ↦ y j) (quantizeUniformCLM a ha u) =
      quantizeUniformCLM a ha (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ y j) u) +
        Complex.I • quantizeUniformCLM (frequencyDeriv j a) (ha.frequencyDeriv j) u := by
  have hg : (fun y : CoordinateSpace n ↦ y j).HasTemperateGrowth :=
    (EuclideanSpace.proj j).hasTemperateGrowth
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg]
  simpa using a.ofLp_smul_quantizeSchwartzValue j u x

/-- A constant symbol `T` quantizes to the composition with `T`. -/
theorem quantizeUniformCLM_const [CompleteSpace V] [CompleteSpace W] (T : V →L[ℂ] W) :
    quantizeUniformCLM (const T) (isUniform_const T) =
      SchwartzMap.postcompCLM (E := CoordinateSpace n) T := by
  have hT : (const T : Symbol n V W 0).coefficient = fun _ ↦ T := funext (coefficient_const T)
  ext u x
  simpa [hT] using quantizeSchwartzValue_comp_fst (fun _ ↦ T) u x

end Symbol

end TauCeti

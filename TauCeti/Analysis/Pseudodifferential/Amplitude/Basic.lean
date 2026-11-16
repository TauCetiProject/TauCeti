/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.OscillatoryIntegral
public import TauCeti.Analysis.Pseudodifferential.Sobolev
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.Fourier.Parametric
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Amplitudes

An *amplitude* of order `m` on `ℝⁿ` (`TauCeti.Amplitude n V W m`) is a smooth map
`a : ℝⁿ × ℝⁿ × ℝⁿ → (V →L[ℂ] W)` of an output position `x`, an input position `y` and a
frequency `ξ` such that, on every compact set of pairs of positions,

`‖∂_x^α ∂_y^γ ∂_ξ^β a(x, y, ξ)‖ ≤ C ⟨ξ⟩^(m - |β|)`.

Its quantization is the oscillatory integral
`Op(a) u (x) = (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) a(x, y, ξ) u(y) dy dξ`. A symbol `b(x, ξ)` is an
amplitude independent of `y`, and `b(y, ξ)` is the amplitude of its right quantization; the
composition, adjoint and coordinate change formulas of the pseudodifferential calculus produce
amplitudes depending on both positions. Amplitudes with compact support in the input position
reduce to left symbols (`TauCeti.Amplitude.leftSymbol`, in
`TauCeti.Analysis.Pseudodifferential.Amplitude.LeftSymbol`).

## Main declarations

* `TauCeti.Amplitude`: amplitudes, with the derivatives `TauCeti.Amplitude.spatialDerivFst`
  (`∂_{x_j}`), `TauCeti.Amplitude.spatialDerivSnd` (`∂_{y_j}`) and
  `TauCeti.Amplitude.frequencyDeriv` (`∂_{ξ_j}`, lowering the order by one), which commute with
  each other (`TauCeti.Amplitude.spatialDerivFst_spatialDerivSnd_comm` and its companions).
* `TauCeti.Amplitude.exists_norm_mixedDeriv_le_of_leibniz`: symbol estimates for a family of
  functions of `(x, ξ)` built from amplitudes, from its Leibniz rules and a bound on the family.
* `TauCeti.Amplitude.diagonal`: the restriction `(x, ξ) ↦ a(x, x, ξ)` of an amplitude to the
  diagonal, a symbol of order `m`, with the Leibniz rules `TauCeti.Amplitude.spatialDeriv_diagonal`
  and `TauCeti.Amplitude.frequencyDeriv_diagonal`.
* `TauCeti.Amplitude.ofRight`: the amplitude `b(y, ξ)` of the right quantization of a symbol `b`.
* `TauCeti.Amplitude.HasCompactInputSupport`: the amplitude vanishes for input positions outside a
  compact set; then its estimates hold uniformly in `y`
  (`TauCeti.Amplitude.HasCompactInputSupport.exists_bound`).
* `TauCeti.Amplitude.HasCompactInputSupport.exists_norm_fourier_slice_le`: rapid decay
  `‖â(x, θ, ξ)‖ ≤ C ⟨ξ⟩^m ⟨θ⟩^(-r)` of the Fourier transform `â(x, θ, ξ)` of the input slice
  `y ↦ a(x, y, ξ)`, uniformly for `x` in a compact set, and
  `TauCeti.Amplitude.HasCompactInputSupport.fourier_spatialDerivSnd_slice`, the Fourier transform
  of `∂_{y_j} a`.
* `TauCeti.quantizeAmplitudeValue`: the quantization of an amplitude on a Schwartz function, with
  `TauCeti.quantizeAmplitudeValue_eq_smul_oscillatoryIntegral` identifying it with the oscillatory
  integral above, and `TauCeti.quantizeAmplitudeValue_eq_quantizeSchwartzValue` with the
  quantization of a symbol when `a` does not depend on `y`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.21)–(1.28).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §7.8.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Module
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology

namespace TauCeti

variable {n : ℕ}

/-- The directions of the mixed derivative `∂_x^α ∂_y^γ ∂_ξ^β` in `ℝⁿ × ℝⁿ × ℝⁿ`: the standard
basis vectors of the output position space named by `α`, followed by those of the input position
space named by `γ` and those of the frequency space named by `β`. -/
def amplitudeDirections (α γ β : List (Fin n)) :
    List (CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :=
  α.map (fun j ↦ (EuclideanSpace.single j 1, 0)) ++ (mixedDirections γ β).map fun v ↦ (0, v)

theorem amplitudeDirections_def (α γ β : List (Fin n)) :
    amplitudeDirections α γ β = α.map (fun j ↦ (EuclideanSpace.single j 1, 0)) ++
      γ.map (fun j ↦ (0, EuclideanSpace.single j 1, 0)) ++
        β.map (fun j ↦ (0, 0, EuclideanSpace.single j 1)) := by
  simp [amplitudeDirections, mixedDirections_def, Function.comp_def, List.append_assoc]

@[simp]
theorem length_amplitudeDirections (α γ β : List (Fin n)) :
    (amplitudeDirections α γ β).length = α.length + γ.length + β.length := by
  simp [amplitudeDirections_def, Nat.add_assoc]

/-- An **amplitude** of order `m` on `ℝⁿ`: a smooth map `a : ℝⁿ × ℝⁿ × ℝⁿ → (V →L[ℂ] W)`,
`(x, y, ξ) ↦ a(x, y, ξ)`, of an output position `x`, an input position `y` and a frequency `ξ`,
such that on every compact set `K` of pairs of positions every mixed derivative satisfies

`‖∂_x^α ∂_y^γ ∂_ξ^β a(x, y, ξ)‖ ≤ C_{K,α,γ,β} ⟨ξ⟩^(m - |β|)` for `(x, y) ∈ K` and all `ξ`.

The quantization of `a` is `u ↦ (2π)^(-n) ∫∫ e^{i(x-y)·ξ} a(x, y, ξ) u(y) dy dξ`
(`TauCeti.quantizeAmplitudeValue`). A symbol `b(x, ξ)` is the amplitude independent of `y`. -/
@[ext]
structure Amplitude (n : ℕ) (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (m : ℝ) where
  /-- The coefficient `a(x, y, ξ)` of the amplitude at the output position `x`, the input position
  `y` and the frequency `ξ`. -/
  coefficient : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W
  contDiff_coefficient : ContDiff ℝ ∞ coefficient
  exists_bound : ∀ K : Set (CoordinateSpace n × CoordinateSpace n), IsCompact K →
    ∀ α γ β : List (Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ,
      ‖iteratedFDerivAlong ℝ (amplitudeDirections α γ β) coefficient (x, y, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)

/-! ### The quantization of an amplitude -/

section Quantization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The **quantization of an amplitude** `a(x, y, ξ)` on a Schwartz function `u`, evaluated at the
output position `x`:

`Op(a) u (x) = ∫ exp(2πi ⟪ζ, x⟫) 𝓕(y ↦ a(x, y, 2πζ) u(y))(ζ) dζ`,

the iterated form, with Mathlib's Fourier transform `𝓕`, of the oscillatory integral
`(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) a(x, y, ξ) u(y) dy dξ`
(`TauCeti.quantizeAmplitudeValue_eq_smul_oscillatoryIntegral`). For an amplitude independent of
`y` it is the quantization `TauCeti.quantizeSchwartzValue` of the symbol
(`TauCeti.quantizeAmplitudeValue_eq_quantizeSchwartzValue`). -/
def quantizeAmplitudeValue (a : E × E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) : W :=
  ∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (fun y ↦ a (x, y, (2 * π) • ζ) (u y)) ζ

theorem quantizeAmplitudeValue_def (a : E × E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeAmplitudeValue a u x = ∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (fun y ↦ a (x, y, (2 * π) • ζ) (u y)) ζ :=
  (rfl)

/-- An amplitude `a(x, y, ξ) = b(x, ξ)` independent of the input position quantizes to the
quantization of the symbol `b`. -/
theorem quantizeAmplitudeValue_eq_quantizeSchwartzValue [CompleteSpace V] [CompleteSpace W]
    (b : E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeAmplitudeValue (fun p ↦ b (p.1, p.2.2)) u x = quantizeSchwartzValue b u x := by
  rw [quantizeAmplitudeValue_def, quantizeSchwartzValue_def]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  have hint : Integrable fun y ↦ (𝐞 (-⟪y, ζ⟫) : ℂ) • u y := by
    simpa only [Circle.smul_def] using
      (Real.fourierIntegral_convergent_iff (μ := volume) ζ).2 u.integrable
  simp only [Real.fourier_eq, Circle.smul_def, ← map_smul]
  rw [ContinuousLinearMap.integral_comp_comm _ hint, map_smul, SchwartzMap.fourier_coe,
    Real.fourier_eq]
  simp only [Circle.smul_def]

/-- **The quantization of an amplitude as an oscillatory integral.** The quantization of an
amplitude `a` on a Schwartz function `u` at `x` is `(2π)⁻ⁿ` times the oscillatory integral of
`b(y, ξ) = exp(i ⟪x, ξ⟫) a(x, y, ξ) u(y)`, with `n = finrank ℝ E`: the textbook formula
`(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) a(x, y, ξ) u(y) dy dξ`, with the position integral inside. -/
theorem quantizeAmplitudeValue_eq_smul_oscillatoryIntegral (a : E × E × E → V →L[ℂ] W)
    (u : 𝓢(E, V)) (x : E) :
    quantizeAmplitudeValue a u x = ((2 * π) ^ finrank ℝ E)⁻¹ •
      oscillatoryIntegral fun p : E × E ↦
        Complex.exp (⟪x, p.2⟫ * Complex.I) • a (x, p.1, p.2) (u p.1) := by
  have hpos : 0 < ((2 * π) ^ finrank ℝ E)⁻¹ := by positivity
  rw [oscillatoryIntegral_def, ← abs_of_pos hpos, ← Measure.integral_comp_smul,
    quantizeAmplitudeValue_def]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  simp only [smul_smul, ← Complex.exp_add]
  rw [Circle.smul_def, Real.fourierChar_apply, Real.fourier_eq', ← integral_smul]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  simp only [smul_smul, ← Complex.exp_add, inner_smul_right, real_inner_comm ζ x]
  congr 2
  push_cast
  ring

end Quantization


namespace Amplitude

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

private theorem contDiff_iteratedFDerivAlong_singleton (a : Amplitude n V W m)
    (d : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    ContDiff ℝ ∞ (iteratedFDerivAlong ℝ [d] a.coefficient) :=
  a.contDiff_coefficient.iteratedFDerivAlong [d] (by simp)

/-- The derivative `∂_{x_j} a` in the output position, an amplitude of the same order. -/
def spatialDerivFst (j : Fin n) (a : Amplitude n V W m) : Amplitude n V W m where
  coefficient := iteratedFDerivAlong ℝ [(EuclideanSpace.single j 1, 0)] a.coefficient
  contDiff_coefficient := a.contDiff_iteratedFDerivAlong_singleton _
  exists_bound K hK α γ β := by
    obtain ⟨C, hC0, hC⟩ := a.exists_bound K hK (α ++ [j]) γ β
    refine ⟨C, hC0, fun x y hxy ξ ↦ ?_⟩
    rw [← iteratedFDerivAlong_append, List.Perm.iteratedFDerivAlong_eq _ a.contDiff_coefficient
      (by simp)]
    · exact hC x y hxy ξ
    · simp only [amplitudeDirections_def, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc]
      exact List.Perm.append_left _ (by rw [← List.append_assoc]; exact List.perm_append_comm)

/-- The derivative `∂_{y_j} a` in the input position, an amplitude of the same order. -/
def spatialDerivSnd (j : Fin n) (a : Amplitude n V W m) : Amplitude n V W m where
  coefficient := iteratedFDerivAlong ℝ [(0, EuclideanSpace.single j 1, 0)] a.coefficient
  contDiff_coefficient := a.contDiff_iteratedFDerivAlong_singleton _
  exists_bound K hK α γ β := by
    obtain ⟨C, hC0, hC⟩ := a.exists_bound K hK α (γ ++ [j]) β
    refine ⟨C, hC0, fun x y hxy ξ ↦ ?_⟩
    rw [← iteratedFDerivAlong_append, List.Perm.iteratedFDerivAlong_eq _ a.contDiff_coefficient
      (by simp)]
    · exact hC x y hxy ξ
    · simp only [amplitudeDirections_def, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc]
      exact List.Perm.append_left _ (List.Perm.append_left _ (List.perm_append_comm))

/-- The derivative `∂_{ξ_j} a` in the frequency, an amplitude of order `m - 1`. -/
def frequencyDeriv (j : Fin n) (a : Amplitude n V W m) : Amplitude n V W (m - 1) where
  coefficient := iteratedFDerivAlong ℝ [(0, 0, EuclideanSpace.single j 1)] a.coefficient
  contDiff_coefficient := a.contDiff_iteratedFDerivAlong_singleton _
  exists_bound K hK α γ β := by
    obtain ⟨C, hC0, hC⟩ := a.exists_bound K hK α γ (β ++ [j])
    refine ⟨C, hC0, fun x y hxy ξ ↦ ?_⟩
    have h := hC x y hxy ξ
    rw [← iteratedFDerivAlong_append]
    simp only [amplitudeDirections_def, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.length_append, List.length_cons, List.length_nil] at h ⊢
    convert h using 3
    push_cast
    ring

@[simp]
theorem coefficient_spatialDerivFst (j : Fin n) (a : Amplitude n V W m)
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (spatialDerivFst j a).coefficient p =
      fderiv ℝ a.coefficient p (EuclideanSpace.single j 1, 0) := by
  simp [spatialDerivFst]

@[simp]
theorem coefficient_spatialDerivSnd (j : Fin n) (a : Amplitude n V W m)
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (spatialDerivSnd j a).coefficient p =
      fderiv ℝ a.coefficient p (0, EuclideanSpace.single j 1, 0) := by
  simp [spatialDerivSnd]

@[simp]
theorem coefficient_frequencyDeriv (j : Fin n) (a : Amplitude n V W m)
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (frequencyDeriv j a).coefficient p =
      fderiv ℝ a.coefficient p (0, 0, EuclideanSpace.single j 1) := by
  simp [frequencyDeriv]


/-! ### Commuting derivatives -/

section Comm

/-- The coefficient of `∂_{x_j} a` as a directional derivative of the coefficient of `a`. -/
theorem coefficient_spatialDerivFst_eq_iteratedFDerivAlong (j : Fin n) (a : Amplitude n V W m) :
    (spatialDerivFst j a).coefficient =
      iteratedFDerivAlong ℝ [(EuclideanSpace.single j 1, 0)] a.coefficient :=
  (rfl)

/-- The coefficient of `∂_{y_j} a` as a directional derivative of the coefficient of `a`. -/
theorem coefficient_spatialDerivSnd_eq_iteratedFDerivAlong (j : Fin n) (a : Amplitude n V W m) :
    (spatialDerivSnd j a).coefficient =
      iteratedFDerivAlong ℝ [(0, EuclideanSpace.single j 1, 0)] a.coefficient :=
  (rfl)

/-- The coefficient of `∂_{ξ_j} a` as a directional derivative of the coefficient of `a`. -/
theorem coefficient_frequencyDeriv_eq_iteratedFDerivAlong (j : Fin n) (a : Amplitude n V W m) :
    (frequencyDeriv j a).coefficient =
      iteratedFDerivAlong ℝ [(0, 0, EuclideanSpace.single j 1)] a.coefficient :=
  (rfl)

/-- Derivatives of an amplitude along two directions commute. -/
private theorem iteratedFDerivAlong_pair_comm (a : Amplitude n V W m)
    (d e : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    iteratedFDerivAlong ℝ [d] (iteratedFDerivAlong ℝ [e] a.coefficient) =
      iteratedFDerivAlong ℝ [e] (iteratedFDerivAlong ℝ [d] a.coefficient) := by
  rw [← iteratedFDerivAlong_append, ← iteratedFDerivAlong_append]
  exact (List.Perm.swap e d []).iteratedFDerivAlong_eq a.contDiff_coefficient (by simp)

/-- Two derivatives in the output position commute. -/
theorem spatialDerivFst_comm (j l : Fin n) (a : Amplitude n V W m) :
    spatialDerivFst j (spatialDerivFst l a) = spatialDerivFst l (spatialDerivFst j a) :=
  Amplitude.ext (iteratedFDerivAlong_pair_comm a _ _)

/-- Two derivatives in the input position commute. -/
theorem spatialDerivSnd_comm (j l : Fin n) (a : Amplitude n V W m) :
    spatialDerivSnd j (spatialDerivSnd l a) = spatialDerivSnd l (spatialDerivSnd j a) :=
  Amplitude.ext (iteratedFDerivAlong_pair_comm a _ _)

/-- Two frequency derivatives commute. -/
theorem frequencyDeriv_comm (j l : Fin n) (a : Amplitude n V W m) :
    frequencyDeriv j (frequencyDeriv l a) = frequencyDeriv l (frequencyDeriv j a) :=
  Amplitude.ext (iteratedFDerivAlong_pair_comm a _ _)

/-- Derivatives in the output and in the input position commute. -/
theorem spatialDerivFst_spatialDerivSnd_comm (j l : Fin n) (a : Amplitude n V W m) :
    spatialDerivFst j (spatialDerivSnd l a) = spatialDerivSnd l (spatialDerivFst j a) :=
  Amplitude.ext (iteratedFDerivAlong_pair_comm a _ _)

/-- Derivatives in the output position and in the frequency commute. -/
theorem spatialDerivFst_frequencyDeriv_comm (j l : Fin n) (a : Amplitude n V W m) :
    spatialDerivFst j (frequencyDeriv l a) = frequencyDeriv l (spatialDerivFst j a) :=
  Amplitude.ext (iteratedFDerivAlong_pair_comm a _ _)

/-- Derivatives in the input position and in the frequency commute. -/
theorem spatialDerivSnd_frequencyDeriv_comm (j l : Fin n) (a : Amplitude n V W m) :
    spatialDerivSnd j (frequencyDeriv l a) = frequencyDeriv l (spatialDerivSnd j a) :=
  Amplitude.ext (iteratedFDerivAlong_pair_comm a _ _)

end Comm

/-- The amplitude `a(x, y, ξ) = b(y, ξ)` of the **right quantization**
`u ↦ (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) b(y, ξ) u(y) dy dξ` of a symbol `b`. -/
def ofRight (b : Symbol n V W m) : Amplitude n V W m where
  coefficient p := b.coefficient p.2
  contDiff_coefficient := b.contDiff_coefficient.comp contDiff_snd
  exists_bound K hK α γ β := by
    obtain ⟨C, hC0, hC⟩ := b.exists_bound (Prod.snd '' K) (hK.image continuous_snd) γ β
    refine ⟨C, hC0, fun x y hxy ξ ↦ ?_⟩
    rw [iteratedFDerivAlong_comp_of_hasFDerivAt (fun _ ↦ hasFDerivAt_snd) b.contDiff_coefficient _
      (by simp)]
    cases α with
    | nil =>
      have h : (amplitudeDirections [] γ β).map
          (ContinuousLinearMap.snd ℝ (CoordinateSpace n) (CoordinateSpace n × CoordinateSpace n))
            = mixedDirections γ β := by
        simp [amplitudeDirections, Function.comp_def]
      rw [h, ← mixedDeriv_eq_iteratedFDerivAlong _ _ (b.contDiff_coefficient.of_le (by simp))]
      exact hC y ⟨(x, y), hxy, rfl⟩ ξ
    | cons j α =>
      simp only [amplitudeDirections, List.map_cons, List.cons_append, List.map_append,
        iteratedFDerivAlong_cons_apply, ContinuousLinearMap.coe_snd', map_zero, norm_zero]
      positivity

@[simp]
theorem coefficient_ofRight (b : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (ofRight b).coefficient p = b.coefficient p.2 :=
  (rfl)

/-! ### Slices -/

/-- The derivative of the input-position slice `y ↦ a(x, y, ξ)`. -/
private theorem fderiv_slice_snd_apply (a : Amplitude n V W m) (x y ξ v : CoordinateSpace n) :
    fderiv ℝ (fun y ↦ a.coefficient (x, y, ξ)) y v =
      fderiv ℝ a.coefficient (x, y, ξ) (0, v, 0) := by
  have h := (a.contDiff_coefficient.differentiable (by simp) _).hasFDerivAt.comp y
    ((hasFDerivAt_prodMk_right (𝕜 := ℝ) x (y, ξ)).comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y ξ))
  simp only [Function.comp_def] at h
  simp [h.fderiv]

/-- The coordinate derivatives of the input-position slice `y ↦ a(x, y, ξ)` are the mixed
derivatives `∂_y^γ a`. -/
private theorem coordinateDeriv_slice_snd (a : Amplitude n V W m) (γ : List (Fin n))
    (x y ξ : CoordinateSpace n) :
    coordinateDeriv γ (fun y ↦ a.coefficient (x, y, ξ)) y =
      iteratedFDerivAlong ℝ (amplitudeDirections [] γ []) a.coefficient (x, y, ξ) := by
  have hφ : ∀ z, HasFDerivAt (fun z : CoordinateSpace n ↦ (x, z, ξ))
      ((ContinuousLinearMap.inr ℝ (CoordinateSpace n) _).comp
        (ContinuousLinearMap.inl ℝ (CoordinateSpace n) (CoordinateSpace n))) z := fun z ↦
    (hasFDerivAt_prodMk_right x (z, ξ)).comp z (hasFDerivAt_prodMk_left z ξ)
  rw [coordinateDeriv_eq_iteratedFDerivAlong,
    iteratedFDerivAlong_comp_of_hasFDerivAt hφ a.contDiff_coefficient _ (by simp)]
  simp [amplitudeDirections_def, Function.comp_def]

/-! ### Compact input support -/

/-- An amplitude has **compact input support** if it vanishes, for every output position and
every frequency, at all input positions `y` outside a fixed compact set. Its quantization is then
an absolutely convergent iterated integral, and it reduces to a left symbol
(`TauCeti.Amplitude.leftSymbol`). -/
def HasCompactInputSupport (a : Amplitude n V W m) : Prop :=
  ∃ L : Set (CoordinateSpace n), IsCompact L ∧ ∀ x, ∀ y ∉ L, ∀ ξ, a.coefficient (x, y, ξ) = 0

theorem hasCompactInputSupport_iff {a : Amplitude n V W m} :
    a.HasCompactInputSupport ↔
      ∃ L : Set (CoordinateSpace n), IsCompact L ∧ ∀ x, ∀ y ∉ L, ∀ ξ, a.coefficient (x, y, ξ) = 0 :=
  Iff.rfl

/-- Outside a closed set of input positions on which an amplitude vanishes, all its derivatives
vanish. -/
private theorem iteratedFDerivAlong_eq_zero_of_notMem {a : Amplitude n V W m}
    {L : Set (CoordinateSpace n)} (hL : IsClosed L)
    (hLa : ∀ x, ∀ y ∉ L, ∀ ξ, a.coefficient (x, y, ξ) = 0)
    (vs : List (CoordinateSpace n × CoordinateSpace n × CoordinateSpace n))
    {x y ξ : CoordinateSpace n} (hy : y ∉ L) :
    iteratedFDerivAlong ℝ vs a.coefficient (x, y, ξ) = 0 := by
  refine iteratedFDerivAlong_eq_zero_of_eventuallyEq_zero ?_ vs
  have hU : IsOpen {p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n | p.2.1 ∉ L} :=
    hL.isOpen_compl.preimage (continuous_fst.comp continuous_snd)
  filter_upwards [hU.mem_nhds hy] with p hp
  exact hLa p.1 p.2.1 hp p.2.2

private theorem HasCompactInputSupport.exists_iteratedFDerivAlong_singleton_eq_zero
    {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (d : CoordinateSpace n × CoordinateSpace n ×
      CoordinateSpace n) :
    ∃ L : Set (CoordinateSpace n), IsCompact L ∧ ∀ x, ∀ y ∉ L, ∀ ξ,
      iteratedFDerivAlong ℝ [d] a.coefficient (x, y, ξ) = 0 := by
  obtain ⟨L, hL, hLa⟩ := ha
  exact ⟨L, hL, fun x y hy ξ ↦ iteratedFDerivAlong_eq_zero_of_notMem hL.isClosed hLa _ hy⟩

theorem HasCompactInputSupport.spatialDerivFst {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (j : Fin n) : (spatialDerivFst j a).HasCompactInputSupport :=
  ha.exists_iteratedFDerivAlong_singleton_eq_zero _

theorem HasCompactInputSupport.spatialDerivSnd {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (j : Fin n) : (spatialDerivSnd j a).HasCompactInputSupport :=
  ha.exists_iteratedFDerivAlong_singleton_eq_zero _

theorem HasCompactInputSupport.frequencyDeriv {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (j : Fin n) : (frequencyDeriv j a).HasCompactInputSupport :=
  ha.exists_iteratedFDerivAlong_singleton_eq_zero _

/-- The input-position slices of an amplitude with compact input support are compactly
supported. -/
theorem HasCompactInputSupport.hasCompactSupport_slice {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (x ξ : CoordinateSpace n) :
    HasCompactSupport fun y ↦ a.coefficient (x, y, ξ) := by
  obtain ⟨L, hL, hLa⟩ := ha
  exact HasCompactSupport.intro hL fun y hy ↦ hLa x y hy ξ

/-- The amplitude of the right quantization of a symbol with compact spatial support has compact
input support. -/
theorem _root_.TauCeti.Symbol.HasCompactSpatialSupport.hasCompactInputSupport_ofRight
    {b : Symbol n V W m} (hb : b.HasCompactSpatialSupport) :
    (ofRight b).HasCompactInputSupport := by
  obtain ⟨L, hL, hLb⟩ := Symbol.hasCompactSpatialSupport_iff.mp hb
  exact ⟨L, hL, fun _ y hy ξ ↦ hLb y hy ξ⟩

/-- For an amplitude with compact input support, the estimates hold for all input positions,
uniformly for output positions in a compact set. -/
theorem HasCompactInputSupport.exists_bound {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (α γ β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ y ξ,
      ‖iteratedFDerivAlong ℝ (amplitudeDirections α γ β) a.coefficient (x, y, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨L, hL, hLa⟩ := ha
  obtain ⟨C, hC0, hC⟩ := a.exists_bound (K ×ˢ L) (hK.prod hL) α γ β
  refine ⟨C, hC0, fun x hx y ξ ↦ ?_⟩
  by_cases hy : y ∈ L
  · exact hC x y ⟨hx, hy⟩ ξ
  · rw [iteratedFDerivAlong_eq_zero_of_notMem hL.isClosed hLa _ hy, norm_zero]
    positivity

/-! ### The Fourier transform in the input position -/

/-- The `L¹` norms of the derivatives of the input-position slices of an amplitude with compact
input support grow at most like `⟨ξ⟩ ^ m`, uniformly for output positions in a compact set. -/
private theorem HasCompactInputSupport.exists_integral_norm_iteratedFDeriv_slice_le
    {a : Amplitude n V W m} (ha : a.HasCompactInputSupport) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) (k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ x ∈ K, ∀ ξ,
      ∫ y, ‖iteratedFDeriv ℝ k (fun y ↦ a.coefficient (x, y, ξ)) y‖ ≤
        B * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨L, hL, hLa⟩ := id ha
  choose C hC0 hC using fun r : Fin k → Fin n ↦ ha.exists_bound hK [] (List.ofFn r) []
  set D := ∑ r, C r
  have hD : 0 ≤ D := Finset.sum_nonneg fun r _ ↦ hC0 r
  refine ⟨D * (volume L).toReal, mul_nonneg hD ENNReal.toReal_nonneg, fun x hx ξ ↦ ?_⟩
  have hsmooth : ContDiff ℝ ∞ fun y ↦ a.coefficient (x, y, ξ) :=
    a.contDiff_coefficient.comp (by fun_prop)
  -- The `k`-th derivative is bounded by `D ⟨ξ⟩ ^ m` and vanishes outside `L`.
  have hpt : ∀ y, ‖iteratedFDeriv ℝ k (fun y ↦ a.coefficient (x, y, ξ)) y‖ ≤
      L.indicator (fun _ ↦ D * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) y := by
    intro y
    by_cases hy : y ∈ L
    · rw [Set.indicator_of_mem hy, Finset.sum_mul]
      refine (norm_iteratedFDeriv_le_sum_coordinateDeriv (hsmooth.of_le (by simp)) y).trans
        (Finset.sum_le_sum fun r _ ↦ ?_)
      rw [coordinateDeriv_slice_snd]
      simpa using hC r x hx y ξ
    · rw [Set.indicator_of_notMem hy, norm_le_zero_iff]
      exact image_eq_zero_of_notMem_tsupport fun hmem ↦ hy <|
        (closure_minimal (s := Function.support fun y ↦ a.coefficient (x, y, ξ))
          (fun y hy' ↦ by_contra fun h ↦ Function.mem_support.1 hy' (hLa x y h ξ)) hL.isClosed)
          (tsupport_iteratedFDeriv_subset k hmem)
  calc ∫ y, ‖iteratedFDeriv ℝ k (fun y ↦ a.coefficient (x, y, ξ)) y‖
      ≤ ∫ y, L.indicator (fun _ ↦ D * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) y :=
        integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
          ((integrable_indicator_iff hL.measurableSet).2
            (integrableOn_const hL.measure_lt_top.ne)) (.of_forall hpt)
    _ = D * (volume L).toReal * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
        rw [integral_indicator_const _ hL.measurableSet, smul_eq_mul, measureReal_def]
        ring

/-- **Rapid decay of the Fourier transform in the input position.** For an amplitude `a` of order
`m` with compact input support and every `r`, the Fourier transform `â(x, θ, ξ)` of the input
slice `y ↦ a(x, y, ξ)` satisfies `‖â(x, θ, ξ)‖ ≤ C ⟨ξ⟩ ^ m ⟨θ⟩ ^ (-r)`, uniformly for output
positions `x` in a compact set. -/
theorem HasCompactInputSupport.exists_norm_fourier_slice_le {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ θ ξ,
      ‖𝓕 (fun y ↦ a.coefficient (x, y, ξ)) θ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖ ^ 2) ^ (-r / 2) := by
  set N := ⌈r⌉₊
  obtain ⟨B₀, hB₀, h₀⟩ := ha.exists_integral_norm_iteratedFDeriv_slice_le hK 0
  obtain ⟨B₁, hB₁, h₁⟩ := ha.exists_integral_norm_iteratedFDeriv_slice_le hK N
  refine ⟨2 ^ N * (B₀ + B₁), by positivity, fun x hx θ ξ ↦ ?_⟩
  set f := fun y ↦ a.coefficient (x, y, ξ)
  have hsmooth : ContDiff ℝ ∞ f := a.contDiff_coefficient.comp (by fun_prop)
  have hint : ∀ k, Integrable (iteratedFDeriv ℝ k f) := fun k ↦
    (hsmooth.continuous_iteratedFDeriv (by simp)).integrable_of_hasCompactSupport
      ((ha.hasCompactSupport_slice x ξ).iteratedFDeriv k)
  have e₀ := pow_mul_norm_fourier_le_integral_norm_iteratedFDeriv (N := 0)
    (fun n hn ↦ (Nat.not_lt_zero n hn).elim) (fun k _ ↦ hint k) θ
  have e₁ := pow_mul_norm_fourier_le_integral_norm_iteratedFDeriv (N := N)
    (fun n _ ↦ hsmooth.differentiable_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n))
    (fun k _ ↦ hint k) θ
  rw [pow_zero, one_mul] at e₀
  have hw : 0 < (1 + ‖θ‖ ^ 2) ^ (r / 2) := by positivity
  -- `⟨θ⟩ ^ r ≤ 2 ^ N (1 + ‖θ‖ ^ N)` and `‖θ‖ ^ N ≤ (2π‖θ‖) ^ N`.
  have hbr : (1 + ‖θ‖ ^ 2) ^ (r / 2) ≤ 2 ^ N * (1 + ‖θ‖ ^ N) :=
    (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖θ‖])
      (by linarith [Nat.le_ceil r])).trans
      (one_add_norm_sq_rpow_le_two_pow_mul_one_add_norm_pow θ N)
  have h2π : ‖θ‖ ^ N ≤ (2 * π * ‖θ‖) ^ N := by
    gcongr
    nlinarith [Real.two_le_pi, norm_nonneg θ]
  rw [neg_div, Real.rpow_neg (by positivity), ← div_eq_mul_inv,
    le_div_iff₀ hw]
  calc ‖𝓕 f θ‖ * (1 + ‖θ‖ ^ 2) ^ (r / 2) ≤ ‖𝓕 f θ‖ * (2 ^ N * (1 + ‖θ‖ ^ N)) := by gcongr
    _ = 2 ^ N * (‖𝓕 f θ‖ + ‖θ‖ ^ N * ‖𝓕 f θ‖) := by ring
    _ ≤ 2 ^ N * ((∫ y, ‖iteratedFDeriv ℝ 0 f y‖) + ∫ y, ‖iteratedFDeriv ℝ N f y‖) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
        · simpa using e₀
        · exact (mul_le_mul_of_nonneg_right h2π (norm_nonneg _)).trans e₁
    _ ≤ 2 ^ N * (B₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2) + B₁ * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add (h₀ x hx ξ) (h₁ x hx ξ)) (by positivity)
    _ = _ := by ring


/-- The Fourier transform `â(x, θ, ξ)` of the input slices of an amplitude with compact input
support is jointly continuous in the dual variable `θ`, the output position `x` and the
frequency `ξ`. -/
theorem HasCompactInputSupport.continuous_fourier_slice {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun y ↦ a.coefficient (q.2.1, y, q.2.2)) q.1 := by
  obtain ⟨L, hL, hLa⟩ := ha
  simpa only [Real.fourier_eq, Circle.smul_def] using continuous_integral_fourierChar_smul
    (g := fun r : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      a.coefficient (r.2.1, r.1, r.2.2))
    (a.contDiff_coefficient.continuous.comp (by fun_prop)) hL fun y hy q ↦ hLa q.1 y hy q.2

/-- The Fourier transform of the input slices of `∂_{y_j} a` is `2πi θⱼ â(x, θ, ξ)`. -/
theorem HasCompactInputSupport.fourier_spatialDerivSnd_slice {a : Amplitude n V W m}
    (ha : a.HasCompactInputSupport) (j : Fin n) (θ x ξ : CoordinateSpace n) :
    𝓕 (fun y ↦ (Amplitude.spatialDerivSnd j a).coefficient (x, y, ξ)) θ =
      ((2 * π * Complex.I * θ j : ℂ)) • 𝓕 (fun y ↦ a.coefficient (x, y, ξ)) θ := by
  set f := fun y ↦ a.coefficient (x, y, ξ)
  have hsmooth : ContDiff ℝ ∞ f := a.contDiff_coefficient.comp (by fun_prop)
  have hsupp := ha.hasCompactSupport_slice x ξ
  have h := fourier_fderiv_apply (hsmooth.continuous.integrable_of_hasCompactSupport hsupp)
    (hsmooth.differentiable (by simp))
    ((hsmooth.continuous_fderiv (by simp)).integrable_of_hasCompactSupport (hsupp.fderiv (𝕜 := ℝ)))
    (EuclideanSpace.single j 1) θ
  simp only [f, fderiv_slice_snd_apply, EuclideanSpace.inner_single_right, one_mul,
    conj_trivial] at h
  simpa only [coefficient_spatialDerivSnd] using h

/-! ### Symbol estimates from the Leibniz rules -/

section Leibniz

/-- **Symbol estimates from the Leibniz rules for amplitudes.** Let `F a ha` be a family of smooth
functions of the position and the frequency, indexed by the amplitudes `a` of order `m` satisfying
a predicate `P` that is stable under the derivatives `∂_{x_j}`, `∂_{y_j}` and `∂_{ξ_j}`, which
satisfies the Leibniz rules `∂_{x_j} (F a) = F (∂_{x_j} a) + F (∂_{y_j} a)` and
`∂_{ξ_j} (F a) = F (∂_{ξ_j} a)`. If every member is bounded by `C ⟨ξ⟩ ^ (m - s)` for positions in a
compact set, then so is every mixed derivative `∂_x^α ∂_ξ^β (F a)`, with the weight
`⟨ξ⟩ ^ (m - s - |β|)`. -/
theorem exists_norm_mixedDeriv_le_of_leibniz (s : ℝ) (P : ∀ {m : ℝ}, Amplitude n V W m → Prop)
    (hPfst : ∀ {m : ℝ} {a : Amplitude n V W m}, P a → ∀ j, P (spatialDerivFst j a))
    (hPsnd : ∀ {m : ℝ} {a : Amplitude n V W m}, P a → ∀ j, P (spatialDerivSnd j a))
    (hPfreq : ∀ {m : ℝ} {a : Amplitude n V W m}, P a → ∀ j, P (frequencyDeriv j a))
    (F : ∀ {m : ℝ} (a : Amplitude n V W m), P a →
      CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (hF : ∀ {m : ℝ} (a : Amplitude n V W m) (ha : P a), ContDiff ℝ ∞ (F a ha))
    (hspatial : ∀ {m : ℝ} (a : Amplitude n V W m) (ha : P a) (j : Fin n)
      (x ξ : CoordinateSpace n), coordinateDeriv [j] (fun y ↦ F a ha (y, ξ)) x =
        F (spatialDerivFst j a) (hPfst ha j) (x, ξ) + F (spatialDerivSnd j a) (hPsnd ha j) (x, ξ))
    (hfrequency : ∀ {m : ℝ} (a : Amplitude n V W m) (ha : P a) (j : Fin n)
      (x ξ : CoordinateSpace n), coordinateDeriv [j] (fun η ↦ F a ha (x, η)) ξ =
        F (frequencyDeriv j a) (hPfreq ha j) (x, ξ))
    (hbound : ∀ {m : ℝ} (a : Amplitude n V W m) (ha : P a) {K : Set (CoordinateSpace n)},
      IsCompact K → ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
        ‖F a ha (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - s) / 2))
    (a : Amplitude n V W m) (ha : P a) (α β : List (Fin n)) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (F a ha) x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - s - β.length) / 2) := by
  obtain ⟨D, hD⟩ : ∃ D, α.length + β.length = D := ⟨_, rfl⟩
  induction D generalizing m α β with
  | zero =>
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by
      simpa [List.length_eq_zero_iff] using hD
    obtain ⟨C, hC0, hC⟩ := hbound a ha hK
    exact ⟨C, hC0, fun x hx ξ ↦ by simpa using hC x hx ξ⟩
  | succ D ih =>
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hD
      · obtain ⟨C₁, hC₁0, hC₁⟩ := ih (spatialDerivFst j a) (hPfst ha j) α' [] (by simpa using hD)
        obtain ⟨C₂, hC₂0, hC₂⟩ := ih (spatialDerivSnd j a) (hPsnd ha j) α' [] (by simpa using hD)
        refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x hx ξ ↦ ?_⟩
        have hfun : (fun q : CoordinateSpace n × CoordinateSpace n ↦
            coordinateDeriv [j] (fun y ↦ F a ha (y, q.2)) q.1) =
              F (spatialDerivFst j a) (hPfst ha j) + F (spatialDerivSnd j a) (hPsnd ha j) :=
          funext fun q ↦ hspatial a ha j q.1 q.2
        rw [← mixedDeriv_coordinateDeriv_fst (hF a ha), hfun]
        exact norm_mixedDeriv_add_le (hF _ _) (hF _ _) (hC₁ x hx ξ) (hC₂ x hx ξ)
    · have hlen : α.length + β'.length = D := by
        simp only [List.length_append, List.length_singleton] at hD
        omega
      obtain ⟨C, hC0, hC⟩ := ih (frequencyDeriv j a) (hPfreq ha j) α β' hlen
      refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
      have hfun : (fun q : CoordinateSpace n × CoordinateSpace n ↦
          coordinateDeriv [j] (fun η ↦ F a ha (q.1, η)) q.2) =
            F (frequencyDeriv j a) (hPfreq ha j) :=
        funext fun q ↦ hfrequency a ha j q.1 q.2
      have e : (m - 1 - s - β'.length) / 2 = (m - s - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      have h := hC x hx ξ
      rw [e] at h
      rw [← mixedDeriv_coordinateDeriv_snd, hfun]
      exact h

end Leibniz

/-! ### The restriction to the diagonal -/

section Diagonal

/-- The derivative of `x ↦ a(x, x, ξ)` in the direction `e_j` is `∂_{x_j} a + ∂_{y_j} a` at
`(x, x, ξ)`. -/
private theorem coordinateDeriv_diagonal_fst (a : Amplitude n V W m) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun y ↦ a.coefficient (y, y, ξ)) x =
      (spatialDerivFst j a).coefficient (x, x, ξ) +
        (spatialDerivSnd j a).coefficient (x, x, ξ) := by
  have hφ : HasFDerivAt (fun y : CoordinateSpace n ↦ (y, y, ξ))
      ((ContinuousLinearMap.id ℝ (CoordinateSpace n)).prod
        ((ContinuousLinearMap.id ℝ (CoordinateSpace n)).prod 0)) x :=
    (hasFDerivAt_id x).prodMk ((hasFDerivAt_id x).prodMk (hasFDerivAt_const ξ x))
  have h := (a.contDiff_coefficient.differentiable (by simp) _).hasFDerivAt.comp x hφ
  rw [coordinateDeriv_cons, coordinateDeriv_nil, coefficient_spatialDerivFst,
    coefficient_spatialDerivSnd, ← map_add]
  simp only [Function.comp_def] at h
  rw [h.fderiv]
  simp

/-- The derivative of `ξ ↦ a(x, x, ξ)` in the direction `e_j` is `∂_{ξ_j} a` at `(x, x, ξ)`. -/
private theorem coordinateDeriv_diagonal_snd (a : Amplitude n V W m) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun η ↦ a.coefficient (x, x, η)) ξ =
      (frequencyDeriv j a).coefficient (x, x, ξ) := by
  have hφ : HasFDerivAt (fun η : CoordinateSpace n ↦ (x, x, η))
      ((0 : CoordinateSpace n →L[ℝ] CoordinateSpace n).prod
        ((0 : CoordinateSpace n →L[ℝ] CoordinateSpace n).prod
          (ContinuousLinearMap.id ℝ (CoordinateSpace n)))) ξ :=
    (hasFDerivAt_const x ξ).prodMk ((hasFDerivAt_const x ξ).prodMk (hasFDerivAt_id ξ))
  have h := (a.contDiff_coefficient.differentiable (by simp) _).hasFDerivAt.comp ξ hφ
  rw [coordinateDeriv_cons, coordinateDeriv_nil, coefficient_frequencyDeriv]
  simp only [Function.comp_def] at h
  rw [h.fderiv]
  simp

/-- The restriction `(x, ξ) ↦ a(x, x, ξ)` of an amplitude of order `m` to the diagonal, a symbol of
order `m`. It is the leading term of the left symbol
(`TauCeti.Amplitude.leftSymbol_eq_diagonal_add_leftRemainder_one`). -/
def diagonal (a : Amplitude n V W m) : Symbol n V W m where
  coefficient p := a.coefficient (p.1, p.1, p.2)
  contDiff_coefficient := a.contDiff_coefficient.comp (by fun_prop)
  exists_bound K hK α β :=
    exists_norm_mixedDeriv_le_of_leibniz 0 (fun _ ↦ True) (fun _ _ ↦ trivial)
      (fun _ _ ↦ trivial) (fun _ _ ↦ trivial)
      (fun a _ p ↦ a.coefficient (p.1, p.1, p.2))
      (fun a _ ↦ a.contDiff_coefficient.comp (by fun_prop))
      (fun a _ j x ξ ↦ coordinateDeriv_diagonal_fst a j x ξ)
      (fun a _ j x ξ ↦ coordinateDeriv_diagonal_snd a j x ξ)
      (fun a _ K hK ↦ by
        obtain ⟨C, hC0, hC⟩ := a.exists_bound (K ×ˢ K) (hK.prod hK) [] [] []
        exact ⟨C, hC0, fun x hx ξ ↦ by
          simpa [amplitudeDirections_def] using hC x x ⟨hx, hx⟩ ξ⟩)
      a trivial α β hK |>.imp fun _ h ↦ by simpa using h

@[simp]
theorem coefficient_diagonal (a : Amplitude n V W m) (x ξ : CoordinateSpace n) :
    a.diagonal.coefficient (x, ξ) = a.coefficient (x, x, ξ) :=
  (rfl)

/-- **Leibniz rule in the position** for the restriction to the diagonal. -/
theorem spatialDeriv_diagonal (j : Fin n) (a : Amplitude n V W m) :
    Symbol.spatialDeriv j a.diagonal =
      (spatialDerivFst j a).diagonal + (spatialDerivSnd j a).diagonal := by
  ext1
  funext ⟨x, ξ⟩
  simp only [Symbol.coefficient_spatialDeriv, Symbol.coefficient_add, Pi.add_apply,
    coefficient_diagonal]
  exact coordinateDeriv_diagonal_fst a j x ξ

/-- **Leibniz rule in the frequency** for the restriction to the diagonal. -/
theorem frequencyDeriv_diagonal (j : Fin n) (a : Amplitude n V W m) :
    Symbol.frequencyDeriv j a.diagonal = (frequencyDeriv j a).diagonal := by
  ext1
  funext ⟨x, ξ⟩
  simp only [Symbol.coefficient_frequencyDeriv, coefficient_diagonal]
  exact coordinateDeriv_diagonal_snd a j x ξ

/-- The amplitude `b(y, ξ)` of the right quantization of a symbol `b` restricts on the diagonal
to `b`. -/
@[simp]
theorem diagonal_ofRight (b : Symbol n V W m) : (ofRight b).diagonal = b := by
  ext1
  funext ⟨x, ξ⟩
  simp

end Diagonal

end Amplitude

end TauCeti

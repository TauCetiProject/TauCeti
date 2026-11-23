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
amplitude independent of `y` (`TauCeti.Amplitude.ofLeft`), and `b(y, ξ)` is the amplitude of its
right quantization (`TauCeti.Amplitude.ofRight`); the composition, adjoint and coordinate change
formulas of the pseudodifferential calculus produce amplitudes depending on both positions.
Amplitudes with proper input support, vanishing for input positions outside a compact set as long
as the output position stays in a compact set, reduce to left symbols
(`TauCeti.Amplitude.leftSymbol`, in `TauCeti.Analysis.Pseudodifferential.Amplitude.LeftSymbol`);
these include the amplitudes supported near the diagonal of properly supported operators.

## Main declarations

* `TauCeti.Amplitude`: amplitudes, their module structure and order inclusion
  (`TauCeti.Amplitude.inclusion`), and the derivatives `TauCeti.Amplitude.spatialDerivFst`
  (`∂_{x_j}`), `TauCeti.Amplitude.spatialDerivSnd` (`∂_{y_j}`) and
  `TauCeti.Amplitude.frequencyDeriv` (`∂_{ξ_j}`, lowering the order by one), which commute with
  each other (`TauCeti.Amplitude.spatialDerivFst_spatialDerivSnd_comm` and its companions).
* `TauCeti.Amplitude.exists_norm_mixedDeriv_le_of_leibniz`: symbol estimates for a family of
  functions of `(x, ξ)` built from amplitudes, from its Leibniz rules and a bound on the family.
* `TauCeti.Amplitude.diagonal`: the restriction `(x, ξ) ↦ a(x, x, ξ)` of an amplitude to the
  diagonal, a symbol of order `m`, with the Leibniz rules `TauCeti.Amplitude.spatialDeriv_diagonal`
  and `TauCeti.Amplitude.frequencyDeriv_diagonal`.
* `TauCeti.Amplitude.ofLeft` and `TauCeti.Amplitude.ofRight`: the left and right quantization
  amplitudes `b(x, ξ)` and `b(y, ξ)` of a symbol `b`.
* `TauCeti.Amplitude.ofBoundedFrequencySupport`: a smooth coefficient vanishing at all large
  frequencies, an amplitude of every order; so a smooth coefficient agreeing with an amplitude at
  all large frequencies is an amplitude of the same order
  (`TauCeti.Amplitude.exists_coefficient_eq_of_forall_le_norm`).
* `TauCeti.Amplitude.smulPositions`: the product `φ(x, y) a(x, y, ξ)` with a smooth function of the
  positions, an amplitude of the same order; cutoffs `φ(x, y) = χ(x - y)` localize the kernel near
  the diagonal.
* `TauCeti.Amplitude.HasProperInputSupport`: for output positions in a compact set, the amplitude
  vanishes for input positions outside a compact set; then its estimates hold uniformly in `y`
  for `x` in a compact set (`TauCeti.Amplitude.HasProperInputSupport.exists_bound`). Amplitudes
  supported near the diagonal have it (`TauCeti.Amplitude.hasProperInputSupport_of_lt_dist`).
* `TauCeti.Amplitude.HasProperInputSupport.exists_norm_fourier_slice_le`: rapid decay
  `‖â(x, θ, ξ)‖ ≤ C ⟨ξ⟩^m ⟨θ⟩^(-r)` of the Fourier transform `â(x, θ, ξ)` of the input slice
  `y ↦ a(x, y, ξ)`, uniformly for `x` in a compact set, and
  `TauCeti.Amplitude.HasProperInputSupport.fourier_spatialDerivSnd_slice`, the Fourier transform
  of `∂_{y_j} a`.
* `TauCeti.quantizeAmplitudeValue`: the quantization of an amplitude on a Schwartz function, with
  `TauCeti.quantizeAmplitudeValue_eq_smul_oscillatoryIntegral` identifying it with the oscillatory
  integral above, and `TauCeti.quantizeAmplitudeValue_eq_quantizeSchwartzValue` with the
  quantization of a symbol when `a` does not depend on `y`.

## References

* M. E. Taylor, *Pseudodifferential Operators*, Princeton University Press, 1981, Chapter II,
  §§1–2.
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

/-- Appending an output-position direction, when there are no other directions. -/
theorem amplitudeDirections_append_singleton_left (α : List (Fin n)) (j : Fin n) :
    amplitudeDirections (α ++ [j]) [] [] =
      amplitudeDirections α [] [] ++ [(EuclideanSpace.single j 1, 0, 0)] := by
  simp [amplitudeDirections_def, Prod.mk_zero_zero]

/-- Appending an input-position direction, when there are no frequency directions. -/
theorem amplitudeDirections_append_singleton_mid (α γ : List (Fin n)) (j : Fin n) :
    amplitudeDirections α (γ ++ [j]) [] =
      amplitudeDirections α γ [] ++ [(0, EuclideanSpace.single j 1, 0)] := by
  simp [amplitudeDirections_def]

/-- Appending a frequency direction. -/
theorem amplitudeDirections_append_singleton_right (α γ β : List (Fin n)) (j : Fin n) :
    amplitudeDirections α γ (β ++ [j]) =
      amplitudeDirections α γ β ++ [(0, 0, EuclideanSpace.single j 1)] := by
  simp [amplitudeDirections_def]

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

/-- Two amplitude-function pairs whose applied input slices agree at output position `x` quantize
to the same value at `x`. -/
theorem quantizeAmplitudeValue_congr_apply_at {V₁ V₂ : Type*} [NormedAddCommGroup V₁]
    [NormedSpace ℂ V₁] [NormedAddCommGroup V₂] [NormedSpace ℂ V₂]
    {a₁ : E × E × E → V₁ →L[ℂ] W} {a₂ : E × E × E → V₂ →L[ℂ] W}
    {u₁ : 𝓢(E, V₁)} {u₂ : 𝓢(E, V₂)} {x : E}
    (h : ∀ y ξ, a₁ (x, y, ξ) (u₁ y) = a₂ (x, y, ξ) (u₂ y)) :
    quantizeAmplitudeValue a₁ u₁ x = quantizeAmplitudeValue a₂ u₂ x := by
  simp only [quantizeAmplitudeValue_def]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  dsimp only
  rw [funext fun y ↦ h y ((2 * π) • ζ)]

/-- Two amplitudes whose coefficients agree on all input positions and frequencies at output
position `x` quantize to the same value at `x`. -/
theorem quantizeAmplitudeValue_congr_at {a₁ a₂ : E × E × E → V →L[ℂ] W}
    (u : 𝓢(E, V)) {x : E} (h : ∀ y ξ, a₁ (x, y, ξ) = a₂ (x, y, ξ)) :
    quantizeAmplitudeValue a₁ u x = quantizeAmplitudeValue a₂ u x :=
  quantizeAmplitudeValue_congr_apply_at fun y ξ ↦ by rw [h y ξ]

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

/-! ### Module structure and order inclusion -/

section Module

theorem coefficient_injective :
    Function.Injective (coefficient : Amplitude n V W m → _ → V →L[ℂ] W) :=
  fun _ _ h ↦ Amplitude.ext h

instance : Zero (Amplitude n V W m) where
  zero :=
    { coefficient := 0
      contDiff_coefficient := contDiff_const
      exists_bound := fun _ _ _ _ _ ↦ ⟨0, le_rfl, fun _ _ _ _ ↦ by simp⟩ }

instance : Add (Amplitude n V W m) where
  add a b :=
    { coefficient := a.coefficient + b.coefficient
      contDiff_coefficient := a.contDiff_coefficient.add b.contDiff_coefficient
      exists_bound := fun K hK α γ β ↦ by
        obtain ⟨C, hC0, ha⟩ := a.exists_bound K hK α γ β
        obtain ⟨D, hD0, hb⟩ := b.exists_bound K hK α γ β
        refine ⟨C + D, add_nonneg hC0 hD0, fun x y hxy ξ ↦ ?_⟩
        rw [iteratedFDerivAlong_add a.contDiff_coefficient b.contDiff_coefficient _ (by simp),
          Pi.add_apply, add_mul]
        exact (norm_add_le _ _).trans (add_le_add (ha x y hxy ξ) (hb x y hxy ξ)) }

instance : SMul ℂ (Amplitude n V W m) where
  smul c a :=
    { coefficient := c • a.coefficient
      contDiff_coefficient := a.contDiff_coefficient.const_smul c
      exists_bound := fun K hK α γ β ↦ by
        obtain ⟨C, hC0, ha⟩ := a.exists_bound K hK α γ β
        refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC0, fun x y hxy ξ ↦ ?_⟩
        rw [iteratedFDerivAlong_const_smul a.contDiff_coefficient c _ (by simp),
          Pi.smul_apply, norm_smul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (ha x y hxy ξ) (norm_nonneg c) }

instance : Neg (Amplitude n V W m) where
  neg a :=
    { coefficient := -a.coefficient
      contDiff_coefficient := a.contDiff_coefficient.neg
      exists_bound := fun K hK α γ β ↦ by
        obtain ⟨C, hC0, ha⟩ := a.exists_bound K hK α γ β
        refine ⟨C, hC0, fun x y hxy ξ ↦ ?_⟩
        rw [iteratedFDerivAlong_neg, Pi.neg_apply, norm_neg]
        exact ha x y hxy ξ }

instance : Sub (Amplitude n V W m) where sub a b := a + -b
instance : SMul ℕ (Amplitude n V W m) where smul k a := (k : ℂ) • a
instance : SMul ℤ (Amplitude n V W m) where smul k a := (k : ℂ) • a

@[simp]
theorem coefficient_zero : (0 : Amplitude n V W m).coefficient = 0 := (rfl)

@[simp]
theorem coefficient_add (a b : Amplitude n V W m) :
    (a + b).coefficient = a.coefficient + b.coefficient := (rfl)

@[simp]
theorem coefficient_smul (c : ℂ) (a : Amplitude n V W m) :
    (c • a).coefficient = c • a.coefficient := (rfl)

@[simp]
theorem coefficient_neg (a : Amplitude n V W m) : (-a).coefficient = -a.coefficient := (rfl)

@[simp]
theorem coefficient_sub (a b : Amplitude n V W m) :
    (a - b).coefficient = a.coefficient - b.coefficient := (sub_eq_add_neg _ _).symm

@[simp]
theorem coefficient_nsmul (k : ℕ) (a : Amplitude n V W m) :
    (k • a).coefficient = k • a.coefficient := Nat.cast_smul_eq_nsmul ℂ k a.coefficient

@[simp]
theorem coefficient_zsmul (k : ℤ) (a : Amplitude n V W m) :
    (k • a).coefficient = k • a.coefficient := Int.cast_smul_eq_zsmul ℂ k a.coefficient

instance : AddCommGroup (Amplitude n V W m) :=
  coefficient_injective.addCommGroup _ coefficient_zero coefficient_add coefficient_neg
    coefficient_sub (fun a k ↦ coefficient_nsmul k a) (fun a k ↦ coefficient_zsmul k a)

instance : Module ℂ (Amplitude n V W m) :=
  coefficient_injective.module ℂ ⟨⟨coefficient, coefficient_zero⟩, coefficient_add⟩ coefficient_smul

/-- Order inclusion `A^m ⊆ A^{m'}` for `m ≤ m'`. -/
def inclusion {m' : ℝ} (h : m ≤ m') (a : Amplitude n V W m) : Amplitude n V W m' where
  coefficient := a.coefficient
  contDiff_coefficient := a.contDiff_coefficient
  exists_bound K hK α γ β := by
    obtain ⟨C, hC0, hC⟩ := a.exists_bound K hK α γ β
    refine ⟨C, hC0, fun x y hxy ξ ↦ (hC x y hxy ξ).trans ?_⟩
    gcongr
    nlinarith [sq_nonneg ‖ξ‖]

@[simp]
theorem coefficient_inclusion {m' : ℝ} (h : m ≤ m') (a : Amplitude n V W m) :
    (inclusion h a).coefficient = a.coefficient := (rfl)

end Module

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

/-- Without output position derivatives, the amplitude directions project to the mixed
derivative directions of the input position and the frequency. -/
private theorem map_snd_amplitudeDirections_nil (γ β : List (Fin n)) :
    (amplitudeDirections [] γ β).map
        (ContinuousLinearMap.snd ℝ (CoordinateSpace n) (CoordinateSpace n × CoordinateSpace n)) =
      mixedDirections γ β := by
  simp [amplitudeDirections, Function.comp_def]

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
      rw [map_snd_amplitudeDirections_nil,
        ← mixedDeriv_eq_iteratedFDerivAlong _ _ (b.contDiff_coefficient.of_le (by simp))]
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

private theorem exists_bound_ofLeft (b : Symbol n V W m)
    {K : Set (CoordinateSpace n × CoordinateSpace n)} (hK : IsCompact K) (α γ β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ,
      ‖iteratedFDerivAlong ℝ (amplitudeDirections α γ β)
        (fun p ↦ b.coefficient (p.1, p.2.2)) (x, y, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  set L : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n →L[ℝ]
      CoordinateSpace n × CoordinateSpace n :=
    (ContinuousLinearMap.fst ℝ _ _).prod
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
  have hL : ∀ p, HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      (p.1, p.2.2)) L p :=
    fun p ↦ hasFDerivAt_fst.prodMk (hasFDerivAt_snd.comp p hasFDerivAt_snd)
  obtain ⟨C, hC0, hC⟩ := b.exists_bound (Prod.fst '' K) (hK.image continuous_fst) α β
  refine ⟨C, hC0, fun x y hxy ξ ↦ ?_⟩
  rw [iteratedFDerivAlong_comp_of_hasFDerivAt hL b.contDiff_coefficient _ (by simp)]
  cases γ with
  | nil =>
    have hmap : (amplitudeDirections α [] β).map L = mixedDirections α β := by
      simp [amplitudeDirections_def, mixedDirections_def, L, Function.comp_def]
    rw [hmap, ← mixedDeriv_eq_iteratedFDerivAlong _ _ (b.contDiff_coefficient.of_le (by simp))]
    exact hC x ⟨(x, y), hxy, rfl⟩ ξ
  | cons j γ' =>
    have hL0 : L (0, EuclideanSpace.single j 1, 0) = 0 := by simp [L]
    have hperm : ((amplitudeDirections α (j :: γ') β).map L).Perm
        ((0 : CoordinateSpace n × CoordinateSpace n) :: (amplitudeDirections α γ' β).map L) := by
      simp only [amplitudeDirections_def, List.map_cons, List.append_assoc, List.map_append,
        List.cons_append]
      rw [hL0]
      exact List.perm_middle
    rw [hperm.iteratedFDerivAlong_eq b.contDiff_coefficient (by simp),
      iteratedFDerivAlong_cons_apply, map_zero, norm_zero]
    positivity

/-- The amplitude `a(x, y, ξ) = b(x, ξ)` of the **left quantization** of a symbol `b`. -/
def ofLeft (b : Symbol n V W m) : Amplitude n V W m where
  coefficient p := b.coefficient (p.1, p.2.2)
  contDiff_coefficient :=
    b.contDiff_coefficient.comp (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))
  exists_bound _ hK α γ β := exists_bound_ofLeft b hK α γ β

@[simp]
theorem coefficient_ofLeft (b : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (ofLeft b).coefficient p = b.coefficient (p.1, p.2.2) := (rfl)

@[simp]
theorem spatialDerivSnd_ofLeft (j : Fin n) (b : Symbol n V W m) :
    spatialDerivSnd j (ofLeft b) = 0 := by
  refine Amplitude.ext (funext fun p ↦ ?_)
  have h : HasFDerivAt (ofLeft b).coefficient _ p :=
    (b.contDiff_coefficient.differentiable (by simp) _).hasFDerivAt.comp p
      (hasFDerivAt_fst.prodMk (hasFDerivAt_snd.comp p hasFDerivAt_snd))
  rw [coefficient_spatialDerivSnd, coefficient_zero, Pi.zero_apply, h.fderiv]
  simp [Prod.mk_zero_zero]

/-- The derivatives of the amplitude `b(y, ξ)` of a right quantization in the input position and
the frequency are those of `b`. -/
theorem iteratedFDerivAlong_amplitudeDirections_nil_ofRight (b : Symbol n V W m)
    (γ β : List (Fin n)) (x y ξ : CoordinateSpace n) :
    iteratedFDerivAlong ℝ (amplitudeDirections [] γ β) (ofRight b).coefficient (x, y, ξ) =
      mixedDeriv γ β b.coefficient y ξ := by
  rw [show (ofRight b).coefficient = fun p ↦ b.coefficient p.2 from
      funext (coefficient_ofRight b),
    iteratedFDerivAlong_comp_of_hasFDerivAt (fun _ ↦ hasFDerivAt_snd) b.contDiff_coefficient _
      (by simp), map_snd_amplitudeDirections_nil,
    ← mixedDeriv_eq_iteratedFDerivAlong _ _ (b.contDiff_coefficient.of_le (by simp))]

/-! ### Coefficients with bounded frequency support -/

section BoundedFrequencySupport

/-- A smooth coefficient vanishing at every frequency of norm at least `R` satisfies the
amplitude estimates of every order. -/
private theorem exists_bound_of_forall_le_norm_eq_zero
    {f : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W}
    (hf : ContDiff ℝ ∞ f) (R : ℝ) (hR : ∀ x y ξ, R ≤ ‖ξ‖ → f (x, y, ξ) = 0) (s : ℝ)
    {K : Set (CoordinateSpace n × CoordinateSpace n)} (hK : IsCompact K)
    (ds : List (CoordinateSpace n × CoordinateSpace n × CoordinateSpace n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ,
      ‖iteratedFDerivAlong ℝ ds f (x, y, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (s / 2) := by
  -- On `K × closedBall 0 R` the continuous quotient of the derivative by the weight is bounded;
  -- beyond the radius `R` the coefficient vanishes on a neighbourhood, and so do its derivatives.
  have hw : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      (1 + ‖q.2‖ ^ 2) ^ (s / 2) :=
    (continuous_const.add (continuous_snd.norm.pow 2)).rpow_const fun q ↦
      Or.inl (by positivity : (0 : ℝ) < 1 + ‖q.2‖ ^ 2).ne'
  have hD : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      ‖iteratedFDerivAlong ℝ ds f (q.1.1, q.1.2, q.2)‖ :=
    ((hf.iteratedFDerivAlong (m := 0) ds (by simp)).continuous.comp (by fun_prop)).norm
  obtain ⟨M, hM⟩ := (hK.prod (isCompact_closedBall (0 : CoordinateSpace n) R))
    |>.exists_bound_of_continuousOn (hD.div hw fun q ↦ (rpow_weight_pos q.2 _).ne').continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x y hxy ξ ↦ ?_⟩
  rcases le_or_gt ‖ξ‖ R with hξ | hξ
  · have h := hM ((x, y), ξ) ⟨hxy, mem_closedBall_zero_iff.2 hξ⟩
    rw [Real.norm_eq_abs] at h
    rw [← div_le_iff₀ (rpow_weight_pos ξ _)]
    exact (le_abs_self _).trans (h.trans (le_max_left M 0))
  · have hzero : f =ᶠ[𝓝 (x, y, ξ)] 0 := by
      filter_upwards [(isOpen_lt continuous_const
        (continuous_norm.comp (continuous_snd.comp continuous_snd))).mem_nhds hξ] with q hq
      exact hR q.1 q.2.1 q.2.2 hq.le
    rw [iteratedFDerivAlong_eq_zero_of_eventuallyEq_zero hzero, norm_zero]
    exact mul_nonneg (le_max_right _ _) (rpow_weight_pos ξ _).le

/-- A smooth coefficient vanishing at every frequency of norm at least `R`, such as the difference
of a coefficient and an amplitude agreeing at large frequencies, is an amplitude of every order
`m`. -/
def ofBoundedFrequencySupport
    (f : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (hf : ContDiff ℝ ∞ f) (R : ℝ) (hR : ∀ x y ξ, R ≤ ‖ξ‖ → f (x, y, ξ) = 0) :
    Amplitude n V W m where
  coefficient := f
  contDiff_coefficient := hf
  exists_bound _ hK α γ β :=
    exists_bound_of_forall_le_norm_eq_zero hf R hR _ hK (amplitudeDirections α γ β)

@[simp]
theorem coefficient_ofBoundedFrequencySupport
    (f : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (hf : ContDiff ℝ ∞ f) (R : ℝ) (hR : ∀ x y ξ, R ≤ ‖ξ‖ → f (x, y, ξ) = 0) :
    (ofBoundedFrequencySupport f hf R hR : Amplitude n V W m).coefficient = f :=
  (rfl)

/-- A smooth coefficient that agrees with an amplitude `b` of order `m' ≤ m` at all frequencies of
norm at least `R` is an amplitude of order `m`: the difference vanishes at large frequencies. -/
theorem exists_coefficient_eq_of_forall_le_norm
    {f : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W}
    (hf : ContDiff ℝ ∞ f) {m' : ℝ} (b : Amplitude n V W m') (hm : m' ≤ m) (R : ℝ)
    (h : ∀ x y ξ, R ≤ ‖ξ‖ → f (x, y, ξ) = b.coefficient (x, y, ξ)) :
    ∃ c : Amplitude n V W m, c.coefficient = f := by
  -- `f` is `b` plus the difference `f - b`, an amplitude of every order.
  have hg : ContDiff ℝ ∞ (f - b.coefficient) := hf.sub b.contDiff_coefficient
  let d : Amplitude n V W m := ofBoundedFrequencySupport (f - b.coefficient) hg R
    fun x y ξ hξ ↦ sub_eq_zero.2 (h x y ξ hξ)
  refine ⟨⟨f, hf, fun K hK α γ β ↦ ?_⟩, rfl⟩
  obtain ⟨C, hC0, hC⟩ := b.exists_bound K hK α γ β
  obtain ⟨D, hD0, hD⟩ := d.exists_bound K hK α γ β
  refine ⟨C + D, add_nonneg hC0 hD0, fun x y hxy ξ ↦ ?_⟩
  have e : f = b.coefficient + d.coefficient := by simp [d]
  rw [e, iteratedFDerivAlong_add b.contDiff_coefficient d.contDiff_coefficient _ (by simp),
    Pi.add_apply, add_mul]
  exact (norm_add_le _ _).trans (add_le_add ((hC x y hxy ξ).trans
    (mul_le_mul_of_nonneg_left (rpow_weight_le_rpow_weight ξ (by linarith)) hC0))
    (hD x y hxy ξ))

end BoundedFrequencySupport

/-! ### Multiplication by functions of the positions -/

section SMulPositions

/-- The pair of positions `(x, y)` of a point `(x, y, ξ)`, as a continuous linear map. -/
private def positions :
    CoordinateSpace n × CoordinateSpace n × CoordinateSpace n →L[ℝ]
      CoordinateSpace n × CoordinateSpace n :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

private theorem positions_apply (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    positions p = (p.1, p.2.1) :=
  (rfl)

/-- The derivative of `p ↦ φ(x, y) • f(p)` along `v`: the product rule, where the derivative of `φ`
only sees the position components of `v`. -/
private theorem iteratedFDerivAlong_singleton_smul_positions
    {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {f : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W}
    (hf : ContDiff ℝ ∞ f) (v : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    iteratedFDerivAlong ℝ [v] (fun p ↦ φ (positions p) • f p) =
      (fun p ↦ fderiv ℝ φ (positions p) (positions v) • f p) +
        fun p ↦ φ (positions p) • iteratedFDerivAlong ℝ [v] f p := by
  funext p
  have hc : HasFDerivAt (fun p ↦ φ (positions p)) ((fderiv ℝ φ (positions p)).comp positions) p :=
    (hφ.differentiable (by simp) _).hasFDerivAt.comp p positions.hasFDerivAt
  simp only [Pi.add_apply, iteratedFDerivAlong_cons_apply, iteratedFDerivAlong_nil]
  rw [fderiv_fun_smul hc.differentiableAt (hf.differentiable (by simp) p), hc.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply]
  rw [add_comm]

private theorem smul_positions_contDiff {φ : CoordinateSpace n × CoordinateSpace n → ℂ}
    (hφ : ContDiff ℝ ∞ φ)
    {f : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ fun p ↦ φ (positions p) • f p :=
  (hφ.comp positions.contDiff).smul hf

/-- The product rule for the derivative along `v` applied first, followed by the derivatives
along `ds`. -/
private theorem iteratedFDerivAlong_append_singleton_smul_positions
    {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {f : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W}
    (hf : ContDiff ℝ ∞ f) (ds : List (CoordinateSpace n × CoordinateSpace n × CoordinateSpace n))
    (v : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    iteratedFDerivAlong ℝ (ds ++ [v]) (fun p ↦ φ (positions p) • f p) =
      iteratedFDerivAlong ℝ ds (fun p ↦ fderiv ℝ φ (positions p) (positions v) • f p) +
        iteratedFDerivAlong ℝ ds (fun p ↦ φ (positions p) • iteratedFDerivAlong ℝ [v] f p) := by
  rw [iteratedFDerivAlong_append, iteratedFDerivAlong_singleton_smul_positions hφ hf,
    iteratedFDerivAlong_add
      (smul_positions_contDiff ((hφ.fderiv_right le_rfl).clm_apply contDiff_const) hf)
      (smul_positions_contDiff hφ (hf.iteratedFDerivAlong [v] (by simp))) _ (by simp)]

/-- The induction step of `exists_bound_smul_positions` for a derivative along `v` that falls on
`φ` or on `a`: bounds for the two terms of the product rule bound their sum. Here `b` is the
amplitude `∂_v a`. -/
private theorem exists_bound_append_singleton_smul_positions {m : ℝ} {a : Amplitude n V W m}
    {v : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n} (b : Amplitude n V W m)
    (hb : b.coefficient = iteratedFDerivAlong ℝ [v] a.coefficient)
    {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {ds es : List (CoordinateSpace n × CoordinateSpace n × CoordinateSpace n)}
    (hes : es = ds ++ [v]) {K : Set (CoordinateSpace n × CoordinateSpace n)} {e : ℝ}
    (h₁ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ, ‖iteratedFDerivAlong ℝ ds
      (fun p ↦ fderiv ℝ φ (positions p) (positions v) • a.coefficient p) (x, y, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ e)
    (h₂ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ, ‖iteratedFDerivAlong ℝ ds
      (fun p ↦ φ (positions p) • b.coefficient p) (x, y, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ, ‖iteratedFDerivAlong ℝ es
      (fun p ↦ φ (positions p) • a.coefficient p) (x, y, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ e := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂0, hC₂⟩ := h₂
  refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x y hxy ξ ↦ ?_⟩
  rw [hes, iteratedFDerivAlong_append_singleton_smul_positions hφ a.contDiff_coefficient, ← hb,
    Pi.add_apply, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC₁ x y hxy ξ) (hC₂ x y hxy ξ))

/-- The induction step of `exists_bound_smul_positions` for a frequency derivative `∂_{ξ_j}`: it
does not see `φ`, and falls on `a` as the amplitude `∂_{ξ_j} a` of order `m - 1`. -/
private theorem exists_bound_append_frequency_smul_positions {m : ℝ} {a : Amplitude n V W m}
    (j : Fin n) {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {α γ β : List (Fin n)} {K : Set (CoordinateSpace n × CoordinateSpace n)}
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ, ‖iteratedFDerivAlong ℝ
      (amplitudeDirections α γ β) (fun p ↦ φ (positions p) • (frequencyDeriv j a).coefficient p)
        (x, y, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - 1 - β.length) / 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ, ‖iteratedFDerivAlong ℝ
      (amplitudeDirections α γ (β ++ [j])) (fun p ↦ φ (positions p) • a.coefficient p)
        (x, y, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - (β ++ [j]).length) / 2) := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, hC0, fun x y hxy ξ ↦ ?_⟩
  have hd : amplitudeDirections α γ (β ++ [j]) =
      amplitudeDirections α γ β ++ [(0, 0, EuclideanSpace.single j 1)] := by
    simp [amplitudeDirections_def]
  have hzero : (fun p ↦ fderiv ℝ φ (positions p) (positions
      ((0, 0, EuclideanSpace.single j 1) :
        CoordinateSpace n × CoordinateSpace n × CoordinateSpace n)) • a.coefficient p) = 0 := by
    funext p
    simp [positions_apply, Prod.mk_zero_zero]
  rw [hd, iteratedFDerivAlong_append_singleton_smul_positions hφ a.contDiff_coefficient, hzero,
    iteratedFDerivAlong_zero, zero_add]
  refine (hC x y hxy ξ).trans_eq ?_
  simp only [List.length_append, List.length_cons, List.length_nil]
  push_cast
  ring_nf

/-- The estimates of an amplitude multiplied by a smooth function `φ(x, y)` of the positions, by
induction on the number of derivatives, peeling off the derivative applied first with the product
rule. -/
private theorem exists_bound_smul_positions :
    ∀ (k : ℕ) (α γ β : List (Fin n)), α.length + γ.length + β.length = k →
      ∀ {m : ℝ} (a : Amplitude n V W m) {φ : CoordinateSpace n × CoordinateSpace n → ℂ},
        ContDiff ℝ ∞ φ → ∀ K : Set (CoordinateSpace n × CoordinateSpace n), IsCompact K →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ,
            ‖iteratedFDerivAlong ℝ (amplitudeDirections α γ β)
                (fun p ↦ φ (positions p) • a.coefficient p) (x, y, ξ)‖ ≤
              C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  intro k
  induction k with
  | zero =>
    intro α γ β hk m a φ hφ K hK
    obtain ⟨rfl, rfl, rfl⟩ : α = [] ∧ γ = [] ∧ β = [] := by
      simp only [Nat.add_eq_zero_iff, List.length_eq_zero_iff] at hk
      exact ⟨hk.1.1, hk.1.2, hk.2⟩
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hφ.continuous.continuousOn
    obtain ⟨C, hC0, hC⟩ := a.exists_bound K hK [] [] []
    refine ⟨max M 0 * C, by positivity, fun x y hxy ξ ↦ ?_⟩
    simp only [amplitudeDirections_def, List.map_nil, List.append_nil, iteratedFDerivAlong_nil,
      positions_apply, List.length_nil, CharP.cast_eq_zero, sub_zero] at hC ⊢
    rw [norm_smul, mul_assoc]
    exact mul_le_mul ((hM _ hxy).trans (le_max_left _ _)) (by simpa using hC x y hxy ξ)
      (norm_nonneg _) (le_max_right _ _)
  | succ k ih =>
    intro α γ β hk m a φ hφ K hK
    have hφ' (w : CoordinateSpace n × CoordinateSpace n) :
        ContDiff ℝ ∞ fun q ↦ fderiv ℝ φ q w :=
      (hφ.fderiv_right le_rfl).clm_apply contDiff_const
    -- Peel off the derivative applied first, along the last direction of the list. A position
    -- derivative falls on `φ` or on `a`; a frequency derivative falls on `a` only.
    obtain hβ | ⟨β', j, rfl⟩ := β.eq_nil_or_concat'
    · subst hβ
      obtain hγ | ⟨γ', j, rfl⟩ := γ.eq_nil_or_concat'
      · subst hγ
        obtain hα | ⟨α', j, rfl⟩ := α.eq_nil_or_concat'
        · simp [hα] at hk
        have hk' : α'.length + ([] : List (Fin n)).length + ([] : List (Fin n)).length = k := by
          simpa using hk
        exact exists_bound_append_singleton_smul_positions (spatialDerivFst j a)
          (coefficient_spatialDerivFst_eq_iteratedFDerivAlong j a) hφ
          (by simp [amplitudeDirections_def]) (ih α' [] [] hk' a (hφ' _) K hK)
          (ih α' [] [] hk' _ hφ K hK)
      have hk' : α.length + γ'.length + ([] : List (Fin n)).length = k := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hk ⊢
        omega
      exact exists_bound_append_singleton_smul_positions (spatialDerivSnd j a)
        (coefficient_spatialDerivSnd_eq_iteratedFDerivAlong j a) hφ
        (by simp [amplitudeDirections_def]) (ih α γ' [] hk' a (hφ' _) K hK)
        (ih α γ' [] hk' _ hφ K hK)
    have hk' : α.length + γ.length + β'.length = k := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hk
      omega
    exact exists_bound_append_frequency_smul_positions j hφ (ih α γ β' hk' _ hφ K hK)

/-- The product `φ(x, y) a(x, y, ξ)` of an amplitude with a smooth function of the positions, an
amplitude of the same order. With a cutoff `φ(x, y) = χ(x - y)` it localizes the kernel of the
quantization near the diagonal. -/
def smulPositions (φ : CoordinateSpace n × CoordinateSpace n → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (a : Amplitude n V W m) : Amplitude n V W m where
  coefficient p := φ (p.1, p.2.1) • a.coefficient p
  contDiff_coefficient := by
    simpa only [positions_apply] using smul_positions_contDiff hφ a.contDiff_coefficient
  exists_bound K hK α γ β := by
    simpa only [positions_apply] using exists_bound_smul_positions _ α γ β rfl a hφ K hK

@[simp]
theorem coefficient_smulPositions (φ : CoordinateSpace n × CoordinateSpace n → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (a : Amplitude n V W m)
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (smulPositions φ hφ a).coefficient p = φ (p.1, p.2.1) • a.coefficient p :=
  (rfl)

end SMulPositions

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

/-! ### Proper input support -/

/-- An amplitude has **proper input support** if, for output positions in any compact set, it
vanishes at all input positions outside some compact set: the projection of its support to the
output position is proper. This holds for the amplitude of the right quantization of a symbol with
compact spatial support, and for every amplitude supported near the diagonal, such as those of
properly supported operators (`TauCeti.Amplitude.hasProperInputSupport_of_lt_dist`). For each
output position the quantization is then an absolutely convergent iterated integral, and the
amplitude reduces to a left symbol (`TauCeti.Amplitude.leftSymbol`). -/
def HasProperInputSupport (a : Amplitude n V W m) : Prop :=
  ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ L : Set (CoordinateSpace n), IsCompact L ∧
    ∀ x ∈ K, ∀ y ∉ L, ∀ ξ, a.coefficient (x, y, ξ) = 0

theorem hasProperInputSupport_iff {a : Amplitude n V W m} :
    a.HasProperInputSupport ↔ ∀ K : Set (CoordinateSpace n), IsCompact K →
      ∃ L : Set (CoordinateSpace n), IsCompact L ∧
        ∀ x ∈ K, ∀ y ∉ L, ∀ ξ, a.coefficient (x, y, ξ) = 0 :=
  Iff.rfl

/-- Outside a closed set of spatial pairs on which an amplitude vanishes, all its derivatives
vanish. -/
theorem iteratedFDerivAlong_eq_zero_of_notMem {a : Amplitude n V W m}
    {S : Set (CoordinateSpace n × CoordinateSpace n)} (hS : IsClosed S)
    (hSa : ∀ x y, (x, y) ∉ S → ∀ ξ, a.coefficient (x, y, ξ) = 0)
    (vs : List (CoordinateSpace n × CoordinateSpace n × CoordinateSpace n))
    {x y ξ : CoordinateSpace n} (hxy : (x, y) ∉ S) :
    iteratedFDerivAlong ℝ vs a.coefficient (x, y, ξ) = 0 := by
  refine iteratedFDerivAlong_eq_zero_of_eventuallyEq_zero ?_ vs
  have hU : IsOpen {p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n |
      (p.1, p.2.1) ∉ S} :=
    hS.isOpen_compl.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  filter_upwards [hU.mem_nhds hxy] with p hp
  exact hSa p.1 p.2.1 hp p.2.2

/-- An amplitude vanishing at all pairs of positions at distance more than `R` has proper input
support. -/
theorem hasProperInputSupport_of_lt_dist {a : Amplitude n V W m} {R : ℝ}
    (ha : ∀ x y ξ, R < dist x y → a.coefficient (x, y, ξ) = 0) : a.HasProperInputSupport :=
  fun K hK ↦ ⟨Metric.cthickening R K, hK.cthickening, fun x hx y hy ξ ↦
    ha x y ξ (lt_of_not_ge fun h ↦ hy (Metric.mem_cthickening_of_dist_le y x R K hx
      (dist_comm x y ▸ h)))⟩

/-- For output positions near a compact set, an amplitude with proper input support vanishes at
input positions outside a suitable compact set. -/
theorem HasProperInputSupport.exists_eventually_eq_zero {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ L : Set (CoordinateSpace n), IsCompact L ∧
      ∀ᶠ x in 𝓝ˢ K, ∀ y ∉ L, ∀ ξ, a.coefficient (x, y, ξ) = 0 := by
  obtain ⟨L, hL, hLa⟩ := ha _ (hK.cthickening (r := 1))
  exact ⟨L, hL, Filter.mem_of_superset (Metric.cthickening_mem_nhdsSet K one_pos) hLa⟩

/-- Near an output position and frequency, an amplitude with proper input support vanishes for
input positions outside a compact set. -/
theorem HasProperInputSupport.exists_eventually_nhds_eq_zero {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (q : CoordinateSpace n × CoordinateSpace n) :
    ∃ L : Set (CoordinateSpace n), IsCompact L ∧ ∀ᶠ q' in 𝓝 q, ∀ y ∉ L,
      a.coefficient (q'.1, y, q'.2) = 0 := by
  obtain ⟨L, hL, hLa⟩ := ha.exists_eventually_eq_zero (isCompact_singleton (x := q.1))
  rw [nhdsSet_singleton] at hLa
  exact ⟨L, hL, ((continuous_fst.tendsto q).eventually hLa).mono fun q' h y hy ↦ h y hy q'.2⟩

/-- For output positions in a compact set, all derivatives of an amplitude with proper input
support vanish at input positions outside a suitable compact set: there the amplitude vanishes
near the point. -/
private theorem HasProperInputSupport.exists_iteratedFDerivAlong_eq_zero
    {a : Amplitude n V W m} (ha : a.HasProperInputSupport) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) :
    ∃ L : Set (CoordinateSpace n), IsCompact L ∧ ∀ vs, ∀ x ∈ K, ∀ y ∉ L, ∀ ξ,
      iteratedFDerivAlong ℝ vs a.coefficient (x, y, ξ) = 0 := by
  obtain ⟨L, hL, hLa⟩ := ha.exists_eventually_eq_zero hK
  refine ⟨L, hL, fun vs x hx y hy ξ ↦ iteratedFDerivAlong_eq_zero_of_eventuallyEq_zero ?_ vs⟩
  filter_upwards [(continuous_fst.tendsto (x, y, ξ)).eventually (hLa.filter_mono
    (nhds_le_nhdsSet hx)), (continuous_fst.comp continuous_snd).continuousAt.preimage_mem_nhds
    (hL.isClosed.isOpen_compl.mem_nhds hy)] with p hp hpy
  exact hp p.2.1 hpy p.2.2

private theorem HasProperInputSupport.iteratedFDerivAlong_singleton {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (d : CoordinateSpace n × CoordinateSpace n ×
      CoordinateSpace n) :
    ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ L : Set (CoordinateSpace n), IsCompact L ∧
      ∀ x ∈ K, ∀ y ∉ L, ∀ ξ, iteratedFDerivAlong ℝ [d] a.coefficient (x, y, ξ) = 0 :=
  fun _ hK ↦ (ha.exists_iteratedFDerivAlong_eq_zero hK).imp fun _ hL ↦ ⟨hL.1, hL.2 [d]⟩

theorem HasProperInputSupport.spatialDerivFst {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (j : Fin n) : (spatialDerivFst j a).HasProperInputSupport :=
  ha.iteratedFDerivAlong_singleton _

theorem HasProperInputSupport.spatialDerivSnd {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (j : Fin n) : (spatialDerivSnd j a).HasProperInputSupport :=
  ha.iteratedFDerivAlong_singleton _

theorem HasProperInputSupport.frequencyDeriv {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (j : Fin n) : (frequencyDeriv j a).HasProperInputSupport :=
  ha.iteratedFDerivAlong_singleton _

/-- The input-position slices of an amplitude with proper input support are compactly
supported. -/
theorem HasProperInputSupport.hasCompactSupport_slice {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (x ξ : CoordinateSpace n) :
    HasCompactSupport fun y ↦ a.coefficient (x, y, ξ) := by
  obtain ⟨L, hL, hLa⟩ := ha {x} isCompact_singleton
  exact HasCompactSupport.intro hL fun y hy ↦ hLa x rfl y hy ξ

/-- The amplitude of the right quantization of a symbol with compact spatial support has proper
input support. -/
theorem _root_.TauCeti.Symbol.HasCompactSpatialSupport.hasProperInputSupport_ofRight
    {b : Symbol n V W m} (hb : b.HasCompactSpatialSupport) :
    (ofRight b).HasProperInputSupport := by
  obtain ⟨L, hL, hLb⟩ := Symbol.hasCompactSpatialSupport_iff.mp hb
  exact fun _ _ ↦ ⟨L, hL, fun _ _ y hy ξ ↦ hLb y hy ξ⟩

/-- Multiplying by a smooth function of the positions keeps proper input support. -/
theorem HasProperInputSupport.smulPositions {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) {φ : CoordinateSpace n × CoordinateSpace n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) : (a.smulPositions φ hφ).HasProperInputSupport :=
  fun K hK ↦ (ha K hK).imp fun _ hL ↦ ⟨hL.1, fun x hx y hy ξ ↦ by
    rw [coefficient_smulPositions, hL.2 x hx y hy ξ, smul_zero]⟩

/-- Multiplying by a smooth function `φ(x, y)` of the positions vanishing at distance more than `R`
from the diagonal gives proper input support. -/
theorem hasProperInputSupport_smulPositions_of_lt_dist
    {φ : CoordinateSpace n × CoordinateSpace n → ℂ} (hφ : ContDiff ℝ ∞ φ) {R : ℝ}
    (hR : ∀ x y, R < dist x y → φ (x, y) = 0) (a : Amplitude n V W m) :
    (a.smulPositions φ hφ).HasProperInputSupport :=
  hasProperInputSupport_of_lt_dist fun x y ξ h ↦ by
    rw [coefficient_smulPositions, hR x y h, zero_smul]

/-- For an amplitude with proper input support, the estimates hold for all input positions,
uniformly for output positions in a compact set. -/
theorem HasProperInputSupport.exists_bound {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (α γ β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ y ξ,
      ‖iteratedFDerivAlong ℝ (amplitudeDirections α γ β) a.coefficient (x, y, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨L, hL, hLa⟩ := ha.exists_iteratedFDerivAlong_eq_zero hK
  obtain ⟨C, hC0, hC⟩ := a.exists_bound (K ×ˢ L) (hK.prod hL) α γ β
  refine ⟨C, hC0, fun x hx y ξ ↦ ?_⟩
  by_cases hy : y ∈ L
  · exact hC x y ⟨hx, hy⟩ ξ
  · rw [hLa _ x hx y hy ξ, norm_zero]
    positivity

/-! ### The Fourier transform in the input position -/

/-- The derivatives of the input-position slices of an amplitude with proper input support grow
at most like `⟨ξ⟩ ^ m`, uniformly for output positions in a compact set and all input positions. -/
theorem HasProperInputSupport.exists_norm_iteratedFDeriv_slice_le {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (k : ℕ) :
    ∃ D, 0 ≤ D ∧ ∀ x ∈ K, ∀ y ξ,
      ‖iteratedFDeriv ℝ k (fun y ↦ a.coefficient (x, y, ξ)) y‖ ≤
        D * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  choose C hC0 hC using fun r : Fin k → Fin n ↦ ha.exists_bound hK [] (List.ofFn r) []
  refine ⟨∑ r, C r, Finset.sum_nonneg fun r _ ↦ hC0 r, fun x hx y ξ ↦ ?_⟩
  have hsmooth : ContDiff ℝ ∞ fun y ↦ a.coefficient (x, y, ξ) :=
    a.contDiff_coefficient.comp (by fun_prop)
  rw [Finset.sum_mul]
  refine (norm_iteratedFDeriv_le_sum_coordinateDeriv (hsmooth.of_le (by simp)) y).trans
    (Finset.sum_le_sum fun r _ ↦ ?_)
  rw [coordinateDeriv_slice_snd]
  simpa using hC r x hx y ξ

/-- The `L¹` norms of the derivatives of the input-position slices of an amplitude with proper
input support grow at most like `⟨ξ⟩ ^ m`, uniformly for output positions in a compact set. -/
private theorem HasProperInputSupport.exists_integral_norm_iteratedFDeriv_slice_le
    {a : Amplitude n V W m} (ha : a.HasProperInputSupport) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) (k : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ x ∈ K, ∀ ξ,
      ∫ y, ‖iteratedFDeriv ℝ k (fun y ↦ a.coefficient (x, y, ξ)) y‖ ≤
        B * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨L, hL, hLa⟩ := ha K hK
  obtain ⟨D, hD, hDb⟩ := ha.exists_norm_iteratedFDeriv_slice_le hK k
  refine ⟨D * (volume L).toReal, mul_nonneg hD ENNReal.toReal_nonneg, fun x hx ξ ↦ ?_⟩
  -- The `k`-th derivative is bounded by `D ⟨ξ⟩ ^ m` and vanishes outside `L`.
  have hpt : ∀ y, ‖iteratedFDeriv ℝ k (fun y ↦ a.coefficient (x, y, ξ)) y‖ ≤
      L.indicator (fun _ ↦ D * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) y := by
    intro y
    by_cases hy : y ∈ L
    · rw [Set.indicator_of_mem hy]
      exact hDb x hx y ξ
    · rw [Set.indicator_of_notMem hy, norm_le_zero_iff]
      exact image_eq_zero_of_notMem_tsupport fun hmem ↦ hy <|
        (closure_minimal (s := Function.support fun y ↦ a.coefficient (x, y, ξ))
          (fun y hy' ↦ by_contra fun h ↦ Function.mem_support.1 hy' (hLa x hx y h ξ))
          hL.isClosed)
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
`m` with proper input support and every `r`, the Fourier transform `â(x, θ, ξ)` of the input
slice `y ↦ a(x, y, ξ)` satisfies `‖â(x, θ, ξ)‖ ≤ C ⟨ξ⟩ ^ m ⟨θ⟩ ^ (-r)`, uniformly for output
positions `x` in a compact set. -/
theorem HasProperInputSupport.exists_norm_fourier_slice_le {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (r : ℝ) :
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


/-- The Fourier transform `â(x, θ, ξ)` of the input slices of an amplitude with proper input
support is jointly continuous in the dual variable `θ`, the output position `x` and the
frequency `ξ`. -/
theorem HasProperInputSupport.continuous_fourier_slice {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun y ↦ a.coefficient (q.2.1, y, q.2.2)) q.1 := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ ?_
  obtain ⟨L, hL, hLa⟩ := ha.exists_eventually_nhds_eq_zero q₀.2
  simpa only [Real.fourier_eq, Circle.smul_def] using continuousAt_integral_fourierChar_smul
    (g := fun r : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      a.coefficient (r.2.1, r.1, r.2.2))
    (a.contDiff_coefficient.continuous.comp (by fun_prop)) hL hLa

/-- The Fourier transform of the input slices of `∂_{y_j} a` is `2πi θⱼ â(x, θ, ξ)`. -/
theorem HasProperInputSupport.fourier_spatialDerivSnd_slice {a : Amplitude n V W m}
    (ha : a.HasProperInputSupport) (j : Fin n) (θ x ξ : CoordinateSpace n) :
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

/-- The amplitude `b(x, ξ)` of the left quantization of a symbol `b` restricts on the diagonal to
`b`. -/
@[simp]
theorem diagonal_ofLeft (b : Symbol n V W m) : (ofLeft b).diagonal = b := by
  ext1
  funext ⟨x, ξ⟩
  simp

end Diagonal

end Amplitude

end TauCeti

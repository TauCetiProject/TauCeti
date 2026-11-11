/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency
import TauCeti.Analysis.Distribution.TemperateGrowth

/-!
# Frequency multipliers in the Kohn–Nirenberg calculus

A coefficient `b(ξ)` that depends only on the frequency quantizes to a Fourier multiplier
`b(D)`: with the left quantization `Op(a) u (x) = ∫ exp(2πi ⟪x, ζ⟫) a(x, 2πζ) (𝓕 u ζ) dζ` of
`TauCeti.quantizeSchwartzValue`, the Fourier transform of `Op(b) u` is `ζ ↦ b(2πζ) (𝓕 u ζ)`.
For operator-valued `b` of temperate growth this is a continuous linear map of Schwartz spaces,
`TauCeti.quantizeFrequencyCLM b : 𝓢(E, V) →L[ℂ] 𝓢(E, W)`, extending Mathlib's scalar
`SchwartzMap.fourierMultiplierCLM` to matrix-valued (bundle) symbols.

Composition on the right with a frequency multiplier is exact in the left quantization:
`Op(a) ∘ Op(b) = Op(a b)`, with the pointwise product `a(x, ξ) ∘ b(ξ)`, and no lower-order
correction (`TauCeti.quantizeSchwartzValue_quantizeFrequencyCLM`). In particular composing a
quantization with Mathlib's Bessel potential `J^s`, the Fourier multiplier
`(1 + ‖ζ‖²) ^ (s / 2)` in Mathlib's frequency `ζ`, multiplies its symbol by the Bessel weight
`(1 + ‖ξ / 2π‖²) ^ (s / 2)` in the angular frequency `ξ = 2πζ`. Composition on the left is not
exact and needs the full composition calculus.

On `ℝⁿ`, a smooth coefficient `b(ξ)` with `‖D^k b(ξ)‖ ≤ C_k ⟨ξ⟩ ^ (m - k)` is a symbol of order
`m` with estimates uniform in the position (`TauCeti.Symbol.ofFrequency`), and its quantization
is `b(D)`. For the examples of `TauCeti.Analysis.Pseudodifferential.Symbol.Frequency`, the
quantization of the Bessel weight (`TauCeti.Symbol.besselPotential`, of order `s`) is Mathlib's
Fourier multiplier `(1 + ‖ζ‖²) ^ (s / 2)`, the Schwartz-space form of
`TemperedDistribution.besselPotential`, and the quantization of the linear coefficient `⟪ξ, v⟫`
(`TauCeti.Symbol.ofInner`) is `-i ∂_v`.

## Main declarations

* `TauCeti.quantizeFrequencyCLM`: the Fourier multiplier `b(D)` of an operator-valued
  frequency coefficient, with `TauCeti.fourier_quantizeFrequencyCLM_apply` and
  `TauCeti.quantizeSchwartzValue_comp_snd`.
* `TauCeti.quantizeSchwartzValue_quantizeFrequencyCLM`: `Op(a) (b(D) u) = Op(a b) u`, and
  `TauCeti.quantizeSchwartzValue_fourierMultiplierCLM` for Mathlib's scalar multipliers, which
  are frequency multipliers by `TauCeti.fourierMultiplierCLM_eq_quantizeFrequencyCLM`.
* `TauCeti.quantizeFrequencyCLM_comp`: frequency multipliers compose by the pointwise product.
* `TauCeti.quantizeFrequencyCLM_besselWeight`,
  `TauCeti.toTemperedDistribution_quantizeFrequencyCLM_besselPotential`: the Bessel weight
  quantizes to Mathlib's Bessel multiplier and Bessel potential.
* `TauCeti.Symbol.quantizeSchwartzValue_ofFrequency`: the frequency-only symbol
  `TauCeti.Symbol.ofFrequency` quantizes to `b(D)`.
* `TauCeti.Symbol.quantizeSchwartzValue_besselPotential` and
  `TauCeti.Symbol.quantizeSchwartzValue_ofInner`: the quantizations of the example symbols.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.1)–(1.4) and (2.5)–(2.7).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff LineDeriv
open MeasureTheory Real FourierTransform

noncomputable section

namespace TauCeti

section Multiplier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

open scoped Classical in
/-- The quantization `b(D)` of a coefficient `b(ξ)` depending only on the angular frequency, as a
continuous linear map of Schwartz spaces: `u ↦ 𝓕⁻ (ζ ↦ b(2πζ) (𝓕 u ζ))`. For a scalar
coefficient this is Mathlib's `SchwartzMap.fourierMultiplierCLM` with the frequency rescaled by
`2π` (`TauCeti.quantizeFrequencyCLM_smul_id`). If `b` does not have temperate growth, the map is
defined to be `0`. -/
def quantizeFrequencyCLM (b : E → V →L[ℂ] W) : 𝓢(E, V) →L[ℂ] 𝓢(E, W) :=
  if hb : b.HasTemperateGrowth then
    fourierInvCLM ℂ 𝓢(E, W) ∘L
      SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ W)
        (g := fun ζ : E ↦ b ((2 * π) • ζ)) (by fun_prop) ∘L
      fourierCLM ℂ 𝓢(E, V)
  else 0

/-- The multiplier of a coefficient without temperate growth is defined to be `0`. -/
theorem quantizeFrequencyCLM_of_not_hasTemperateGrowth {b : E → V →L[ℂ] W}
    (hb : ¬b.HasTemperateGrowth) : quantizeFrequencyCLM b = 0 := by
  simp [quantizeFrequencyCLM, hb]

variable [CompleteSpace W] {b : E → V →L[ℂ] W}

/-- The Fourier transform of `b(D) u` is `ζ ↦ b(2πζ) (𝓕 u ζ)`. -/
@[simp]
theorem fourier_quantizeFrequencyCLM_apply (hb : b.HasTemperateGrowth) (u : 𝓢(E, V)) (ζ : E) :
    𝓕 (quantizeFrequencyCLM b u) ζ = b ((2 * π) • ζ) (𝓕 u ζ) := by
  simp [quantizeFrequencyCLM, hb]

/-- **Quantization of a frequency-only coefficient.** The left quantization of `(x, ξ) ↦ b(ξ)` is
the Fourier multiplier `b(D)`. -/
theorem quantizeSchwartzValue_comp_snd (hb : b.HasTemperateGrowth) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (fun p ↦ b p.2) u x = quantizeFrequencyCLM b u x := by
  conv_rhs => rw [← FourierPair.fourierInv_fourier_eq (F := 𝓢(E, W)) (quantizeFrequencyCLM b u)]
  rw [quantizeSchwartzValue_eq_fourierInv, SchwartzMap.fourierInv_coe]
  exact congrArg (fun f : E → W ↦ 𝓕⁻ f x)
    (funext fun ζ ↦ (fourier_quantizeFrequencyCLM_apply hb u ζ).symm)

/-- **Composition with a frequency multiplier on the right is exact.** In the left quantization,
`Op(a) ∘ b(D) = Op(a b)` for the pointwise product `(a b)(x, ξ) = a(x, ξ) ∘ b(ξ)`. -/
theorem quantizeSchwartzValue_quantizeFrequencyCLM (hb : b.HasTemperateGrowth)
    (a : E × E → W →L[ℂ] U) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue a (quantizeFrequencyCLM b u) x =
      quantizeSchwartzValue (fun p ↦ (a p).comp (b p.2)) u x := by
  simp [quantizeSchwartzValue_def, hb]

/-- Frequency multipliers compose by the pointwise product of their coefficients. -/
theorem quantizeFrequencyCLM_comp [CompleteSpace U] {c : E → W →L[ℂ] U}
    (hb : b.HasTemperateGrowth) (hc : c.HasTemperateGrowth) :
    (quantizeFrequencyCLM c).comp (quantizeFrequencyCLM b) =
      quantizeFrequencyCLM (fun ξ ↦ (c ξ).comp (b ξ)) := by
  have hcb : (fun ξ ↦ (c ξ).comp (b ξ)).HasTemperateGrowth :=
    (ContinuousLinearMap.compL ℂ V W U).bilinear_hasTemperateGrowth hc hb
  ext u x
  rw [ContinuousLinearMap.comp_apply, ← quantizeSchwartzValue_comp_snd hc,
    quantizeSchwartzValue_quantizeFrequencyCLM hb, ← quantizeSchwartzValue_comp_snd hcb]

/-- For a scalar coefficient `g(ξ)`, the multiplier `g(D)` is Mathlib's Fourier multiplier with
the frequency rescaled by `2π`. -/
theorem quantizeFrequencyCLM_smul_id [CompleteSpace V] {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    quantizeFrequencyCLM (fun ξ ↦ g ξ • ContinuousLinearMap.id ℂ V) =
      SchwartzMap.fourierMultiplierCLM V (fun ζ ↦ g ((2 * π) • ζ)) := by
  ext u x
  rw [← quantizeSchwartzValue_comp_snd (by fun_prop),
    quantizeSchwartzValue_eq_fourierMultiplierCLM hg]

omit [CompleteSpace W] in
/-- Mathlib's scalar Fourier multiplier `g(D)` in the frequency `ζ` is the multiplier with
coefficient `g(ξ / 2π)` in the angular frequency `ξ = 2πζ`. -/
theorem fourierMultiplierCLM_eq_quantizeFrequencyCLM [CompleteSpace V] {g : E → ℂ}
    (hg : g.HasTemperateGrowth) :
    SchwartzMap.fourierMultiplierCLM V g =
      quantizeFrequencyCLM (fun ξ ↦ g ((2 * π)⁻¹ • ξ) • ContinuousLinearMap.id ℂ V) := by
  rw [quantizeFrequencyCLM_smul_id (by fun_prop)]
  simp only [inv_smul_smul₀ (by positivity : (2 * π) ≠ 0)]

omit [CompleteSpace W] in
/-- **Composition with a scalar Fourier multiplier on the right.** For Mathlib's multiplier
`g(D)` in the frequency `ζ`, `Op(a) ∘ g(D) = Op(g(ξ / 2π) a)` in the angular frequency `ξ`. -/
theorem quantizeSchwartzValue_fourierMultiplierCLM [CompleteSpace V] {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (a : E × E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue a (SchwartzMap.fourierMultiplierCLM V g u) x =
      quantizeSchwartzValue (fun p ↦ g ((2 * π)⁻¹ • p.2) • a p) u x := by
  rw [fourierMultiplierCLM_eq_quantizeFrequencyCLM hg,
    quantizeSchwartzValue_quantizeFrequencyCLM (by fun_prop)]
  simp

/-- **The Bessel weight quantizes to the Bessel multiplier.** The multiplier with coefficient
`(1 + ‖ξ / 2π‖²) ^ (s / 2)` in the angular frequency `ξ` is Mathlib's Fourier multiplier
`(1 + ‖ζ‖²) ^ (s / 2)` in the frequency `ζ = ξ / 2π`. -/
theorem quantizeFrequencyCLM_besselWeight [CompleteSpace V] (s : ℝ) :
    quantizeFrequencyCLM (fun ξ : E ↦
        (((1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V) =
      SchwartzMap.fourierMultiplierCLM V (fun ζ : E ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) :=
  (fourierMultiplierCLM_eq_quantizeFrequencyCLM
    (g := fun ζ : E ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (by fun_prop)).symm

/-- **The Bessel weight quantizes to the Bessel potential.** As a tempered distribution, the
multiplier with coefficient `(1 + ‖ξ / 2π‖²) ^ (s / 2)` in the angular frequency `ξ` is Mathlib's
Bessel potential `TemperedDistribution.besselPotential E V s`, the multiplier
`(1 + ‖ζ‖²) ^ (s / 2)` in the frequency `ζ = ξ / 2π`. -/
theorem toTemperedDistribution_quantizeFrequencyCLM_besselPotential [CompleteSpace V] (s : ℝ)
    (u : 𝓢(E, V)) :
    (quantizeFrequencyCLM (fun ξ : E ↦
        (((1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V) u :
          𝓢'(E, V)) =
      TemperedDistribution.besselPotential E V s u := by
  rw [quantizeFrequencyCLM_besselWeight, TemperedDistribution.besselPotential,
    TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]

end Multiplier

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

section Frequency

variable {b : CoordinateSpace n → V →L[ℂ] W} (hb : ContDiff ℝ ∞ b)
  (hbound : ∀ k : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k b ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2))

/-- The quantization of a frequency-only symbol is the Fourier multiplier `b(D)`. -/
theorem quantizeSchwartzValue_ofFrequency [CompleteSpace W] (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofFrequency b hb hbound).coefficient u x =
      quantizeFrequencyCLM b u x := by
  rw [funext (coefficient_ofFrequency hb hbound)]
  exact quantizeSchwartzValue_comp_snd
    (Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow hb hbound) u x

end Frequency

section Examples

/-- The quantization of the Bessel weight is the Schwartz-space form of Mathlib's Bessel potential:
the Fourier multiplier `(1 + ‖ζ‖²) ^ (s / 2)` in the frequency `ζ = ξ / 2π`. -/
theorem quantizeSchwartzValue_besselPotential (s : ℝ) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (besselPotential s : Symbol n V V s).coefficient u x =
      SchwartzMap.fourierMultiplierCLM V
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u x := by
  rw [funext (coefficient_besselPotential (n := n) (V := V) s),
    quantizeSchwartzValue_eq_fourierMultiplierCLM
      (g := fun ξ ↦ (((1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) (by fun_prop)]
  simp only [inv_smul_smul₀ (by positivity : (2 * π) ≠ 0)]

/-- The symbol `⟪ξ, v⟫` quantizes to `D_v = -i ∂_v`. -/
theorem quantizeSchwartzValue_ofInner [CompleteSpace V] (v : CoordinateSpace n)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofInner v : Symbol n V V 1).coefficient u x =
      -Complex.I • ∂_{v} u x := by
  rw [funext (coefficient_ofInner (V := V) v)]
  exact quantizeSchwartzValue_inner_eq_lineDerivOp v u x

end Examples

end Symbol

end TauCeti

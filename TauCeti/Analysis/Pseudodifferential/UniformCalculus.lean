/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
public import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Pseudodifferential.OutputSupport

/-!
# Composition of quantizations on Schwartz space

The quantization `Op(a)` of a symbol `a` whose estimates are uniform in the position is a
continuous linear map of Schwartz spaces (`TauCeti.Symbol.quantizeUniformCLM`). This file shows
that these operators compose within the calculus: for a uniform symbol `a` and a symbol `b` with
compact spatial support,

`Op(a) ∘ Op(b) = Op(a # b)`

as continuous linear maps of Schwartz spaces (`TauCeti.Symbol.quantizeUniformCLM_sharp`), where
`a # b` is the composition symbol `TauCeti.Symbol.sharp`. The composition symbol is again uniform
(`TauCeti.Symbol.IsUniform.sharp`), although it does not have compact spatial support in
general. The pointwise form `Op(a) (Op(b) u) = Op(a # b) u`
(`TauCeti.Symbol.quantizeSchwartzValue_quantizeUniformCLM`) holds for every symbol `a`, uniform
or not, since `Op(b) u` is a Schwartz function.

Composition with frequency multipliers stays in this calculus on both sides. On the right it is
exact, `Op(a) ∘ b(D) = Op(a ∘ b)` with the pointwise product of the symbols
(`TauCeti.Symbol.quantizeUniformCLM_comp_quantizeFrequencyCLM`); on the left,
`b(D) ∘ Op(a) = Op(b # a)` for a symbol `a` with compact spatial support
(`TauCeti.Symbol.quantizeFrequencyCLM_comp_quantizeUniformCLM`). For Mathlib's Bessel multiplier
`J^s`, the Fourier multiplier `(1 + ‖ζ‖²) ^ (s / 2)` and Schwartz-space form of
`TemperedDistribution.besselPotential`, these read `Op(a) ∘ J^s = Op(a ∘ ⟨ξ / 2π⟩ ^ s)`
(`TauCeti.Symbol.quantizeUniformCLM_comp_fourierMultiplierCLM`) and
`J^s ∘ Op(a) = Op(⟨ξ / 2π⟩ ^ s # a)`
(`TauCeti.Symbol.fourierMultiplierCLM_comp_quantizeUniformCLM`). The Bessel multipliers are not
properly supported, and `⟨ξ / 2π⟩ ^ s # a` need not have compact spatial support, but it is a
uniform symbol of order `s + m`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (2.5)–(2.7).
-/

public section

noncomputable section

open scoped ContDiff SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### Composition of quantizations -/

section Sharp

variable [CompleteSpace W] [CompleteSpace U] {b : Symbol n V W m}

/-- **Composition of quantizations, pointwise form.** For a symbol `b` with compact spatial
support, `Op(b) u` is a Schwartz function, and `Op(a) (Op(b) u) = Op(a # b) u` for every
symbol `a`. -/
theorem quantizeSchwartzValue_quantizeUniformCLM (a : Symbol n W U m')
    (hb : b.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V)) :
    quantizeSchwartzValue a.coefficient (quantizeUniformCLM b hb.isUniform u) =
      quantizeSchwartzValue (a.sharp b hb).coefficient u := by
  funext x
  rw [quantizeSchwartzValue_sharp hb u x, quantizeSchwartzValue_def, SchwartzMap.fourier_coe,
    coe_quantizeUniformCLM]

/-- **Composition of quantizations.** For a uniform symbol `a` and a symbol `b` with compact
spatial support, `Op(a) ∘ Op(b) = Op(a # b)` as continuous linear maps of Schwartz spaces. -/
theorem quantizeUniformCLM_sharp {a : Symbol n W U m'} (ha : a.IsUniform)
    (hb : b.HasCompactSpatialSupport) :
    quantizeUniformCLM (a.sharp b hb) (ha.sharp hb) =
      (quantizeUniformCLM a ha).comp (quantizeUniformCLM b hb.isUniform) := by
  ext u x
  rw [ContinuousLinearMap.comp_apply, quantizeUniformCLM_apply, quantizeUniformCLM_apply,
    quantizeSchwartzValue_quantizeUniformCLM]

end Sharp

/-! ### Composition with frequency multipliers -/

section Frequency

variable [CompleteSpace W] {b : CoordinateSpace n → V →L[ℂ] W} (hb : ContDiff ℝ ∞ b)
  (hbound : ∀ k : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k b ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2))

/-- **Composition with a frequency multiplier on the right.** For a uniform symbol `a`,
`Op(a) ∘ b(D) = Op(a ∘ b)` exactly, with the pointwise product of `a` and the frequency-only
symbol `b`. -/
theorem quantizeUniformCLM_comp_quantizeFrequencyCLM {a : Symbol n W U m'}
    (ha : a.IsUniform) :
    (quantizeUniformCLM a ha).comp (quantizeFrequencyCLM b) =
      quantizeUniformCLM (a.comp (ofFrequency b hb hbound))
        (ha.comp (isUniform_ofFrequency hb hbound)) := by
  ext u x
  rw [ContinuousLinearMap.comp_apply, quantizeUniformCLM_apply, quantizeUniformCLM_apply,
    quantizeSchwartzValue_quantizeFrequencyCLM
      (Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow hb hbound)]
  have h : (a.comp (ofFrequency b hb hbound)).coefficient =
      fun p ↦ (a.coefficient p).comp (b p.2) :=
    funext fun p ↦ by rw [coefficient_comp, coefficient_ofFrequency]
  rw [h]

/-- **Composition with a frequency multiplier on the left.** For a symbol `a` with compact
spatial support, `b(D) ∘ Op(a) = Op(b # a)`, the quantization of a uniform symbol. -/
theorem quantizeFrequencyCLM_comp_quantizeUniformCLM [CompleteSpace V] {a : Symbol n U V m'}
    (ha : a.HasCompactSpatialSupport) :
    (quantizeFrequencyCLM b).comp (quantizeUniformCLM a ha.isUniform) =
      quantizeUniformCLM ((ofFrequency b hb hbound).sharp a ha)
        ((isUniform_ofFrequency hb hbound).sharp ha) := by
  ext u x
  rw [ContinuousLinearMap.comp_apply, quantizeUniformCLM_apply,
    ← quantizeSchwartzValue_quantizeUniformCLM, quantizeSchwartzValue_ofFrequency]

end Frequency

section Bessel

variable [CompleteSpace V]

/-- **Composition with the Bessel multiplier on the right.** For a uniform symbol `a`, composing
`Op(a)` with Mathlib's Bessel multiplier `J^s`, the Fourier multiplier `(1 + ‖ζ‖²) ^ (s / 2)`,
multiplies the symbol by the Bessel weight `⟨ξ / 2π⟩ ^ s` in the angular frequency `ξ`. -/
theorem quantizeUniformCLM_comp_fourierMultiplierCLM {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ) :
    (quantizeUniformCLM a ha).comp (SchwartzMap.fourierMultiplierCLM V
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))) =
      quantizeUniformCLM (a.comp (besselPotential s)) (ha.comp (isUniform_besselPotential s)) := by
  rw [← quantizeFrequencyCLM_besselWeight]
  simp only [besselPotential_eq_ofFrequency]
  exact quantizeUniformCLM_comp_quantizeFrequencyCLM _ _ ha

/-- **Composition with the Bessel multiplier on the left.** For a symbol `a` with compact
spatial support, composing Mathlib's Bessel multiplier `J^s`, the Fourier multiplier
`(1 + ‖ζ‖²) ^ (s / 2)`, with `Op(a)` gives the quantization of the uniform symbol
`⟨ξ / 2π⟩ ^ s # a` of order `s + m`. -/
theorem fourierMultiplierCLM_comp_quantizeUniformCLM {a : Symbol n U V m}
    (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    (SchwartzMap.fourierMultiplierCLM V
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))).comp
          (quantizeUniformCLM a ha.isUniform) =
      quantizeUniformCLM ((besselPotential s).sharp a ha)
        ((isUniform_besselPotential s).sharp ha) := by
  rw [← quantizeFrequencyCLM_besselWeight]
  simp only [besselPotential_eq_ofFrequency]
  exact quantizeFrequencyCLM_comp_quantizeUniformCLM _ _ ha

end Bessel

end Symbol

end TauCeti

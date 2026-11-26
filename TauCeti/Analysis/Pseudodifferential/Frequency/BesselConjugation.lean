/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
import TauCeti.Analysis.Pseudodifferential.Composition.Uniform.Quantize

/-!
# Conjugation of uniform symbols by Bessel multipliers

Write `J^t` for Mathlib's Bessel multiplier, the Fourier multiplier `(1 + ‖ζ‖²) ^ (t / 2)`; it is
the quantization of the uniform symbol `⟨ξ / 2π⟩ ^ t` of order `t`
(`TauCeti.Symbol.besselPotential`, `TauCeti.Symbol.quantizeUniformCLM_besselPotential`).
Composition with `J^t` on the right is exact: `Op(a) ∘ J^t` is the quantization of
`a ⟨ξ / 2π⟩ ^ t` (`TauCeti.Symbol.quantizeUniformCLM_comp_besselMultiplier`). Composition on the
left is given by the uniform composition symbol `TauCeti.Symbol.uniformSharp`
(`TauCeti.Symbol.quantizeUniformCLM_uniformSharp`), so `J^{s - m} ∘ Op(a) = Op(c)` for the uniform
symbol `c = (besselPotential (s - m)).uniformSharp a ha` of order `s`. Hence, for a uniform symbol
`a` of order `m` and every real `s`,

`J^{s - m} ∘ Op(a) = Op(b) ∘ J^s` with `b = c ⟨ξ / 2π⟩ ^ (-s)` of order `0`

on Schwartz space (`TauCeti.Symbol.IsUniform.exists_besselMultiplier_comp_quantizeUniformCLM_eq`).
This reduces the mapping of `Op(a)` between Bessel-potential spaces of orders `s` and `s - m` to
the boundedness of an operator of order `0`, on `L²` by Calderón–Vaillancourt and on `Lᵖ` by
Calderón–Zygmund.

## Main declarations

* `TauCeti.Symbol.IsUniform.exists_besselMultiplier_comp_quantizeUniformCLM_eq`: conjugating
  `Op(a)` by Bessel multipliers reduces its order to `0`, for complex normed fibres.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3.
-/

public section

noncomputable section

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- **Conjugation by Bessel multipliers.** For a uniform symbol `a` of order `m` and every real
`s` there is a uniform symbol `b` of order `0` with `J^{s - m} ∘ Op(a) = Op(b) ∘ J^s` on Schwartz
space. -/
theorem IsUniform.exists_besselMultiplier_comp_quantizeUniformCLM_eq {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ) :
    ∃ (b : Symbol n V W 0) (hb : b.IsUniform),
      SchwartzMap.fourierMultiplierCLM W
          (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ)) ∘L
        quantizeUniformCLM a ha =
      quantizeUniformCLM b hb ∘L SchwartzMap.fourierMultiplierCLM V
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) := by
  -- `J^{s - m} ∘ Op(a) = Op(c)` for `c = (besselPotential (s - m)).uniformSharp a ha` of order `s`.
  set c := (besselPotential (V := W) (n := n) (s - m)).uniformSharp a ha
  have hc := (isUniform_besselPotential (V := W) (n := n) (s - m)).uniformSharp ha
  -- `Op(c) = Op(b) ∘ J^s` for `b = c ⟨ξ / 2π⟩ ^ (-s)`, of order `s + -s = 0`.
  have hc' := hc.comp (isUniform_besselPotential (V := V) (n := n) (-s))
  have h0 : s - m + m + -s ≤ 0 := by linarith
  refine ⟨Symbol.inclusion h0 (c.comp (besselPotential (-s))), hc'.inclusion h0, ?_⟩
  rw [← quantizeUniformCLM_besselPotential,
    ← quantizeUniformCLM_uniformSharp (isUniform_besselPotential (s - m)) ha,
    quantizeUniformCLM_inclusion hc' h0, quantizeUniformCLM_comp_besselMultiplier]
  exact quantizeUniformCLM_congr _ _ (by
    rw [coefficient_comp_besselPotential_comp_besselPotential, neg_add_cancel,
      coefficient_comp_besselPotential_zero])

end Symbol

end TauCeti

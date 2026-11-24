/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.BesselPotentialSpace
public import TauCeti.Analysis.Pseudodifferential.Lp.CalderonZygmund
import TauCeti.Analysis.Pseudodifferential.Frequency.BesselConjugation

/-!
# Uniform pseudodifferential operators on `H^{s,p}`

Let `a` be a symbol of order `m` on `ℝⁿ`, with values in operators `V →L[ℂ] W` between complex
Hilbert spaces, whose estimates `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(m - |β|)` hold uniformly in
the position (`TauCeti.Symbol.IsUniform`), and let `1 < p < ∞`. This file proves that the operator
`TauCeti.Symbol.quantizeUniformBesselPotentialSpace : H^{s,p}(ℝⁿ; V) → H^{s - m,p}(ℝⁿ; W)` between
Mathlib's Bessel-potential spaces extends the left quantization `Op(a)` from Schwartz functions, for
every real `s` (`TauCeti.Symbol.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM`).
For `p = 2` this is the Sobolev mapping theorem
`TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM`; for symbols with compact spatial support
and finite-dimensional normed fibres it is
`HasCompactSpatialSupport.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM` in the
namespace `TauCeti.Symbol`. Uniform symbols of order `0` include the smooth operator-valued
functions `f` all of whose derivatives are bounded (`TauCeti.Symbol.isUniform_ofSpatial_iff`), so
each gives a bounded operator on every `H^{s,p}`; for finite-dimensional `V` and `W` this operator
is multiplication by `f`, by the lemma `toDistr_quantizeUniformBesselPotentialSpace_ofSpatial` in
the namespace `TauCeti.Symbol.HasBesselPotentialSpaceExtension` applied to
`TauCeti.Symbol.IsUniform.hasBesselPotentialSpaceExtension`.

## The argument

Write `J^t` for the Bessel multiplier, the Fourier multiplier with symbol `⟨ζ⟩ ^ t`, so that the
`H^{r,p}` norm of a Schwartz function `v` is the `Lᵖ` norm of `J^r v`
(`SchwartzMap.norm_toBesselPotentialSpaceCLM_eq_eLpNorm`). Conjugation by Bessel multipliers
reduces the order to `0`
(`TauCeti.Symbol.IsUniform.exists_besselMultiplier_comp_quantizeUniformCLM_eq`):

`J^{s - m} ∘ Op(a) = Op(b) ∘ J^s`

on Schwartz space for a uniform symbol `b` of order `0`. The `Lᵖ` boundedness of `Op(b)`, the
Calderón–Zygmund theorem for pseudodifferential operators of order `0`
(`TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt`), then gives
`‖Op(a) u‖_{H^{s - m,p}} ≤ C ‖u‖_{H^{s,p}}`, and the operator extends by density of the Schwartz
functions.

## Main declarations

* `TauCeti.Symbol.quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM`: the operator
  `H^{s,p} → H^{s - m,p}` extends `Op(a)` from Schwartz functions.
* `TauCeti.Symbol.IsUniform.hasBesselPotentialSpaceExtension`: equivalently, `a` has the extension
  property `TauCeti.Symbol.HasBesselPotentialSpaceExtension`. The lemmas in that namespace then give
  the linearity of the operator in the symbol
  (`TauCeti.Symbol.HasBesselPotentialSpaceExtension.quantizeUniformBesselPotentialSpace_add` and
  the lemmas after it), its compatibility with raising the order, with the inclusions
  `H^{s,p} ⊆ H^{r,p}`, with composition and across exponents, and the multiplication operators of
  symbols `f(x)`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture II, §1
  (`Lᵖ` and `H^{s,p}` mapping of operators of order `m`).
* E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993, Chapter VI, §5.
-/

public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **The `H^{s,p}` estimate on Schwartz functions.** For a uniform symbol `a` of order `m` and
`1 < p < ∞`, `‖Op(a) u‖_{H^{s - m,p}} ≤ C ‖u‖_{H^{s,p}}` for every Schwartz function `u`. -/
private theorem IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha u)‖ ≤
        C * ‖toBesselPotentialSpaceCLM s p u‖ := by
  obtain ⟨b, hb, hab⟩ := ha.exists_besselMultiplier_comp_quantizeUniformCLM_eq s
  obtain ⟨C, hC⟩ := hb.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt hp hp_top
  refine ⟨C, fun u ↦ ?_⟩
  -- `J^{s - m} (Op(a) u) = Op(b) (J^s u)`, and `Op(b)` is bounded on `Lᵖ`.
  rw [norm_toBesselPotentialSpaceCLM_eq_eLpNorm, norm_toBesselPotentialSpaceCLM_eq_eLpNorm,
    ← ContinuousLinearMap.comp_apply, hab, ContinuousLinearMap.comp_apply, coe_quantizeUniformCLM]
  refine (ENNReal.toReal_mono ?_ (hC _)).trans_eq (by simp [ENNReal.toReal_mul])
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top (SchwartzMap.memLp _ p volume).eLpNorm_ne_top

variable {a : Symbol n V W m} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Mapping of uniform pseudodifferential operators on `H^{s,p}`.** Let `1 < p < ∞`. On a
Schwartz function `u`, the operator `Op(a) : H^{s,p} → H^{s - m,p}` is the Schwartz function
`Op(a) u`. -/
@[simp]
theorem quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM (ha : a.IsUniform) (s : ℝ)
    (hp : 1 < p) (hp_top : p ≠ ∞) (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniformBesselPotentialSpace ha s p (toBesselPotentialSpaceCLM s p u) =
      toBesselPotentialSpaceCLM (s - m) p (quantizeUniformCLM a ha u) := by
  obtain ⟨C, hC⟩ := ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s hp hp_top
  exact quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM_of_norm_le ha hp_top hC u

/-- For `1 < p < ∞`, a uniform symbol between complex Hilbert spaces has the extension property
`TauCeti.Symbol.HasBesselPotentialSpaceExtension`. -/
theorem IsUniform.hasBesselPotentialSpaceExtension (ha : a.IsUniform) (hp : 1 < p)
    (hp_top : p ≠ ∞) : a.HasBesselPotentialSpaceExtension ha p :=
  hasBesselPotentialSpaceExtension_iff.2 fun s ↦
    quantizeUniformBesselPotentialSpace_toBesselPotentialSpaceCLM ha s hp hp_top

end Symbol

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Bochner.BochnerTheorem
public import TauCeti.Analysis.Bochner.CharFun.PositiveDefinite
import TauCeti.Analysis.Bochner.Fourier.Convention

/-!
# Bochner's theorem in characteristic-function form

`TauCeti.bochner` represents a continuous positive-definite function on a finite-dimensional real
inner-product space `V` in the Fourier convention `v ↦ ∫ q, exp (-2πi⟪v, q⟫) ∂μ`. Probability
and much of classical harmonic analysis use the characteristic-function convention
`v ↦ ∫ q, exp (i⟪q, v⟫) ∂μ` instead, which is Mathlib's `MeasureTheory.charFun μ`. This file
restates Bochner's theorem in that convention: a function `F : V → ℂ` is continuous and positive
definite if and only if it is the characteristic function of a unique finite Borel measure, and
the normalization `F 0 = 1` corresponds to that measure being a probability measure
(the Bochner–Khinchin theorem). On `V = ℝ` this is the classical statement
`F x = ∫ ξ, exp (i x ξ) dμ(ξ)`.

The two conventions differ by the rescaling `q ↦ (-2π) • q` of the representing measure:
the characteristic-function representing measure of `F` is the image of
`TauCeti.bochnerMeasure F` under this rescaling (`TauCeti.charFun_map_bochnerMeasure`).

## Main declarations

* `TauCeti.charFun_map_bochnerMeasure`: the rescaled Bochner measure has characteristic
  function `F`.
* `TauCeti.bochner_charFun`: **Bochner's theorem, characteristic-function form**.
* `TauCeti.bochner_charFun_probabilityMeasure`: the normalized form — continuous positive-definite
  functions with `F 0 = 1` are exactly the characteristic functions of probability measures.
* `TauCeti.bochner_real`: the classical statement on the real line.

## References

* S. Bochner, *Vorlesungen über Fouriersche Integrale*, Akademische Verlagsgesellschaft (1932).
* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II (1971),
  Section XIX.2.
* W. Rudin, *Fourier Analysis on Groups* (1962), Theorem 1.4.3.
-/

public section

open MeasureTheory Complex

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **The characteristic-function representing measure.** The image of the Bochner measure of a
continuous positive-definite function `F` under the rescaling `q ↦ (-2π) • q` has characteristic
function `F`. -/
theorem charFun_map_bochnerMeasure {F : V → ℂ} (hcont : Continuous F)
    (hpd : IsPositiveDefiniteSub F) :
    charFun ((bochnerMeasure F).map ((-2 * Real.pi) • ·)) = F := by
  funext v
  rw [charFun_map_smul, ← integral_fourierAtom_eq_charFun_neg_two_pi_smul,
    integral_fourierAtom_bochnerMeasure hcont hpd]

/-- **Bochner's theorem, characteristic-function form.** A function `F` on a finite-dimensional
real inner-product space is continuous and positive definite if and only if it is the
characteristic function `v ↦ ∫ q, exp (i⟪q, v⟫) ∂μ` of a unique finite Borel measure `μ`. -/
theorem bochner_charFun (F : V → ℂ) :
    (Continuous F ∧ IsPositiveDefiniteSub F) ↔
      ∃! μ : Measure V, IsFiniteMeasure μ ∧ charFun μ = F := by
  constructor
  · rintro ⟨hcont, hpd⟩
    refine ⟨_, ⟨inferInstance, charFun_map_bochnerMeasure hcont hpd⟩, ?_⟩
    rintro ν ⟨hν, hνF⟩
    exact Measure.ext_of_charFun (hνF.trans (charFun_map_bochnerMeasure hcont hpd).symm)
  · rintro ⟨μ, ⟨hμ, rfl⟩, -⟩
    exact ⟨continuous_charFun, isPositiveDefiniteSub_charFun⟩

/-- **The Bochner–Khinchin theorem.** A function `F` on a finite-dimensional real inner-product
space is continuous, positive definite and normalized by `F 0 = 1` if and only if it is the
characteristic function of a unique Borel probability measure. -/
theorem bochner_charFun_probabilityMeasure (F : V → ℂ) :
    (Continuous F ∧ IsPositiveDefiniteSub F ∧ F 0 = 1) ↔
      ∃! μ : Measure V, IsProbabilityMeasure μ ∧ charFun μ = F := by
  constructor
  · rintro ⟨hcont, hpd, hF0⟩
    obtain ⟨μ, ⟨hμ, hμF⟩, huniq⟩ := (bochner_charFun F).mp ⟨hcont, hpd⟩
    have hprob : IsProbabilityMeasure μ := isProbabilityMeasure_iff_real.mpr <| by
      have h0 := congrFun hμF 0
      rw [charFun_zero, hF0] at h0
      exact_mod_cast h0
    exact ⟨μ, ⟨hprob, hμF⟩, fun ν ⟨_, hνF⟩ => huniq ν ⟨inferInstance, hνF⟩⟩
  · rintro ⟨μ, ⟨hμ, rfl⟩, -⟩
    exact ⟨continuous_charFun, isPositiveDefiniteSub_charFun, by simp⟩

/-- **Bochner's theorem on the real line**, in its classical form: a function `F : ℝ → ℂ` is
continuous and positive definite if and only if `F x = ∫ ξ, exp (i x ξ) dμ(ξ)` for a unique
finite Borel measure `μ` on `ℝ`. -/
theorem bochner_real (F : ℝ → ℂ) :
    (Continuous F ∧ IsPositiveDefiniteSub F) ↔
      ∃! μ : Measure ℝ, IsFiniteMeasure μ ∧ ∀ x, F x = ∫ ξ, exp (x * ξ * I) ∂μ := by
  simp_rw [bochner_charFun F, funext_iff, charFun_apply_real, eq_comm (a := F _)]

end TauCeti

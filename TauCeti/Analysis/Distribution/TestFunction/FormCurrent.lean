/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.ExtDeriv
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.MeasureTheory.Integral.Bochner.Alternating
import TauCeti.Analysis.Calculus.DifferentialForm.Integral
import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The current of a locally integrable form

Let `E` be a real vector space of finite dimension `j + l` with an orientation `o`, and let `Ω` be
an open subset of `E`. A `j`-form `ω` on `E` that is locally integrable on `Ω` defines the
`l`-current

`[ω] ζ = ∫_Ω ω ∧ ζ`

on test `l`-forms `ζ` on `Ω` (`Orientation.formCurrent o Ω ω`). In coordinates, for any basis `b`
of `E` with orientation `o`, `[ω] ζ = ∫ x, (ω x ∧ ζ x) b ∂b.addHaar`, the integral of the
coefficient of the top form `ω ∧ ζ` against the Haar measure normalized by `b`
(`Orientation.formCurrent_apply`). As for the integration current `[[Ω]]`, this does not depend on
the basis. Local integrability may be checked against any additive Haar measure; if it fails, the
current is defined to be zero. Continuity comes from Mathlib's
`TestFunction.integralAgainstBilinCLM`.

Currents of forms are the smooth (absolutely continuous) currents. A typical example is the
curvature current `(2π)⁻¹ ∫ i F_A ∧ ζ` of a unitary connection on a Hermitian line bundle, whose
weak limits are studied through its mass. If `ω` is a closed `C¹` form, its current has zero
boundary, `[ω] (d η) = 0` (`Orientation.formCurrent_comp_extDerivCLM_of_extDeriv_eq_zero`); this is
Stokes' theorem `∫ ω ∧ dη = ± ∫ dω ∧ η` for compactly supported `η`.

## Main declarations

* `Orientation.formCurrent o Ω ω`: the current `ζ ↦ ∫_Ω ω ∧ ζ` of a locally integrable form `ω`.
* `Orientation.formCurrent_apply_eq_signBasis_mul`, `Orientation.formCurrent_apply`: its
  coordinate formula in an arbitrary basis and in a basis of orientation `o`.
* `Orientation.formCurrent_of_not_locallyIntegrableOn`,
  `Orientation.formCurrent_eq_zero_of_finrank_ne`: the current is zero when `ω` is not locally
  integrable on `Ω`, or when `j + l` is not the dimension of `E`.
* `Orientation.formCurrent_comp_extDerivCLM_of_extDeriv_eq_zero`: closed forms give currents with
  zero boundary.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (currents represented by integration).
-/

public section

namespace Orientation

open MeasureTheory TopologicalSpace TestFunction Module ContinuousAlternatingMap
open scoped Distributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {j l : ℕ} {n : ℕ∞}
  {ω : E → E [⋀^Fin j]→L[ℝ] ℝ}

/-- The continuous bilinear pairing `(ζ, ω) ↦ (ω ∧ ζ) v` of an `l`-form and a `j`-form, evaluated
on a family `v` of `j + l` vectors. -/
private noncomputable def wedgeApplyCLM (v : Fin (j + l) → E) :
    (E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] (E [⋀^Fin j]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.compL ℝ _ _ ℝ (ContinuousAlternatingMap.apply ℝ E ℝ v) ∘L
    (pairedWedgeCLM (ContinuousLinearMap.mul ℝ ℝ)).flip

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem wedgeApplyCLM_apply (v : Fin (j + l) → E) (ζ : E [⋀^Fin l]→L[ℝ] ℝ)
    (φ : E [⋀^Fin j]→L[ℝ] ℝ) : wedgeApplyCLM v ζ φ = wedge φ ζ v := by
  simp [wedgeApplyCLM, wedge_def]

/-- The **current of a form** `[ω]`: for a `j`-form `ω` on an oriented real vector space `E` of
dimension `j + l`, the continuous linear functional `ζ ↦ ∫_Ω ω ∧ ζ` on test `l`-forms on `Ω`. For
any basis `b` of orientation `o` it is `ζ ↦ ∫ x, (ω x ∧ ζ x) b ∂b.addHaar`
(`Orientation.formCurrent_apply`) when `ω` is locally integrable on `Ω`; otherwise it is zero. If
`j + l` is not the dimension of `E`, it is zero. -/
noncomputable def formCurrent (o : Orientation ℝ E (Fin (j + l))) (Ω : Opens E)
    (ω : E → E [⋀^Fin j]→L[ℝ] ℝ) : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  if h : finrank ℝ E = j + l then
    letI b := finBasisOfFinrankEq ℝ E h
    (o.signBasis b : ℝ) • integralAgainstBilinCLM (wedgeApplyCLM ⇑b) b.addHaar ω
  else 0

/-- The current of a form `ω` that is locally integrable on `Ω`, evaluated on a test form `ζ` and
computed in an arbitrary basis `b`: the integral of the coefficient `(ω x ∧ ζ x) b` against the
Haar measure normalized by `b`, multiplied by the sign of `b` relative to `o`. Local integrability
may be checked against any additive Haar measure `μ`. -/
theorem formCurrent_apply_eq_signBasis_mul (o : Orientation ℝ E (Fin (j + l))) (Ω : Opens E)
    (b : Basis (Fin (j + l)) ℝ E) {μ : Measure E} [μ.IsAddHaarMeasure]
    (hω : LocallyIntegrableOn ω Ω μ) (ζ : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ)) :
    o.formCurrent Ω ω ζ = (o.signBasis b : ℝ) * ∫ x, wedge (ω x) (ζ x) b ∂b.addHaar := by
  have h : finrank ℝ E = j + l := by simpa using finrank_eq_card_basis b
  let b₀ := finBasisOfFinrankEq ℝ E h
  rw [← b₀.integral_signed_apply_eq o b fun x ↦ wedge (ω x) (ζ x)]
  simp [formCurrent, h, b₀, integralAgainstBilinCLM_eq_integral
    (hω.of_isAddHaarMeasure b₀.addHaar), wedgeApplyCLM_apply]

/-- The current of a form `ω` that is locally integrable on `Ω`, evaluated on a test form `ζ`, is
the integral of the coefficient `(ω x ∧ ζ x) b` against the Haar measure normalized by `b`, for
every basis `b` of the given orientation. -/
theorem formCurrent_apply (o : Orientation ℝ E (Fin (j + l))) (Ω : Opens E)
    (b : Basis (Fin (j + l)) ℝ E) (hb : b.orientation = o) {μ : Measure E}
    [μ.IsAddHaarMeasure] (hω : LocallyIntegrableOn ω Ω μ) (ζ : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ)) :
    o.formCurrent Ω ω ζ = ∫ x, wedge (ω x) (ζ x) b ∂b.addHaar := by
  subst hb
  simp [formCurrent_apply_eq_signBasis_mul _ Ω b hω]

/-- The current of a form vanishes when `j + l` is not the dimension of the space. -/
theorem formCurrent_eq_zero_of_finrank_ne (o : Orientation ℝ E (Fin (j + l))) (Ω : Opens E)
    (ω : E → E [⋀^Fin j]→L[ℝ] ℝ) (h : finrank ℝ E ≠ j + l) :
    (o.formCurrent Ω ω : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ℝ) = 0 := by
  simp [formCurrent, h]

/-- The current of a form that is not locally integrable on `Ω` is zero. -/
theorem formCurrent_of_not_locallyIntegrableOn (o : Orientation ℝ E (Fin (j + l)))
    (Ω : Opens E) {μ : Measure E} [μ.IsAddHaarMeasure] (hω : ¬LocallyIntegrableOn ω Ω μ) :
    (o.formCurrent Ω ω : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ℝ) = 0 := by
  unfold formCurrent
  split_ifs with h
  · ext ζ
    have hω₀ : ¬LocallyIntegrableOn ω Ω (finBasisOfFinrankEq ℝ E h).addHaar :=
      fun h' ↦ hω (h'.of_isAddHaarMeasure μ)
    simp [integralAgainstBilinCLM_apply, hω₀]
  · rfl

/-- **Stokes' theorem for the current of a closed form.** The current of a closed `C¹` form `ω`
has zero boundary: `[ω] (d η) = ∫ ω ∧ dη = 0` for every test form `η`. -/
theorem formCurrent_comp_extDerivCLM_of_extDeriv_eq_zero {k : ℕ}
    (o : Orientation ℝ E (Fin (j + (k + 1)))) (Ω : Opens E) (hω : ContDiff ℝ 1 ω)
    (hdω : extDeriv ω = 0) :
    o.formCurrent Ω ω ∘L (extDerivCLM : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] _) = 0 := by
  by_cases h : finrank ℝ E = j + (k + 1)
  · let b := finBasisOfFinrankEq ℝ E h
    ext η
    have hint := b.integral_extDeriv_wedge_eq_integral_wedge_extDeriv (by omega) hω
      (η.contDiff.of_le (by exact_mod_cast le_top)) η.hasCompactSupport
    rw [hdω] at hint
    have hloc : LocallyIntegrableOn ω Ω b.addHaar :=
      (hω.continuous.locallyIntegrable).locallyIntegrableOn _
    simpa [formCurrent_apply_eq_signBasis_mul o Ω b hloc, extDerivCLM_apply, wedge_def] using
      hint.symm
  · simp [formCurrent_eq_zero_of_finrank_ne o Ω ω h]

end Orientation

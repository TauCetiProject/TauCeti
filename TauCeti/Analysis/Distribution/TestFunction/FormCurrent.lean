/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.ExtDeriv
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.MeasureTheory.Integral.Bochner.Alternating
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Calculus.DifferentialForm.Integral
import TauCeti.Analysis.Calculus.DifferentialForm.Wedge
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
`TestFunction.integralAgainstBilinCLM`, applied to the bilinear pairing
`ContinuousAlternatingMap.wedgeApplyCLM`.

These are the currents represented by locally integrable forms, which are absolutely continuous
with respect to Haar measure; the coefficients of `ω` need not be smooth. The current depends
linearly on `ω` and only on the almost-everywhere class of `ω` on `Ω`. A typical example is the
curvature current `(2π)⁻¹ ∫ i F_A ∧ ζ` of a unitary connection on a Hermitian line bundle, whose
weak limits are studied through its mass. If `ω` is `C¹` and closed on `Ω`, its current has zero
boundary, `[ω] (d η) = 0` (`Orientation.formCurrent_comp_extDerivCLM_of_extDeriv_eq_zero`); this is
Stokes' theorem `∫ ω ∧ dη = ± ∫ dω ∧ η` for `η` compactly supported in `Ω`.

## Main declarations

* `Orientation.formCurrent o Ω ω`: the current `ζ ↦ ∫_Ω ω ∧ ζ` of a locally integrable form `ω`.
* `Orientation.formCurrent_apply_eq_signBasis_mul`, `Orientation.formCurrent_apply`: its
  coordinate formula in an arbitrary basis and in a basis of orientation `o`.
* `Orientation.formCurrent_of_not_locallyIntegrableOn`,
  `Orientation.formCurrent_eq_zero_of_finrank_ne`: the current is zero when `ω` is not locally
  integrable on `Ω`, or when `j + l` is not the dimension of `E`.
* `Orientation.formCurrent_zero`, `Orientation.formCurrent_add`, `Orientation.formCurrent_smul`,
  `Orientation.formCurrent_neg`: linearity in the form.
* `Orientation.formCurrent_congr_ae`: forms that agree almost everywhere on `Ω` have the same
  current.
* `Orientation.formCurrent_comp_extDerivCLM_of_extDeriv_eq_zero`: forms closed on `Ω` give currents
  with zero boundary.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (currents represented by integration).
-/

public section

namespace Orientation

open MeasureTheory TopologicalSpace TestFunction Module ContinuousAlternatingMap Filter
open scoped Distributions Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {j l : ℕ} {n : ℕ∞}
  {ω ω' : E → E [⋀^Fin j]→L[ℝ] ℝ}

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

/-- The current of the zero form is zero. -/
@[simp]
theorem formCurrent_zero (o : Orientation ℝ E (Fin (j + l))) (Ω : Opens E) :
    (o.formCurrent Ω (0 : E → E [⋀^Fin j]→L[ℝ] ℝ) : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      0 := by
  by_cases h : finrank ℝ E = j + l
  · let b := finBasisOfFinrankEq ℝ E h
    ext ζ
    rw [formCurrent_apply_eq_signBasis_mul o Ω b
      ((continuous_zero.locallyIntegrable (μ := b.addHaar)).locallyIntegrableOn _)]
    simp [wedge_def]
  · exact formCurrent_eq_zero_of_finrank_ne o Ω 0 h

/-- The current of a sum of forms that are locally integrable on `Ω` is the sum of their
currents. -/
theorem formCurrent_add (o : Orientation ℝ E (Fin (j + l))) (Ω : Opens E) {μ : Measure E}
    [μ.IsAddHaarMeasure] (hω : LocallyIntegrableOn ω Ω μ) (hω' : LocallyIntegrableOn ω' Ω μ) :
    (o.formCurrent Ω (ω + ω') : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      o.formCurrent Ω ω + o.formCurrent Ω ω' := by
  by_cases h : finrank ℝ E = j + l
  · let b := finBasisOfFinrankEq ℝ E h
    have hb := hω.of_isAddHaarMeasure b.addHaar
    have hb' := hω'.of_isAddHaarMeasure b.addHaar
    ext ζ
    have hi := ζ.integrable_bilin (wedgeApplyCLM ⇑b) hb
    have hi' := ζ.integrable_bilin (wedgeApplyCLM ⇑b) hb'
    simp only [wedgeApplyCLM_apply] at hi hi'
    rw [_root_.add_apply, formCurrent_apply_eq_signBasis_mul o Ω b (hb.add hb'),
      formCurrent_apply_eq_signBasis_mul o Ω b hb, formCurrent_apply_eq_signBasis_mul o Ω b hb',
      ← mul_add, ← integral_add hi hi']
    simp
  · simp [formCurrent_eq_zero_of_finrank_ne o Ω _ h]

/-- The current of a scalar multiple of a form is the scalar multiple of its current. -/
@[simp]
theorem formCurrent_smul (o : Orientation ℝ E (Fin (j + l))) (Ω : Opens E) (c : ℝ)
    (ω : E → E [⋀^Fin j]→L[ℝ] ℝ) :
    (o.formCurrent Ω (c • ω) : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      c • o.formCurrent Ω ω := by
  by_cases h : finrank ℝ E = j + l
  · let b := finBasisOfFinrankEq ℝ E h
    by_cases hω : LocallyIntegrableOn ω Ω b.addHaar
    · ext ζ
      simp only [_root_.smul_apply, smul_eq_mul,
        formCurrent_apply_eq_signBasis_mul o Ω b hω,
        formCurrent_apply_eq_signBasis_mul o Ω b (hω.smul c), Pi.smul_apply, wedge_smul_left,
        ContinuousAlternatingMap.smul_apply, integral_const_mul]
      ring
    · rcases eq_or_ne c 0 with rfl | hc
      · simp
      · have hcω : ¬LocallyIntegrableOn (c • ω) Ω b.addHaar := fun h' ↦
          hω (((locallyIntegrableOn_smul_iff c).1 h').resolve_left hc)
        simp [formCurrent_of_not_locallyIntegrableOn o Ω hω,
          formCurrent_of_not_locallyIntegrableOn o Ω hcω]
  · simp [formCurrent_eq_zero_of_finrank_ne o Ω _ h]

/-- The current of the negative of a form is the negative of its current. -/
@[simp]
theorem formCurrent_neg (o : Orientation ℝ E (Fin (j + l))) (Ω : Opens E)
    (ω : E → E [⋀^Fin j]→L[ℝ] ℝ) :
    (o.formCurrent Ω (-ω) : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ℝ) = -o.formCurrent Ω ω := by
  rw [← neg_one_smul ℝ ω, formCurrent_smul]
  ext
  simp

/-- Forms that agree almost everywhere on `Ω`, for some additive Haar measure, have the same
current. -/
theorem formCurrent_congr_ae (o : Orientation ℝ E (Fin (j + l))) (Ω : Opens E) {μ : Measure E}
    [μ.IsAddHaarMeasure] (hωω' : ω =ᵐ[μ.restrict Ω] ω') :
    (o.formCurrent Ω ω : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ℝ) = o.formCurrent Ω ω' := by
  by_cases h : finrank ℝ E = j + l
  · let b := finBasisOfFinrankEq ℝ E h
    have hb : ω =ᵐ[b.addHaar.restrict Ω] ω' := by
      rw [Measure.isAddLeftInvariant_eq_smul b.addHaar μ, Measure.restrict_smul]
      exact Measure.ae_smul_measure hωω' _
    by_cases hω : LocallyIntegrableOn ω Ω b.addHaar
    · ext ζ
      rw [formCurrent_apply_eq_signBasis_mul o Ω b hω,
        formCurrent_apply_eq_signBasis_mul o Ω b (hω.congr hb)]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hb] with x hx
      by_cases hxΩ : x ∈ Ω
      · rw [hx hxΩ]
      · have hζ : ζ x = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ hxΩ (ζ.tsupport_subset h')
        simp [hζ, wedge_def]
    · rw [formCurrent_of_not_locallyIntegrableOn o Ω hω,
        formCurrent_of_not_locallyIntegrableOn o Ω fun h' ↦ hω (h'.congr hb.symm)]
  · simp [formCurrent_eq_zero_of_finrank_ne o Ω _ h]

/-- **Stokes' theorem for the current of a closed form.** The current of a form `ω` that is `C¹`
and closed on `Ω` has zero boundary: `[ω] (d η) = ∫ ω ∧ dη = 0` for every test form `η`. -/
theorem formCurrent_comp_extDerivCLM_of_extDeriv_eq_zero {k : ℕ}
    (o : Orientation ℝ E (Fin (j + (k + 1)))) (Ω : Opens E) (hω : ContDiffOn ℝ 1 ω Ω)
    (hdω : Set.EqOn (extDeriv ω) 0 Ω) :
    o.formCurrent Ω ω ∘L (extDerivCLM : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] _) = 0 := by
  by_cases h : finrank ℝ E = j + (k + 1)
  · let b := finBasisOfFinrankEq ℝ E h
    ext η
    have hloc : LocallyIntegrableOn ω Ω b.addHaar :=
      hω.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
    have hη : ContDiff ℝ 1 η := η.contDiff.of_le (by exact_mod_cast le_top)
    -- Off `Ω` the test form `η`, and with it `ω ∧ η`, vanishes near every point.
    have hη₀ (x : E) (hx : x ∉ Ω) : (η : E → E [⋀^Fin k]→L[ℝ] ℝ) =ᶠ[𝓝 x] 0 :=
      notMem_tsupport_iff_eventuallyEq.1 fun h' ↦ hx (η.tsupport_subset h')
    have hψ₀ (x : E) (hx : x ∉ Ω) : (fun y ↦ wedge (ω y) (η y)) =ᶠ[𝓝 x] 0 :=
      (hη₀ x hx).mono fun y hy ↦ by simp [show η y = 0 from hy, wedge_def]
    -- So `ω ∧ η` is a compactly supported `C¹` form on all of `E`.
    have hψ : ContDiff ℝ 1 fun x ↦ wedge (ω x) (η x) := by
      refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
      by_cases hx : x ∈ Ω
      · simpa only [wedge_def] using contDiffAt_const.pairedWedge
          (hω.contDiffAt (Ω.isOpen.mem_nhds hx)) hη.contDiffAt
      · exact contDiffAt_const.congr_of_eventuallyEq (hψ₀ x hx)
    obtain ⟨-, hzero⟩ := b.integral_extDeriv_eq_zero (n := j + k) hψ η.hasCompactSupport.wedge_left
    -- By the Leibniz rule and `dω = 0` on `Ω`, `d (ω ∧ η) = (-1) ^ j ω ∧ dη`.
    have hL (x : E) : extDeriv (fun y ↦ wedge (ω y) (η y)) x b =
        (-1 : ℝ) ^ j * wedge (ω x) (extDeriv η x) b := by
      by_cases hx : x ∈ Ω
      · have := TauCeti.extDeriv_pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
          ((hω.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt one_ne_zero)
          (hη.differentiable one_ne_zero x) b
        simpa [wedge_def, hdω hx] using this
      · have hd₀ (m : ℕ) : extDeriv (0 : E → E [⋀^Fin m]→L[ℝ] ℝ) x = 0 := by
          simp [extDeriv, ← alternatizeUncurryFinCLM_apply]
        rw [(hψ₀ x hx).extDeriv_eq, (hη₀ x hx).extDeriv_eq, hd₀, hd₀]
        simp [wedge_def]
    simp_rw [hL, integral_const_mul] at hzero
    have hint : ∫ x, wedge (ω x) (extDeriv η x) b ∂b.addHaar = 0 := by
      simpa using hzero
    simp [formCurrent_apply_eq_signBasis_mul o Ω b hloc, extDerivCLM_apply, hint]
  · simp [formCurrent_eq_zero_of_finrank_ne o Ω ω h]

end Orientation

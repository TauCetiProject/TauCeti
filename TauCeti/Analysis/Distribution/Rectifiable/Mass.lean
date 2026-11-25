/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Rectifiable.Basic
import TauCeti.Analysis.Distribution.TestFunction.NormDuality
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# The mass of the current of an oriented set with multiplicity

Let `V` be a finite-dimensional real inner product space, `Ω` an open subset, `θ : V → ℝ` a
multiplicity locally integrable on `Ω` for `μHE[k]`, and `τ : V → Fin k → V` measurable
orientation frames, orthonormal wherever `θ` does not vanish. The mass of the frame current
`ω ↦ ∫ θ(x) ω_x(τ(x)) dμHE[k](x)` on an open set `U` is the integral of the absolute multiplicity
over `U ∩ Ω`:

`localMass (frameCurrent θ τ) U = ∫⁻ x in U ∩ Ω, |θ x| dμHE[k]`

(`Distribution.localMass_frameCurrent`), and its mass is `∫_Ω |θ| dμHE[k]`
(`Distribution.mass_frameCurrent`): the mass measure of `θ μHE[k] ∧ ξ` is `|θ| μHE[k]`.

The bound `≤` is `Distribution.localMass_frameCurrent_le`. For the reverse bound, the current is
the integral of the field of functionals `G x : ω ↦ θ(x) ω(τ(x))` on forms, of norm `|θ(x)|`,
and the norm is attained at the form `sign θ(x) ⟪τ₁(x) ∧ ⋯ ∧ τₖ(x), ·⟫` of comass one. The
duality `MeasureTheory.LocallyIntegrableOn.exists_contDiff_lt_ofReal_integral_apply`, which
holds for every measure, in particular for `μHE[k]`, which is not locally finite when
`k < dim V`, then produces test forms supported in `U ∩ Ω` whose pairings approach
`∫_{U ∩ Ω} |θ| dμHE[k]`.

## Main declarations

* `Distribution.localMass_frameCurrent`: the local mass on an open set `U` is
  `∫_{U ∩ Ω} |θ| dμHE[k]`.
* `Distribution.mass_frameCurrent`: the mass is `∫_Ω |θ| dμHE[k]`.

## References

* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §3 (integer multiplicity
  rectifiable currents `τ(M, θ, ξ)` and their mass).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction MeasureTheory exteriorPower
open scoped Distributions ENNReal RealInnerProductSpace

namespace Distribution

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {Ω : Opens V} {n : ℕ∞} {k : ℕ}

/-- The functional `ω ↦ θ(x) ω(τ(x))` on forms whose integral against `μHE[k]` is the frame
current. -/
private def frameFunctional (θ : V → ℝ) (τ : V → Fin k → V) (x : V) :
    (V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  formVectorPairing.flip (frameDensity θ τ x)

omit [MeasurableSpace V] [BorelSpace V] in
private theorem frameFunctional_apply (θ : V → ℝ) (τ : V → Fin k → V) (x : V)
    (ω : V [⋀^Fin k]→L[ℝ] ℝ) : frameFunctional θ τ x ω = θ x * ω (τ x) := by
  simp [frameFunctional]

/-- The form `sign θ(x) ⟪τ₁(x) ∧ ⋯ ∧ τₖ(x), ·⟫`, which attains the norm of the frame
functional. -/
private def frameNormingForm (θ : V → ℝ) (τ : V → Fin k → V) (x : V) : V [⋀^Fin k]→L[ℝ] ℝ :=
  (|θ x|⁻¹ * θ x) • TauCeti.alternatingFormEquiv V k (ιMulti ℝ k (τ x))

omit [MeasurableSpace V] [BorelSpace V] in
private theorem norm_frameNormingForm_le {θ : V → ℝ} {τ : V → Fin k → V} {x : V}
    (hx : θ x ≠ 0 → Orthonormal ℝ (τ x)) : ‖frameNormingForm θ τ x‖ ≤ 1 := by
  by_cases hθ : θ x = 0
  · simp [frameNormingForm, hθ]
  rw [frameNormingForm, norm_smul, TauCeti.norm_alternatingFormEquiv_ιMulti,
    (hx hθ).norm_ιMulti, norm_mul, norm_inv, Real.norm_eq_abs, abs_abs, Real.norm_eq_abs,
    inv_mul_cancel₀ (abs_ne_zero.2 hθ), mul_one]

omit [MeasurableSpace V] [BorelSpace V] in
private theorem frameFunctional_frameNormingForm {θ : V → ℝ} {τ : V → Fin k → V} {x : V}
    (hx : θ x ≠ 0 → Orthonormal ℝ (τ x)) :
    frameFunctional θ τ x (frameNormingForm θ τ x) = |θ x| := by
  by_cases hθ : θ x = 0
  · simp [frameFunctional_apply, hθ]
  rw [frameFunctional_apply, frameNormingForm, ContinuousAlternatingMap.smul_apply,
    TauCeti.alternatingFormEquiv_apply, real_inner_self_eq_norm_sq, (hx hθ).norm_ιMulti,
    one_pow, smul_eq_mul, mul_one, ← mul_assoc, mul_comm (θ x), mul_assoc, ← sq, ← sq_abs,
    sq, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.2 hθ), one_mul]

omit [MeasurableSpace V] [BorelSpace V] in
/-- At an orthonormal frame, the frame functional has norm `|θ(x)|`. -/
private theorem norm_frameFunctional {θ : V → ℝ} {τ : V → Fin k → V} {x : V}
    (hx : θ x ≠ 0 → Orthonormal ℝ (τ x)) : ‖frameFunctional θ τ x‖ = |θ x| := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _) fun ω ↦ ?_) ?_
  · rw [frameFunctional_apply]
    by_cases hθ : θ x = 0
    · simp [hθ]
    rw [norm_mul, Real.norm_eq_abs]
    gcongr
    simpa [(hx hθ).1] using ω.le_opNorm (τ x)
  · calc |θ x| = frameFunctional θ τ x (frameNormingForm θ τ x) :=
          (frameFunctional_frameNormingForm hx).symm
      _ ≤ ‖frameFunctional θ τ x (frameNormingForm θ τ x)‖ := Real.le_norm_self _
      _ ≤ ‖frameFunctional θ τ x‖ * ‖frameNormingForm θ τ x‖ :=
          (frameFunctional θ τ x).le_opNorm _
      _ ≤ ‖frameFunctional θ τ x‖ :=
          mul_le_of_le_one_right (frameFunctional θ τ x).opNorm_nonneg
            (norm_frameNormingForm_le hx)

/-- **The mass of a frame current.** For a multiplicity `θ` locally integrable on `Ω` and
measurable frames `τ`, orthonormal where `θ` does not vanish, the local mass of the frame current
on an open set `U` is `∫_{U ∩ Ω} |θ| dμHE[k]`. -/
theorem localMass_frameCurrent {θ : V → ℝ} {τ : V → Fin k → V}
    (hθ : LocallyIntegrableOn θ Ω μHE[k]) (hτ : Measurable τ)
    (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) {U : Set V} (hU : IsOpen U) :
    localMass (frameCurrent θ τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) U =
      ∫⁻ x in U ∩ Ω, ‖θ x‖ₑ ∂μHE[k] := by
  refine le_antisymm ?_ (le_of_forall_lt fun c hc ↦ ?_)
  · refine (localMass_le_iff.2 fun φ hφU hφ ↦ ?_).trans
      (localMass_frameCurrent_le (n := n) (Ω := Ω) hτo _)
    exact enorm_le_localMass (subset_inter hφU φ.tsupport_subset) hφ
  set W := U ∩ (Ω : Set V)
  have hθW : LocallyIntegrableOn θ W μHE[k] := hθ.mono_set inter_subset_right
  have hθm : AEMeasurable θ (μHE[k].restrict W) := hθW.aestronglyMeasurable.aemeasurable
  have hform : Continuous fun x : Fin k → V ↦ TauCeti.alternatingFormEquiv V k (ιMulti ℝ k x) :=
    LinearMap.continuous_of_finiteDimensional (TauCeti.alternatingFormEquiv V k).toLinearMap |>.comp
      (exteriorPower.ιMulti ℝ k (M := V)).toMultilinearMap.continuous_of_finiteDimensional
  have hσm : AEStronglyMeasurable (frameNormingForm θ τ) (μHE[k].restrict W) :=
    (((continuous_abs.measurable.comp_aemeasurable hθm).inv.mul hθm).aestronglyMeasurable).smul
      (hform.comp_aestronglyMeasurable hτ.aestronglyMeasurable)
  -- The frame functional is `θ` times a continuous function of the frame.
  have hH : Continuous fun v : Fin k → V ↦
      (formVectorPairing (E := V) (k := k)).flip (ιMulti ℝ k v) :=
    (formVectorPairing (E := V) (k := k)).flip.continuous.comp
      (exteriorPower.ιMulti ℝ k (M := V)).toMultilinearMap.continuous_of_finiteDimensional
  have hGe : frameFunctional θ τ =
      fun y ↦ θ y • (formVectorPairing (E := V) (k := k)).flip (ιMulti ℝ k (τ y)) := by
    funext y
    simp [frameFunctional, frameDensity_apply]
  -- The integrability of the frame functional is stated through the duality lemma itself, whose
  -- statement fixes the extended norm on the iterated operator space.
  obtain ⟨ψ, hψd, hψc, hψW, hψ1, hψ⟩ :=
    LocallyIntegrableOn.exists_contDiff_lt_ofReal_integral_apply (G := frameFunctional θ τ)
      (μ := μHE[k]) (W := W) (fun x hx ↦ by
        obtain ⟨t, ht, hint⟩ := hθW x hx
        refine ⟨t, ht, ?_⟩
        unfold IntegrableOn at hint ⊢
        refine Integrable.mono' (Integrable.norm hint) ?_ (ae_of_all _ fun y ↦ ?_)
        · rw [hGe]
          exact hint.aestronglyMeasurable.smul
            (hH.comp_aestronglyMeasurable hτ.aestronglyMeasurable)
        · rw [norm_frameFunctional (hτo y), Real.norm_eq_abs])
      (hU.inter Ω.isOpen) hσm (fun x ↦ norm_frameNormingForm_le (hτo x))
      (ae_of_all _ fun x _ ↦ by
        rw [frameFunctional_frameNormingForm (hτo x), norm_frameFunctional (hτo x)])
      (hc.trans_eq (lintegral_congr fun x ↦ by
        rw [← ofReal_norm, ← ofReal_norm, norm_frameFunctional (hτo x), Real.norm_eq_abs]))
  let Φ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) :=
    ⟨ψ, hψd.of_le (by exact_mod_cast le_top), hψc, hψW.trans inter_subset_right⟩
  have hΦ : frameCurrent θ τ Φ = ∫ x, frameFunctional θ τ x (ψ x) ∂μHE[k] := by
    rw [frameCurrent_apply hθ hτ hτo]
    simp [frameFunctional_apply, Φ]
  refine hψ.trans_le ((ENNReal.ofReal_le_ofReal (le_abs_self _)).trans ?_)
  rw [← hΦ, ← Real.eNorm_eq_ofReal_abs]
  exact enorm_le_localMass (by simpa [Φ] using hψW.trans inter_subset_left) hψ1

/-- **The mass of a frame current** is `∫_Ω |θ| dμHE[k]`, for a multiplicity `θ` locally
integrable on `Ω` and measurable frames `τ`, orthonormal where `θ` does not vanish. -/
theorem mass_frameCurrent {θ : V → ℝ} {τ : V → Fin k → V}
    (hθ : LocallyIntegrableOn θ Ω μHE[k]) (hτ : Measurable τ)
    (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) :
    mass (frameCurrent θ τ : 𝓓^{n}(Ω, V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      ∫⁻ x in Ω, ‖θ x‖ₑ ∂μHE[k] := by
  rw [← localMass_univ, localMass_frameCurrent hθ hτ hτo isOpen_univ, univ_inter]

end Distribution

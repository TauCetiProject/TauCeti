/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Rectifiable.Basic
import TauCeti.Analysis.Distribution.TestFunction.NormDuality
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
-- Supplies the extended norm on the operator space `(V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ`.
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

omit [MeasurableSpace V] [BorelSpace V] in
private theorem frameFunctional_eq_formDualEquiv (θ : V → ℝ) (τ : V → Fin k → V) (x : V) :
    frameFunctional θ τ x = formDualEquiv ℝ V k (frameDensity θ τ x) := by
  ext ω
  simp [frameFunctional, formVectorPairing_apply]

omit [MeasurableSpace V] [BorelSpace V] in
private theorem frameFunctional_eq_smul (θ : V → ℝ) (τ : V → Fin k → V) (x : V) :
    frameFunctional θ τ x = θ x • formDualEquiv ℝ V k (ιMulti ℝ k (τ x)) := by
  rw [frameFunctional_eq_formDualEquiv, frameDensity_apply, map_smul]

/-- The frame functional is locally integrable on `Ω`: it is the frame density composed with the
continuous linear map `exteriorPower.formVectorPairing.flip`. -/
private theorem locallyIntegrableOn_frameFunctional {θ : V → ℝ} {τ : V → Fin k → V}
    (hθ : LocallyIntegrableOn θ Ω μHE[k]) (hτ : Measurable τ)
    (hτo : ∀ x, θ x ≠ 0 → Orthonormal ℝ (τ x)) :
    LocallyIntegrableOn (frameFunctional θ τ) Ω μHE[k] := fun x hx ↦ by
  obtain ⟨t, ht, hi⟩ := locallyIntegrableOn_frameDensity hθ hτ hτo x hx
  refine ⟨t, ht, ?_⟩
  unfold IntegrableOn
  refine Integrable.mono' (β := (V [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (hi.norm.const_mul √((Module.finrank ℝ V).choose k)) ?_ (ae_of_all _ fun y ↦ ?_)
  · exact (formVectorPairing (E := V) (k := k)).flip.continuous.comp_aestronglyMeasurable hi.1
  · rw [frameFunctional_eq_formDualEquiv]
    exact norm_formDualEquiv_le _

/-- The form `sign θ(x) ⟪τ₁(x) ∧ ⋯ ∧ τₖ(x), ·⟫`, which attains the norm of the frame
functional. -/
private def frameNormingForm (θ : V → ℝ) (τ : V → Fin k → V) (x : V) : V [⋀^Fin k]→L[ℝ] ℝ :=
  |θ x|⁻¹ • TauCeti.alternatingFormEquiv V k (frameDensity θ τ x)

omit [MeasurableSpace V] [BorelSpace V] in
private theorem norm_frameNormingForm_le {θ : V → ℝ} {τ : V → Fin k → V} {x : V}
    (hx : θ x ≠ 0 → Orthonormal ℝ (τ x)) : ‖frameNormingForm θ τ x‖ ≤ 1 := by
  by_cases hθ : θ x = 0
  · simp [frameNormingForm, frameDensity_apply, hθ]
  simp [frameNormingForm, frameDensity_apply, norm_smul, TauCeti.norm_alternatingFormEquiv_ιMulti,
    (hx hθ).norm_ιMulti, hθ]

omit [MeasurableSpace V] [BorelSpace V] in
private theorem frameFunctional_frameNormingForm {θ : V → ℝ} {τ : V → Fin k → V} {x : V}
    (hx : θ x ≠ 0 → Orthonormal ℝ (τ x)) :
    frameFunctional θ τ x (frameNormingForm θ τ x) = |θ x| := by
  by_cases hθ : θ x = 0
  · simp [frameFunctional_apply, hθ]
  simp only [frameFunctional_apply, frameNormingForm, frameDensity_apply, map_smul,
    TauCeti.alternatingFormEquiv_apply, real_inner_self_eq_norm_sq, (hx hθ).norm_ιMulti, one_pow,
    smul_eq_mul]
  field_simp
  exact (sq_abs _).symm

omit [MeasurableSpace V] [BorelSpace V] in
/-- At an orthonormal frame, the frame functional has norm `|θ(x)|`. -/
private theorem norm_frameFunctional {θ : V → ℝ} {τ : V → Fin k → V} {x : V}
    (hx : θ x ≠ 0 → Orthonormal ℝ (τ x)) : ‖frameFunctional θ τ x‖ = |θ x| := by
  by_cases hθ : θ x = 0
  · simp [frameFunctional_eq_smul, hθ]
  refine le_antisymm ?_ ?_
  · rw [frameFunctional_eq_smul]
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans_eq ?_
    rw [norm_formDualEquiv_ιMulti, (hx hθ).norm_ιMulti, mul_one, Real.norm_eq_abs]
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
  have hθm : AEMeasurable θ (μHE[k].restrict W) :=
    (hθ.mono_set inter_subset_right).aestronglyMeasurable.aemeasurable
  have hσm : AEStronglyMeasurable (frameNormingForm θ τ) (μHE[k].restrict W) :=
    ((continuous_abs.measurable.comp_aemeasurable hθm).inv.aestronglyMeasurable).smul
      ((TauCeti.alternatingFormEquiv V k).toContinuousLinearMap.continuous
        |>.comp_aestronglyMeasurable ((locallyIntegrableOn_frameDensity hθ hτ hτo).mono_set
          inter_subset_right).aestronglyMeasurable)
  obtain ⟨ψ, hψd, hψc, hψW, hψ1, hψ⟩ :=
    ((locallyIntegrableOn_frameFunctional hθ hτ hτo).mono_set inter_subset_right
      ).exists_contDiff_lt_ofReal_integral_apply (hU.inter Ω.isOpen) hσm
      (fun x ↦ norm_frameNormingForm_le (hτo x))
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

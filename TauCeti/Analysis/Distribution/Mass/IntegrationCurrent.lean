/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Measure
public import TauCeti.Analysis.Distribution.TestFunction.IntegrationCurrent
import TauCeti.Analysis.Distribution.TestFunction.TopDegree
import TauCeti.Analysis.InnerProductSpace.Comass

/-!
# The mass of the oriented integration current

Let `E` be a finite-dimensional real inner product space of dimension `m` with an orientation `o`,
and let `Ω` be an open subset of `E`. The integration current `[[Ω]] = o.integrationCurrent Ω`
integrates test `m`-forms over `Ω`. On an inner product space the pointwise norm of a form used
by `Distribution.mass` is the comass, and the comass of a top-degree form is the absolute value of
its coefficient in an orthonormal basis
(`ContinuousAlternatingMap.norm_eq_norm_apply_orthonormalBasis`). This file shows that the mass
of `[[Ω]]` is the volume of `Ω` and that its mass measure is the volume measure on `Ω`. This is
the Euclidean model of the comparison between the mass measure of a top-dimensional integration
current and the Riemannian volume.

The upper bound is the domination `|[[Ω]] ω| ≤ ∫ ‖ω‖`. For the lower bound, a scalar test `ψ` with
`|ψ| ≤ 1` gives the test form `ψ • det_b` in an orthonormal basis `b`, which has comass `|ψ|`
pointwise and on which `[[Ω]]` is `± ∫ ψ`. The supremum of these integrals is the volume of `Ω`
by `MeasureTheory.LocallyIntegrableOn.iSup_ofReal_integral_apply_eq_setLIntegral_enorm`.
Neither the orientation nor the regularity `n` of the tests affects the result. The local mass on
an open set `U` is the volume of `Ω ∩ U`, so `[[Ω]]` has locally finite mass, and the uniqueness
of the mass measure identifies it with the volume.

## Main declarations

* `Orientation.enorm_integrationCurrent_apply_le_lintegral_enorm`: `|[[Ω]] ω| ≤ ∫ ‖ω‖`.
* `Orientation.localMass_integrationCurrent_le`: the local mass on any set is at most its volume.
* `Orientation.hasLocallyFiniteMass_integrationCurrent`: `[[Ω]]` has locally finite mass.
* `Orientation.mass_integrationCurrent`: `M([[Ω]])` is the volume of `Ω`.
* `Orientation.localMass_integrationCurrent`: the local mass on an open `U` is the volume of
  `Ω ∩ U`.
* `Orientation.massMeasure_integrationCurrent`: `‖[[Ω]]‖` is the volume measure on `Ω`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (the mass of a current) and §1.8.1 (comass).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

namespace Orientation

open MeasureTheory TopologicalSpace TestFunction Module Distribution Set
open scoped Distributions ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {m : ℕ} {n : ℕ∞}

/-- The integration current, evaluated in an orthonormal basis `b`: up to the sign of `b`, it is
the volume integral of the coefficient of the test form in `b`. -/
private theorem enorm_integrationCurrent_apply_eq (o : Orientation ℝ E (Fin m))
    (b : OrthonormalBasis (Fin m) ℝ E) (ω : 𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ)) :
    ‖o.integrationCurrent Ω ω‖ₑ = ‖∫ x, ω x b‖ₑ := by
  rw [integrationCurrent_apply_eq_signBasis_mul o Ω b.toBasis, b.addHaar_eq_volume, enorm_mul,
    b.coe_toBasis]
  rcases Int.units_eq_one_or (o.signBasis b.toBasis) with h | h <;> simp [h]

/-- **Domination by the comass**: `|[[Ω]] ω| ≤ ∫ ‖ω‖` against the volume. -/
theorem enorm_integrationCurrent_apply_le_lintegral_enorm (o : Orientation ℝ E (Fin m))
    (ω : 𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ)) : ‖o.integrationCurrent Ω ω‖ₑ ≤ ∫⁻ x, ‖ω x‖ₑ := by
  by_cases hm : finrank ℝ E = m
  · let b : OrthonormalBasis (Fin m) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr hm)
    rw [enorm_integrationCurrent_apply_eq o b]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
    rw [← ofReal_norm, ← ofReal_norm, (ω x).norm_eq_norm_apply_orthonormalBasis b]
  · simp [integrationCurrent_eq_zero_of_finrank_ne o Ω hm]

/-- The local mass of the integration current on any set `U` is at most the volume of `U`. -/
theorem localMass_integrationCurrent_le (o : Orientation ℝ E (Fin m)) (Ω : Opens E) (U : Set E) :
    localMass (o.integrationCurrent Ω : 𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ) U ≤ volume U := by
  refine localMass_le_iff.2 fun ω hωU hω =>
    (o.enorm_integrationCurrent_apply_le_lintegral_enorm ω).trans ?_
  calc ∫⁻ x, ‖ω x‖ₑ ≤ ∫⁻ x, (tsupport ω).indicator 1 x := lintegral_mono fun x => by
        by_cases hx : x ∈ tsupport ω
        · simpa [hx, ← ofReal_norm] using hω x
        · simp [hx, image_eq_zero_of_notMem_tsupport hx, ← ofReal_norm]
    _ = volume (tsupport ω) := lintegral_indicator_one (isClosed_tsupport _).measurableSet
    _ ≤ volume U := measure_mono hωU

/-- The integration current has **locally finite mass**. -/
theorem hasLocallyFiniteMass_integrationCurrent (o : Orientation ℝ E (Fin m)) (Ω : Opens E) :
    HasLocallyFiniteMass
      (o.integrationCurrent Ω : 𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ) :=
  (hasLocallyFiniteMass_iff_localMass_ne_top _).2 fun K hK _ =>
    ((o.localMass_integrationCurrent_le Ω K).trans_lt hK.measure_lt_top).ne

/-- **The mass of the integration current** of an open set `Ω` of an oriented inner product space
is the volume of `Ω`; both may be infinite. -/
theorem mass_integrationCurrent (o : Orientation ℝ E (Fin m)) (hm : finrank ℝ E = m)
    (Ω : Opens E) :
    mass (o.integrationCurrent Ω : 𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ) = volume (Ω : Set E) := by
  refine le_antisymm ((localMass_eq_mass_of_subset subset_rfl).symm.trans_le
    (o.localMass_integrationCurrent_le Ω _)) ?_
  let b : OrthonormalBasis (Fin m) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr hm)
  have hG : LocallyIntegrableOn (fun _ : E => ContinuousLinearMap.id ℝ ℝ) Ω volume :=
    (locallyIntegrable_const _).locallyIntegrableOn _
  rw [← setLIntegral_one, ← ENNReal.ofReal_one, ← ContinuousLinearMap.norm_id (𝕜 := ℝ) (E := ℝ),
    ofReal_norm, ← hG.iSup_ofReal_integral_apply_eq_setLIntegral_enorm]
  refine iSup₂_le fun ψ hψ => ?_
  -- The test form `ψ • det_b`, with the regularity lowered to `n`.
  let ω : 𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ) := monoCLM ℝ (b.toBasis.testTopFormEquiv.symm ψ)
  have hωb (x : E) : ω x b = ψ x := by
    have hx : ω x = b.toBasis.testTopFormEquiv.symm ψ x := by
      simp only [ω, monoCLM_apply, le_top, le_refl, and_self, ↓reduceIte]
    rw [hx, ← b.coe_toBasis, Basis.testTopFormEquiv_symm_apply, Basis.det_self, mul_one]
  have hω (x : E) : ‖ω x‖ ≤ 1 := by
    rw [(ω x).norm_eq_norm_apply_orthonormalBasis b, hωb]
    exact hψ x
  calc ENNReal.ofReal (∫ x, ContinuousLinearMap.id ℝ ℝ (ψ x)) ≤ ‖∫ x, ω x b‖ₑ := by
        simpa [hωb, ← ofReal_norm] using ENNReal.ofReal_le_ofReal (Real.le_norm_self _)
    _ = ‖o.integrationCurrent Ω ω‖ₑ := (enorm_integrationCurrent_apply_eq o b ω).symm
    _ ≤ _ := enorm_le_mass hω

/-- **The local mass of the integration current** on an open set `U` is the volume of `Ω ∩ U`. -/
theorem localMass_integrationCurrent (o : Orientation ℝ E (Fin m)) (hm : finrank ℝ E = m)
    (Ω : Opens E) {U : Set E} (hU : IsOpen U) :
    localMass (o.integrationCurrent Ω : 𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ) U =
      volume ((Ω : Set E) ∩ U) := by
  set T := (o.integrationCurrent Ω : 𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ)
  let Ω' : Opens E := Ω ⊓ ⟨U, hU⟩
  -- Tests on `Ω` are supported in `Ω`, so only `Ω ∩ U` matters.
  have hU' : localMass T U = localMass T Ω' :=
    le_antisymm (localMass_le_iff.2 fun φ hφU hφ =>
        enorm_le_localMass (subset_inter φ.tsupport_subset hφU) hφ)
      (localMass_mono inter_subset_right)
  have hT : ⇑T ∘ (monoCLM ℝ : 𝓓^{n}(Ω', E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] 𝓓^{n}(Ω, _)) =
      o.integrationCurrent Ω' := by
    ext ω
    exact o.integrationCurrent_monoCLM inf_le_left ω
  rw [hU', ← mass_comp_monoCLM (inf_le_left : Ω' ≤ Ω), hT, o.mass_integrationCurrent hm]
  simp

/-- **The mass measure of the integration current** is the volume measure on `Ω`. -/
theorem massMeasure_integrationCurrent (o : Orientation ℝ E (Fin m)) (hm : finrank ℝ E = m)
    (Ω : Opens E) :
    massMeasure (o.integrationCurrent Ω : 𝓓^{n}(Ω, E [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] ℝ) =
      volume.comap ((↑) : Ω → E) := by
  have hemb : MeasurableEmbedding ((↑) : Ω → E) :=
    MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet
  have : (volume.comap ((↑) : Ω → E)).OuterRegular :=
    Measure.OuterRegular.comap' _ continuous_subtype_val hemb
  refine (eq_massMeasure_of_preimage_coe (o.hasLocallyFiniteMass_integrationCurrent Ω) _
    fun U hU => ?_).symm
  rw [hemb.comap_apply, image_preimage_eq_inter_range, Subtype.range_coe_subtype, inter_comm,
    o.localMass_integrationCurrent hm Ω hU, SetLike.setOfPred_mem_eq]

end Orientation

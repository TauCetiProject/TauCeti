/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import TauCeti.MeasureTheory.Group.Integral
public import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The modular character: continuity, right translation and inversion

The modular character of a locally compact group is continuous. Its real value can be
computed as the ratio of the integrals of a compactly supported continuous test function
and its right translate. This supplies the continuous weight used in convolution involutions.

We use Mathlib's convention: right translation of the argument multiplies an integral by
`c(g) = Measure.modularCharacter g`. This is the inverse of the modular function in Dana Williams,
*Crossed Products of C*-Algebras*, Lemma 1.61.

For a Haar measure `μ` and a compactly supported continuous function `f` with values in a real
normed space, we prove the right-translation formula `∫ f (x * g) dμ = c(g) • ∫ f dμ` and the
inversion formula `∫ f x⁻¹ dμ = ∫ c(x) • f x dμ`, equivalently `∫ c(x) • f x⁻¹ dμ = ∫ f dμ`.
These need no regularity, countability or σ-finiteness of `μ`. For an inner regular Haar
measure we deduce the measure identity `μ.inv = μ.withDensity c`; inversion of a left Haar
measure thus has the continuous, strictly positive density `c`. These are the
change-of-variables formulas behind the twisted involution `f*(s) = c(s) α_s(f(s⁻¹)*)` of
crossed-product convolution algebras.

The same identities hold for a regular Haar measure, which need not be inner regular when the
group is not σ-compact; the canonical `MeasureTheory.Measure.haar` is regular. Mathlib's
right-translation identity `map (· * g) μ = c(g) • μ` assumes inner regularity; for a regular `μ`
it follows from uniqueness of regular left invariant measures, since right translation is a
homeomorphism and preserves regularity. For the inversion formula, `(μ.withDensity c).inv` is a
left Haar measure agreeing with `μ` on compact sets, hence on open sets, and outer regularity of
`μ` compares the two on all sets. Consequently right translation and inversion preserve null sets
of a regular Haar measure, and both change-of-variables formulas hold for every integrand. Unlike
Mathlib's `MeasureTheory.measure_inv_null` and `MeasureTheory.quasiMeasurePreserving_mul_right`,
none of this assumes σ-finiteness.

## Main statements

* `TauCeti.integral_mul_right_eq_modularCharacter_smul`: right translation of compactly
  supported integrands.
* `TauCeti.integral_modularCharacter_smul_inv_eq_self` and
  `TauCeti.integral_inv_eq_integral_modularCharacter_smul`: the inversion formula on compactly
  supported integrands.
* `MeasureTheory.Measure.isMulRightInvariant_withDensity_modularCharacter`: `μ.withDensity c`
  is right invariant for an inner regular Haar measure `μ`.
* `MeasureTheory.Measure.inv_eq_withDensity_modularCharacter`: `μ.inv = μ.withDensity c` for an
  inner regular Haar measure `μ`.
* `MeasureTheory.Measure.map_right_mul_eq_modularCharacter_smul_of_regular`:
  `map (· * g) μ = c(g) • μ` for a regular Haar measure `μ`.
* `MeasureTheory.Measure.inv_eq_withDensity_modularCharacter_of_regular`:
  `μ.inv = μ.withDensity c` for a regular Haar measure `μ`.
* `MeasureTheory.Measure.quasiMeasurePreserving_mul_right_of_regular`,
  `MeasureTheory.Measure.quasiMeasurePreserving_inv_of_regular` and
  `MeasureTheory.Measure.quasiMeasurePreserving_inv_mul_of_regular`: right translation, inversion
  and `y ↦ y⁻¹ * x` preserve null sets of a regular Haar measure.
* `TauCeti.integral_mul_right_eq_modularCharacter_smul_of_regular`,
  `TauCeti.integral_inv_eq_integral_modularCharacter_smul_of_regular` and their lower Lebesgue
  versions `TauCeti.lintegral_mul_right_eq_modularCharacter_mul_of_regular` and
  `TauCeti.lintegral_inv_eq_lintegral_modularCharacter_mul_of_regular`: the change-of-variables
  formulas for every integrand, against a regular Haar measure.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Lemma 1.61, for the modular function and
  the inversion formula in the convention `Δ = c⁻¹`.
-/

public section

open MeasureTheory
open scoped NNReal ENNReal

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- The bundled modular character evaluates to the modular character function. -/
theorem modularCharacter_apply (g : G) :
    Measure.modularCharacter g = Measure.modularCharacterFun g := rfl

/-- A nonzero test integral computes the modular character by right translation.
No regularity assumption on the Haar measure is needed. -/
theorem modularCharacter_eq_integral_div [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] {f : G → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfi : ∫ x, f x ∂μ ≠ 0) (g : G) :
    (Measure.modularCharacter g : ℝ) = (∫ x, f (x * g) ∂μ) / ∫ x, f x ∂μ := by
  rw [modularCharacter_apply, Measure.modularCharacterFun_eq_haarScalarFactor μ g,
    Measure.haarScalarFactor_eq_integral_div _ _ hf hfc hfi,
    integral_map (by fun_prop) hf.aestronglyMeasurable]

/-- The modular character is continuous, without countability or separation assumptions. -/
@[fun_prop]
theorem continuous_modularCharacter : Continuous (Measure.modularCharacter : G → ℝ≥0) := by
  borelize G
  obtain ⟨f, hfc, hfn, hf1⟩ := exists_continuous_nonneg_pos (1 : G)
  have hfi : ∫ x, f x ∂(Measure.haar : Measure G) ≠ 0 :=
    (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hfn hf1).ne'
  have hc : Continuous (fun g : G => ∫ x, f (x * g) ∂(Measure.haar : Measure G)) := by
    have h := continuous_integral_apply_inv_mul (μ := (Measure.haar : Measure G).inv)
      f.continuous hfc
    simpa only [integral_inv_measure, inv_inv] using h
  exact continuous_induced_rng.mpr <| (hc.div_const _).congr fun g =>
    (modularCharacter_eq_integral_div f.continuous hfc hfi g).symm


section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]

/-- **Right translation of a compactly supported integrand** multiplies its Haar integral by the
modular character. No regularity of the Haar measure is needed. -/
theorem integral_mul_right_eq_modularCharacter_smul {f : G → E} (hf : Continuous f)
    (hfc : HasCompactSupport f) (g : G) :
    ∫ x, f (x * g) ∂μ = (Measure.modularCharacter g : ℝ) • ∫ x, f x ∂μ := by
  have hreal : ∀ {F : G → ℝ}, Continuous F → HasCompactSupport F →
      ∫ x, F (x * g) ∂μ = (Measure.modularCharacter g : ℝ) • ∫ x, F x ∂μ := by
    intro F hF hFc
    rw [← integral_map (by fun_prop) hF.aestronglyMeasurable,
      Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport _ μ hF hFc,
      integral_smul_nnreal_measure, modularCharacter_apply,
      Measure.modularCharacterFun_eq_haarScalarFactor μ g, NNReal.smul_def]
  -- Pass from real-valued integrands to `E`-valued ones by testing against the dual of `E`.
  by_cases hE : CompleteSpace E
  · refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun φ => ?_
    have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport hfc
    have hgi : Integrable (fun x => f (x * g)) μ :=
      (hf.comp (continuous_id.mul continuous_const)).integrable_of_hasCompactSupport
        (hfc.comp_homeomorph (Homeomorph.mulRight g))
    rw [map_smul, ← φ.integral_comp_comm hfi, ← φ.integral_comp_comm hgi]
    exact hreal (φ.continuous.comp hf) (hfc.comp_left φ.map_zero)
  · simp [integral_of_not_completeSpace hE]

/-- The real-valued case of `integral_modularCharacter_smul_inv_eq_self`:
`∫ c(x) * F x⁻¹ dμ = ∫ F dμ` for a continuous compactly supported `F : G → ℝ`. -/
private theorem integral_modularCharacter_mul_inv_eq_self_real {F : G → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    ∫ x, (Measure.modularCharacter x : ℝ) * F x⁻¹ ∂μ = ∫ x, F x ∂μ := by
  -- Compare `μ` with the right invariant measure `μ.inv` using Mathlib's
  -- `Measure.integral_isMulLeftInvariant_isMulRightInvariant_combo`; the density it involves is
  -- computed by the right-translation formula.
  obtain ⟨g, hgc, hgn, hg1⟩ := exists_continuous_nonneg_pos (1 : G)
  have hgi : 0 < ∫ x, g x ∂μ :=
    g.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hgc hgn hg1
  have hD : ∀ y, ∫ z, g (z⁻¹ * y) ∂μ.inv = (Measure.modularCharacter y : ℝ) * ∫ x, g x ∂μ := by
    intro y
    rw [integral_inv_measure (fun z => g (z⁻¹ * y)) μ]
    simp only [inv_inv]
    exact integral_mul_right_eq_modularCharacter_smul g.continuous hgc y
  have hc : ∀ y : G, ((Measure.modularCharacter y⁻¹ : ℝ) * ∫ x, g x ∂μ)⁻¹ =
      (Measure.modularCharacter y : ℝ) * (∫ x, g x ∂μ)⁻¹ := by
    intro y
    rw [map_inv, NNReal.coe_inv, mul_inv, inv_inv]
  rw [Measure.integral_isMulLeftInvariant_isMulRightInvariant_combo (ν := μ.inv) hF hFc
    g.continuous hgc hgn hg1]
  simp_rw [hD, integral_inv_measure (fun y => F y * _) μ, hc, ← mul_assoc, integral_mul_const,
    inv_mul_cancel_right₀ hgi.ne']
  congr with x
  ring

/-- **The inversion formula** for a compactly supported integrand, in the form used by the
twisted involution `f*(x) = c(x) f(x⁻¹)`: weighting by the modular character makes inversion
preserve Haar integrals. No regularity of the Haar measure is needed. -/
theorem integral_modularCharacter_smul_inv_eq_self {f : G → E} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    ∫ x, (Measure.modularCharacter x : ℝ) • f x⁻¹ ∂μ = ∫ x, f x ∂μ := by
  -- Pass from real-valued integrands to `E`-valued ones by testing against the dual of `E`.
  by_cases hE : CompleteSpace E
  · refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun φ => ?_
    have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport hfc
    have hgi : Integrable (fun x => (Measure.modularCharacter x : ℝ) • f x⁻¹) μ :=
      ((NNReal.continuous_coe.comp continuous_modularCharacter).smul
        (hf.comp continuous_inv)).integrable_of_hasCompactSupport
          ((hfc.comp_homeomorph (Homeomorph.inv G)).smul_left)
    rw [← φ.integral_comp_comm hfi, ← φ.integral_comp_comm hgi]
    simp only [map_smul, smul_eq_mul]
    exact integral_modularCharacter_mul_inv_eq_self_real (F := fun x => φ (f x))
      (φ.continuous.comp hf) (hfc.comp_left φ.map_zero)
  · simp [integral_of_not_completeSpace hE]

/-- **The inversion formula** for a compactly supported integrand: inverting the argument
weights a Haar integral by the modular character. No regularity of the Haar measure is
needed. -/
theorem integral_inv_eq_integral_modularCharacter_smul {f : G → E} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    ∫ x, f x⁻¹ ∂μ = ∫ x, (Measure.modularCharacter x : ℝ) • f x ∂μ := by
  simpa only [inv_inv] using (integral_modularCharacter_smul_inv_eq_self (f := fun x => f x⁻¹)
    (hf.comp continuous_inv) (hfc.comp_homeomorph (Homeomorph.inv G))).symm

end Integral

end TauCeti

namespace MeasureTheory.Measure

open TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G)

/-- Inverting `μ.withDensity c` and weighting the result by `c` gives back `μ.inv`, for any
measure `μ`, since `c(y⁻¹) c(y) = 1`. -/
private theorem inv_withDensity_modularCharacter_withDensity :
    (μ.withDensity fun x => (modularCharacter x : ℝ≥0∞)).inv.withDensity
      (fun x => (modularCharacter x : ℝ≥0∞)) = μ.inv := by
  set c : G → ℝ≥0∞ := fun x => (modularCharacter x : ℝ≥0∞)
  have hcm : Measurable c :=
    measurable_coe_nnreal_ennreal.comp continuous_modularCharacter.measurable
  have h := MeasurableEquiv.map_withDensity (MeasurableEquiv.inv G) μ c
  simp only [MeasurableEquiv.inv_apply, MeasurableEquiv.symm_inv] at h
  rw [inv_def, h, ← inv_def,
    ← withDensity_mul (f := fun y => c y⁻¹) _ (hcm.comp measurable_inv) hcm]
  convert withDensity_one (μ := μ.inv)
  ext x
  simp only [c, Pi.mul_apply, Pi.one_apply, ← ENNReal.coe_mul, ← map_mul, inv_mul_cancel,
    map_one, ENNReal.coe_one]

/-- Weighting a measure by the modular character gives a right invariant measure, as soon as
right translation scales the measure by the modular character. -/
private theorem isMulRightInvariant_withDensity_modularCharacter_of_map
    (hμ : ∀ g : G, map (· * g) μ = modularCharacter g • μ) :
    (μ.withDensity fun x => (modularCharacter x : ℝ≥0∞)).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h := MeasurableEquiv.map_withDensity (MeasurableEquiv.mulRight g) μ
    fun x => (modularCharacter x : ℝ≥0∞)
  simp only [MeasurableEquiv.coe_mulRight, MeasurableEquiv.symm_mulRight] at h
  have hm : Measurable fun y : G => (modularCharacter (y * g⁻¹) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp
      ((continuous_modularCharacter.comp (continuous_id.mul continuous_const)).measurable)
  rw [h, hμ g, ENNReal.smul_def, withDensity_smul_measure, ← withDensity_smul _ hm]
  congr with x
  simp only [Pi.smul_apply, smul_eq_mul, ← ENNReal.coe_mul]
  rw [map_mul, mul_left_comm, ← map_mul, mul_inv_cancel, map_one, mul_one]

variable [μ.IsHaarMeasure]

/-- Weighting an inner regular Haar measure by the modular character gives a right invariant
measure. -/
theorem isMulRightInvariant_withDensity_modularCharacter [μ.InnerRegular] :
    (μ.withDensity fun x => (modularCharacter x : ℝ≥0∞)).IsMulRightInvariant :=
  isMulRightInvariant_withDensity_modularCharacter_of_map μ
    (map_right_mul_eq_modularCharacterFun_smul μ)

/-- If `μ.withDensity c` is right invariant, then its inverse is a left invariant measure with
the same Haar scalar factor as `μ`. -/
private theorem haarScalarFactor_inv_withDensity_modularCharacter
    [(μ.withDensity fun x => (modularCharacter x : ℝ≥0∞)).IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts (μ.withDensity fun x => (modularCharacter x : ℝ≥0∞)).inv] :
    haarScalarFactor (μ.withDensity fun x => (modularCharacter x : ℝ≥0∞)).inv μ = 1 := by
  -- Both measures are left invariant, and the inversion formula shows that they integrate
  -- compactly supported functions alike.
  set ν := μ.withDensity fun x => (modularCharacter x : ℝ≥0∞) with hν
  obtain ⟨g, hgc, hgn, hg1⟩ := exists_continuous_nonneg_pos (1 : G)
  have hgi : 0 < ∫ x, g x ∂μ :=
    g.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hgc hgn hg1
  have hint : ∫ x, g x ∂ν.inv = ∫ x, g x ∂μ := by
    rw [integral_inv_measure, hν,
      integral_withDensity_eq_integral_smul continuous_modularCharacter.measurable]
    simp_rw [NNReal.smul_def]
    exact integral_modularCharacter_smul_inv_eq_self g.continuous hgc
  have h := integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport ν.inv μ g.continuous hgc
  rw [hint, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at h
  exact_mod_cast (mul_eq_right₀ hgi.ne').1 h.symm

/-- If `μ.withDensity c` is right invariant, then its inverse agrees with `μ` on compact
sets. -/
private theorem inv_withDensity_modularCharacter_apply_of_isCompact
    [(μ.withDensity fun x => (modularCharacter x : ℝ≥0∞)).IsMulRightInvariant] {K : Set G}
    (hK : IsCompact K) :
    (μ.withDensity fun x => (modularCharacter x : ℝ≥0∞)).inv K = μ K := by
  have : IsLocallyFiniteMeasure (μ.withDensity fun x => (modularCharacter x : ℝ≥0∞)) :=
    IsLocallyFiniteMeasure.withDensity_coe continuous_modularCharacter
  simpa [haarScalarFactor_inv_withDensity_modularCharacter μ] using
    measure_isMulInvariant_eq_smul_of_isCompact_closure
      (μ.withDensity fun x => (modularCharacter x : ℝ≥0∞)).inv μ hK.closure

/-- **The inversion formula** for an inner regular Haar measure: the inverse measure `μ.inv`,
that is `μ.map Inv.inv`, has density `modularCharacter` with respect to `μ`. -/
theorem inv_eq_withDensity_modularCharacter [μ.InnerRegular] :
    μ.inv = μ.withDensity fun x => (modularCharacter x : ℝ≥0∞) := by
  set ν := μ.withDensity fun x => (modularCharacter x : ℝ≥0∞) with hν
  have : ν.IsMulRightInvariant := isMulRightInvariant_withDensity_modularCharacter μ
  have : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_coe
    continuous_modularCharacter
  -- Inner regularity of `μ.inv` and agreement on compact sets give `μ.inv ≤ ν`.
  have hle : μ.inv ≤ ν := by
    refine le_iff.2 fun s hs => ?_
    rw [hs.measure_eq_iSup_isCompact]
    refine iSup₂_le fun K hKs => iSup_le fun hK => ?_
    calc μ.inv K = ν K := by
          rw [inv_apply, ← inv_withDensity_modularCharacter_apply_of_isCompact μ hK.inv,
            inv_apply, inv_inv]
      _ ≤ ν s := measure_mono hKs
  -- Inverting `μ.inv ≤ ν` and reweighting by `c` gives the reverse inequality.
  have h₁ : μ ≤ ν.inv :=
    calc μ = μ.inv.inv := μ.inv_inv.symm
      _ ≤ ν.inv := map_mono hle measurable_inv
  have hge : ν ≤ μ.inv :=
    calc ν ≤ ν.inv.withDensity fun x => (modularCharacter x : ℝ≥0∞) := le_iff.2 fun s hs => by
          rw [hν, withDensity_apply _ hs, withDensity_apply _ hs]
          exact lintegral_mono' (restrict_mono subset_rfl h₁) le_rfl
      _ = μ.inv := inv_withDensity_modularCharacter_withDensity μ
  exact le_antisymm hle hge

section Regular

variable [μ.Regular]

/-- **Right translation of a regular Haar measure** multiplies it by the modular character.
This is the counterpart, for regular instead of inner regular Haar measures, of Mathlib's
`MeasureTheory.Measure.map_right_mul_eq_modularCharacterFun_smul`. -/
theorem map_right_mul_eq_modularCharacter_smul_of_regular (g : G) :
    map (· * g) μ = modularCharacter g • μ := by
  have := Regular.map (μ := μ) (Homeomorph.mulRight g)
  rw [Homeomorph.coe_mulRight] at this
  rw [modularCharacter_apply, modularCharacterFun_eq_haarScalarFactor μ g]
  exact isMulLeftInvariant_eq_smul_of_regular _ μ

/-- Right translation scales the measure of every set, measurable or not, by the modular
character of a regular Haar measure. -/
theorem measure_preimage_mul_right_eq_modularCharacter_mul_of_regular (g : G) (s : Set G) :
    μ ((· * g) ⁻¹' s) = modularCharacter g * μ s := by
  have h := (MeasurableEquiv.mulRight g).map_apply (μ := μ) s
  rw [MeasurableEquiv.coe_mulRight, map_right_mul_eq_modularCharacter_smul_of_regular,
    smul_apply, nnreal_smul_coe_apply] at h
  exact h.symm

/-- Right translation preserves null sets of a regular Haar measure. -/
theorem measure_mul_right_null_of_regular (g : G) {s : Set G} :
    μ ((· * g) ⁻¹' s) = 0 ↔ μ s = 0 := by
  have hg : modularCharacter g ≠ 0 := (modularCharacterFun_pos g).ne'
  simp [measure_preimage_mul_right_eq_modularCharacter_mul_of_regular, hg]

/-- Right translation is quasi-measure-preserving for a regular Haar measure. -/
@[fun_prop]
theorem quasiMeasurePreserving_mul_right_of_regular (g : G) :
    QuasiMeasurePreserving (· * g) μ μ :=
  ⟨measurable_mul_const g, by
    rw [map_right_mul_eq_modularCharacter_smul_of_regular]
    exact smul_absolutelyContinuous⟩

/-- Weighting a regular Haar measure by the modular character gives a right invariant
measure. -/
theorem isMulRightInvariant_withDensity_modularCharacter_of_regular :
    (μ.withDensity fun x => (modularCharacter x : ℝ≥0∞)).IsMulRightInvariant :=
  isMulRightInvariant_withDensity_modularCharacter_of_map μ
    (map_right_mul_eq_modularCharacter_smul_of_regular μ)

/-- **The inversion formula** for a regular Haar measure: the inverse measure `μ.inv`, that is
`μ.map Inv.inv`, has density `modularCharacter` with respect to `μ`. No inner regularity or
σ-finiteness of `μ` is assumed. -/
theorem inv_eq_withDensity_modularCharacter_of_regular :
    μ.inv = μ.withDensity fun x => (modularCharacter x : ℝ≥0∞) := by
  set ν := μ.withDensity fun x => (modularCharacter x : ℝ≥0∞) with hν
  have : ν.IsMulRightInvariant := isMulRightInvariant_withDensity_modularCharacter_of_regular μ
  have : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_coe
    continuous_modularCharacter
  -- `ν.inv` agrees with `μ` on compact sets, so it is positive on nonempty open sets and hence
  -- a left Haar measure with the same scalar factor as `μ`.
  have : ν.inv.IsOpenPosMeasure := by
    refine ⟨fun U hU ⟨x, hx⟩ => ?_⟩
    obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
    refine (measure_pos_of_nonempty_interior μ ⟨x, hxK⟩).trans_le ?_ |>.ne'
    rw [← inv_withDensity_modularCharacter_apply_of_isCompact μ hK]
    exact measure_mono hKU
  have : ν.inv.IsHaarMeasure := {}
  -- Two Haar measures agree on open sets up to their scalar factor, which is `1` here; outer
  -- regularity of `μ` then gives `ν.inv ≤ μ`.
  have hle : ν.inv ≤ μ := le_iff'.2 fun s => by
    rw [Set.measure_eq_iInf_isOpen s μ]
    refine le_iInf₂ fun U hsU => le_iInf fun hU => ?_
    calc ν.inv s ≤ ν.inv U := measure_mono hsU
      _ = μ U := by
        rw [measure_isHaarMeasure_eq_smul_of_isOpen ν.inv μ hU,
          haarScalarFactor_inv_withDensity_modularCharacter μ, one_smul]
  -- Inverting gives `ν ≤ μ.inv`; reweighting `ν.inv ≤ μ` by `c` gives the reverse inequality.
  have hge : ν ≤ μ.inv :=
    calc ν = ν.inv.inv := ν.inv_inv.symm
      _ ≤ μ.inv := map_mono hle measurable_inv
  refine le_antisymm ?_ hge
  calc μ.inv = ν.inv.withDensity fun x => (modularCharacter x : ℝ≥0∞) :=
        (inv_withDensity_modularCharacter_withDensity μ).symm
    _ ≤ ν := le_iff.2 fun s hs => by
        rw [hν, withDensity_apply _ hs, withDensity_apply _ hs]
        exact lintegral_mono' (restrict_mono subset_rfl hle) le_rfl

/-- Inversion maps null sets of a regular Haar measure to null sets: `μ.inv ≪ μ`. Mathlib's
`MeasureTheory.inv_absolutelyContinuous` needs σ-finiteness instead of regularity. -/
theorem inv_absolutelyContinuous_of_regular : μ.inv ≪ μ := by
  rw [inv_eq_withDensity_modularCharacter_of_regular μ]
  exact withDensity_absolutelyContinuous _ _

/-- A regular Haar measure is absolutely continuous with respect to its inverse. -/
theorem absolutelyContinuous_inv_of_regular : μ ≪ μ.inv := by
  rw [inv_eq_withDensity_modularCharacter_of_regular μ]
  exact withDensity_absolutelyContinuous' (by fun_prop) <|
    .of_forall fun x => ENNReal.coe_ne_zero.2 (modularCharacterFun_pos x).ne'

/-- Inversion preserves null sets of a regular Haar measure. -/
@[simp]
theorem measure_inv_null_of_regular {s : Set G} : μ s⁻¹ = 0 ↔ μ s = 0 := by
  rw [← inv_apply]
  exact ⟨fun h => absolutelyContinuous_inv_of_regular μ h,
    fun h => inv_absolutelyContinuous_of_regular μ h⟩

/-- Inversion is quasi-measure-preserving for a regular Haar measure. -/
@[fun_prop]
theorem quasiMeasurePreserving_inv_of_regular : QuasiMeasurePreserving Inv.inv μ μ :=
  ⟨measurable_inv, inv_absolutelyContinuous_of_regular μ⟩

/-- For a regular Haar measure, `y ↦ y⁻¹ * x` is quasi-measure-preserving: it is inversion
followed by right translation by `x`. -/
@[fun_prop]
theorem quasiMeasurePreserving_inv_mul_of_regular (x : G) :
    QuasiMeasurePreserving (fun y => y⁻¹ * x) μ μ :=
  (quasiMeasurePreserving_mul_right_of_regular μ x).comp (quasiMeasurePreserving_inv_of_regular μ)

end Regular

end MeasureTheory.Measure

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] [μ.Regular]

/-- **Right translation of a lower Lebesgue integral** against a regular Haar measure multiplies
it by the modular character, for every integrand. -/
theorem lintegral_mul_right_eq_modularCharacter_mul_of_regular (f : G → ℝ≥0∞) (g : G) :
    ∫⁻ x, f (x * g) ∂μ = Measure.modularCharacter g * ∫⁻ x, f x ∂μ := by
  have h := lintegral_map_equiv (μ := μ) f (MeasurableEquiv.mulRight g)
  simp only [MeasurableEquiv.coe_mulRight,
    Measure.map_right_mul_eq_modularCharacter_smul_of_regular, lintegral_smul_measure,
    ENNReal.smul_def, smul_eq_mul] at h
  exact h.symm

/-- **The inversion formula** for a regular Haar measure: inverting the argument weights the
lower Lebesgue integral by the modular character, for every integrand. -/
theorem lintegral_inv_eq_lintegral_modularCharacter_mul_of_regular (f : G → ℝ≥0∞) :
    ∫⁻ x, f x⁻¹ ∂μ = ∫⁻ x, Measure.modularCharacter x * f x ∂μ := by
  have h := lintegral_map_equiv (μ := μ) f (MeasurableEquiv.inv G)
  rw [MeasurableEquiv.inv_apply, ← Measure.inv,
    Measure.inv_eq_withDensity_modularCharacter_of_regular,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      continuous_modularCharacter.measurable.coe_nnreal_ennreal
      (.of_forall fun _ => ENNReal.coe_lt_top)] at h
  exact h.symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Right translation of a Bochner integral** against a regular Haar measure multiplies it by
the modular character, for every integrand. -/
theorem integral_mul_right_eq_modularCharacter_smul_of_regular (f : G → E) (g : G) :
    ∫ x, f (x * g) ∂μ = (Measure.modularCharacter g : ℝ) • ∫ x, f x ∂μ := by
  have h := integral_map_equiv (μ := μ) (MeasurableEquiv.mulRight g) f
  simp only [MeasurableEquiv.coe_mulRight,
    Measure.map_right_mul_eq_modularCharacter_smul_of_regular, integral_smul_nnreal_measure,
    NNReal.smul_def] at h
  exact h.symm

/-- **The inversion formula** for a regular Haar measure: inverting the argument weights the
Bochner integral by the modular character, for every integrand. -/
theorem integral_inv_eq_integral_modularCharacter_smul_of_regular (f : G → E) :
    ∫ x, f x⁻¹ ∂μ = ∫ x, (Measure.modularCharacter x : ℝ) • f x ∂μ := by
  rw [← integral_inv_measure, Measure.inv_eq_withDensity_modularCharacter_of_regular,
    integral_withDensity_eq_integral_smul continuous_modularCharacter.measurable]
  simp_rw [NNReal.smul_def]

end TauCeti

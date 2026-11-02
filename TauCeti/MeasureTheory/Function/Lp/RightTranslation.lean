/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import TauCeti.MeasureTheory.Function.Lp.LeftTranslation
public import TauCeti.MeasureTheory.Group.ModularCharacter

/-!
# Right translation on `Lᵖ` of a locally compact group

Let `μ` be a regular left Haar measure on a locally compact group `G`, and write
`c = MeasureTheory.Measure.modularCharacter`, so that `∫ f (x * g) dμ = c(g) ∫ f dμ`. Right
translation `x ↦ x * g` scales `‖·‖_p ^ p` by `c(g)`, so the weighted right translation

```text
(R_g f)(x) = c(g⁻¹)^(1/p) • f (x * g),        R_g R_h = R_(g * h),
```

is an isometry of `Lᵖ`, with the convention `1/∞ = 0`. On `L¹` it is `f ↦ c(g⁻¹) • f (· * g)`.
Unlike left translation, it is not given by a measure-preserving map unless `G` is unimodular.

We obtain it by conjugating left translation with the *modular inversion*

```text
(J f)(x) = c(x)^(1/p) • f x⁻¹,
```

which is an isometric involution of `Lᵖ` by the inversion formula `μ.inv = μ.withDensity c`.
Indeed `J L_g J = R_g`, so right translation inherits from left translation the group law and,
for `p < ∞`, strong continuity: each orbit `g ↦ R_g f` is continuous. By left invariance and
the inversion formula, the convolution `(h ⋆ k)(x) = ∫ y, h y * k (y⁻¹ * x) dμ` of `L¹`
functions is `∫ z, k z * c(z) * h (x * z⁻¹) dμ`, an average of the right translates
`R_(z⁻¹) h` of `h` weighted by `k`. Strong continuity of right translation on `L¹` is therefore
the input for showing that convolution on the right with kernels concentrated near the
identity approximates `h`.

No σ-finiteness of `μ` and no countability of `G` is assumed.

## Main definitions

* `MeasureTheory.Lp.modularInversion μ p 𝕜`: the isometric involution
  `f ↦ (x ↦ c(x)^(1/p) • f x⁻¹)` of `Lp E p μ`.
* `MeasureTheory.Lp.rightTranslation μ p 𝕜`: right translation `g ↦ R_g` on `Lp E p μ`, as a
  group homomorphism to linear isometry equivalences.

## Main results

* `TauCeti.eLpNorm_modularCharacter_rpow_smul_comp_inv`: the weighted inversion preserves
  the `Lᵖ` seminorm.
* `MeasureTheory.Lp.coeFn_modularInversion`, `MeasureTheory.Lp.coeFn_rightTranslation`: the
  pointwise formulas, almost everywhere.
* `MeasureTheory.Lp.modularInversion_modularInversion`: the modular inversion is an involution.
* `MeasureTheory.Lp.leftTranslation_rightTranslation`: left and right translations commute.
* `MeasureTheory.Lp.rightTranslation_le_rightTranslation_iff`: right translation is an order
  automorphism of real `Lᵖ`.
* `MeasureTheory.Lp.integral_rightTranslation`: right translation on `L¹` preserves the integral.
* `MeasureTheory.Lp.continuous_rightTranslation_apply`: right translation is strongly continuous
  for `p < ∞`.
* `MeasureTheory.eLpNorm_comp_mul_right_of_regular`: the unweighted right translate satisfies
  `‖f (· * g)‖_p = c(g)^(1/p) ‖f‖_p`.
* `MeasureTheory.MemLp.tendsto_eLpNorm_comp_mul_right_sub_of_regular`: `‖f (· * g) - f‖_p → 0`
  as `g → 1`, for `1 ≤ p < ∞`.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, §§2.4–2.5, for the modular function
  and the continuity of translations in `Lᵖ`.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix A.3.
-/

public section

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure TauCeti
open scoped ENNReal NNReal

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] [μ.Regular] [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞}

namespace MeasureTheory

/-- The weighted inversion `x ↦ c(x)^r • f x⁻¹` of an almost everywhere strongly measurable
function is almost everywhere strongly measurable. -/
theorem AEStronglyMeasurable.modularCharacter_rpow_smul_comp_inv {f : G → E}
    (hf : AEStronglyMeasurable f μ) (r : ℝ) :
    AEStronglyMeasurable (fun x => (modularCharacter x : ℝ) ^ r • f x⁻¹) μ :=
  (continuous_modularCharacter.measurable.coe_nnreal_real.pow_const r).aestronglyMeasurable.smul
    (hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_inv_of_regular μ))

end MeasureTheory

namespace TauCeti

/-- The weighted inversion `x ↦ c(x)^(1/p) • f x⁻¹` preserves the `Lᵖ` seminorm of an almost
everywhere strongly measurable function, for a regular Haar measure. -/
theorem eLpNorm_modularCharacter_rpow_smul_comp_inv {f : G → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => (modularCharacter x : ℝ) ^ p.toReal⁻¹ • f x⁻¹) p μ = eLpNorm f p μ := by
  have hJf := hf.modularCharacter_rpow_smul_comp_inv p.toReal⁻¹
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLpNorm_exponent_zero hJf, eLpNorm_exponent_zero hf]
  rcases eq_or_ne p ∞ with rfl | hptop
  · -- For `p = ∞` the weight is `1`, and `μ` and `μ.inv` have the same null sets.
    simp only [ENNReal.toReal_top, inv_zero, Real.rpow_zero, one_smul] at hJf ⊢
    rw [eLpNorm_exponent_top hJf, eLpNorm_exponent_top hf, eLpNormEssSup_eq_essSup_enorm,
      eLpNormEssSup_eq_essSup_enorm]
    have h := (MeasurableEquiv.inv G).measurableEmbedding.essSup_map_measure (μ := μ)
      (g := fun x => ‖f x‖ₑ)
    rw [MeasurableEquiv.inv_apply, ← Measure.inv] at h
    rw [← Function.comp_def (fun x => ‖f x‖ₑ) Inv.inv, ← h]
    exact le_antisymm (essSup_mono_measure (inv_absolutelyContinuous_of_regular μ))
      (essSup_mono_measure (absolutelyContinuous_inv_of_regular μ))
  -- For `0 < p < ∞`, the weight raised to the power `p` is the density `c` of `μ.inv`.
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hJf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf]
  congr 1
  have hweight (x : G) : ‖(modularCharacter x : ℝ) ^ p.toReal⁻¹ • f x⁻¹‖ₑ ^ p.toReal =
      modularCharacter x * ‖f x⁻¹‖ₑ ^ p.toReal := by
    rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hq.le, Real.enorm_of_nonneg (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le, ← Real.rpow_mul (by positivity),
      inv_mul_cancel₀ hq.ne', Real.rpow_one, ENNReal.ofReal_coe_nnreal]
  have h := lintegral_inv_eq_lintegral_modularCharacter_mul_of_regular (μ := μ)
    fun y => modularCharacter y⁻¹ * ‖f y‖ₑ ^ p.toReal
  simp only [inv_inv, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one,
    ENNReal.coe_one, one_mul] at h
  simp_rw [hweight, h]

end TauCeti

namespace MeasureTheory

/-- The weighted inversion `x ↦ c(x)^(1/p) • f x⁻¹` of an `Lᵖ` function is in `Lᵖ`, for a regular
Haar measure. -/
theorem MemLp.modularCharacter_rpow_smul_comp_inv {f : G → E} (hf : MemLp f p μ) :
    MemLp (fun x => (modularCharacter x : ℝ) ^ p.toReal⁻¹ • f x⁻¹) p μ :=
  memLp_iff.2 <| (eLpNorm_modularCharacter_rpow_smul_comp_inv hf.aestronglyMeasurable).trans_lt
    (memLp_iff.1 hf)

namespace Lp

variable (μ p) (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  [SMulCommClass ℝ 𝕜 E]

/-- The modular inversion as a linear map, before its involutivity is proved. -/
private def modularInversionₗ : Lp E p μ →ₗ[𝕜] Lp E p μ where
  toFun f := (Lp.memLp f).modularCharacter_rpow_smul_comp_inv.toLp _
  map_add' f f' := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (Lp.memLp (f + f')).modularCharacter_rpow_smul_comp_inv,
      Lp.coeFn_add (MemLp.toLp _ (Lp.memLp f).modularCharacter_rpow_smul_comp_inv)
        (MemLp.toLp _ (Lp.memLp f').modularCharacter_rpow_smul_comp_inv),
      MemLp.coeFn_toLp (Lp.memLp f).modularCharacter_rpow_smul_comp_inv,
      MemLp.coeFn_toLp (Lp.memLp f').modularCharacter_rpow_smul_comp_inv,
      (quasiMeasurePreserving_inv_of_regular μ).ae (Lp.coeFn_add f f')] with x h h' hf hf' hadd
    rw [h, h', Pi.add_apply, hf, hf', hadd, Pi.add_apply, smul_add]
  map_smul' k f := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (Lp.memLp (k • f)).modularCharacter_rpow_smul_comp_inv,
      Lp.coeFn_smul k (MemLp.toLp _ (Lp.memLp f).modularCharacter_rpow_smul_comp_inv),
      MemLp.coeFn_toLp (Lp.memLp f).modularCharacter_rpow_smul_comp_inv,
      (quasiMeasurePreserving_inv_of_regular μ).ae (Lp.coeFn_smul k f)] with x h h' hf hsmul
    rw [h, RingHom.id_apply, h', Pi.smul_apply, hf, hsmul, Pi.smul_apply, smul_comm]

private theorem coeFn_modularInversionₗ (f : Lp E p μ) :
    modularInversionₗ μ p 𝕜 f =ᵐ[μ] fun x => (modularCharacter x : ℝ) ^ p.toReal⁻¹ • f x⁻¹ :=
  MemLp.coeFn_toLp (Lp.memLp f).modularCharacter_rpow_smul_comp_inv

private theorem modularInversionₗ_involutive :
    Function.Involutive (modularInversionₗ (E := E) μ p 𝕜) :=
  fun f => Lp.ext <| by
    filter_upwards [coeFn_modularInversionₗ μ p 𝕜 (modularInversionₗ μ p 𝕜 f),
      (quasiMeasurePreserving_inv_of_regular μ).ae (coeFn_modularInversionₗ μ p 𝕜 f)]
      with x h h'
    rw [h, h', inv_inv, smul_smul, modularCharacter_rpow_mul_inv, one_smul]

variable [Fact (1 ≤ p)]

/-- The **modular inversion** `(J f)(x) = c(x)^(1/p) • f x⁻¹` on `Lp E p μ` for a regular Haar
measure `μ`, where `c` is the modular character and `1/∞ = 0`. It is a linear isometric
involution. -/
def modularInversion : Lp E p μ ≃ₗᵢ[𝕜] Lp E p μ where
  toLinearEquiv := .ofInvolutive (modularInversionₗ μ p 𝕜) (modularInversionₗ_involutive μ p 𝕜)
  norm_map' f := by
    rw [LinearEquiv.coe_ofInvolutive, norm_def, norm_def,
      eLpNorm_congr_ae (coeFn_modularInversionₗ μ p 𝕜 f),
      eLpNorm_modularCharacter_rpow_smul_comp_inv (Lp.aestronglyMeasurable f)]

variable {μ p 𝕜}

/-- The modular inversion `J f` is almost everywhere the function `x ↦ c(x)^(1/p) • f x⁻¹`. -/
theorem coeFn_modularInversion (f : Lp E p μ) :
    modularInversion μ p 𝕜 f =ᵐ[μ] fun x => (modularCharacter x : ℝ) ^ p.toReal⁻¹ • f x⁻¹ :=
  coeFn_modularInversionₗ μ p 𝕜 f

/-- The modular inversion is an involution. -/
@[simp]
theorem modularInversion_modularInversion (f : Lp E p μ) :
    modularInversion μ p 𝕜 (modularInversion μ p 𝕜 f) = f :=
  modularInversionₗ_involutive μ p 𝕜 f

/-- The modular inversion is its own inverse. -/
@[simp]
theorem modularInversion_symm :
    (modularInversion μ p 𝕜).symm = modularInversion (E := E) μ p 𝕜 :=
  LinearIsometryEquiv.ext fun f => by
    rw [LinearIsometryEquiv.symm_apply_eq, modularInversion_modularInversion]

/-- The modular inversion squares to the identity in the group of linear isometry
equivalences. -/
@[simp]
theorem modularInversion_mul_self :
    modularInversion μ p 𝕜 * modularInversion μ p 𝕜 = (1 : Lp E p μ ≃ₗᵢ[𝕜] Lp E p μ) :=
  LinearIsometryEquiv.ext modularInversion_modularInversion

variable (μ p 𝕜)

/-- Right translation `g ↦ R_g` on `Lp E p μ` for a regular Haar measure `μ`, where
`(R_g f)(x) = c(g⁻¹)^(1/p) • f (x * g)`, `c` is the modular character and `1/∞ = 0`, as a group
homomorphism to linear isometry equivalences. It is the conjugate `J L_g J` of left translation
by the modular inversion `J`. -/
def rightTranslation : G →* (Lp E p μ ≃ₗᵢ[𝕜] Lp E p μ) :=
  (MulAut.conj (modularInversion μ p 𝕜)).toMonoidHom.comp (leftTranslation μ p 𝕜)

variable {μ p 𝕜}

/-- Right translation is left translation conjugated by the modular inversion. -/
theorem rightTranslation_apply (g : G) (f : Lp E p μ) :
    rightTranslation μ p 𝕜 g f =
      modularInversion μ p 𝕜 (leftTranslation μ p 𝕜 g (modularInversion μ p 𝕜 f)) := by
  simp [rightTranslation, MulAut.conj_apply]

/-- The right translate `R_g f` is almost everywhere the function
`x ↦ c(g⁻¹)^(1/p) • f (x * g)`. -/
theorem coeFn_rightTranslation (g : G) (f : Lp E p μ) :
    rightTranslation μ p 𝕜 g f =ᵐ[μ]
      fun x => (modularCharacter g⁻¹ : ℝ) ^ p.toReal⁻¹ • f (x * g) := by
  have hinv := quasiMeasurePreserving_inv_of_regular μ
  have hmul := (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.comp hinv
  filter_upwards [coeFn_modularInversion (𝕜 := 𝕜)
      (leftTranslation μ p 𝕜 g (modularInversion μ p 𝕜 f)),
    hinv.ae (coeFn_leftTranslation (𝕜 := 𝕜) g (modularInversion μ p 𝕜 f)),
    hmul.ae (coeFn_modularInversion (𝕜 := 𝕜) f)] with x h h' h''
  simp only [Function.comp_apply] at h''
  rw [rightTranslation_apply, h, h', h'', smul_smul, mul_inv_rev, inv_inv, inv_inv]
  -- The weights combine to `c(x)^(1/p) * c(g⁻¹)^(1/p) * c(x⁻¹)^(1/p) = c(g⁻¹)^(1/p)`.
  congr 1
  rw [map_mul, NNReal.coe_mul, Real.mul_rpow (by positivity) (by positivity), mul_left_comm,
    modularCharacter_rpow_mul_inv, mul_one]

/-- The inverse of right translation by `g` is right translation by `g⁻¹`. -/
@[simp]
theorem rightTranslation_symm (g : G) :
    (rightTranslation μ p 𝕜 g).symm = rightTranslation μ p 𝕜 (E := E) g⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- Left and right translations commute. -/
theorem leftTranslation_rightTranslation (g h : G) (f : Lp E p μ) :
    leftTranslation μ p 𝕜 h (rightTranslation μ p 𝕜 g f) =
      rightTranslation μ p 𝕜 g (leftTranslation μ p 𝕜 h f) :=
  Lp.ext <| by
    filter_upwards [coeFn_leftTranslation (𝕜 := 𝕜) h (rightTranslation μ p 𝕜 g f),
      (measurePreserving_mul_left μ h⁻¹).quasiMeasurePreserving.ae
        (coeFn_rightTranslation (𝕜 := 𝕜) g f),
      coeFn_rightTranslation (𝕜 := 𝕜) g (leftTranslation μ p 𝕜 h f),
      (quasiMeasurePreserving_mul_right_of_regular μ g).ae
        (coeFn_leftTranslation (𝕜 := 𝕜) h f)] with x h₁ h₂ h₃ h₄
    rw [h₁, h₂, h₃, h₄, mul_assoc]

/-- Right translation is monotone on real `Lᵖ`. -/
theorem rightTranslation_mono (g : G) {f f' : Lp ℝ p μ} (h : f ≤ f') :
    rightTranslation μ p ℝ g f ≤ rightTranslation μ p ℝ g f' := by
  rw [← coeFn_le] at h ⊢
  filter_upwards [coeFn_rightTranslation (𝕜 := ℝ) g f, coeFn_rightTranslation (𝕜 := ℝ) g f',
    (quasiMeasurePreserving_mul_right_of_regular μ g).ae h] with x hx hx' hle
  rw [hx, hx']
  exact smul_le_smul_of_nonneg_left hle (by positivity)

/-- Right translation is an order automorphism of real `Lᵖ`. -/
@[simp]
theorem rightTranslation_le_rightTranslation_iff {g : G} {f f' : Lp ℝ p μ} :
    rightTranslation μ p ℝ g f ≤ rightTranslation μ p ℝ g f' ↔ f ≤ f' := by
  refine ⟨fun h => ?_, rightTranslation_mono g⟩
  simpa [← rightTranslation_symm] using rightTranslation_mono (μ := μ) g⁻¹ h

/-- Right translation on `L¹` preserves the integral: the weight `c(g⁻¹)` of
`(R_g f)(x) = c(g⁻¹) • f (x * g)` compensates the factor `c(g)` by which right translation scales
the integral. -/
@[simp]
theorem integral_rightTranslation (g : G) (f : Lp E 1 μ) :
    ∫ x, rightTranslation μ 1 𝕜 g f x ∂μ = ∫ x, f x ∂μ := by
  have hc : (modularCharacter g : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 (modularCharacterFun_pos g).ne'
  rw [integral_congr_ae (coeFn_rightTranslation g f)]
  simp [integral_smul, integral_mul_right_eq_modularCharacter_smul_of_regular, smul_smul, hc]

/-- **Right translation is strongly continuous** on `Lᵖ` for `p < ∞`: every orbit map
`g ↦ R_g f` is continuous. -/
theorem continuous_rightTranslation_apply (hp : p ≠ ∞) (f : Lp E p μ) :
    Continuous fun g : G => rightTranslation μ p 𝕜 g f := by
  have : Fact (p ≠ ∞) := ⟨hp⟩
  simp only [rightTranslation_apply, leftTranslation_apply]
  exact (modularInversion μ p 𝕜).continuous.comp
    ((DomMulAct.continuous_mk.comp continuous_inv).smul continuous_const)

end Lp

omit [NormedSpace ℝ E] in
/-- The unweighted right translate `f (· * g)` has `Lᵖ` seminorm `c(g)^(1/p) ‖f‖_p`, where `c` is
the modular character, for every function and every exponent. -/
@[simp]
theorem eLpNorm_comp_mul_right_of_regular (f : G → E) (g : G) (p : ℝ≥0∞) :
    eLpNorm (fun x => f (x * g)) p μ =
      (modularCharacter g ^ p.toReal⁻¹ : ℝ≥0) * eLpNorm f p μ := by
  have h := (MeasurableEquiv.mulRight g).measurableEmbedding.eLpNorm_map_measure (g := f) (μ := μ)
    (p := p)
  have hc : modularCharacter g ≠ 0 := (modularCharacterFun_pos g).ne'
  rw [MeasurableEquiv.coe_mulRight, map_right_mul_eq_modularCharacter_smul_of_regular,
    eLpNorm_smul_measure_of_ne_zero' hc] at h
  exact h.symm

omit [NormedSpace ℝ E] in
/-- The unweighted right translate of an `Lᵖ` function is in `Lᵖ`. -/
theorem MemLp.comp_mul_right_of_regular {f : G → E} (hf : MemLp f p μ) (g : G) :
    MemLp (fun x => f (x * g)) p μ :=
  memLp_iff.2 <| (eLpNorm_comp_mul_right_of_regular f g p).trans_lt <|
    ENNReal.mul_lt_top ENNReal.coe_lt_top hf

omit [NormedSpace ℝ E] in
/-- A function is in `Lᵖ` exactly when its unweighted right translate is. -/
theorem memLp_comp_mul_right_iff_of_regular {f : G → E} (g : G) :
    MemLp (fun x => f (x * g)) p μ ↔ MemLp f p μ :=
  ⟨fun h => by simpa [mul_assoc] using h.comp_mul_right_of_regular g⁻¹,
    fun h => h.comp_mul_right_of_regular g⟩

open Topology in
/-- The unweighted right translates of an `Lᵖ` function converge to it in `Lᵖ` for
`1 ≤ p < ∞`: `‖f (· * g) - f‖_p → 0` as `g → 1`. This is the counterpart for a regular left
Haar measure of `MeasureTheory.MemLp.tendsto_eLpNorm_comp_add_sub` in
`TauCeti/MeasureTheory/Function/Lp/Translation.lean`. -/
theorem MemLp.tendsto_eLpNorm_comp_mul_right_sub_of_regular {f : G → E} (hf : MemLp f p μ)
    (hp₁ : 1 ≤ p) (hp : p ≠ ∞) :
    Tendsto (fun g => eLpNorm (fun x => f (x * g) - f x) p μ) (𝓝 1) (𝓝 0) := by
  have := Fact.mk hp₁
  -- `f (· * g) = c(g)^(1/p) • R_g f`, and both factors tend to their values at `g = 1`.
  set F := hf.toLp f
  set a : G → ℝ := fun g => (modularCharacter g : ℝ) ^ p.toReal⁻¹
  have ha : Continuous a := (NNReal.continuous_coe.comp continuous_modularCharacter).rpow_const
    fun _ => Or.inr (inv_nonneg.2 ENNReal.toReal_nonneg)
  have h : Tendsto (fun g => a g • Lp.rightTranslation μ p ℝ g F - F) (𝓝 1) (𝓝 0) := by
    simpa [a] using ((ha.tendsto 1).smul
      ((Lp.continuous_rightTranslation_apply hp F).tendsto 1)).sub_const F
  refine (enorm_zero (E := Lp E p μ) ▸ (continuous_enorm.tendsto 0).comp h).congr' <|
    Eventually.of_forall fun g => ?_
  rw [Function.comp_apply, Lp.enorm_def]
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (a g • Lp.rightTranslation μ p ℝ g F) F,
    Lp.coeFn_smul (a g) (Lp.rightTranslation μ p ℝ g F),
    Lp.coeFn_rightTranslation (𝕜 := ℝ) g F, hf.coeFn_toLp,
    (quasiMeasurePreserving_mul_right_of_regular μ g).ae hf.coeFn_toLp] with x h₁ h₂ h₃ h₄ h₅
  rw [h₁, Pi.sub_apply, h₂, Pi.smul_apply, h₃, smul_smul, modularCharacter_rpow_mul_inv,
    one_smul, h₄, h₅]

end MeasureTheory

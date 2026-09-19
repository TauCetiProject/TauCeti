/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.CompleteBernstein

/-!
# Inversion of the parameter of Stieltjes and complete Bernstein functions

The substitution `t ↦ t⁻¹` exchanges the two ends of `(0, ∞)`, and the Stieltjes class is
stable under the normalized substitution `f ↦ (t ↦ f(t⁻¹) / t)`.  On representing data it acts by
exchanging the singular coefficient `a` of `a / t` with the constant coefficient `b`, and by the
measure transformation

`μ ↦ ν`, the image of `x⁻¹ μ(dx)` under `x ↦ x⁻¹`,

because for `x > 0` the kernels satisfy `(t⁻¹ + x)⁻¹ / t = x⁻¹ (t + x⁻¹)⁻¹`.  This measure
transformation, `MeasureTheory.Measure.stieltjesInversion`, preserves the Stieltjes weight
condition, never charges `0`, and is an involution on measures without an atom at `0`.
Consequently the substitution is an involution of the Stieltjes class.

Combined with the correspondence `f ↦ t f(t)` between Stieltjes and complete Bernstein functions,
this yields two further standard dualities: `f` is Stieltjes exactly when `t ↦ f(t⁻¹)` on
`(0, ∞)` extends to a complete Bernstein function, and a complete Bernstein function `f` has the
complete Bernstein dual `t ↦ t f(t⁻¹)`.  The value at `0` of these extensions is the constant
coefficient `b = lim_{t → ∞} f(t)` of the original Stieltjes function, which is why they are stated
as extensions of functions given on `(0, ∞)`.

## Main declarations

* `MeasureTheory.Measure.stieltjesInversion`: the measure transformation `μ ↦ (x⁻¹ • μ).inv`.
* `MeasureTheory.Measure.integral_stieltjesInversion`,
  `MeasureTheory.Measure.lintegral_stieltjesInversion` and
  `MeasureTheory.Measure.integrable_stieltjesInversion_iff`: integration against the transformed
  measure.
* `MeasureTheory.Measure.stieltjesInversion_singleton_zero` and
  `MeasureTheory.Measure.integrable_weight_stieltjesInversion_iff`: the transform never charges
  `0` and preserves the Stieltjes weight condition.
* `MeasureTheory.Measure.stieltjesInversion_stieltjesInversion`: the transformation is an
  involution on measures without an atom at `0`.
* `TauCeti.RepresentsStieltjes.comp_inv_div` and `TauCeti.representsStieltjes_comp_inv_div_iff`:
  the effect of the substitution on representing data.
* `TauCeti.IsStieltjesFunction.comp_inv_div` and `TauCeti.isStieltjesFunction_comp_inv_div_iff`:
  the Stieltjes class is invariant under the substitution.
* `TauCeti.isStieltjesFunction_iff_exists_isCompleteBernsteinFunction_eqOn_comp_inv`: `f` is
  Stieltjes exactly when `t ↦ f(t⁻¹)` has a complete Bernstein extension.
* `TauCeti.IsCompleteBernsteinFunction.exists_isCompleteBernsteinFunction_eqOn_mul_comp_inv`:
  the dual `t ↦ t f(t⁻¹)` of a complete Bernstein function is complete Bernstein.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  de Gruyter, 2nd ed. (2012), Chapter 7.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

/-- The measure transformation dual to the substitution `t ↦ t⁻¹` in a Stieltjes
representation: the image of the measure `x⁻¹ μ(dx)` under `x ↦ x⁻¹`.  The density `x⁻¹` is
taken in `ℝ≥0`, so it vanishes at `x = 0` and the transformed measure never charges `0`. -/
def stieltjesInversion (μ : Measure ℝ≥0) : Measure ℝ≥0 :=
  (μ.withDensity fun x => ((x⁻¹ : ℝ≥0) : ℝ≥0∞)).inv

variable {μ : Measure ℝ≥0}

/-- Integration against `stieltjesInversion μ` in terms of `μ`. -/
theorem integral_stieltjesInversion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ≥0 → E) :
    ∫ y, g y ∂stieltjesInversion μ = ∫ x, ((x : ℝ)⁻¹) • g x⁻¹ ∂μ := by
  rw [stieltjesInversion, Measure.inv, measurableEmbedding_inv.integral_map,
    integral_withDensity_eq_integral_smul (by fun_prop)]
  simp [NNReal.smul_def]

/-- Lower Lebesgue integration against `stieltjesInversion μ` in terms of `μ`. -/
theorem lintegral_stieltjesInversion (g : ℝ≥0 → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂stieltjesInversion μ = ∫⁻ x, ((x⁻¹ : ℝ≥0) : ℝ≥0∞) * g x⁻¹ ∂μ := by
  rw [stieltjesInversion, Measure.inv, measurableEmbedding_inv.lintegral_map,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply]

/-- Integrability against `stieltjesInversion μ` in terms of `μ`. -/
theorem integrable_stieltjesInversion_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ≥0 → E} :
    Integrable g (stieltjesInversion μ) ↔
      Integrable (fun x : ℝ≥0 => ((x : ℝ)⁻¹) • g x⁻¹) μ := by
  rw [stieltjesInversion, Measure.inv, measurableEmbedding_inv.integrable_map_iff,
    integrable_withDensity_iff_integrable_smul (by fun_prop)]
  simp [NNReal.smul_def]

/-- The transformed measure never charges `0`, because its density vanishes there. -/
@[simp]
theorem stieltjesInversion_singleton_zero : stieltjesInversion μ {0} = 0 := by
  rw [stieltjesInversion, Measure.inv_apply, Set.inv_singleton, inv_zero,
    withDensity_apply _ (measurableSet_singleton 0)]
  simp

/-- Applying `stieltjesInversion` twice removes exactly the atom at `0`. -/
theorem stieltjesInversion_stieltjesInversion_eq_restrict :
    stieltjesInversion (stieltjesInversion μ) = μ.restrict {0}ᶜ := by
  refine (Measure.ext_of_lintegral (μ.restrict {0}ᶜ) fun g hg => ?_)
  rw [lintegral_stieltjesInversion g hg, lintegral_stieltjesInversion _ (by fun_prop)]
  rw [← lintegral_indicator (measurableSet_singleton 0).compl]
  refine lintegral_congr fun x => ?_
  by_cases hx : x = 0
  · subst x
    simp
  rw [indicator_of_mem (by simp [hx])]
  simp only [inv_inv]
  rw [← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hx, ENNReal.coe_one, one_mul]

/-- `stieltjesInversion` is an involution on measures without an atom at `0`. -/
@[simp]
theorem stieltjesInversion_stieltjesInversion (hμ : μ {0} = 0) :
    stieltjesInversion (stieltjesInversion μ) = μ := by
  rw [stieltjesInversion_stieltjesInversion_eq_restrict,
    Measure.restrict_eq_self_of_ae_mem]
  simpa only [mem_compl_iff] using measure_eq_zero_iff_ae_notMem.mp hμ

/-- The transformed measure satisfies the Stieltjes weight condition exactly when the original
measure does, provided the latter has no atom at `0`.  Indeed `x⁻¹ (1 + x⁻¹)⁻¹ = (1 + x)⁻¹`
for `x > 0`. -/
theorem integrable_weight_stieltjesInversion_iff (hμ : μ {0} = 0) :
    Integrable TauCeti.stieltjesWeight (stieltjesInversion μ) ↔
      Integrable TauCeti.stieltjesWeight μ := by
  rw [integrable_stieltjesInversion_iff]
  refine integrable_congr ((measure_eq_zero_iff_ae_notMem.mp hμ).mono fun x hx => ?_)
  have hx' : (x : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr (notMem_singleton_iff.mp hx)
  simp only [TauCeti.stieltjesWeight_apply, NNReal.coe_inv, smul_eq_mul]
  have : (1 + (x : ℝ)) ≠ 0 := by positivity
  field_simp
  ring

end MeasureTheory.Measure

namespace TauCeti

namespace RepresentsStieltjes

variable {a b : ℝ≥0} {f : ℝ → ℝ}

/-- **Inversion of a Stieltjes representation.**  If `(μ, a, b)` represents `f`, then
`t ↦ f(t⁻¹) / t` is represented by `(stieltjesInversion μ, b, a)`: the singular and constant
coefficients are exchanged. -/
theorem comp_inv_div (h : RepresentsStieltjes μ a b f) :
    RepresentsStieltjes μ.stieltjesInversion b a (fun t => f t⁻¹ / t) := by
  refine representsStieltjes_iff.mpr ⟨Measure.stieltjesInversion_singleton_zero,
    (Measure.integrable_weight_stieltjesInversion_iff h.measure_singleton_zero).mpr
      h.integrable_weight,
    fun t ht => ?_⟩
  rw [h.eq_div_add_add_integral_inv_add (inv_pos.mpr ht), Measure.integral_stieltjesInversion,
    add_div, add_div, ← integral_div]
  have hint : ∫ x : ℝ≥0, (t⁻¹ + (x : ℝ))⁻¹ / t ∂μ =
      ∫ x : ℝ≥0, ((x : ℝ)⁻¹) • (t + ((x⁻¹ : ℝ≥0) : ℝ))⁻¹ ∂μ := by
    refine integral_congr_ae
      ((measure_eq_zero_iff_ae_notMem.mp h.measure_singleton_zero).mono fun x hx => ?_)
    have hx' : 0 < (x : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (notMem_singleton_iff.mp hx))
    simp only [NNReal.coe_inv, smul_eq_mul]
    field_simp
    ring
  rw [hint]
  field_simp
  ring

end RepresentsStieltjes

/-- The substitution `f ↦ (t ↦ f(t⁻¹) / t)` is reversible on representing data: `(ν, b, a)`
represents `t ↦ f(t⁻¹) / t` exactly when `(stieltjesInversion ν, a, b)` represents `f`, for any
`ν` without an atom at `0`. -/
theorem representsStieltjes_comp_inv_div_iff {ν : Measure ℝ≥0} {a b : ℝ≥0} {f : ℝ → ℝ}
    (hν : ν {0} = 0) :
    RepresentsStieltjes ν b a (fun t => f t⁻¹ / t) ↔
      RepresentsStieltjes ν.stieltjesInversion a b f := by
  constructor
  · intro h
    refine h.comp_inv_div.congr fun t ht => ?_
    have ht' : t ≠ 0 := (mem_Ioi.mp ht).ne'
    simp [ht']
  · intro h
    simpa [Measure.stieltjesInversion_stieltjesInversion hν] using h.comp_inv_div

namespace IsStieltjesFunction

variable {f : ℝ → ℝ}

/-- If `f` is a Stieltjes function, then so is `t ↦ f(t⁻¹) / t`. -/
theorem comp_inv_div (hf : IsStieltjesFunction f) : IsStieltjesFunction (fun t => f t⁻¹ / t) := by
  obtain ⟨a, b, μ, hμ⟩ := isStieltjesFunction_iff.mp hf
  exact isStieltjesFunction_iff.mpr ⟨b, a, μ.stieltjesInversion, hμ.comp_inv_div⟩

end IsStieltjesFunction

/-- The Stieltjes class is invariant under the involution `f ↦ (t ↦ f(t⁻¹) / t)`. -/
theorem isStieltjesFunction_comp_inv_div_iff {f : ℝ → ℝ} :
    IsStieltjesFunction (fun t => f t⁻¹ / t) ↔ IsStieltjesFunction f := by
  refine ⟨fun h => h.comp_inv_div.congr fun t ht => ?_, IsStieltjesFunction.comp_inv_div⟩
  have ht' : t ≠ 0 := (mem_Ioi.mp ht).ne'
  simp [ht']

/-- **Stieltjes functions and complete Bernstein functions under inversion.**  A function `f` is
Stieltjes exactly when `t ↦ f(t⁻¹)` on `(0, ∞)` extends to a complete Bernstein function on
`[0, ∞)`.  The extension's value at `0` is the constant coefficient of the Stieltjes
representation of `f`. -/
theorem isStieltjesFunction_iff_exists_isCompleteBernsteinFunction_eqOn_comp_inv
    {f : ℝ → ℝ} :
    IsStieltjesFunction f ↔
      ∃ g : ℝ → ℝ, IsCompleteBernsteinFunction g ∧ EqOn g (fun t => f t⁻¹) (Ioi 0) := by
  rw [← isStieltjesFunction_comp_inv_div_iff,
    isStieltjesFunction_iff_exists_isCompleteBernsteinFunction_eqOn_mul]
  refine exists_congr fun g => and_congr_right fun _ => ?_
  refine ⟨fun h t ht => ?_, fun h t ht => ?_⟩ <;>
  · have ht' : t ≠ 0 := (mem_Ioi.mp ht).ne'
    simp [h ht, ht', mul_div_cancel₀]

/-- **Duality of complete Bernstein functions.**  If `f` is a complete Bernstein function, then
`t ↦ t f(t⁻¹)` on `(0, ∞)` extends to a complete Bernstein function on `[0, ∞)`. -/
theorem IsCompleteBernsteinFunction.exists_isCompleteBernsteinFunction_eqOn_mul_comp_inv
    {f : ℝ → ℝ} (hf : IsCompleteBernsteinFunction f) :
    ∃ g : ℝ → ℝ, IsCompleteBernsteinFunction g ∧ EqOn g (fun t => t * f t⁻¹) (Ioi 0) := by
  obtain ⟨g, hg, hgf⟩ :=
    isStieltjesFunction_iff_exists_isCompleteBernsteinFunction_eqOn_comp_inv.mp
      hf.isStieltjesFunction_div
  refine ⟨g, hg, fun t ht => ?_⟩
  simp [hgf ht, div_inv_eq_mul, mul_comm]

end TauCeti

end

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Integral
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Variation
public import TauCeti.MeasureTheory.VectorMeasure.WithDensity
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Matrix elements of the integral against a projection-valued measure

Let `P` be a projection-valued measure on `X` acting on a complex Hilbert space `H`. For vectors
`ψ ξ : H`, the polarized complex measure `μ_(ψ,ξ) = P.polarizedComplexMeasure ψ ξ` takes the value
`⟪ψ, P(B) ξ⟫` on a measurable set `B`, and has finite variation. This file identifies the matrix
elements of the operator integral `P.integral f = ∫ f dP` of a bounded Borel symbol `f` with
Mathlib's integral against this complex measure, through the multiplication pairing `ℂ × ℂ → ℂ`:

`⟪ψ, (∫ f dP) ξ⟫ = ∫ᵛ x, f x ∂[mul ℝ ℂ; μ_(ψ,ξ)]`.

So the operator integral is determined by scalar integration against the polarized measures, and
the scalar integration theory of complex measures applies to its matrix elements.

On the diagonal, the variation of the polarized measure `μ_(ξ,ξ)` is the finite positive measure
`P.diag ξ` (`variation_polarizedComplexMeasure_self`), and integrating any complex function
against `μ_(ξ,ξ)` gives the Bochner integral against `P.diag ξ`.

## Main declarations

* `ProjValMeasure.integral_polarizedComplexMeasure_eq_inner_integral`: the matrix element
  `⟪ψ, (∫ f dP) ξ⟫` is the integral of `f` against `μ_(ψ,ξ)`.
* `ProjValMeasure.integral_polarizedComplexMeasure_self`: integration of any `f : X → ℂ` against
  `μ_(ξ,ξ)` is the Bochner integral against `P.diag ξ`.
* `ProjValMeasure.polarizedComplexMeasure_integral_right` and
  `ProjValMeasure.polarizedComplexMeasure_integral_left`: applying `∫ g dP` to either vector
  weights `μ_(ψ,ξ)` by `g` or `star g`.
* `ProjValMeasure.lintegral_enorm_variation_polarizedComplexMeasure_le`,
  `ProjValMeasure.lintegral_enorm_variation_polarizedComplexMeasure_le_eLpNorm`,
  `ProjValMeasure.integrable_polarizedComplexMeasure_of_memLp`,
  `ProjValMeasure.integrable_polarizedComplexMeasure_of_memLp_left`,
  `ProjValMeasure.integral_norm_variation_polarizedComplexMeasure_le`,
  `ProjValMeasure.integral_norm_variation_polarizedComplexMeasure_le_left`,
  `ProjValMeasure.eNorm_integral_polarizedComplexMeasure_le`, and
  `ProjValMeasure.norm_integral_polarizedComplexMeasure_le`: Cauchy–Schwarz estimates and
  `L²`-to-`L¹(|μ_(ψ,ξ)|)` integrability for polarized spectral measures.
* `ProjValMeasure.integral_polarizedComplexMeasure_star`: conjugate symmetry of polarized
  integrals.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill, 1991, Theorem 12.21.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Section 4.2.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace TauCeti
namespace ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The matrix element of the integral of a simple symbol is its integral against the polarized
measure. -/
private theorem integral_polarizedComplexMeasure_ofSimpleFunc (P : ProjValMeasure X H)
    (s : SimpleFunc X ℂ) (ψ ξ : H) :
    ∫ᵛ x, s x ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ] =
      ⟪ψ, P.integral (BoundedBorelFunction.ofSimpleFunc s) ξ⟫_ℂ := by
  induction s using SimpleFunc.induction with
  | @const c B hB =>
    have hs : ⇑(SimpleFunc.piecewise B hB (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
        B.indicator fun _ => c := by
      ext x
      by_cases hx : x ∈ B <;> simp [SimpleFunc.piecewise_apply, hx]
    have h : BoundedBorelFunction.ofSimpleFunc
        (SimpleFunc.piecewise B hB (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
          c • BoundedBorelFunction.indicator B hB 1 := by
      ext x
      by_cases hx : x ∈ B <;> simp [hx]
    rw [hs, VectorMeasure.integral_indicator_const _ hB, h]
    simp [integral_indicator, inner_smul_right, polarizedComplexMeasure_apply _ _ _ _ hB]
  | @add s t _ hs ht =>
    rw [FunLike.coe_add, VectorMeasure.integral_add (SimpleFunc.integrable_of_isFiniteMeasure s)
      (SimpleFunc.integrable_of_isFiniteMeasure t), hs, ht]
    simp [inner_add_right]

/-- **Matrix elements of the integral against a projection-valued measure.** For a bounded Borel
symbol `f`, `⟪ψ, (∫ f dP) ξ⟫` is the integral of `f` against the polarized complex measure
`μ_(ψ,ξ)`, whose value on a measurable set `B` is `⟪ψ, P(B) ξ⟫`, through the multiplication
pairing. -/
theorem integral_polarizedComplexMeasure_eq_inner_integral (P : ProjValMeasure X H)
    (f : BoundedBorelFunction X) (ψ ξ : H) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ] =
      ⟪ψ, P.integral f ξ⟫_ℂ := by
  obtain ⟨s, hs_le, hs⟩ := BoundedBorelFunction.exists_seq_tendsto_ofSimpleFunc f
  have hcont : Continuous fun g => ⟪ψ, P.integral g ξ⟫_ℂ :=
    continuous_const.inner ((ContinuousLinearMap.apply ℂ H ξ).continuous.comp
      P.continuous_integral)
  refine tendsto_nhds_unique (l := atTop)
    (f := fun n => ∫ᵛ x, s n x ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ])
    ?_ (((hcont.tendsto f).comp hs).congr fun n => ?_)
  · -- Dominated convergence, with the constant bound `‖f‖` and pointwise convergence.
    refine VectorMeasure.tendsto_integral_filter_of_norm_le_const
      (Eventually.of_forall fun n => (s n).aestronglyMeasurable)
      ⟨‖f‖, Eventually.of_forall fun n => Eventually.of_forall (hs_le n)⟩
      (Eventually.of_forall fun x => ?_)
    rw [BoundedBorelFunction.tendsto_iff_tendstoUniformly] at hs
    simpa using hs.tendsto_at x
  · exact (P.integral_polarizedComplexMeasure_ofSimpleFunc (s n) ψ ξ).symm

/-- Integration of a complex function against the diagonal polarized measure through the
multiplication pairing is the Bochner integral against the diagonal measure. Both sides vanish
when `f` is not integrable, since the variation of the polarized measure is the diagonal
measure. -/
@[simp]
theorem integral_polarizedComplexMeasure_self (P : ProjValMeasure X H) (f : X → ℂ) (ξ : H) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ξ ξ] =
      ∫ x, f x ∂(P.diag ξ) := by
  rw [polarizedComplexMeasure_self_eq_withDensityᵥ, VectorMeasure.integral_mul_withDensityᵥ_one]

/-- Applying `∫ g dP` in the linear argument weights the polarized complex measure by `g`. -/
theorem polarizedComplexMeasure_integral_right (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) (ψ ξ : H) :
    P.polarizedComplexMeasure ψ (P.integral g ξ) =
      (P.polarizedComplexMeasure ψ ξ).withDensity g (ContinuousLinearMap.mul ℝ ℂ) := by
  ext B hB
  rw [P.polarizedComplexMeasure_apply ψ (P.integral g ξ) B hB, P.proj_integral_apply hB g ξ,
    ← P.integral_polarizedComplexMeasure_eq_inner_integral,
    BoundedBorelFunction.coe_indicator, VectorMeasure.integral_indicator hB,
    VectorMeasure.withDensity_apply (g.integrable _)]

/-- Applying `∫ g dP` in the conjugate-linear argument weights the polarized complex measure by
`star g`. -/
theorem polarizedComplexMeasure_integral_left (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) (ψ ξ : H) :
    P.polarizedComplexMeasure (P.integral g ψ) ξ =
      (P.polarizedComplexMeasure ψ ξ).withDensity (star g) (ContinuousLinearMap.mul ℝ ℂ) := by
  have heq : P.polarizedComplexMeasure (P.integral g ψ) ξ =
      P.polarizedComplexMeasure ψ (P.integral (star g) ξ) := by
    ext B hB
    rw [P.polarizedComplexMeasure_apply _ _ B hB, P.polarizedComplexMeasure_apply _ _ B hB,
      ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star, P.integral_proj_apply (star g) hB ξ, P.proj_integral_apply hB (star g) ξ]
  rw [heq, P.polarizedComplexMeasure_integral_right (star g) ψ ξ, BoundedBorelFunction.coe_star]

/-- For a bounded Borel symbol `g`, the lower Lebesgue integral of `‖g‖ₑ` against the variation of
`μ_(ψ,ξ)` is bounded by `‖ψ‖ * ‖(∫ g dP) ξ‖`. -/
theorem lintegral_enorm_variation_polarizedComplexMeasure_le (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) (ψ ξ : H) :
    ∫⁻ t, ‖g t‖ₑ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ENNReal.ofReal (‖ψ‖ * ‖P.integral g ξ‖) := by
  refine (P.lintegral_variation_polarizedComplexMeasure_le ψ ξ fun t => ‖g t‖ₑ).trans_eq ?_
  have hsq : ∫⁻ t, ‖g t‖ₑ ^ 2 ∂(P.diag ξ) = ‖P.integral g ξ‖ₑ ^ 2 := by
    rw [← P.diag_univ, P.diag_integral, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ]
  rw [hsq, ← ENNReal.rpow_two, one_div, ENNReal.rpow_rpow_inv two_ne_zero,
    ← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_mul (norm_nonneg _)]

/-- For any function `f : X → E` that is almost everywhere strongly measurable for `P.diag ξ`,
the lower Lebesgue integral of `‖f‖ₑ` against the variation of `P.polarizedComplexMeasure ψ ξ` is
bounded by `‖ψ‖ₑ * eLpNorm f 2 (P.diag ξ)`. -/
theorem lintegral_enorm_variation_polarizedComplexMeasure_le_eLpNorm {E : Type*}
    [NormedAddCommGroup E] (P : ProjValMeasure X H) {f : X → E} {ξ : H}
    (hf : AEStronglyMeasurable f (P.diag ξ)) (ψ : H) :
    ∫⁻ t, ‖f t‖ₑ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ₑ * eLpNorm f 2 (P.diag ξ) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hf]
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    P.lintegral_variation_polarizedComplexMeasure_le ψ ξ fun t => ‖f t‖ₑ

/-- Every function in `L²(P.diag ξ)` is integrable against `P.polarizedComplexMeasure ψ ξ`. -/
theorem integrable_polarizedComplexMeasure_of_memLp {E : Type*} [NormedAddCommGroup E]
    (P : ProjValMeasure X H) {f : X → E} {ξ : H} (hf : MemLp f 2 (P.diag ξ)) (ψ : H) :
    (P.polarizedComplexMeasure ψ ξ).Integrable f :=
  ⟨hf.aestronglyMeasurable.mono_ac
      (P.variation_polarizedComplexMeasure_absolutelyContinuous_diag ψ ξ),
    (P.lintegral_enorm_variation_polarizedComplexMeasure_le_eLpNorm
      hf.aestronglyMeasurable ψ).trans_lt (ENNReal.mul_lt_top eNorm_lt_top hf.eLpNorm_lt_top)⟩

/-- Every function in `L²(P.diag ψ)` is integrable against `P.polarizedComplexMeasure ψ ξ`. -/
theorem integrable_polarizedComplexMeasure_of_memLp_left {E : Type*} [NormedAddCommGroup E]
    (P : ProjValMeasure X H) {f : X → E} {ψ : H} (hf : MemLp f 2 (P.diag ψ)) (ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).Integrable f := by
  rw [VectorMeasure.Integrable, P.variation_polarizedComplexMeasure_comm ψ ξ]
  exact P.integrable_polarizedComplexMeasure_of_memLp hf ξ

/-- **Cauchy–Schwarz variation estimate** for the polarized spectral measure: for `f ∈ L²(P.diag ξ)`
and any `ψ : H`, `∫ t, ‖f t‖ ∂|μ_(ψ,ξ)| ≤ ‖ψ‖ * √(∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ))`. -/
theorem integral_norm_variation_polarizedComplexMeasure_le {E : Type*} [NormedAddCommGroup E]
    (P : ProjValMeasure X H) {f : X → E} {ξ : H} (hf : MemLp f 2 (P.diag ξ)) (ψ : H) :
    ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ)) := by
  have hac := P.variation_polarizedComplexMeasure_absolutelyContinuous_diag ψ ξ
  rw [integral_norm_eq_lintegral_eNorm (hf.aestronglyMeasurable.mono_ac hac)]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [ENNReal.ofReal_mul (norm_nonneg ψ), ofReal_norm, ← hf.eLpNorm_two_eq_ofReal_sqrt_integral]
  exact P.lintegral_enorm_variation_polarizedComplexMeasure_le_eLpNorm hf.aestronglyMeasurable ψ

/-- **Left-slot Cauchy–Schwarz variation estimate** for the polarized spectral measure: for
`f ∈ L²(P.diag ψ)` and any `ξ : H`,
`∫ t, ‖f t‖ ∂|μ_(ψ,ξ)| ≤ ‖ξ‖ * √(∫ t, ‖f t‖ ^ 2 ∂(P.diag ψ))`. -/
theorem integral_norm_variation_polarizedComplexMeasure_le_left {E : Type*} [NormedAddCommGroup E]
    (P : ProjValMeasure X H) {f : X → E} {ψ : H} (hf : MemLp f 2 (P.diag ψ)) (ξ : H) :
    ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ξ‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag ψ)) := by
  rw [P.variation_polarizedComplexMeasure_comm ψ ξ]
  exact P.integral_norm_variation_polarizedComplexMeasure_le hf ξ

/-- Extended-norm Cauchy–Schwarz bound for integration against a polarized spectral measure.
No measurability or integrability hypothesis is needed. -/
theorem eNorm_integral_polarizedComplexMeasure_le (P : ProjValMeasure X H) (f : X → ℂ)
    (ψ ξ : H) :
    ‖∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ]‖ₑ ≤
      ‖ψ‖ₑ * (∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) := by
  refine VectorMeasure.eNorm_integral_le_lintegral_eNorm.trans ?_
  rw [eNorm_eq_nnNorm, ContinuousLinearMap.opNNNorm_mul, ENNReal.coe_one, one_mul]
  exact P.lintegral_variation_polarizedComplexMeasure_le ψ ξ fun t => ‖f t‖ₑ

/-- Norm Cauchy–Schwarz bound for integration against a polarized spectral measure. -/
theorem norm_integral_polarizedComplexMeasure_le (P : ProjValMeasure X H) {f : X → ℂ} {ξ : H}
    (hf : MemLp f 2 (P.diag ξ)) (ψ : H) :
    ‖∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ]‖ ≤
      ‖ψ‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ)) := by
  refine VectorMeasure.norm_integral_le_integral_norm.trans ?_
  calc ‖ContinuousLinearMap.mul ℝ ℂ‖ * ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure ψ ξ).variation
      ≤ 1 * ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure ψ ξ).variation := by
        gcongr
        exact ContinuousLinearMap.opNorm_mul_le ℝ ℂ
    _ = ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure ψ ξ).variation := one_mul _
    _ ≤ ‖ψ‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ)) :=
        P.integral_norm_variation_polarizedComplexMeasure_le hf ψ

/-- **Conjugate symmetry of polarized integrals.** Integrating `star f` against `μ_(ξ,ψ)` is the
conjugate of integrating `f` against `μ_(ψ,ξ)`, with no integrability hypothesis on `f`. -/
@[simp]
theorem integral_polarizedComplexMeasure_star (P : ProjValMeasure X H) (f : X → ℂ) (ψ ξ : H) :
    ∫ᵛ t, starRingEnd ℂ (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ξ ψ] =
      starRingEnd ℂ (∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ]) := by
  have hmap : P.polarizedComplexMeasure ξ ψ =
      VectorMeasure.mapRangeL (Complex.conjCLE : ℂ →L[ℝ] ℂ)
        (P.polarizedComplexMeasure ψ ξ) :=
    (P.mapRangeL_conjCLE_polarizedComplexMeasure ψ ξ).symm
  by_cases hf : (P.polarizedComplexMeasure ψ ξ).Integrable f
  · have hf' : (P.polarizedComplexMeasure ψ ξ).Integrable (fun t => starRingEnd ℂ (f t)) :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf
    have hnat := VectorMeasure.map_integral_comp_eq_integral_mapRangeL
      (P.polarizedComplexMeasure ψ ξ) hf'
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) (Complex.conjCLE : ℂ →L[ℝ] ℂ)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ)
      (B := ContinuousLinearMap.mul ℝ ℂ) (B' := ContinuousLinearMap.mul ℝ ℂ)
      (fun x y => by simp)
    rw [← hmap] at hnat
    simpa [Complex.conjCLE_apply] using hnat.symm
  · have hfs : ¬ (P.polarizedComplexMeasure ξ ψ).Integrable (fun t => starRingEnd ℂ (f t)) := by
      intro h
      rw [VectorMeasure.Integrable, P.variation_polarizedComplexMeasure_comm] at h
      exact hf (by simpa [Complex.conjCLE_apply] using
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h)
    rw [VectorMeasure.integral_undef hf, VectorMeasure.integral_undef hfs, map_zero]

end ProjValMeasure
end TauCeti

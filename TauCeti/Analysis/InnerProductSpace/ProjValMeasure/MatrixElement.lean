/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Integral
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Variation
public import TauCeti.MeasureTheory.VectorMeasure.WithDensity

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
* `ProjValMeasure.integrable_polarizedComplexMeasure_of_memLp`,
  `ProjValMeasure.eNorm_integral_polarizedComplexMeasure_le`,
  `ProjValMeasure.integral_norm_variation_polarizedComplexMeasure_le`,
  `ProjValMeasure.norm_integral_polarizedComplexMeasure_le`: `L²`-integrability and
  Cauchy–Schwarz bounds for integration against polarized spectral measures.
* `ProjValMeasure.integral_polarizedComplexMeasure_star`: conjugate symmetry of polarized
  integrals.
* `ProjValMeasure.polarizedComplexMeasure_integral_right`,
  `ProjValMeasure.polarizedComplexMeasure_integral_left`: action of bounded Borel operators on
  polarized measures as scalar densities.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill, 1991, Theorem 12.21.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Section 4.2.
-/

public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

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

/-- Every function in `L²(P.diag ξ)` is integrable against `P.polarizedComplexMeasure ψ ξ`. -/
theorem integrable_polarizedComplexMeasure_of_memLp {E : Type*} [NormedAddCommGroup E]
    (P : ProjValMeasure X H) (ψ : H) {ξ : H} {f : X → E} (hf : MemLp f 2 (P.diag ξ)) :
    (P.polarizedComplexMeasure ψ ξ).Integrable f := by
  refine ⟨hf.aestronglyMeasurable.mono_ac
    (P.polarizedComplexMeasure_variation_absolutelyContinuous_right ψ ξ), ?_⟩
  rw [HasFiniteIntegral]
  refine (P.lintegral_variation_polarizedComplexMeasure_le ψ ξ fun t => ‖f t‖ₑ).trans_lt ?_
  have hsq : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable).1 hf.eLpNorm_lt_top
    simpa [ENNReal.rpow_two] using h
  exact ENNReal.mul_lt_top eNorm_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hsq.ne)

/-- Extended-norm Cauchy–Schwarz bound for integration against a polarized spectral measure.
No measurability or integrability hypothesis is needed. -/
theorem eNorm_integral_polarizedComplexMeasure_le (P : ProjValMeasure X H) (f : X → ℂ)
    (ψ ξ : H) :
    ‖∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ]‖ₑ ≤
      ‖ψ‖ₑ * (∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) := by
  refine VectorMeasure.eNorm_integral_le_lintegral_eNorm.trans ?_
  rw [eNorm_eq_nnNorm, ContinuousLinearMap.opNNNorm_mul, ENNReal.coe_one, one_mul]
  exact P.lintegral_variation_polarizedComplexMeasure_le ψ ξ fun t => ‖f t‖ₑ

/-- Real Cauchy–Schwarz bound for the variation integral of a function in `L²(P.diag ξ)`:
`∫ t, ‖f t‖ ∂|μ_(ψ,ξ)| ≤ ‖ψ‖ * √(∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ))`. -/
theorem integral_norm_variation_polarizedComplexMeasure_le {E : Type*} [NormedAddCommGroup E]
    (P : ProjValMeasure X H) (ψ : H) {ξ : H} {f : X → E} (hf : MemLp f 2 (P.diag ξ)) :
    ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ)) := by
  have hint := P.integrable_polarizedComplexMeasure_of_memLp ψ hf
  have hsq : Integrable (fun t => ‖f t‖ ^ 2) (P.diag ξ) := by
    simpa using hf.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
  have hsq_lt : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) ≠ ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable).1 hf.eLpNorm_lt_top
    simpa [ENNReal.rpow_two] using h.ne
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => norm_nonneg _)
    hint.norm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _)
    hsq.aestronglyMeasurable, Real.sqrt_eq_rpow]
  have h1 : ∫⁻ t, ENNReal.ofReal ‖f t‖ ∂(P.polarizedComplexMeasure ψ ξ).variation =
      ∫⁻ t, ‖f t‖ₑ ∂(P.polarizedComplexMeasure ψ ξ).variation := by simp_rw [ofReal_norm]
  have h2 : ∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(P.diag ξ) = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) := by
    simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [h1, h2, ENNReal.toReal_rpow, ← toReal_eNorm ψ, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top eNorm_ne_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hsq_lt).ne)
    (P.lintegral_variation_polarizedComplexMeasure_le ψ ξ fun t => ‖f t‖ₑ)

/-- Norm Cauchy–Schwarz bound for integration against a polarized spectral measure. -/
theorem norm_integral_polarizedComplexMeasure_le (P : ProjValMeasure X H) (ψ : H) {ξ : H}
    {f : X → ℂ} (hf : MemLp f 2 (P.diag ξ)) :
    ‖∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ]‖ ≤
      ‖ψ‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ)) := by
  refine VectorMeasure.norm_integral_le_integral_norm.trans ?_
  calc ‖ContinuousLinearMap.mul ℝ ℂ‖ * ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure ψ ξ).variation
      ≤ 1 * ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure ψ ξ).variation := by
        gcongr
        exact ContinuousLinearMap.opNorm_mul_le ℝ ℂ
    _ = ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure ψ ξ).variation := one_mul _
    _ ≤ ‖ψ‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ)) :=
        P.integral_norm_variation_polarizedComplexMeasure_le ψ hf

/-- **Conjugate symmetry of polarized integrals.** Integrating `star f` against `μ_(ξ,ψ)` is the
conjugate of integrating `f` against `μ_(ψ,ξ)`, with no integrability hypothesis on `f`. -/
theorem integral_polarizedComplexMeasure_star (P : ProjValMeasure X H) (f : X → ℂ) (ψ ξ : H) :
    ∫ᵛ t, star (f t) ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ξ ψ] =
      star (∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ]) := by
  have hmap : P.polarizedComplexMeasure ξ ψ =
      VectorMeasure.mapRangeL Complex.conjCLE.toContinuousLinearMap
        (P.polarizedComplexMeasure ψ ξ) := by
    ext B _
    simpa [VectorMeasure.mapRangeL_apply] using P.polarizedComplexMeasure_swap_apply ψ ξ B
  by_cases hf : (P.polarizedComplexMeasure ψ ξ).Integrable f
  · have hf' : (P.polarizedComplexMeasure ψ ξ).Integrable (fun t => star (f t)) :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hf
    have hnat := VectorMeasure.map_integral_comp_eq_integral_mapRangeL
      (P.polarizedComplexMeasure ψ ξ) hf'
      Complex.conjCLE.toContinuousLinearMap Complex.conjCLE.toContinuousLinearMap
      Complex.conjCLE.toContinuousLinearMap
      (B := ContinuousLinearMap.mul ℝ ℂ) (B' := ContinuousLinearMap.mul ℝ ℂ)
      (fun x y => by simp)
    rw [← hmap] at hnat
    simpa [Complex.conjCLE_apply] using hnat.symm
  · have hfs : ¬ (P.polarizedComplexMeasure ξ ψ).Integrable (fun t => star (f t)) := by
      intro h
      rw [VectorMeasure.Integrable, P.variation_polarizedComplexMeasure_swap] at h
      exact hf (by simpa [Complex.conjCLE_apply] using
        Complex.conjCLE.toContinuousLinearMap.integrable_comp h)
    rw [VectorMeasure.integral_undef hf, VectorMeasure.integral_undef hfs, star_zero]

/-- Applying a bounded Borel operator `P.integral g` to the right vector multiplies the polarized
complex measure by the density `g`. -/
theorem polarizedComplexMeasure_integral_right (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) (ψ ξ : H) :
    P.polarizedComplexMeasure ψ (P.integral g ξ) =
      (P.polarizedComplexMeasure ψ ξ).withDensity g (ContinuousLinearMap.mul ℝ ℂ) := by
  ext B hB
  rw [P.polarizedComplexMeasure_apply _ _ B hB,
    VectorMeasure.withDensity_apply (g.integrable _),
    ← P.integral_indicator hB, ← mul_apply_eq_comp, ← map_mul,
    ← P.integral_polarizedComplexMeasure_eq_inner_integral, ← VectorMeasure.integral_indicator hB]
  congr 1
  ext t
  by_cases ht : t ∈ B <;> simp [ht, BoundedBorelFunction.indicator_apply]

/-- Every bounded Borel integral commutes with every spectral projection. -/
private theorem integral_proj_apply (P : ProjValMeasure X H) (g : BoundedBorelFunction X)
    (B : Set X) (hB : MeasurableSet B) (ξ : H) :
    P.integral g (P.proj B hB ξ) = P.proj B hB (P.integral g ξ) := by
  have hcomm : Commute (P.proj B hB) (P.integral g) :=
    (P.forall_commute_integral_iff (P.proj B hB)).2 (fun C hC => P.proj_mul_comm B C hB hC) g
  exact (ContinuousLinearMap.ext_iff.1 hcomm.eq ξ).symm

/-- Applying a bounded Borel operator `P.integral g` to the left vector multiplies the polarized
complex measure by the density `star g`. -/
theorem polarizedComplexMeasure_integral_left (P : ProjValMeasure X H)
    (g : BoundedBorelFunction X) (ψ ξ : H) :
    P.polarizedComplexMeasure (P.integral g ψ) ξ =
      (P.polarizedComplexMeasure ψ ξ).withDensity (star ⇑g) (ContinuousLinearMap.mul ℝ ℂ) := by
  have hswap : P.polarizedComplexMeasure (P.integral g ψ) ξ =
      P.polarizedComplexMeasure ψ (P.integral (star g) ξ) := by
    ext B hB
    rw [P.polarizedComplexMeasure_apply _ _ B hB, P.polarizedComplexMeasure_apply _ _ B hB]
    calc ⟪P.integral g ψ, P.proj B hB ξ⟫_ℂ
        = ⟪ψ, P.integral (star g) (P.proj B hB ξ)⟫_ℂ := by
          rw [map_star, ContinuousLinearMap.star_eq_adjoint,
            ContinuousLinearMap.adjoint_inner_right]
      _ = ⟪ψ, P.proj B hB (P.integral (star g) ξ)⟫_ℂ := by
          rw [P.integral_proj_apply]
  rw [hswap, P.polarizedComplexMeasure_integral_right]
  rfl

end ProjValMeasure
end TauCeti

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
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

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
  `ProjValMeasure.integral_norm_variation_polarizedComplexMeasure_le`, and
  `ProjValMeasure.integral_norm_variation_polarizedComplexMeasure_le_left`: Cauchy–Schwarz variation
  estimates and `L²`-to-`L¹(|μ_(ψ,ξ)|)` integrability for polarized spectral measures.

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
  have hvar := P.polarizedComplexMeasure_variation_univ_le ψ (P.integral g ξ)
  rwa [P.polarizedComplexMeasure_integral_right g ψ ξ,
    VectorMeasure.variation_withDensity_mul (g.integrable _),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hvar

/-- For any function `f : X → E` that is almost everywhere strongly measurable for `P.diag ξ`,
the lower Lebesgue integral of `‖f‖ₑ` against the variation of `P.polarizedComplexMeasure ψ ξ` is
bounded by `‖ψ‖ₑ * eLpNorm f 2 (P.diag ξ)`. -/
theorem lintegral_enorm_variation_polarizedComplexMeasure_le_eLpNorm {E : Type*}
    [NormedAddCommGroup E] (P : ProjValMeasure X H) {f : X → E} {ξ : H}
    (hf : AEStronglyMeasurable f (P.diag ξ)) (ψ : H) :
    ∫⁻ t, ‖f t‖ₑ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ₑ * eLpNorm f 2 (P.diag ξ) := by
  have hac := P.variation_polarizedComplexMeasure_absolutelyContinuous_diag ψ ξ
  let φ : X → ℂ := fun t => (‖hf.mk f t‖ : ℂ)
  have hφ : Measurable φ :=
    Complex.continuous_ofReal.measurable.comp hf.stronglyMeasurable_mk.norm.measurable
  have hφ_enorm (t : X) : ‖φ t‖ₑ = ‖hf.mk f t‖ₑ := by
    simp [φ, ← ofReal_norm]
  calc
    ∫⁻ t, ‖f t‖ₑ ∂(P.polarizedComplexMeasure ψ ξ).variation
        = ∫⁻ t, ‖φ t‖ₑ ∂(P.polarizedComplexMeasure ψ ξ).variation :=
      lintegral_congr_ae ((hac.ae_eq hf.ae_eq_mk).mono fun t ht => by
        dsimp only; rw [ht, hφ_enorm])
    _ = ⨆ n : ℕ, ∫⁻ t, ‖BoundedBorelFunction.truncate φ hφ n t‖ₑ
          ∂(P.polarizedComplexMeasure ψ ξ).variation := by
      simpa only [pow_one] using
        (BoundedBorelFunction.iSup_lintegral_enorm_pow_truncate hφ 1 _).symm
    _ ≤ ‖ψ‖ₑ * eLpNorm f 2 (P.diag ξ) := by
      refine iSup_le fun n =>
        (P.lintegral_enorm_variation_polarizedComplexMeasure_le
          (BoundedBorelFunction.truncate φ hφ n) ψ ξ).trans ?_
      rw [ENNReal.ofReal_mul (norm_nonneg ψ), ofReal_norm, ofReal_norm]
      gcongr
      refine (ENNReal.rpow_le_rpow_iff (show (0 : ℝ) < 2 by norm_num)).1 ?_
      have heLp_sq : eLpNorm f 2 (P.diag ξ) ^ 2 = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) := by
        simpa only [Nat.cast_ofNat] using
          (TauCeti.lintegral_enorm_pow_eq_eLpNorm_pow (n := 2) two_ne_zero hf).symm
      rw [ENNReal.rpow_two, ENNReal.rpow_two, ← P.diag_univ, P.diag_integral,
        withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, heLp_sq]
      calc
        ∫⁻ t, ‖BoundedBorelFunction.truncate φ hφ n t‖ₑ ^ 2 ∂(P.diag ξ)
            ≤ ∫⁻ t, ‖φ t‖ₑ ^ 2 ∂(P.diag ξ) :=
          lintegral_mono fun t => pow_le_pow_left'
            (eNorm_le_iff_norm_le.2 (BoundedBorelFunction.norm_truncate_apply_le φ hφ n t)) 2
        _ = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) :=
          lintegral_congr_ae (hf.ae_eq_mk.mono fun t ht => by
            dsimp only; rw [ht, hφ_enorm])

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

end ProjValMeasure
end TauCeti

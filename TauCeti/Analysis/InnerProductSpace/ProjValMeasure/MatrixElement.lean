/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Integral
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Variation
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

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

On the diagonal, the polarized measure `μ_(ξ,ξ)` is the finite positive measure `P.diag ξ`
regarded as a complex measure, namely `(P.diag ξ).withDensityᵥ 1`. Its variation is `P.diag ξ`,
and integrating any complex function against it gives the Bochner integral against `P.diag ξ`.

## Main declarations

* `ProjValMeasure.integral_polarizedComplexMeasure_eq_inner_integral`: the matrix element
  `⟪ψ, (∫ f dP) ξ⟫` is the integral of `f` against `μ_(ψ,ξ)`.
* `ProjValMeasure.polarizedComplexMeasure_self_eq_withDensityᵥ`: `μ_(ξ,ξ)` is `P.diag ξ` with the
  constant complex density `1`.
* `ProjValMeasure.variation_polarizedComplexMeasure_self`: the variation of `μ_(ξ,ξ)` is
  `P.diag ξ`.
* `ProjValMeasure.integral_polarizedComplexMeasure_self`: integration of any `f : X → ℂ` against
  `μ_(ξ,ξ)` is the Bochner integral against `P.diag ξ`.

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
    rw [SimpleFunc.coe_add, VectorMeasure.integral_add (SimpleFunc.integrable_of_isFiniteMeasure s)
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

/-- On the diagonal, the polarized measure is the diagonal measure `P.diag ξ` regarded as a
complex measure, that is, with the constant complex density `1`. -/
theorem polarizedComplexMeasure_self_eq_withDensityᵥ (P : ProjValMeasure X H) (ξ : H) :
    P.polarizedComplexMeasure ξ ξ = (P.diag ξ).withDensityᵥ fun _ => (1 : ℂ) := by
  ext B hB
  rw [polarizedComplexMeasure_diag _ _ _ hB, withDensityᵥ_apply (integrable_const _) hB,
    setIntegral_const, measureReal_def, Complex.real_smul, mul_one]

/-- The variation of the diagonal polarized measure is the diagonal measure. -/
@[simp]
theorem variation_polarizedComplexMeasure_self (P : ProjValMeasure X H) (ξ : H) :
    (P.polarizedComplexMeasure ξ ξ).variation = P.diag ξ := by
  rw [polarizedComplexMeasure_self_eq_withDensityᵥ,
    Measure.variation_withDensityᵥ (integrable_const _)]
  simp

/-- Integration of a complex function against the diagonal polarized measure through the
multiplication pairing is the Bochner integral against the diagonal measure. Both sides vanish
when `f` is not integrable, since the variation of the polarized measure is the diagonal
measure. -/
theorem integral_polarizedComplexMeasure_self (P : ProjValMeasure X H) (f : X → ℂ) (ξ : H) :
    ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ξ ξ] =
      ∫ x, f x ∂(P.diag ξ) := by
  -- Following the proof of Mathlib's `MeasureTheory.VectorMeasure.integral_toSignedMeasure`.
  rw [VectorMeasure.integral_eq_setToFun, MeasureTheory.integral_eq_setToFun]
  simp only [variation_polarizedComplexMeasure_self]
  refine setToFun_congr_left' _ _ (fun B hB _ => ?_) f
  ext x
  simp [transpose_eq_cbmApplyMeasure, polarizedComplexMeasure_diag _ _ _ hB, weightedSMul_apply,
    measureReal_def, mul_comm]

end ProjValMeasure
end TauCeti

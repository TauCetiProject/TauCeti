/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic
public import TauCeti.MeasureTheory.Function.BoundedBorel
public import TauCeti.MeasureTheory.Function.SimpleFunc.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.FinMeasAdditive

/-!
# Integration of bounded Borel symbols against a projection-valued measure

For a projection-valued measure `P` on `X` acting on a complex Hilbert space `H`, this file
constructs the operator integral `P.integral f = ∫ f dP` of a bounded Borel symbol
`f : BoundedBorelFunction X` as a unital star algebra homomorphism
`BoundedBorelFunction X →⋆ₐ[ℂ] (H →L[ℂ] H)`.

On a simple symbol taking the value `c` on the measurable fibre `s ⁻¹' {c}`, the integral is
the finite sum `∑ c • P(s ⁻¹' {c})`. Because the fibres are disjoint, the projections
`P(s ⁻¹' {c})` are mutually orthogonal, and the diagonal matrix element of this sum against `ξ`
is the integral of `s` against the diagonal measure `P.diag ξ`. This gives the contraction
bound `‖∫ s dP‖ ≤ ‖s‖` for the supremum norm. Simple symbols are dense among bounded Borel
symbols, so the integral extends uniquely by continuity; in particular it does not depend on
the choice of partition or of uniformly approximating simple symbols. The algebraic laws pass
to the limit.

The vector measure `B ↦ P(B) ξ` need not have finite variation, so this integral is not an
instance of integration against a vector measure; the construction instead uses Mathlib's
extension of additive set functions to simple functions, `SimpleFunc.setToSimpleFunc`, and the
continuous extension `LinearMap.extendOfNorm`.

## Main declarations

* `ProjValMeasure.integral`: the integral against `P`, a unital star algebra homomorphism.
* `ProjValMeasure.integral_ofSimpleFunc`: the integral of a simple symbol is the finite sum of
  its values times the projections of its fibres.
* `ProjValMeasure.eq_integral_of_continuous`: a continuous map agreeing with the integral on
  simple symbols is the integral.
* `ProjValMeasure.integral_indicator`: the integral of a measurable indicator is the projection.
* `ProjValMeasure.integral_diag_eq_inner_integral`: diagonal matrix elements of the integral are
  integrals against the diagonal measures.
* `ProjValMeasure.norm_integral_le`: a pointwise bound on the symbol bounds the operator norm.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill, 1991, Theorem 12.21.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Section 4.2.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace TauCeti
namespace ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Simple symbols -/

open scoped Classical in
/-- The projection field of `P`, extended by zero to non-measurable sets. -/
private def projOrZero (P : ProjValMeasure X H) (B : Set X) : H →L[ℂ] H :=
  if hB : MeasurableSet B then P.proj B hB else 0

private theorem projOrZero_of_measurableSet (P : ProjValMeasure X H) {B : Set X}
    (hB : MeasurableSet B) : P.projOrZero B = P.proj B hB := by
  simp [projOrZero, hB]

/-- The real-linear set function `B ↦ (c ↦ c • P(B))` that `setToSimpleFunc` extends to simple
symbols. -/
private def smulProj (P : ProjValMeasure X H) (B : Set X) : ℂ →L[ℝ] H →L[ℂ] H :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight (P.projOrZero B)

private theorem smulProj_apply (P : ProjValMeasure X H) (B : Set X) (c : ℂ) :
    P.smulProj B c = c • P.projOrZero B :=
  rfl

private theorem smulProj_empty (P : ProjValMeasure X H) : P.smulProj ∅ = 0 := by
  ext c : 1
  simp [smulProj_apply, projOrZero_of_measurableSet P MeasurableSet.empty]

/-- Finite additivity of `smulProj`. The zero measure is used so that every simple symbol is
integrable and every measurable set qualifies. -/
private theorem finMeasAdditive_smulProj (P : ProjValMeasure X H) :
    FinMeasAdditive (0 : Measure X) P.smulProj := by
  intro s t hs ht _ _ hst
  ext c : 1
  simp [smulProj_apply, projOrZero_of_measurableSet P (hs.union ht),
    projOrZero_of_measurableSet P hs, projOrZero_of_measurableSet P ht, P.proj_union hs ht hst]

private theorem setToSimpleFunc_smulProj_add (P : ProjValMeasure X H) (s t : SimpleFunc X ℂ) :
    (s + t).setToSimpleFunc P.smulProj =
      s.setToSimpleFunc P.smulProj + t.setToSimpleFunc P.smulProj :=
  SimpleFunc.setToSimpleFunc_add _ P.finMeasAdditive_smulProj integrable_zero_measure
    integrable_zero_measure

private theorem setToSimpleFunc_smulProj_piecewise (P : ProjValMeasure X H) (c : ℂ) {B : Set X}
    (hB : MeasurableSet B) :
    (SimpleFunc.piecewise B hB (SimpleFunc.const X c) (SimpleFunc.const X 0)).setToSimpleFunc
      P.smulProj = c • P.proj B hB := by
  rw [SimpleFunc.setToSimpleFunc_indicator _ P.smulProj_empty hB, smulProj_apply,
    projOrZero_of_measurableSet P hB]

/-- The integral of simple symbols against `P`, as a unital star algebra homomorphism. -/
private def simpleIntegral (P : ProjValMeasure X H) : (SimpleFunc X ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun s := s.setToSimpleFunc P.smulProj
  map_zero' := SimpleFunc.setToSimpleFunc_zero_apply _
  map_add' := P.setToSimpleFunc_smulProj_add
  map_one' := by
    simp [← SimpleFunc.const_one,
      SimpleFunc.setToSimpleFunc_const _ P.smulProj_empty, smulProj_apply,
      projOrZero_of_measurableSet P MeasurableSet.univ, ContinuousLinearMap.one_def]
  map_mul' s t := by
    induction s using SimpleFunc.induction with
    | const c hA =>
      induction t using SimpleFunc.induction with
      | const d hB =>
        rw [SimpleFunc.piecewise_const_mul_piecewise_const, setToSimpleFunc_smulProj_piecewise,
          setToSimpleFunc_smulProj_piecewise, setToSimpleFunc_smulProj_piecewise,
          smul_mul_smul_comm, P.proj_inter]
      | add _ ht₁ ht₂ =>
        rw [mul_add, setToSimpleFunc_smulProj_add,
          setToSimpleFunc_smulProj_add, mul_add, ht₁, ht₂]
    | add _ hs₁ hs₂ =>
      rw [add_mul, setToSimpleFunc_smulProj_add,
        setToSimpleFunc_smulProj_add, add_mul, hs₁, hs₂]
  commutes' c := by
    have hc : algebraMap ℂ (SimpleFunc X ℂ) c = SimpleFunc.const X c := by
      ext; simp [Algebra.algebraMap_eq_smul_one]
    simp [hc, SimpleFunc.setToSimpleFunc_const _ P.smulProj_empty, smulProj_apply,
      projOrZero_of_measurableSet P MeasurableSet.univ, Algebra.algebraMap_eq_smul_one,
      ContinuousLinearMap.one_def]
  map_star' s := by
    induction s using SimpleFunc.induction with
    | const c hA =>
      rw [SimpleFunc.star_piecewise_const, setToSimpleFunc_smulProj_piecewise,
        setToSimpleFunc_smulProj_piecewise, star_smul, (P.isSelfAdjoint_proj _ hA).star_eq]
    | add _ hs₁ hs₂ =>
      rw [star_add, setToSimpleFunc_smulProj_add,
        setToSimpleFunc_smulProj_add, star_add, hs₁, hs₂]

private theorem simpleIntegral_eq_setToSimpleFunc (P : ProjValMeasure X H)
    (s : SimpleFunc X ℂ) : P.simpleIntegral s = s.setToSimpleFunc P.smulProj :=
  rfl

private theorem simpleIntegral_apply (P : ProjValMeasure X H) (s : SimpleFunc X ℂ) :
    P.simpleIntegral s =
      ∑ c ∈ s.range, c • P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) := by
  rw [simpleIntegral_eq_setToSimpleFunc, SimpleFunc.setToSimpleFunc]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smulProj_apply, projOrZero_of_measurableSet]

/-- Diagonal matrix elements of the integral of a simple symbol are integrals against the
diagonal measures. -/
private theorem integral_diag_eq_inner_simpleIntegral (P : ProjValMeasure X H)
    (s : SimpleFunc X ℂ) (ξ : H) : ∫ x, s x ∂(P.diag ξ) = ⟪ξ, P.simpleIntegral s ξ⟫_ℂ := by
  rw [← s.integral_eq_integral (SimpleFunc.integrable_of_isFiniteMeasure s),
    SimpleFunc.integral_eq, simpleIntegral_apply]
  simp [inner_sum, inner_smul_right, P.inner_proj, measureReal_def, mul_comm]

/-- The integral of a simple symbol is bounded in operator norm by its supremum norm. -/
private theorem norm_simpleIntegral_le (P : ProjValMeasure X H) (s : SimpleFunc X ℂ) :
    ‖P.simpleIntegral s‖ ≤ ‖BoundedBorelFunction.ofSimpleFunc s‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ξ => ?_
  -- `‖(∫ s dP) ξ‖ ^ 2 = ⟪ξ, (∫ |s| ^ 2 dP) ξ⟫ = ∫ |s| ^ 2 d(P.diag ξ) ≤ ‖s‖ ^ 2 ‖ξ‖ ^ 2`.
  have hbound (x : X) :
      ‖(star s * s) x‖ ≤ ‖BoundedBorelFunction.ofSimpleFunc s‖ ^ 2 := by
    have hx := BoundedBorelFunction.norm_coe_le_norm (BoundedBorelFunction.ofSimpleFunc s) x
    rw [BoundedBorelFunction.ofSimpleFunc_apply] at hx
    simpa [sq] using mul_le_mul hx hx (norm_nonneg _) (norm_nonneg _)
  have hsq :
      ‖P.simpleIntegral s ξ‖ ^ 2 ≤ (‖BoundedBorelFunction.ofSimpleFunc s‖ * ‖ξ‖) ^ 2 := by
    have hinner : (‖P.simpleIntegral s ξ‖ ^ 2 : ℂ) = ∫ x, (star s * s) x ∂(P.diag ξ) := by
      rw [integral_diag_eq_inner_simpleIntegral]
      simp [map_star, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    have := norm_integral_le_of_norm_le_const (μ := P.diag ξ) (Eventually.of_forall hbound)
    rw [← hinner, P.diag_real_univ] at this
    simpa [mul_pow] using this
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

/-! ## The integral of a bounded Borel symbol -/

/-- The integral against `P` as a continuous linear map: the continuous extension of the simple
integral from the dense subspace of simple symbols. -/
private def integralCLM (P : ProjValMeasure X H) :
    BoundedBorelFunction X →L[ℂ] (H →L[ℂ] H) :=
  P.simpleIntegral.toLinearMap.extendOfNorm BoundedBorelFunction.ofSimpleFunc.toLinearMap

private theorem integralCLM_ofSimpleFunc (P : ProjValMeasure X H) (s : SimpleFunc X ℂ) :
    P.integralCLM (BoundedBorelFunction.ofSimpleFunc s) = P.simpleIntegral s :=
  LinearMap.extendOfNorm_eq BoundedBorelFunction.denseRange_ofSimpleFunc
    ⟨1, fun s => by simpa using P.norm_simpleIntegral_le s⟩ s

/-- The **integral** of a bounded Borel symbol against a projection-valued measure `P`,
`P.integral f = ∫ f dP`, as a unital star algebra homomorphism. It is characterised by
`integral_ofSimpleFunc` on simple symbols and its continuity (`continuous_integral`); see
`eq_integral_of_continuous`. -/
def integral (P : ProjValMeasure X H) : BoundedBorelFunction X →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := P.integralCLM
  map_zero' := map_zero P.integralCLM
  map_add' := map_add P.integralCLM
  map_one' := by
    rw [← map_one BoundedBorelFunction.ofSimpleFunc, integralCLM_ofSimpleFunc, map_one]
  map_mul' f g := by
    induction f, g using BoundedBorelFunction.denseRange_ofSimpleFunc.induction_on₂ with
    | hp =>
      exact isClosed_eq (P.integralCLM.continuous.comp (continuous_fst.mul continuous_snd))
        ((P.integralCLM.continuous.comp continuous_fst).mul
          (P.integralCLM.continuous.comp continuous_snd))
    | h s t => simp only [← map_mul, integralCLM_ofSimpleFunc]
  commutes' c := by
    rw [← AlgHomClass.commutes BoundedBorelFunction.ofSimpleFunc c, integralCLM_ofSimpleFunc,
      AlgHomClass.commutes]
  map_star' f := by
    induction f using BoundedBorelFunction.denseRange_ofSimpleFunc.induction_on with
    | hp =>
      exact isClosed_eq (P.integralCLM.continuous.comp continuous_star)
        (continuous_star.comp P.integralCLM.continuous)
    | ih s => simp only [← map_star, integralCLM_ofSimpleFunc]

private theorem integral_ofSimpleFunc_eq_simpleIntegral (P : ProjValMeasure X H)
    (s : SimpleFunc X ℂ) :
    P.integral (BoundedBorelFunction.ofSimpleFunc s) = P.simpleIntegral s :=
  P.integralCLM_ofSimpleFunc s

/-- The integral against `P` is continuous for the supremum norm on symbols, so uniform limits of
symbols have the limiting integral. -/
theorem continuous_integral (P : ProjValMeasure X H) : Continuous P.integral :=
  P.integralCLM.continuous

/-- A continuous map on bounded Borel symbols that agrees with `P.integral` on simple symbols is
`P.integral`, since simple symbols are dense. -/
theorem eq_integral_of_continuous (P : ProjValMeasure X H)
    {Φ : BoundedBorelFunction X → H →L[ℂ] H} (hΦ : Continuous Φ)
    (h : ∀ s, Φ (BoundedBorelFunction.ofSimpleFunc s) =
      P.integral (BoundedBorelFunction.ofSimpleFunc s)) :
    Φ = ⇑P.integral :=
  funext fun f => BoundedBorelFunction.denseRange_ofSimpleFunc.induction_on f
    (isClosed_eq hΦ P.continuous_integral) h

/-- The integral of a simple symbol `s` is `∑ c • P(s ⁻¹' {c})`, the sum running over the values
of `s`. -/
theorem integral_ofSimpleFunc (P : ProjValMeasure X H) (s : SimpleFunc X ℂ) :
    P.integral (BoundedBorelFunction.ofSimpleFunc s) =
      ∑ c ∈ s.range, c • P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) :=
  (P.integral_ofSimpleFunc_eq_simpleIntegral s).trans (P.simpleIntegral_apply s)

/-- The integral of the indicator of a measurable set `B` is the projection `P(B)`. -/
@[simp]
theorem integral_indicator (P : ProjValMeasure X H) {B : Set X} (hB : MeasurableSet B) :
    P.integral (BoundedBorelFunction.indicator B hB 1) = P.proj B hB := by
  have h : BoundedBorelFunction.indicator B hB 1 = BoundedBorelFunction.ofSimpleFunc
      (SimpleFunc.piecewise B hB (SimpleFunc.const X 1) (SimpleFunc.const X 0)) := by
    ext x
    by_cases hx : x ∈ B <;> simp [SimpleFunc.piecewise_apply, hx]
  rw [h, integral_ofSimpleFunc_eq_simpleIntegral]
  exact (P.setToSimpleFunc_smulProj_piecewise 1 hB).trans (one_smul ℂ _)

/-- Diagonal matrix elements of the integral are integrals against the diagonal measures:
`∫ f d(P.diag ξ) = ⟪ξ, (∫ f dP) ξ⟫`. -/
theorem integral_diag_eq_inner_integral (P : ProjValMeasure X H) (f : BoundedBorelFunction X)
    (ξ : H) : ∫ x, f x ∂(P.diag ξ) = ⟪ξ, P.integral f ξ⟫_ℂ := by
  obtain ⟨s, hs_le, hs⟩ := BoundedBorelFunction.exists_seq_tendsto_ofSimpleFunc f
  have hcont : Continuous fun g => ⟪ξ, P.integral g ξ⟫_ℂ :=
    continuous_const.inner ((ContinuousLinearMap.apply ℂ H ξ).continuous.comp
      P.continuous_integral)
  refine tendsto_nhds_unique (f := fun n => ∫ x, s n x ∂(P.diag ξ)) (l := atTop) ?_
    (((hcont.tendsto f).comp hs).congr fun n => ?_)
  · -- Dominated convergence, with the constant bound `‖f‖` and pointwise convergence.
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (s n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall (hs_le n)) (Eventually.of_forall fun x => ?_)
    rw [BoundedBorelFunction.tendsto_iff_tendstoUniformly] at hs
    simpa using hs.tendsto_at x
  · rw [Function.comp_apply, integral_ofSimpleFunc_eq_simpleIntegral,
      integral_diag_eq_inner_simpleIntegral]

/-- A pointwise bound `‖f x‖ ≤ M` on a symbol bounds the operator norm of its integral. This
includes an empty space, where every symbol and every operator integral has norm zero. -/
theorem norm_integral_le (P : ProjValMeasure X H) {f : BoundedBorelFunction X} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ x, ‖f x‖ ≤ M) : ‖P.integral f‖ ≤ M :=
  (NonUnitalStarAlgHom.norm_apply_le P.integral f).trans
    ((BoundedBorelFunction.norm_le hM).2 hf)

end ProjValMeasure
end TauCeti

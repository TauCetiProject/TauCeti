/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Density

/-!
# Scalar coordinates of a finite-dimensional weak-derivative graph

The native weak-derivative graph over the identity of `Lp F` is continuously linearly equivalent
to a finite tuple of scalar `W1p` spaces, for any finite basis of a finite-dimensional real normed
space `F`. The value and derivative of the inverse are reconstructed in that basis. This permits
scalar Sobolev estimates to be applied to vector-valued fields without a new Sobolev carrier.

## Main declarations

* `coordinatesL`: the native scalar projections, bundled into one continuous linear map.
* `coordinatesEquiv`: their continuous linear equivalence with scalar `W1p` tuples.
* `prev_coordinatesEquiv_symm_ae`, `weakFDeriv_coordinatesEquiv_symm_ae`: reconstruction
  formulas for values and derivatives in every direction on one almost-everywhere set.

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.2.
-/

public noncomputable section

namespace TauCeti.WeakDerivStep

open MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype ι] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The scalar coordinate map on an existing vector-valued weak-derivative graph. -/
def coordinatesL (b : Module.Basis ι ℝ F) :
    WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) →L[ℝ]
      (ι → W1p μ Ω p) :=
  ContinuousLinearMap.pi fun i ↦
    toW1pL (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))
      (b.coord i).toContinuousLinearMap

omit [Fintype ι] in
/-- Each coordinate is the native scalar Sobolev projection. -/
@[simp]
theorem coordinatesL_apply (b : Module.Basis ι ℝ F)
    (u : WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))) (i : ι) :
    coordinatesL b u i = toW1pL (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))
      (b.coord i).toContinuousLinearMap u :=
  (rfl)

omit [Fintype ι] in
/-- A coordinate value is the corresponding scalar projection of the original field. -/
theorem value_coordinatesL (b : Module.Basis ι ℝ F)
    (u : WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))) (i : ι) :
    W1p.value (coordinatesL b u i) =
      (b.coord i).toContinuousLinearMap.compLpL p (μ.restrict Ω)
        (prev (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) u) := by
  simp only [coordinatesL_apply, value_toW1pL, ContinuousLinearMap.id_apply]

omit [Fintype ι] in
/-- The coordinate tuple has the expected scalar values almost everywhere. -/
theorem value_coordinatesL_ae (b : Module.Basis ι ℝ F)
    (u : WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))) (i : ι) :
    W1p.value (coordinatesL b u i) =ᵐ[μ.restrict Ω]
      fun x ↦ b.coord i (prev (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) u x) := by
  rw [value_coordinatesL]
  exact (b.coord i).toContinuousLinearMap.coeFn_compLpL _

omit [Fintype ι] in
/-- The coordinate weak gradients encode every direction of the original weak derivative. -/
theorem inner_gradient_coordinatesL_ae (b : Module.Basis ι ℝ F)
    (u : WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))) (i : ι) :
    ∀ᵐ x ∂μ.restrict Ω, ∀ v, ⟪W1p.gradient (coordinatesL b u i) x, v⟫_ℝ =
      b.coord i (weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) u x v) :=
  inner_gradient_toW1pL_ae _ (b.coord i).toContinuousLinearMap u

/-- The value of the native finite sum is the pointwise basis expansion almost everywhere. -/
private theorem prev_sum_smulRightW1pL_ae (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    prev (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))
      (∑ i, smulRightW1pL (b i) (u i)) =ᵐ[μ.restrict Ω]
        fun x ↦ ∑ i, W1p.value (u i) x • b i := by
  classical
  rw [← prevL_apply, map_sum]
  simp only [prevL_apply, prev_smulRightW1pL]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦
    (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL p (μ.restrict Ω)
      (W1p.value (u i))), ae_all_iff.mpr (fun i ↦
        (ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLpL (W1p.value (u i)))]
    with x hs hc
  simp only [hs, hc, ContinuousLinearMap.toSpanSingleton_apply]

private theorem coordinatesL_sum_smulRightW1pL (b : Module.Basis ι ℝ F)
    (u : ι → W1p μ Ω p) :
    coordinatesL b (∑ i, smulRightW1pL (b i) (u i)) = u := by
  classical
  funext i
  apply W1p.ext_value
  rw [value_coordinatesL]
  apply Lp.ext
  filter_upwards [(b.coord i).toContinuousLinearMap.coeFn_compLpL
      (prev _ (∑ j, smulRightW1pL (b j) (u j))),
    prev_sum_smulRightW1pL_ae b u] with x hc hv
  rw [hc, hv]
  simp [Module.Basis.coord_apply, map_sum, Finsupp.single_apply]

/-- A finite basis identifies the native vector-valued first-order weak-derivative graph with
scalar Sobolev tuples. Its continuous inverse is the sum of the native rank-one maps. -/
def coordinatesEquiv (b : Module.Basis ι ℝ F) :
    WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) ≃L[ℝ]
      (ι → W1p μ Ω p) := by
  classical
  refine ContinuousLinearEquiv.equivOfInverse (coordinatesL b)
    (∑ i, (smulRightW1pL (b i)).comp (ContinuousLinearMap.proj i)) ?_ ?_
  · intro u
    simpa only [sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, coordinatesL_apply] using sum_smulRightW1pL_toW1pL b u
  · intro u
    simpa only [sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] using coordinatesL_sum_smulRightW1pL b u

/-- The coordinate equivalence applies the native scalar projections. -/
@[simp]
theorem coordinatesEquiv_apply (b : Module.Basis ι ℝ F)
    (u : WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))) :
    coordinatesEquiv b u = coordinatesL b u :=
  (rfl)

/-- The inverse of the coordinate equivalence is the sum of the native rank-one Sobolev maps. -/
@[simp]
theorem coordinatesEquiv_symm_apply (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    (coordinatesEquiv b).symm u = ∑ i, smulRightW1pL (b i) (u i) := by
  simp only [coordinatesEquiv, ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.equivOfInverse_apply, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

/-- The inverse coordinate equivalence has the expected almost-everywhere value formula. -/
theorem prev_coordinatesEquiv_symm_ae (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    prev (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) ((coordinatesEquiv b).symm u)
      =ᵐ[μ.restrict Ω] fun x ↦ ∑ i, W1p.value (u i) x • b i := by
  rw [coordinatesEquiv_symm_apply]
  exact prev_sum_smulRightW1pL_ae b u

/-- The inverse coordinate equivalence reconstructs the derivative in every direction on a
single almost-everywhere set. -/
theorem weakFDeriv_coordinatesEquiv_symm_ae (b : Module.Basis ι ℝ F) (u : ι → W1p μ Ω p) :
    ∀ᵐ x ∂μ.restrict Ω, ∀ v,
      weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω)))
        ((coordinatesEquiv b).symm u) x v = ∑ i, ⟪W1p.gradient (u i) x, v⟫_ℝ • b i := by
  classical
  rw [coordinatesEquiv_symm_apply, ← weakFDerivL_apply, map_sum]
  simp only [weakFDerivL_apply, weakFDeriv_smulRightW1pL]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦
      (smulRightGradientL (b i)).compLpL p (μ.restrict Ω) (W1p.gradient (u i))),
    ae_all_iff.mpr (fun i ↦
      (smulRightGradientL (b i)).coeFn_compLpL (W1p.gradient (u i)))] with x hs hc
  intro v
  simp only [hs, hc, sum_apply, smulRightGradientL_apply]

end TauCeti.WeakDerivStep

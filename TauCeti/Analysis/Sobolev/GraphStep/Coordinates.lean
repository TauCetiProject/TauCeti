/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.ScalarProjection
public import TauCeti.Analysis.Sobolev.W1p.Zero
public import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional

/-!
# Scalar coordinates of a finite-dimensional weak-derivative graph

The native weak-derivative graph over the identity of `Lp F` is continuously linearly equivalent
to a finite tuple of scalar `W1p` spaces, for any finite basis of a finite-dimensional real normed
space `F`. The value and derivative of the inverse are reconstructed in that basis. This permits
scalar Sobolev estimates to be applied to vector-valued fields without a new Sobolev carrier.

The inverse is built from coordinate fields: a scalar Sobolev function `u` and a vector `b : F` give
the field `x ↦ u x • b` (`TauCeti.WeakDerivStep.smulRightW1pL`), with weak derivative
`v ↦ ∂ᵥ u • b`, and for a basis `bᵢ` of `F`, with coordinate functionals `ℓᵢ`, a field `u` is the
sum of the fields `ℓᵢ ∘ u • bᵢ` built from its scalar projections `TauCeti.WeakDerivStep.toW1pL`.
Only the reconstruction needs `F` to be finite-dimensional.

## Main declarations

* `TauCeti.WeakDerivStep.smulRightW1pL`: the bounded linear map `u ↦ (x ↦ u x • b)` from scalar
  Sobolev functions to `F`-valued ones.
* `TauCeti.WeakDerivStep.prev_smulRightW1pL_ofTestFunctionₗ_ae_eq`: for a test function `ψ`, this
  field is represented by `x ↦ ψ x • b`.
* `TauCeti.WeakDerivStep.sum_smulRightW1pL_toW1pL`: a field is the sum of its coordinate fields.
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
open scoped ENNReal InnerProductSpace Distributions

section Gradient

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative `v ↦ ⟪g, v⟫ • b` of the field `x ↦ u x • b` at a point where the scalar
function `u` has gradient `g`. -/
def smulRightGradientL (b : F) : E →L[ℝ] E →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ E ℝ F (ContinuousLinearMap.toSpanSingleton ℝ b)).comp
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap

/-- Evaluation formula for `smulRightGradientL`. -/
@[simp]
theorem smulRightGradientL_apply (b : F) (g v : E) :
    smulRightGradientL b g v = inner ℝ g v • b := by
  simp [smulRightGradientL]

end Gradient

section CoordinateFields

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

section CompleteSpace

variable [CompleteSpace F]

/-- The field `x ↦ u x • b` of a scalar Sobolev function has weak derivative
`v ↦ ⟪∇u x, v⟫ • b`. -/
theorem hasWeakFDerivOn_smulRight (b : F) (u : W1p mu Omega p) :
    HasWeakFDerivOn mu Omega
      ((ContinuousLinearMap.toSpanSingleton ℝ b).compLpL p (mu.restrict Omega) (W1p.value u))
      ((smulRightGradientL b).compLpL p (mu.restrict Omega) (W1p.gradient u)) := by
  refine ((W1p.hasWeakFDerivOn u).clm_comp (ContinuousLinearMap.toSpanSingleton ℝ b)).congr_ae
    ((ContinuousLinearMap.toSpanSingleton ℝ b).coeFn_compLpL (W1p.value u)).symm
    |>.congr_ae_deriv ?_
  filter_upwards [(smulRightGradientL b).coeFn_compLpL (W1p.gradient u)] with x hx
  rw [hx]
  ext v
  simp [real_inner_comm]

/-- The bounded linear map sending a scalar Sobolev function `u` to the `F`-valued Sobolev field
`x ↦ u x • b`. -/
def smulRightW1pL (b : F) :
    W1p mu Omega p →L[ℝ]
      WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) :=
  ContinuousLinearMap.codRestrict
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
      ((((ContinuousLinearMap.toSpanSingleton ℝ b).compLpL p (mu.restrict Omega)).comp
          W1p.valueL).prod
        (((smulRightGradientL b).compLpL p (mu.restrict Omega)).comp W1p.gradientL)))
    _ fun u ↦ (mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn _ _).mpr (by
      simpa using hasWeakFDerivOn_smulRight b u)

/-- The value of `smulRightW1pL b u` is the class of `x ↦ u x • b`. -/
@[simp]
theorem prev_smulRightW1pL (b : F) (u : W1p mu Omega p) :
    prev _ (smulRightW1pL b u) =
      (ContinuousLinearMap.toSpanSingleton ℝ b).compLpL p (mu.restrict Omega) (W1p.value u) := by
  simp [prev_coe, smulRightW1pL]

/-- The weak derivative of `smulRightW1pL b u` is the class of `x ↦ (v ↦ ⟪∇u x, v⟫ • b)`. -/
@[simp]
theorem weakFDeriv_smulRightW1pL (b : F) (u : W1p mu Omega p) :
    weakFDeriv _ (smulRightW1pL b u) =
      (smulRightGradientL b).compLpL p (mu.restrict Omega) (W1p.gradient u) := by
  simp [weakFDeriv_coe, smulRightW1pL]

/-- The field `smulRightW1pL b φ` of a test function `φ` is represented by `x ↦ φ x • b`. -/
theorem prev_smulRightW1pL_ofTestFunctionₗ_ae_eq (b : F) (φ : 𝓓(Omega, ℝ)) :
    ⇑(prev _ (smulRightW1pL b (W1p.ofTestFunctionₗ mu Omega p φ)))
      =ᵐ[mu.restrict Omega] fun x ↦ φ x • b := by
  rw [prev_smulRightW1pL, W1p.value_ofTestFunctionₗ]
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ b).coeFn_compLpL
    (testFunctionLp (mu := mu) p φ), testFunctionLp_apply_ae (mu := mu) p φ] with x hx hφ
  rw [hx, ContinuousLinearMap.toSpanSingleton_apply, hφ]

end CompleteSpace

/-- **Coordinate reconstruction.** For a basis `b` of `F`, an `F`-valued Sobolev field is the sum
of the fields `ℓᵢ ∘ u • bᵢ` built from its scalar coordinate projections. -/
theorem sum_smulRightW1pL_toW1pL [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ F)
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    ∑ i, smulRightW1pL (b i) (toW1pL _ (b.coord i).toContinuousLinearMap u) = u := by
  apply ext
  rw [← prevL_apply, map_sum]
  simp only [prevL_apply, prev_smulRightW1pL, value_toW1pL, ContinuousLinearMap.id_apply]
  exact (eq_sum_basis_compLpL b (prev _ u)).symm

end CoordinateFields

section Coordinates

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
  refine ContinuousLinearEquiv.ofContinuousLinearMap (coordinatesL b)
    (∑ i, (smulRightW1pL (b i)).comp (ContinuousLinearMap.proj i))
    (ContinuousLinearMap.ext ?_) (ContinuousLinearMap.ext ?_)
  · intro u
    simpa only [sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.proj_apply] using coordinatesL_sum_smulRightW1pL b u
  · intro u
    simpa only [sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.proj_apply, coordinatesL_apply] using sum_smulRightW1pL_toW1pL b u

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
  simp only [coordinatesEquiv, ContinuousLinearEquiv.symm_ofContinuousLinearMap,
    ContinuousLinearEquiv.coe_ofContinuousLinearMap, sum_apply, ContinuousLinearMap.comp_apply,
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

end Coordinates

end TauCeti.WeakDerivStep

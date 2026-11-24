/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.ScalarProjection
public import TauCeti.Analysis.Sobolev.W1p.Zero
public import TauCeti.LinearAlgebra.Complex.Module
public import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional
import TauCeti.Analysis.Distribution.TestFunction.Lp
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm

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

* `TauCeti.WeakDerivStep.smulRightBaseW1pL`, `TauCeti.WeakDerivStep.smulRightW1pL`: the bounded
  linear maps `u ↦ (x ↦ u x • b)` from scalar Sobolev functions into the `ι`-based and
  identity-based weak-derivative graphs.
* `TauCeti.WeakDerivStep.prev_smulRightBaseW1pL_ofTestFunctionₗ_ae_eq`,
  `TauCeti.WeakDerivStep.prev_smulRightW1pL_ofTestFunctionₗ_ae_eq`,
  `TauCeti.WeakDerivStep.norm_prev_smulRightBaseW1pL_ofTestFunctionₗ_sq`: test-function
  representative and squared `L²` norm formulas for scalar-mode fields.
* `TauCeti.WeakDerivStep.sum_smulRightW1pL_toW1pL`: a field is the sum of its coordinate fields.
* `TauCeti.WeakDerivStep.eq_zero_of_forall_inner_compLpL_prev_eq_zero`: for `T` with dense range,
  the fields `T ∘ u` of the graph space over `ι` are dense in `L²`.
* `smulRightComplexL`, `prev_smulRightComplexL`, `weakFDeriv_smulRightComplexL_ae`:
  rank-one reconstruction of complex scalar graphs in an arbitrary complex normed target.
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

/-- The bounded linear map sending a scalar Sobolev function `w` to `x ↦ w x • a` in the
weak-derivative graph over `ι.compLpL p (mu.restrict Omega)`. -/
def smulRightBaseW1pL {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (ι : D →L[ℝ] F) (a : D) :
    W1p mu Omega p →L[ℝ] WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega)) :=
  ContinuousLinearMap.codRestrict
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
      ((((ContinuousLinearMap.toSpanSingleton ℝ a).compLpL p (mu.restrict Omega)).comp
          W1p.valueL).prod
        (((smulRightGradientL (ι a)).compLpL p (mu.restrict Omega)).comp W1p.gradientL)))
    _ fun w ↦ (mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn _ _).mpr <| by
      have hcomp : ι.comp (ContinuousLinearMap.toSpanSingleton ℝ a) =
          ContinuousLinearMap.toSpanSingleton ℝ (ι a) := by ext; simp
      simpa [ContinuousLinearMap.compLp_compLp, hcomp] using hasWeakFDerivOn_smulRight (ι a) w

/-- The value of `smulRightBaseW1pL ι a w` is the class of `x ↦ w x • a`. -/
@[simp]
theorem prev_smulRightBaseW1pL {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (ι : D →L[ℝ] F) (a : D) (w : W1p mu Omega p) :
    prev _ (smulRightBaseW1pL ι a w) =
      (ContinuousLinearMap.toSpanSingleton ℝ a).compLpL p (mu.restrict Omega) (W1p.value w) := by
  simp [prev_coe, smulRightBaseW1pL]

/-- The weak derivative of `smulRightBaseW1pL ι a w` is the class of
`x ↦ (v ↦ ⟪∇w x, v⟫ • ι a)`. -/
@[simp]
theorem weakFDeriv_smulRightBaseW1pL {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (ι : D →L[ℝ] F) (a : D) (w : W1p mu Omega p) :
    weakFDeriv _ (smulRightBaseW1pL ι a w) =
      (smulRightGradientL (ι a)).compLpL p (mu.restrict Omega) (W1p.gradient w) := by
  simp [weakFDeriv_coe, smulRightBaseW1pL]

/-- The field `smulRightBaseW1pL ι a φ` of a test function `φ` is represented by `x ↦ φ x • a`. -/
theorem prev_smulRightBaseW1pL_ofTestFunctionₗ_ae_eq {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (ι : D →L[ℝ] F) (a : D) (φ : 𝓓(Omega, ℝ)) :
    ⇑(prev _ (smulRightBaseW1pL ι a (W1p.ofTestFunctionₗ mu Omega p φ)))
      =ᵐ[mu.restrict Omega] fun x ↦ φ x • a := by
  rw [prev_smulRightBaseW1pL, W1p.value_ofTestFunctionₗ]
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ a).coeFn_compLpL
    (testFunctionLp (mu := mu) p φ), testFunctionLp_apply_ae (mu := mu) p φ] with x hx hφ
  rw [hx, ContinuousLinearMap.toSpanSingleton_apply, hφ]

omit [Fact (1 ≤ p)] in
/-- The squared `L²` norm of the value of `smulRightBaseW1pL ι a` on a test function `φ` is
`(∫ x, φ x ^ 2 ∂mu) * ‖a‖ ^ 2`. -/
theorem norm_prev_smulRightBaseW1pL_ofTestFunctionₗ_sq {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (ι : D →L[ℝ] F) (a : D) (φ : 𝓓(Omega, ℝ)) :
    ‖prev _ (smulRightBaseW1pL ι a (W1p.ofTestFunctionₗ mu Omega 2 φ))‖ ^ 2 =
      (∫ x, (φ : E → ℝ) x ^ 2 ∂mu) * ‖a‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq,
    integral_congr_ae (g := fun x ↦ (φ : E → ℝ) x ^ 2 * ‖a‖ ^ 2)
      ((prev_smulRightBaseW1pL_ofTestFunctionₗ_ae_eq (p := 2) ι a φ).mono fun x hx ↦ by
        rw [hx, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]),
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (φ.tsupport_subset h)],
    MeasureTheory.integral_mul_const]

/-- The bounded linear map sending a scalar Sobolev function `u` to the `F`-valued Sobolev field
`x ↦ u x • b`. -/
def smulRightW1pL (b : F) :
    W1p mu Omega p →L[ℝ]
      WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) :=
  (toIdL ((ContinuousLinearMap.id ℝ F).compLpL p (mu.restrict Omega))).comp
    (smulRightBaseW1pL (ContinuousLinearMap.id ℝ F) b)

/-- The value of `smulRightW1pL b u` is the class of `x ↦ u x • b`. -/
@[simp]
theorem prev_smulRightW1pL (b : F) (u : W1p mu Omega p) :
    prev _ (smulRightW1pL b u) =
      (ContinuousLinearMap.toSpanSingleton ℝ b).compLpL p (mu.restrict Omega) (W1p.value u) := by
  simp [smulRightW1pL, ContinuousLinearMap.id_compLpL]

/-- The weak derivative of `smulRightW1pL b u` is the class of `x ↦ (v ↦ ⟪∇u x, v⟫ • b)`. -/
@[simp]
theorem weakFDeriv_smulRightW1pL (b : F) (u : W1p mu Omega p) :
    weakFDeriv _ (smulRightW1pL b u) =
      (smulRightGradientL b).compLpL p (mu.restrict Omega) (W1p.gradient u) := by
  simp [smulRightW1pL]

/-- The field `smulRightW1pL b φ` of a test function `φ` is represented by `x ↦ φ x • b`. -/
theorem prev_smulRightW1pL_ofTestFunctionₗ_ae_eq (b : F) (φ : 𝓓(Omega, ℝ)) :
    ⇑(prev _ (smulRightW1pL b (W1p.ofTestFunctionₗ mu Omega p φ)))
      =ᵐ[mu.restrict Omega] fun x ↦ φ x • b := by
  simpa only [prev_smulRightW1pL, ← prev_smulRightBaseW1pL (ContinuousLinearMap.id ℝ F) b] using
    prev_smulRightBaseW1pL_ofTestFunctionₗ_ae_eq (ContinuousLinearMap.id ℝ F) b φ

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

section Density

variable {E F D : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup D] [NormedSpace ℝ D] {mu : Measure E} [mu.IsAddHaarMeasure]

/-- **The fields `T ∘ u` are dense in `L²(E, F)`.** Let `T : D →L[ℝ] F` have dense range, such as
`ι` itself when `D` is a dense domain in `F`. A field `h ∈ L²(E, F)` orthogonal to `T ∘ u` for every
`u` in the graph space `L²(E, D) ∩ W^{1,2}(E, F)` over `ι : D →L[ℝ] F` vanishes. -/
theorem eq_zero_of_forall_inner_compLpL_prev_eq_zero {ι T : D →L[ℝ] F} (hT : DenseRange T)
    {h : Lp F 2 (mu.restrict (⊤ : Opens E))}
    (hh : ∀ u : WeakDerivStep mu ⊤ 2 (ι.compLpL 2 (mu.restrict (⊤ : Opens E))),
      ⟪T.compLpL 2 (mu.restrict (⊤ : Opens E)) (prev _ u), h⟫_ℝ = 0) :
    h = 0 := by
  -- Pair `h` with the fields `x ↦ φ x • T a` for test functions `φ` and vectors `a`.
  refine Lp.eq_zero_of_forall_integral_testFunction_smul_eq_zero fun φ ↦
    hT.eq_zero_of_inner_right ℝ fun a ↦ ?_
  let u := smulRightBaseW1pL ι a (W1p.ofTestFunctionₗ mu ⊤ 2 φ)
  rw [← integral_inner (φ.integrable_smul_of_memLp (Lp.memLp h)), ← hh u, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [prev_smulRightBaseW1pL_ofTestFunctionₗ_ae_eq (p := 2) ι a φ,
    T.coeFn_compLpL (prev _ u)] with x hx hTx
  rw [hTx, hx, map_smul, inner_smul_left, inner_smul_right, conj_trivial]

end Density

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

namespace TauCeti.WeakDerivStep

open MeasureTheory TopologicalSpace
open scoped ENNReal

section ComplexLine

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reconstruct a complex scalar graph along one vector in the original fibre. -/
def smulRightComplexL (Ω : Opens E) (v : F) : WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp ℂ
  p (μ.restrict Ω))) →L[ℝ] WeakDerivStep μ Ω p (ContinuousLinearMap.id ℝ (Lp F p (μ.restrict Ω))) :=
  (WeakDerivStep.smulRightW1pL v).comp
    (WeakDerivStep.toW1pL _ Complex.reCLM) +
  (WeakDerivStep.smulRightW1pL (Complex.I • v)).comp
    (WeakDerivStep.toW1pL _ Complex.imCLM)

/-- Rank-one reconstruction has the expected coefficient value. -/
@[simp]
theorem prev_smulRightComplexL (Ω : Opens E) (v : F) (u : WeakDerivStep μ Ω p
  (ContinuousLinearMap.id ℝ (Lp ℂ p (μ.restrict Ω)))) :
    WeakDerivStep.prev _ (smulRightComplexL Ω v u) =
      (ContinuousLinearMap.toSpanSingleton ℂ v).compLpL p (μ.restrict (Ω : Set E))
        (WeakDerivStep.prev _ u) := by
  rw [smulRightComplexL]
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  rw [← WeakDerivStep.prevL_apply, map_add]
  simp only [WeakDerivStep.prevL_apply, WeakDerivStep.prev_smulRightW1pL,
    WeakDerivStep.value_toW1pL, ContinuousLinearMap.id_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
    ((ContinuousLinearMap.toSpanSingleton ℝ v).compLpL p (μ.restrict (Ω : Set E))
      (Complex.reCLM.compLpL p (μ.restrict (Ω : Set E)) (WeakDerivStep.prev _ u)))
    ((ContinuousLinearMap.toSpanSingleton ℝ (Complex.I • v)).compLpL p
      (μ.restrict (Ω : Set E))
      (Complex.imCLM.compLpL p (μ.restrict (Ω : Set E)) (WeakDerivStep.prev _ u))),
    (ContinuousLinearMap.toSpanSingleton ℝ v).coeFn_compLpL
      (Complex.reCLM.compLpL p (μ.restrict (Ω : Set E)) (WeakDerivStep.prev _ u)),
    (ContinuousLinearMap.toSpanSingleton ℝ (Complex.I • v)).coeFn_compLpL
      (Complex.imCLM.compLpL p (μ.restrict (Ω : Set E)) (WeakDerivStep.prev _ u)),
    Complex.reCLM.coeFn_compLpL (WeakDerivStep.prev _ u),
    Complex.imCLM.coeFn_compLpL (WeakDerivStep.prev _ u),
    (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLpL (WeakDerivStep.prev _ u)]
      with x hadd hreal himag hr hi hc
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hreal, himag, hr, hi, hc]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, Complex.re_smul_add_im_smul]

/-- The line reconstruction also composes the weak derivative. -/
theorem weakFDeriv_smulRightComplexL_ae (Ω : Opens E) (v : F) (u : WeakDerivStep μ Ω p
  (ContinuousLinearMap.id ℝ (Lp ℂ p (μ.restrict Ω)))) :
    WeakDerivStep.weakFDeriv _ (smulRightComplexL Ω v u) =ᵐ[μ.restrict (Ω : Set E)]
      fun x ↦ ((ContinuousLinearMap.toSpanSingleton ℂ v).restrictScalars ℝ).comp
        (WeakDerivStep.weakFDeriv _ u x) := by
  have hu := (WeakDerivStep.hasWeakFDerivOn_base_prev _ u).clm_comp
    ((ContinuousLinearMap.toSpanSingleton ℂ v).restrictScalars ℝ)
  simp only [ContinuousLinearMap.id_apply] at hu
  have hv := (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLpL
    (WeakDerivStep.prev _ u)
  rw [← prev_smulRightComplexL Ω v u] at hv
  have hl := WeakDerivStep.hasWeakFDerivOn_base_prev _ (smulRightComplexL Ω v u)
  simp only [ContinuousLinearMap.id_apply] at hl
  exact hl.ae_eq (hu.congr_ae hv.symm)

end ComplexLine

end TauCeti.WeakDerivStep

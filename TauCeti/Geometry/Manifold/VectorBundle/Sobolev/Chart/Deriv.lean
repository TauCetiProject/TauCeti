/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv

/-!
# The weak derivative of the chart data of a Sobolev tuple

Let `C : TauCeti.SectionChartData E F S` be chart data reading sections as `F`-valued functions
on open subsets of a finite-dimensional real inner product space `E`. The chart data in chart `i`
of a tuple `w` of scalar Sobolev functions of order `k + 1` are weakly differentiable, and their
weak derivative is an `E →L[ℝ] F`-valued function whose components, in the basis
`Module.finBasis ℝ (E →L[ℝ] F)`, are Sobolev functions of order `k`
(`TauCeti.SectionChartData.chartDerivDataL`). They are combinations, with constant coefficients,
of the weak directional derivatives `TauCeti.Wkp.lineDerivL` of the components of `w` along the
vectors of `Module.finBasis ℝ E`.

At order one, the weak derivative is `TauCeti.SectionChartData.chartDerivL`, an `Lᵖ` function
assembled from the weak gradients of the components
(`TauCeti.SectionChartData.hasWeakFDerivOn_chartValueL`); the components constructed at order
`k + 1` record that it has `k` further weak derivatives
(`TauCeti.SectionChartData.sum_value_chartDerivDataL_zero_ae_eq_chartDerivL`).

## Main definitions

* `TauCeti.SectionChartData.chartDerivL`: the weak derivative of the chart data in chart `i` of a
  tuple of order one, as an `Lᵖ` function.
* `TauCeti.SectionChartData.chartDerivDataL`: the components of the weak derivative of the chart
  data in chart `i` of a tuple of order `k + 1`, as Sobolev functions of order `k`.

## Main results

* `TauCeti.SectionChartData.hasWeakFDerivOn_chartValueL`: `chartDerivL` is a weak derivative of
  the chart data of an order-one tuple.
* `TauCeti.SectionChartData.norm_le_mul_norm_chartValueL_add_norm_chartDerivL`: the `W^{1,p}` norm
  of a chart component of an order-one tuple is controlled by the chart data and their weak
  derivative.
* `TauCeti.SectionChartData.hasWeakFDerivOn_chartValueL_chartDerivDataL`: the function assembled
  from these components is a weak derivative of the chart data, and
  `TauCeti.SectionChartData.eq_chartDerivDataL_of_hasWeakFDerivOn`: any order-`k` components
  assembling to a weak derivative of the chart data are these.
* `TauCeti.SectionChartData.sum_value_chartDerivDataL_zero_ae_eq_chartDerivL`: at order one the
  assembled function is `chartDerivL`.
* `TauCeti.SectionChartData.lowerOrderL_chartDerivDataL`: the components commute with forgetting
  the highest weak derivative.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped ENNReal

universe u

namespace TauCeti

namespace SectionChartData

section ChartDeriv

/-! ### The weak derivative of the chart data of an order-one tuple -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {S : Type*} [AddCommGroup S] [Module ℝ S] (C : SectionChartData E F S)
  (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The weak derivative of the chart data in chart `i` of a tuple of order-one Sobolev functions:
the `Lᵖ` field `y ↦ ∑ j, ⟪∇ (w i j) y, ·⟫ • bⱼ` assembled from the weak gradients of the chart-`i`
components of `w`, where `b` is the basis `Module.finBasis ℝ F`
(`TauCeti.SectionChartData.hasWeakFDerivOn_chartValueL`). -/
def chartDerivL (i : Fin C.n) :
    C.SobolevData μ p 1 →L[ℝ] Lp (E →L[ℝ] F) p (μ.restrict (C.image i)) :=
  ∑ j, ((((StrongDual.smulRightL ℝ E F).flip (finBasis ℝ F j)).comp
      (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)).compLpL p _).comp
    ((Wkp.iteratedGradientL 0).comp ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (finrank ℝ F) ↦ Wkp μ (C.image i) p 1) j).comp
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun i : Fin C.n ↦ ∀ _ : Fin (finrank ℝ F), Wkp μ (C.image i) p 1) i)))

/-- Almost everywhere on the image of chart `i`, `chartDerivL` is the sum over the basis vectors
`bⱼ` of `F` of the weak gradients of the chart-`i` components, paired with `bⱼ`. -/
theorem chartDerivL_apply_ae (i : Fin C.n) (w : C.SobolevData μ p 1) :
    ∀ᵐ y ∂μ.restrict (C.image i), C.chartDerivL μ p i w y =
      ∑ j, (innerSL ℝ (W1p.gradient (w i j) y)).smulRight (finBasis ℝ F j) := by
  set L : Fin (finrank ℝ F) → E →L[ℝ] E →L[ℝ] F := fun j ↦
    ((StrongDual.smulRightL ℝ E F).flip (finBasis ℝ F j)).comp
      (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
  have heq : C.chartDerivL μ p i w =
      ∑ j, (L j).compLpL p _ (Wkp.iteratedGradientL 0 (w i j)) := by
    simp only [chartDerivL, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.proj_apply, L]
  have hsum := Lp.coeFn_finsetSum (μ := μ.restrict (C.image i)) (p := p) Finset.univ fun j ↦
    (L j).compLpL p _ (Wkp.iteratedGradientL 0 (w i j))
  have hj (j : Fin (finrank ℝ F)) := ContinuousLinearMap.coeFn_compLpL (p := p)
    (μ := μ.restrict (C.image i)) (L j) (Wkp.iteratedGradientL 0 (w i j))
  filter_upwards [hsum, ae_all_iff.2 hj] with y hy hy'
  rw [heq, hy, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hy' j, Wkp.iteratedGradientL_apply, Wkp.iteratedGradient_zero]
  ext v
  simp [L]

/-- **Weak differentiability of the chart data.** The chart data in chart `i` of a tuple of
order-one Sobolev functions have weak derivative `chartDerivL` on the image of chart `i`. -/
theorem hasWeakFDerivOn_chartValueL (i : Fin C.n) (w : C.SobolevData μ p 1) :
    HasWeakFDerivOn μ (C.image i) (C.chartValueL μ p 1 i w) (C.chartDerivL μ p i w) := by
  have hsum := HasWeakFDerivOn.sum Finset.univ fun j _ ↦
    (Wkp.hasWeakFDerivOn_value (w i j)).clm_comp
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j))
  refine (hsum.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [C.chartValueL_apply_ae μ p 1 i w] with y hy
    simp [hy]
  · filter_upwards [C.chartDerivL_apply_ae μ p i w] with y hy
    rw [hy]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ext v
    simp

/-- **The components are controlled by the chart data and their derivative.** The `W^{1,p}` norm of
the `j`-th chart-`i` component of an order-one tuple is at most the norm of the `j`-th coordinate
functional of `Module.finBasis ℝ F` times the sum of the `Lᵖ` norms of the chart data and of their
weak derivative. -/
theorem norm_le_mul_norm_chartValueL_add_norm_chartDerivL (i : Fin C.n)
    (w : C.SobolevData μ p 1) (j : Fin (finrank ℝ F)) :
    ‖w i j‖ ≤ ‖LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)‖ *
      (‖C.chartValueL μ p 1 i w‖ + ‖C.chartDerivL μ p i w‖) := by
  set c := LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)
  have hv : ‖W1p.value (w i j)‖ ≤ ‖c‖ * ‖C.chartValueL μ p 1 i w‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [C.chartValueL_apply_ae μ p 1 i w] with y hy
    have : c (C.chartValueL μ p 1 i w y) = W1p.value (w i j) y := by
      rw [hy]
      simp [c, Finsupp.single_apply]
    rw [← this]
    exact c.le_opNorm _
  have hg : ‖W1p.gradient (w i j)‖ ≤ ‖c‖ * ‖C.chartDerivL μ p i w‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [C.chartDerivL_apply_ae μ p i w] with y hy
    have : c.comp (C.chartDerivL μ p i w y) = innerSL ℝ (W1p.gradient (w i j) y) := by
      rw [hy]
      ext v
      simp [c, Finsupp.single_apply]
    rw [← innerSL_apply_norm ℝ, ← this]
    exact c.opNorm_comp_le _
  calc ‖w i j‖ ≤ ‖W1p.value (w i j)‖ + ‖W1p.gradient (w i j)‖ :=
        W1p.norm_le_norm_value_add_norm_gradient _
    _ ≤ ‖c‖ * (‖C.chartValueL μ p 1 i w‖ + ‖C.chartDerivL μ p i w‖) := by
        rw [mul_add]
        exact add_le_add hv hg

end ChartDeriv

section HigherOrder

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {S : Type*} [AddCommGroup S] [Module ℝ S] (C : SectionChartData E F S)
  (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- The operator `v ↦ eₘ*(v) • bⱼ`, for the `m`th coordinate functional `eₘ*` of the basis
`Module.finBasis ℝ E` and the `j`th vector `bⱼ` of the basis `Module.finBasis ℝ F`: the vector
`(j, m)` of Mathlib's basis `Basis.linearMap` of `E →ₗ[ℝ] F`. -/
private def coordSMulRight (m : Fin (finrank ℝ E)) (j : Fin (finrank ℝ F)) : E →L[ℝ] F :=
  LinearMap.toContinuousLinearMap ((finBasis ℝ E).linearMap (finBasis ℝ F) (j, m))

/-- The components of the weak derivative of the chart data in chart `i` of a tuple `w` of
Sobolev functions of order `k + 1`, in the basis `Module.finBasis ℝ (E →L[ℝ] F)`, as Sobolev
functions of order `k`. Almost everywhere, the derivative at `y` sends a direction `v` to
`∑ₘ ∑ⱼ (∂ₘ(w i j)(y) * eₘ*(v)) • bⱼ`, where `∂ₘ` is the weak directional derivative along the `m`th
vector of `Module.finBasis ℝ E`, `eₘ*` the corresponding coordinate functional and `bⱼ` the `j`th
vector of `Module.finBasis ℝ F`
(`TauCeti.SectionChartData.hasWeakFDerivOn_chartValueL_chartDerivDataL`). -/
def chartDerivDataL (i : Fin C.n) :
    C.SobolevData μ p (k + 1) →L[ℝ] (Fin (finrank ℝ (E →L[ℝ] F)) → Wkp μ (C.image i) p k) :=
  ContinuousLinearMap.pi fun a ↦ ∑ m, ∑ j,
    (finBasis ℝ (E →L[ℝ] F)).repr (coordSMulRight m j) a •
      (Wkp.lineDerivL (finBasis ℝ E m) k).comp ((ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (finrank ℝ F) ↦ Wkp μ (C.image i) p (k + 1)) j).comp
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun i : Fin C.n ↦ ∀ _ : Fin (finrank ℝ F), Wkp μ (C.image i) p (k + 1)) i))

/-- Almost everywhere on the image of chart `i`, the function assembled from the components
`chartDerivDataL` sends `v` at `y` to `∑ₘ ∑ⱼ (∂ₘ(w i j)(y) * eₘ*(v)) • bⱼ`. -/
private theorem sum_value_chartDerivDataL_ae (i : Fin C.n) (w : C.SobolevData μ p (k + 1)) :
    ∀ᵐ y ∂μ.restrict (C.image i),
      ∑ a, Wkp.value k (C.chartDerivDataL μ p k i w a) y • finBasis ℝ (E →L[ℝ] F) a =
        ∑ m, ∑ j, Wkp.value k (Wkp.lineDerivL (finBasis ℝ E m) k (w i j)) y •
          coordSMulRight m j := by
  set d : Fin (finrank ℝ E) → Fin (finrank ℝ F) → Wkp μ (C.image i) p k :=
    fun m j ↦ Wkp.lineDerivL (finBasis ℝ E m) k (w i j)
  set r : Fin (finrank ℝ (E →L[ℝ] F)) → Fin (finrank ℝ E) → Fin (finrank ℝ F) → ℝ :=
    fun a m j ↦ (finBasis ℝ (E →L[ℝ] F)).repr (coordSMulRight m j) a
  have happly (a : Fin (finrank ℝ (E →L[ℝ] F))) :
      C.chartDerivDataL μ p k i w a = ∑ m, ∑ j, r a m j • d m j := by
    simp [chartDerivDataL, r, d]
  have houter (a : Fin (finrank ℝ (E →L[ℝ] F))) :=
    Wkp.value_finsetSum_ae k Finset.univ fun m ↦ ∑ j, r a m j • d m j
  have hinner (a : Fin (finrank ℝ (E →L[ℝ] F))) (m : Fin (finrank ℝ E)) :=
    Wkp.value_finsetSum_ae k Finset.univ fun j ↦ r a m j • d m j
  have hsmul (a : Fin (finrank ℝ (E →L[ℝ] F))) (m : Fin (finrank ℝ E))
      (j : Fin (finrank ℝ F)) := Wkp.value_smul_ae k (r a m j) (d m j)
  filter_upwards [ae_all_iff.2 houter, ae_all_iff.2 fun a ↦ ae_all_iff.2 (hinner a),
    ae_all_iff.2 fun a ↦ ae_all_iff.2 fun m ↦ ae_all_iff.2 (hsmul a m)] with y h₁ h₂ h₃
  have hval (a : Fin (finrank ℝ (E →L[ℝ] F))) :
      Wkp.value k (C.chartDerivDataL μ p k i w a) y =
        ∑ m, ∑ j, r a m j * Wkp.value k (d m j) y := by
    rw [happly, h₁]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [h₂]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [h₃, Pi.smul_apply, smul_eq_mul]
  simp_rw [hval, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_congr rfl fun a _ ↦ smul_comm (r a m j) (Wkp.value k (d m j) y) _,
    ← Finset.smul_sum]
  exact congrArg _ ((finBasis ℝ (E →L[ℝ] F)).sum_repr (coordSMulRight m j))

/-- **The weak derivative of the chart data of a higher-order tuple.** The chart data in chart `i`
of a tuple `w` of Sobolev functions of order `k + 1` have, as a weak derivative on the image of
chart `i`, the function whose components in the basis `Module.finBasis ℝ (E →L[ℝ] F)` are the
values of the order-`k` Sobolev functions `chartDerivDataL`. -/
theorem hasWeakFDerivOn_chartValueL_chartDerivDataL (i : Fin C.n)
    (w : C.SobolevData μ p (k + 1)) :
    HasWeakFDerivOn μ (C.image i) (C.chartValueL μ p (k + 1) i w) fun y ↦
      ∑ a, Wkp.value k (C.chartDerivDataL μ p k i w a) y • finBasis ℝ (E →L[ℝ] F) a := by
  have hu : LocallyIntegrableOn (C.chartValueL μ p (k + 1) i w) (C.image i) μ :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (C.chartValueL μ p (k + 1) i w)).locallyIntegrable Fact.out)
  refine HasWeakFDerivOn.congr_ae_deriv ?_
    ((C.sum_value_chartDerivDataL_ae μ p k i w).mono fun _ h ↦ h.symm)
  refine (finBasis ℝ E).hasWeakFDerivOn_of_forall hu fun m ↦ ?_
  have hsum := HasWeakLineDerivOn.sum Finset.univ fun j _ ↦
    (Wkp.hasWeakLineDerivOn_lineDerivL (finBasis ℝ E m) k (w i j)).clm_comp
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j))
  refine (hsum.congr_ae ?_).congr_ae_deriv (Filter.Eventually.of_forall fun y ↦ ?_)
  · filter_upwards [C.chartValueL_apply_ae μ p (k + 1) i w] with y hy
    simp [hy]
  · simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
      FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, coordSMulRight, LinearMap.coe_toContinuousLinearMap',
      Basis.linearMap_apply_apply, smul_ite, smul_zero]
    rw [Finset.sum_comm]
    simp

/-- **Uniqueness of the components of the weak derivative.** Sobolev functions of order `k` whose
assembled function is a weak derivative of the chart data in chart `i` are the components
`chartDerivDataL`, since weak derivatives are unique almost everywhere. -/
theorem eq_chartDerivDataL_of_hasWeakFDerivOn (i : Fin C.n) (w : C.SobolevData μ p (k + 1))
    (v : Fin (finrank ℝ (E →L[ℝ] F)) → Wkp μ (C.image i) p k)
    (hv : HasWeakFDerivOn μ (C.image i) (C.chartValueL μ p (k + 1) i w) fun y ↦
      ∑ a, Wkp.value k (v a) y • finBasis ℝ (E →L[ℝ] F) a) :
    v = C.chartDerivDataL μ p k i w := by
  funext a
  refine Wkp.ext k (Lp.ext ?_)
  filter_upwards [hv.ae_eq (C.hasWeakFDerivOn_chartValueL_chartDerivDataL μ p k i w)] with y hy
  simpa [Finsupp.single_apply] using congrArg (fun L ↦ (finBasis ℝ (E →L[ℝ] F)).repr L a) hy

/-- **Agreement at order one.** Almost everywhere on the image of chart `i`, the function
assembled from the order-zero components `chartDerivDataL` of an order-one tuple is the order-one
weak derivative `chartDerivL`. -/
theorem sum_value_chartDerivDataL_zero_ae_eq_chartDerivL (i : Fin C.n)
    (w : C.SobolevData μ p 1) :
    (fun y ↦ ∑ a, Wkp.value 0 (C.chartDerivDataL μ p 0 i w a) y • finBasis ℝ (E →L[ℝ] F) a)
      =ᵐ[μ.restrict (C.image i)] C.chartDerivL μ p i w :=
  (C.hasWeakFDerivOn_chartValueL_chartDerivDataL μ p 0 i w).ae_eq
    (C.hasWeakFDerivOn_chartValueL μ p i w)

/-- **Compatibility with the order.** Forgetting the highest weak derivative of the components
`chartDerivDataL` of a tuple of order `k + 2` gives the components of the tuple regarded as one of
order `k + 1`. -/
theorem lowerOrderL_chartDerivDataL (i : Fin C.n) (w : C.SobolevData μ p (k + 1 + 1))
    (a : Fin (finrank ℝ (E →L[ℝ] F))) :
    Wkp.lowerOrderL k (C.chartDerivDataL μ p (k + 1) i w a) =
      C.chartDerivDataL μ p k i (fun i j ↦ Wkp.lowerOrderL (k + 1) (w i j)) a := by
  refine congrFun (C.eq_chartDerivDataL_of_hasWeakFDerivOn μ p k i
    (fun i j ↦ Wkp.lowerOrderL (k + 1) (w i j))
    (fun a ↦ Wkp.lowerOrderL k (C.chartDerivDataL μ p (k + 1) i w a)) ?_) a
  rw [chartValueL_lowerOrderL]
  convert C.hasWeakFDerivOn_chartValueL_chartDerivDataL μ p (k + 1) i w using 3 with y
  rw [Wkp.lowerOrderL_apply, ← Wkp.value_succ]

end HigherOrder

end SectionChartData

end TauCeti

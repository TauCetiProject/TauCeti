/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic

/-!
# The weak derivative of the chart data of a higher-order Sobolev tuple

Let `C : TauCeti.SectionChartData E F S` be chart data reading sections as `F`-valued functions
on open subsets of a finite-dimensional real inner product space `E`. The chart data in chart `i`
of a tuple `w` of scalar Sobolev functions of order `k + 1` are weakly differentiable, and their
weak derivative is an `E →L[ℝ] F`-valued function whose components, in the basis
`Module.finBasis ℝ (E →L[ℝ] F)`, are Sobolev functions of order `k`
(`TauCeti.SectionChartData.chartDerivDataL`). They are combinations, with constant coefficients,
of the weak directional derivatives `TauCeti.Wkp.lineDerivL` of the components of `w` along the
vectors of `Module.finBasis ℝ E`.

At order one, the same weak derivative is `TauCeti.SectionChartData.chartDerivL`, an `Lᵖ`
function; the components constructed here record that it has `k` further weak derivatives.

## Main definitions

* `TauCeti.SectionChartData.chartDerivDataL`: the components of the weak derivative of the chart
  data in chart `i` of a tuple of order `k + 1`, as Sobolev functions of order `k`.

## Main results

* `TauCeti.SectionChartData.hasWeakFDerivOn_chartValueL_chartDerivDataL`: the function assembled
  from these components is a weak derivative of the chart data.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped ENNReal

universe u

namespace TauCeti

namespace SectionChartData

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {S : Type*} [AddCommGroup S] [Module ℝ S] (C : SectionChartData E F S)
  (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- The operator `v ↦ eₘ*(v) • bⱼ`, for the `m`th coordinate functional `eₘ*` of the basis
`Module.finBasis ℝ E` and the `j`th vector `bⱼ` of the basis `Module.finBasis ℝ F`. -/
private def coordSMulRight (m : Fin (finrank ℝ E)) (j : Fin (finrank ℝ F)) : E →L[ℝ] F :=
  (LinearMap.toContinuousLinearMap ((finBasis ℝ E).coord m)).smulRight (finBasis ℝ F j)

/-- The components of the weak derivative of the chart data in chart `i` of a tuple `w` of
Sobolev functions of order `k + 1`, in the basis `Module.finBasis ℝ (E →L[ℝ] F)`, as Sobolev
functions of order `k`. The derivative is `∑ₘ ∑ⱼ eₘ* • ∂ₘ (w i j) • bⱼ`, where `∂ₘ` is the weak
directional derivative along the `m`th vector of `Module.finBasis ℝ E`, `eₘ*` the corresponding
coordinate functional and `bⱼ` the `j`th vector of `Module.finBasis ℝ F`
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
`chartDerivDataL` is `∑ₘ ∑ⱼ ∂ₘ (w i j) • eₘ* • bⱼ`. -/
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
      Pi.smul_apply, coordSMulRight, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply,
      Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul, zero_smul, smul_ite, smul_zero]
    rw [Finset.sum_comm]
    simp

end SectionChartData

end TauCeti

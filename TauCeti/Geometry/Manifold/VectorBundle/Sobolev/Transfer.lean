/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.Wkp.SmoothCoefficients
public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Transfer
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic

/-!
# Transfer of chart data of Sobolev sections between charts

Let `M` be a smooth manifold without boundary modelled on a finite-dimensional real inner product
space `E`, let `V → M` be a smooth real vector bundle with finite-dimensional model fibre `F`, and
let `A` be a finite bundle atlas. This file compares the chart data of an element of `W^{k,p}(V)`,
for `1 ≤ p < ∞`, in two charts.

On an open set `P` of chart-`i` coordinates with compact closure inside the open set
`A.transferDomain i j`, where chart `j` and both bundle charts are defined, the chart coordinate
change `(A.chart i).symm ≫ₕ A.chart j` is a change of variables of order `k` in the sense of
`TauCeti.Wkp.IsChangeOfVariables` as soon as `M` is `C^(max k 1)`, and the coordinate change of
the bundle is a smooth operator-valued coefficient. The continuous linear map
`TauCeti.FiniteBundleAtlas.transferL` sends chart-`j` data on an open set `Q` containing the image
of `P` under the chart coordinate change to chart-`i` data on `P`: it precomposes with the chart
coordinate change and then multiplies by the coordinate change of the bundle
(`TauCeti.Wkp.contDiffOnOperatorSMulL`). If `P` lies in the overlap of the two chart domains and
`Q ⊆ A.image j`, the chart-`i` data of an element of `W^{k,p}(V)` restricted to `P` are the
transfer of its chart-`j` data restricted to `Q`
(`TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`).

## Main definitions

* `TauCeti.FiniteBundleAtlas.transferL`: the transfer of chart-`j` data to chart-`i` data.

## Main results

* `TauCeti.FiniteBundleAtlas.exists_isChangeOfVariables_coordChange`: chart coordinate changes are
  changes of variables of every order on relatively compact subsets of the transfer domain.
* `TauCeti.FiniteBundleAtlas.value_transferL_ae`, `TauCeti.FiniteBundleAtlas.eq_transferL_iff`:
  the components of a transfer are those of the bundle coordinate change applied to the
  precomposed input values, and this characterizes the transfer.
* `TauCeti.FiniteBundleAtlas.lowerOrder_transferL`: transfer commutes with forgetting the highest
  weak derivative.
* `TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`: chart data of a Sobolev section are
  transferred between charts.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace TauCeti

section ChangeOfVariables

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {M : Type*}
  [TopologicalSpace M] [ChartedSpace E M] {F : Type*} [TopologicalSpace F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] (A : FiniteBundleAtlas E M F V)

namespace FiniteBundleAtlas

/-- **Chart coordinate changes are changes of variables.** On a `C^(max k 1)` manifold, on an open
set `P` with compact closure inside the transfer domain, the coordinate change from chart `i` to
chart `j` is a change of variables of order `k` from `P` into any open set containing its image. -/
theorem exists_isChangeOfVariables_coordChange (k : ℕ) [IsManifold 𝓘(ℝ, E) (max k 1 : ℕ) M]
    {i j : Fin A.n} {P Q : Opens E}
    (hPc : IsCompact (closure (P : Set E))) (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart i).symm ≫ₕ A.chart j) P Q) :
    ∃ L c, Wkp.IsChangeOfVariables k P Q ((A.chart i).symm ≫ₕ A.chart j) L c := by
  have hn : (1 : WithTop ℕ∞) ≤ (max k 1 : ℕ) := by exact_mod_cast le_max_right k 1
  have : IsManifold 𝓘(ℝ, E) 1 M := IsManifold.of_le hn
  have hPO := hPD.trans (transferDomain_subset_source A i j)
  exact Wkp.exists_isChangeOfVariables_of_isCompact_closure
    ((A.chart i).symm ≫ₕ A.chart j).open_source
    (contDiffOn_chartAt_coordChange (A.center i) (A.center j))
    (by exact_mod_cast le_max_left k 1) hn
    (((A.chart i).symm ≫ₕ A.chart j).injOn.mono (subset_closure.trans hPO))
    (fun x hx ↦ det_fderiv_chartAt_coordChange_ne_zero (hPO hx)) hPc hPO hPQ

end FiniteBundleAtlas

end ChangeOfVariables

section Sobolev

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {M : Type*}
  [TopologicalSpace M] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] (A : FiniteBundleAtlas E M F V)

variable [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]

variable (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

namespace FiniteBundleAtlas

/-- **Transfer of chart data.** For `1 ≤ p < ∞`, an open set `P` of chart-`i` coordinates with
compact closure in the transfer domain, and an open set `Q` containing the image of `P` under the
chart coordinate change `(A.chart i).symm ≫ₕ A.chart j`, the continuous linear map sending
chart-`j` components `u` on `Q` to the chart-`i` components on `P` of
`y ↦ g y (u (A.chart j ((A.chart i).symm y)))`, where `g` is the coordinate change from bundle
chart `j` to bundle chart `i`. The chart data of a
Sobolev section are related by this map (`TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`). -/
def transferL (hp : p ≠ ⊤) (i j : Fin A.n) {P Q : Opens E}
    (hPc : IsCompact (closure (P : Set E))) (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart i).symm ≫ₕ A.chart j) P Q) :
    (Fin (finrank ℝ F) → Wkp μ Q p k) →L[ℝ] (Fin (finrank ℝ F) → Wkp μ P p k) :=
  (Wkp.contDiffOnOperatorSMulL (A.isOpen_transferDomain i j).uniqueDiffOn hPc hPD k (finBasis ℝ F)
      (finBasis ℝ F) (A.contDiffOn_coordChangeL_transferDomain i j)).comp
    (ContinuousLinearMap.piMap fun _ ↦ Wkp.compL
      (A.exists_isChangeOfVariables_coordChange k hPc hPD hPQ).choose_spec.choose_spec hp)

/-- The chart-`i` components of a transfer are, almost everywhere on `P`, the components of the
coordinate change from bundle chart `j` to bundle chart `i` applied to the vector whose components
are the values of the input at the image of the point under the chart coordinate change. -/
theorem value_transferL_ae (hp : p ≠ ⊤) (i j : Fin A.n) {P Q : Opens E}
    (hPc : IsCompact (closure (P : Set E))) (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart i).symm ≫ₕ A.chart j) P Q) (u : Fin (finrank ℝ F) → Wkp μ Q p k)
    (m : Fin (finrank ℝ F)) :
    (Wkp.value k (A.transferL μ p k hp i j hPc hPD hPQ u m) : E → ℝ) =ᵐ[μ.restrict P]
      fun y ↦ (finBasis ℝ F).repr ((A.triv j).coordChangeL ℝ (A.triv i) ((A.chart i).symm y)
        (∑ l, Wkp.value k (u l) (((A.chart i).symm ≫ₕ A.chart j) y) • finBasis ℝ F l)) m := by
  set h := (A.exists_isChangeOfVariables_coordChange k hPc hPD hPQ).choose_spec.choose_spec
  filter_upwards [Wkp.value_contDiffOnOperatorSMulL_ae (A.isOpen_transferDomain i j).uniqueDiffOn
      hPc hPD k
      (finBasis ℝ F) (finBasis ℝ F) (A.contDiffOn_coordChangeL_transferDomain i j)
      ((ContinuousLinearMap.piMap fun _ ↦ Wkp.compL h hp) u) m,
    ae_all_iff.2 fun l ↦ Wkp.value_compL_ae h hp (u l)] with y hy hl
  rw [transferL, ContinuousLinearMap.comp_apply, hy]
  simp only [ContinuousLinearMap.coe_piMap', Pi.map_apply, hl, ContinuousLinearEquiv.coe_coe]

/-- A transfer is characterized by its components: `v` is the transfer of `u` exactly when the
components of `v` are, almost everywhere on `P`, those described in
`TauCeti.FiniteBundleAtlas.value_transferL_ae`. -/
theorem eq_transferL_iff (hp : p ≠ ⊤) (i j : Fin A.n) {P Q : Opens E}
    (hPc : IsCompact (closure (P : Set E))) (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart i).symm ≫ₕ A.chart j) P Q) (u : Fin (finrank ℝ F) → Wkp μ Q p k)
    (v : Fin (finrank ℝ F) → Wkp μ P p k) :
    v = A.transferL μ p k hp i j hPc hPD hPQ u ↔ ∀ m,
      (Wkp.value k (v m) : E → ℝ) =ᵐ[μ.restrict P]
        fun y ↦ (finBasis ℝ F).repr ((A.triv j).coordChangeL ℝ (A.triv i) ((A.chart i).symm y)
          (∑ l, Wkp.value k (u l) (((A.chart i).symm ≫ₕ A.chart j) y) • finBasis ℝ F l)) m := by
  refine ⟨fun hv m ↦ hv ▸ A.value_transferL_ae μ p k hp i j hPc hPD hPQ u m, fun hv ↦ ?_⟩
  funext m
  exact Wkp.ext k (Lp.ext ((hv m).trans (A.value_transferL_ae μ p k hp i j hPc hPD hPQ u m).symm))

/-- Transfer commutes with forgetting the highest weak derivative. -/
theorem lowerOrder_transferL (hp : p ≠ ⊤) (i j : Fin A.n) {P Q : Opens E}
    (hPc : IsCompact (closure (P : Set E))) (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart i).symm ≫ₕ A.chart j) P Q)
    (u : Fin (finrank ℝ F) → Wkp μ Q p (k + 1)) :
    (fun m ↦ Wkp.lowerOrder k (A.transferL μ p (k + 1) hp i j hPc hPD hPQ u m)) =
      A.transferL μ p k hp i j hPc hPD hPQ fun l ↦ Wkp.lowerOrder k (u l) := by
  refine (A.eq_transferL_iff μ p k hp i j hPc hPD hPQ _ _).2 fun m ↦ ?_
  simp only [← Wkp.value_succ]
  exact A.value_transferL_ae μ p (k + 1) hp i j hPc hPD hPQ u m

/-- **Chart data of Sobolev sections are transferred between charts.** Let `1 ≤ p < ∞`. If `P`
lies in the overlap of the domains of charts `j` and `i` (read in chart `i`) and has compact
closure in the transfer domain, and `Q ⊆ A.image j` contains the image of `P` under the chart
coordinate change `(A.chart i).symm ≫ₕ A.chart j`, then the chart-`i` components of an element of
`W^{k,p}(V)` restricted to `P` are the transfer of its chart-`j` components restricted to `Q`. -/
theorem restrictL_eq_transferL (hp : p ≠ ⊤) {w : A.sectionChartData.SobolevData μ p k}
    (hw : w ∈ A.sectionChartData.sobolevSections μ p k) {i j : Fin A.n} {P Q : Opens E}
    (hP : (P : Set E) ⊆ A.overlap j i) (hPc : IsCompact (closure (P : Set E)))
    (hPD : closure (P : Set E) ⊆ A.transferDomain i j) (hQ : Q ≤ A.image j)
    (hPQ : MapsTo ((A.chart i).symm ≫ₕ A.chart j) P Q) :
    (fun m ↦ Wkp.restrictL (SetLike.coe_subset_coe.1 (hP.trans (A.overlap_subset_image j i))) k
        (w i m)) =
      A.transferL μ p k hp i j hPc hPD hPQ fun l ↦ Wkp.restrictL hQ k (w j l) := by
  set h := (A.exists_isChangeOfVariables_coordChange k hPc hPD hPQ).choose_spec.choose_spec
  have hPi : P ≤ A.image i := SetLike.coe_subset_coe.1 (hP.trans (A.overlap_subset_image j i))
  funext m
  refine Wkp.ext k (Lp.ext ?_)
  have hcompat := ae_restrict_of_ae_restrict_of_subset hP
    ((SectionChartData.compatible_iff _ _ _ _).1
      (SectionChartData.compatible_of_mem (A.aeTransition_sectionChartData μ) hw j i))
  have htr : ∀ y ∈ (P : Set E), A.transition j i y = ((A.chart i).symm ≫ₕ A.chart j) y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := A.mem_overlap.1 (hP hy)
    rw [A.transition_chart hx.2, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      (A.chart i).left_inv (A.dom_subset_chart_source i hx.2)]
  have hi := ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hPi)
    (A.sectionChartData.chartValueL_apply_ae μ p k i w)
  have hj : ∀ᵐ y ∂μ.restrict P,
      A.sectionChartData.chartValueL μ p k j w (((A.chart i).symm ≫ₕ A.chart j) y) =
        ∑ l, Wkp.value k (w j l) (((A.chart i).symm ≫ₕ A.chart j) y) • finBasis ℝ F l :=
    h.ae_comp (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hQ)
      (A.sectionChartData.chartValueL_apply_ae μ p k j w))
  have hres : ∀ᵐ y ∂μ.restrict P, ∀ l, Wkp.value k (Wkp.restrictL hQ k (w j l))
      (((A.chart i).symm ≫ₕ A.chart j) y) =
        Wkp.value k (w j l) (((A.chart i).symm ≫ₕ A.chart j) y) :=
    h.ae_comp (ae_all_iff.2 fun l ↦ Wkp.value_restrictL_ae hQ k (w j l))
  filter_upwards [Wkp.value_restrictL_ae hPi k (w i m), hcompat, hi, hj, hres,
    A.value_transferL_ae μ p k hp i j hPc hPD hPQ (fun l ↦ Wkp.restrictL hQ k (w j l)) m,
    ae_restrict_mem P.isOpen.measurableSet] with y hy₁ hy₂ hy₃ hy₄ hy₅ hy₆ hyP
  rw [A.sectionChartData_coordChange_of_mem (hP hyP),
    A.sectionChartData_transition_of_mem (hP hyP), htr y hyP] at hy₂
  have hval : Wkp.value k (w i m) y =
      (finBasis ℝ F).repr (A.sectionChartData.chartValueL μ p k i w y) m := by
    rw [hy₃, (finBasis ℝ F).repr_sum_self]
  refine hy₁.trans ((hval.trans ?_).trans hy₆.symm)
  rw [hy₂, hy₄]
  simp only [hy₅, ContinuousLinearEquiv.coe_coe]

end FiniteBundleAtlas

end Sobolev

end TauCeti

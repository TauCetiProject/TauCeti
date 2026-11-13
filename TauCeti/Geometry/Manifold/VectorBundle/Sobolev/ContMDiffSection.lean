/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Sobolev.Wkp.Classical

/-!
# `Cᵏ` sections are Sobolev sections

Let `M` be a `Cᵏ` manifold without boundary modelled on a finite-dimensional real inner product
space `E`, let `V → M` be a `Cᵏ` real vector bundle with finite-dimensional model fibre `F`, and let
`A` be a finite bundle atlas. This file shows that every `Cᵏ` section of `V` defines an element of
the Sobolev space `W^{k,p}(V)` of `TauCeti.SobolevSection`, for every `1 ≤ p ≤ ∞`, and that the
resulting linear map `TauCeti.SobolevSection.ofContMDiffSection` is injective, with norm bounded
by the `Lᵖ` norms of the classical derivatives of the chart components. These are the smooth
elements of the Sobolev scale of sections.

In chart `i` a `Cᵏ` section `s` is read as the `F`-valued function `A.coord i s`, which is `Cᵏ` on
the open set of points whose preimage lies in the base set of the bundle chart
(`TauCeti.FiniteBundleAtlas.contDiffOn_coord`). This open set contains the compact set
`chart i '' closure (dom i)`, so the derivatives of the components of `A.coord i s` through order
`k` are bounded on `A.image i`, and the components lie in `W^{k,p}(A.image i)`
(`TauCeti.Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact`). The resulting tuple consists of
the components of `s` (`TauCeti.SectionChartData.ofComponents`).

## Main definitions

* `TauCeti.SobolevSection.ofContMDiffSection`: the linear map from `Cᵏ` sections of `V` to
  `W^{k,p}(V)`.

## Main results

* `TauCeti.SobolevSection.chartValueL_ofContMDiffSection_ae`: the chart data are the chart
  coordinates of the section.
* `TauCeti.SobolevSection.norm_ofContMDiffSection_le`: the Sobolev norm is bounded by the `Lᵖ`
  norms of the classical derivatives of the chart components.
* `TauCeti.SobolevSection.ofContMDiffSection_injective`: distinct `Cᵏ` sections give distinct
  Sobolev sections.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton (1989), Chapter III, §2.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal

universe u

namespace TauCeti

open FiniteBundleAtlas

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V) (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (k : ℕ)

namespace SobolevSection

variable [IsManifold 𝓘(ℝ, E) k M] [ContMDiffVectorBundle k F V 𝓘(ℝ, E)]

/-- The component of the chart coordinates of a `Cᵏ` section along the `j`th vector of the basis
`Module.finBasis ℝ F` is a `W^{k,p}` function on the image of chart `i`. -/
private theorem exists_value_ae_eq_coord (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) (i : Fin A.n)
    (j : Fin (finrank ℝ F)) :
    ∃ w : Wkp μ (A.image i) p k, (Wkp.value k w : E → ℝ) =ᵐ[μ.restrict (A.image i)]
      fun y ↦ (finBasis ℝ F).coord j (A.sectionChartData.coord i s y) := by
  obtain ⟨w, hw⟩ := Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact k
    ((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet)
    ((LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)).contDiff.comp_contDiffOn
      (A.contDiffOn_coord s.contMDiff i))
    (A.isCompact_chart_image_closure_dom i) (A.image_subset_chart_image_closure_dom i)
    (A.chart_image_closure_dom_subset i) (mu := μ) (p := p)
  exact ⟨w, hw.trans ((A.sectionChartData_coord_ae_eq μ i s).fun_comp _).symm⟩

/-- **`Cᵏ` sections are Sobolev sections.** The linear map sending a `Cᵏ` section `s` of `V` to the
element of `W^{k,p}(V)` whose components in chart `i` are the components of `A.coord i s` in the
basis `Module.finBasis ℝ F`. -/
def ofContMDiffSection : Cₛ^k⟮𝓘(ℝ, E); F, V⟯ →ₗ[ℝ] SobolevSection A μ p k :=
  A.sectionChartData.ofComponents μ p k
    { toFun := fun s ↦ s, map_add' := ContMDiffSection.coe_add,
      map_smul' := ContMDiffSection.coe_smul }
    (exists_value_ae_eq_coord A μ p k)

/-- The chart data in chart `i` of the Sobolev section of a `Cᵏ` section `s` are the chart
coordinates `A.coord i s`, almost everywhere on the image of the chart. -/
theorem chartValueL_ofContMDiffSection_ae (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i (ofContMDiffSection A μ p k s)
      =ᵐ[μ.restrict (A.image i)] A.coord i s :=
  (A.sectionChartData.chartValueL_ofComponents_ae μ p k _ _ s i).trans
    (A.sectionChartData_coord_ae_eq μ i s)

/-- **Norm bound.** The norm of the Sobolev section of a `Cᵏ` section `s` is at most the sum, over
all charts `i` and basis vectors `j`, of the `Lᵖ` norms on `A.image i` of the classical derivatives
of orders `0` through `k` of the components of `A.coord i s`. -/
theorem norm_ofContMDiffSection_le (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) :
    ‖ofContMDiffSection A μ p k s‖ ≤ ∑ i, ∑ j, ∑ l ∈ Finset.range (k + 1),
      lpNorm (iteratedFDeriv ℝ l fun y ↦ (finBasis ℝ F).coord j (A.coord i s y)) p
        (μ.restrict (A.image i)) :=
  A.sectionChartData.norm_le_sum_of_norm_le μ p k fun i j ↦
    Wkp.norm_le_sum_lpNorm_iteratedFDeriv_of_contDiffOn k _
      (((LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)).contDiff.comp_contDiffOn
        (A.contDiffOn_coord s.contMDiff i)).mono
          ((A.image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i)))
      ((A.sectionChartData.value_ofComponents_ae μ p k _ _ s i j).trans
        ((A.sectionChartData_coord_ae_eq μ i s).fun_comp _))

/-- **Injectivity.** A `Cᵏ` section whose Sobolev section vanishes is zero: its chart coordinates
are continuous and vanish almost everywhere on the open chart images, hence everywhere there. -/
theorem ofContMDiffSection_injective : Function.Injective (ofContMDiffSection A μ p k) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs ↦ ContMDiffSection.ext fun x ↦ ?_
  obtain ⟨i, hx⟩ := A.exists_mem_dom x
  have hO := A.chart_image_closure_dom_subset i
  have hcont : ContinuousOn (A.coord i s) (A.image i) :=
    ((A.contDiffOn_coord s.contMDiff i).continuousOn).mono
      ((A.image_subset_chart_image_closure_dom i).trans hO)
  have hae : A.coord i s =ᵐ[μ.restrict (A.image i)] 0 :=
    (A.sectionChartData_coord_ae_eq μ i s).symm.trans
      (A.sectionChartData.coord_ae_eq_zero_of_ofComponents_eq_zero μ p k _ _ hs i)
  have hzero := Measure.eqOn_open_of_ae_eq hae (A.image i).isOpen hcont continuousOn_const
    (A.mem_image.2 ⟨x, hx, rfl⟩)
  rw [A.coord_chart s hx] at hzero
  have hb := A.dom_subset_baseSet i hx
  rw [ContMDiffSection.coe_zero, Pi.zero_apply,
    ← ((A.triv i).continuousLinearEquivAt ℝ x hb).map_eq_zero_iff]
  exact hzero

end SobolevSection

end TauCeti

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
(`TauCeti.Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact`). The chart data of the resulting
tuple are `A.coord i s` (`TauCeti.SobolevSection.chartValueL_ofContMDiffSection_ae`), so the tuple
consists of the components of `s`.

## Main definitions

* `TauCeti.SobolevSection.ofContMDiffSection`: the linear map from `Cᵏ` sections of `V` to
  `W^{k,p}(V)`.

## Main results

* `TauCeti.SobolevSection.value_ofContMDiffSection_ae`,
  `TauCeti.SobolevSection.chartValueL_ofContMDiffSection_ae`: the components and the chart data of
  the Sobolev section of `s` are those of `s`.
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
      fun y ↦ (finBasis ℝ F).coord j (A.coord i s y) :=
  Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact k
    ((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet)
    ((LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)).contDiff.comp_contDiffOn
      (A.contDiffOn_coord s.contMDiff i))
    (A.isCompact_chart_image_closure_dom i) (A.image_subset_chart_image_closure_dom i)
    (A.chart_image_closure_dom_subset i)

/-- The tuple of chartwise `W^{k,p}` components of a `Cᵏ` section. -/
private def toSobolevData (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) : SobolevData A μ p k :=
  fun i j ↦ (exists_value_ae_eq_coord A μ p k s i j).choose

private theorem value_toSobolevData_ae (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) (i : Fin A.n)
    (j : Fin (finrank ℝ F)) :
    (Wkp.value k (toSobolevData A μ p k s i j) : E → ℝ) =ᵐ[μ.restrict (A.image i)]
      fun y ↦ (finBasis ℝ F).coord j (A.coord i s y) :=
  (exists_value_ae_eq_coord A μ p k s i j).choose_spec

private theorem chartValueL_toSobolevData_ae (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) (i : Fin A.n) :
    A.chartValueL μ p k i (toSobolevData A μ p k s) =ᵐ[μ.restrict (A.image i)] A.coord i s := by
  filter_upwards [A.chartValueL_apply_ae μ p k i (toSobolevData A μ p k s),
    ae_all_iff.2 (value_toSobolevData_ae A μ p k s i)] with y hy hj
  rw [hy]
  simp_rw [hj, Basis.coord_apply]
  exact (finBasis ℝ F).sum_repr _

/-- **`Cᵏ` sections are Sobolev sections.** The linear map sending a `Cᵏ` section `s` of `V` to the
element of `W^{k,p}(V)` whose components in chart `i` are the components of `A.coord i s` in the
basis `Module.finBasis ℝ F`. -/
def ofContMDiffSection : Cₛ^k⟮𝓘(ℝ, E); F, V⟯ →ₗ[ℝ] SobolevSection A μ p k where
  toFun s := ⟨toSobolevData A μ p k s,
    (mem_sobolevSections_iff A μ p k).2 ⟨s, chartValueL_toSobolevData_ae A μ p k s⟩⟩
  map_add' s t := ext A μ p k fun i j ↦ Lp.ext <| by
    filter_upwards [value_toSobolevData_ae A μ p k (s + t) i j,
      value_toSobolevData_ae A μ p k s i j, value_toSobolevData_ae A μ p k t i j,
      Wkp.value_add k (toSobolevData A μ p k s i j) (toSobolevData A μ p k t i j) ▸
        Lp.coeFn_add _ _, ae_restrict_mem (A.image i).isOpen.measurableSet]
      with y h h₁ h₂ hadd hy
    simp only [Submodule.coe_add, Pi.add_apply] at hadd ⊢
    rw [h, hadd, h₁, h₂, ContMDiffSection.coe_add, A.coord_add i s t hy, map_add]
  map_smul' c s := ext A μ p k fun i j ↦ Lp.ext <| by
    filter_upwards [value_toSobolevData_ae A μ p k (c • s) i j,
      value_toSobolevData_ae A μ p k s i j,
      Wkp.value_smul k c (toSobolevData A μ p k s i j) ▸ Lp.coeFn_smul _ _,
      ae_restrict_mem (A.image i).isOpen.measurableSet] with y h h₁ hsmul hy
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply] at hsmul ⊢
    rw [h, hsmul, h₁, ContMDiffSection.coe_smul, A.coord_smul i c s hy, map_smul,
      smul_eq_mul]

/-- The components in chart `i` of the Sobolev section of a `Cᵏ` section `s` are the components
of `A.coord i s` in the basis `Module.finBasis ℝ F`, almost everywhere on the image of the chart. -/
theorem value_ofContMDiffSection_ae (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) (i : Fin A.n)
    (j : Fin (finrank ℝ F)) :
    (Wkp.value k ((ofContMDiffSection A μ p k s : SobolevData A μ p k) i j) : E → ℝ)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ (finBasis ℝ F).coord j (A.coord i s y) :=
  value_toSobolevData_ae A μ p k s i j

/-- The chart data in chart `i` of the Sobolev section of a `Cᵏ` section `s` are the coordinates
`A.coord i s`, almost everywhere on the image of the chart. -/
theorem chartValueL_ofContMDiffSection_ae (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) (i : Fin A.n) :
    A.chartValueL μ p k i (ofContMDiffSection A μ p k s) =ᵐ[μ.restrict (A.image i)]
      A.coord i s :=
  chartValueL_toSobolevData_ae A μ p k s i

/-- **Norm bound.** The norm of the Sobolev section of a `Cᵏ` section `s` is at most the sum, over
all charts `i` and basis vectors `j`, of the `Lᵖ` norms on `A.image i` of the classical derivatives
of orders `0` through `k` of the components of `A.coord i s`. -/
theorem norm_ofContMDiffSection_le (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) :
    ‖ofContMDiffSection A μ p k s‖ ≤ ∑ i, ∑ j, ∑ l ∈ Finset.range (k + 1),
      lpNorm (iteratedFDeriv ℝ l fun y ↦ (finBasis ℝ F).coord j (A.coord i s y)) p
        (μ.restrict (A.image i)) := by
  have hcomp (i : Fin A.n) (j : Fin (finrank ℝ F)) :
      ‖(ofContMDiffSection A μ p k s : SobolevData A μ p k) i j‖ ≤
        ∑ l ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ l
          fun y ↦ (finBasis ℝ F).coord j (A.coord i s y)) p (μ.restrict (A.image i)) :=
    Wkp.norm_le_sum_lpNorm_iteratedFDeriv_of_contDiffOn k _
      (((LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)).contDiff.comp_contDiffOn
        (A.contDiffOn_coord s.contMDiff i)).mono
          ((A.image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i)))
      (value_ofContMDiffSection_ae A μ p k s i j)
  have hnonneg (i : Fin A.n) (j : Fin (finrank ℝ F)) :
      0 ≤ ∑ l ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ l
        fun y ↦ (finBasis ℝ F).coord j (A.coord i s y)) p (μ.restrict (A.image i)) :=
    Finset.sum_nonneg fun _ _ ↦ lpNorm_nonneg
  -- The norm of a tuple is the maximum of the component norms, bounded by their sum.
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ ↦
    Finset.sum_nonneg fun j _ ↦ hnonneg i j)).2 fun i ↦ ?_
  refine ((pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ ↦ hnonneg i j)).2 fun j ↦
    (hcomp i j).trans (Finset.single_le_sum (fun j _ ↦ hnonneg i j) (Finset.mem_univ j))).trans
      (Finset.single_le_sum (f := fun i ↦ ∑ j, ∑ l ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv
        ℝ l fun y ↦ (finBasis ℝ F).coord j (A.coord i s y)) p (μ.restrict (A.image i)))
        (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnonneg i j) (Finset.mem_univ i))

/-- **Injectivity.** A `Cᵏ` section whose Sobolev section vanishes is zero: its chart coordinates
are continuous and vanish almost everywhere on the open chart images, hence everywhere there. -/
theorem ofContMDiffSection_injective : Function.Injective (ofContMDiffSection A μ p k) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs ↦ ContMDiffSection.ext fun x ↦ ?_
  obtain ⟨i, hx⟩ := A.exists_mem_dom x
  have hO := A.chart_image_closure_dom_subset i
  have hcont : ContinuousOn (A.coord i s) (A.image i) :=
    ((A.contDiffOn_coord s.contMDiff i).continuousOn).mono
      ((A.image_subset_chart_image_closure_dom i).trans hO)
  -- The chart data of the zero tuple vanish, so `A.coord i s` vanishes almost everywhere.
  have h0 : A.chartValueL μ p k i (ofContMDiffSection A μ p k s : SobolevData A μ p k) = 0 := by
    rw [hs, ZeroMemClass.coe_zero, map_zero]
  have hz := Lp.coeFn_zero F p (μ.restrict (A.image i))
  rw [← h0] at hz
  have hae : A.coord i s =ᵐ[μ.restrict (A.image i)] fun _ ↦ 0 :=
    (chartValueL_ofContMDiffSection_ae A μ p k s i).symm.trans hz
  have hzero := Measure.eqOn_open_of_ae_eq hae (A.image i).isOpen hcont continuousOn_const
    (A.mem_image.2 ⟨x, hx, rfl⟩)
  rw [A.coord_chart s hx] at hzero
  have hb := A.dom_subset_baseSet i hx
  rw [ContMDiffSection.coe_zero, Pi.zero_apply,
    ← ((A.triv i).continuousLinearEquivAt ℝ x hb).map_eq_zero_iff]
  exact hzero

end SobolevSection

end TauCeti

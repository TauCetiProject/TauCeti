/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic
public import TauCeti.Analysis.Sobolev.Local.Norm
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Sobolev.Local.Norm.ContDiff
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

* `TauCeti.SobolevSection.lowerOrdersL_ofContMDiffSection`: lowering the order preserves
  the underlying smooth section.
* `TauCeti.SobolevSection.chartValueL_ofContMDiffSection_ae`: the chart data are the chart
  coordinates of the section.
* `TauCeti.SobolevSection.norm_ofContMDiffSection_le`: the Sobolev norm is bounded by the `Lᵖ`
  norms of the classical derivatives of the chart components.
* `TauCeti.SobolevSection.ofContMDiffSection_injective`: distinct `Cᵏ` sections give distinct
  Sobolev sections.
* `TauCeti.SectionChartData.exists_eLpNormWkp_le_of_chartValueL_ae_eq`,
  `TauCeti.SectionChartData.exists_ofReal_norm_le_eLpNormWkp_of_chartValueL_ae_eq`: for planar
  charts, the norm of the chart-`i` components of a tuple whose chart data agree with a `Cᵏ`
  function `f` is comparable with the `W^{k,p}` norm of `f`.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton (1989), Chapter III, §2.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal NNReal

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
          (A.image_subset_target_inter_preimage_baseSet i))
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

/-- Lowering the Sobolev order preserves the underlying smooth section. -/
theorem lowerOrdersL_ofContMDiffSection (d : ℕ)
    [IsManifold 𝓘(ℝ, E) (k + d : ℕ) M] [ContMDiffVectorBundle (k + d : ℕ) F V 𝓘(ℝ, E)]
    (s : Cₛ^(k + d : ℕ)⟮𝓘(ℝ, E); F, V⟯) :
    A.sectionChartData.lowerOrdersL μ p k d (ofContMDiffSection A μ p (k + d) s) =
      ofContMDiffSection A μ p k
        ⟨s, s.contMDiff.of_le (by exact_mod_cast Nat.le_add_right k d)⟩ := by
  apply SobolevSection.eq_of_ae_eq_coord (s := s)
  · intro i
    rw [SectionChartData.chartValueL_lowerOrdersL]
    exact chartValueL_ofContMDiffSection_ae A μ p (k + d) s i
  · exact fun i ↦ chartValueL_ofContMDiffSection_ae A μ p k
      ⟨s, s.contMDiff.of_le (by exact_mod_cast Nat.le_add_right k d)⟩ i

end SobolevSection

/-! ### Chart data of `Cᵏ` readings on planar charts -/

namespace SectionChartData

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S] (C : SectionChartData ℂ F S)
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- The `j`th coordinate of `Module.finBasis ℝ F`, as a continuous linear map. -/
private def coordL (j : Fin (finrank ℝ F)) : F →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)

/-- The components of a tuple whose chart data in chart `i` agree with `f` are the coordinates of
`f`. -/
private theorem value_ae_eq_coordL {w : C.SobolevData volume p k} {i : Fin C.n} {f : ℂ → F}
    (hw : C.chartValueL volume p k i w =ᵐ[volume.restrict (C.image i)] f)
    (j : Fin (finrank ℝ F)) :
    (Wkp.value k (w i j) : ℂ → ℝ) =ᵐ[volume.restrict (C.image i)] fun y ↦ coordL j (f y) := by
  filter_upwards [C.chartValueL_apply_ae volume p k i w, hw] with y hy hy'
  rw [← hy', hy]
  simp only [coordL, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply,
    Basis.repr_sum_self]

/-- **`W^{k,p}` size of a `Cᵏ` reading.** If the chart data in chart `i` of a tuple agree almost
everywhere with a function `f` that is `Cᵏ` on the image of the chart, the `W^{k,p}` norm of `f`
on the image is bounded by a constant multiple of the norm of the chart-`i` components. -/
theorem exists_eLpNormWkp_le_of_chartValueL_ae_eq (k : ℕ) :
    ∃ c : ℝ≥0, ∀ {w : C.SobolevData volume p k} {i : Fin C.n} {f : ℂ → F},
      ContDiffOn ℝ k f (C.image i) →
      C.chartValueL volume p k i w =ᵐ[volume.restrict (C.image i)] f →
      eLpNormWkp p (C.image i) k f ≤ c * ENNReal.ofReal ‖w i‖ := by
  refine ⟨(k + 1) * ∑ j, ‖finBasis ℝ F j‖₊, fun {w i f} hf hw ↦ ?_⟩
  set U := C.image i
  set L : Fin (finrank ℝ F) → ℝ →L[ℝ] F :=
    fun j ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j)
  have hsum : f = ∑ j, fun y ↦ L j (coordL j (f y)) := by
    funext y
    simp [L, coordL, Finset.sum_apply, Basis.coord_apply, (finBasis ℝ F).sum_repr]
  have hj (j : Fin (finrank ℝ F)) :
      eLpNormWkp p U k (fun y ↦ coordL j (f y)) ≤ (k + 1 : ℝ≥0∞) * ENNReal.ofReal ‖w i‖ := by
    have hg : ContDiffOn ℝ k (fun y ↦ coordL j (f y)) U :=
      (coordL j).contDiff.comp_contDiffOn hf
    have hv := C.value_ae_eq_coordL hw j
    rw [eLpNormWkp_eq_sum_eLpNorm_iteratedFDeriv U.isOpen k hg]
    calc ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l fun y ↦ coordL j (f y)) p
          (volume.restrict U)
        ≤ ∑ _l ∈ Finset.range (k + 1), ENNReal.ofReal ‖w i‖ := by
          refine Finset.sum_le_sum fun l hl ↦ ?_
          have hl : l ≤ k := Finset.mem_range_succ_iff.1 hl
          rw [← ENNReal.ofReal_toReal
            (Wkp.memLp_iteratedFDeriv_of_contDiffOn k (w i j) hg hv l hl).eLpNorm_ne_top]
          exact ENNReal.ofReal_le_ofReal
            ((Wkp.lpNorm_iteratedFDeriv_le_of_contDiffOn k (w i j) hg hv l hl).trans
              (norm_le_pi_norm (w i) j))
      _ = (k + 1 : ℝ≥0∞) * ENNReal.ofReal ‖w i‖ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  calc eLpNormWkp p U k f = eLpNormWkp p U k (∑ j, fun y ↦ L j (coordL j (f y))) := by
        rw [← hsum]
    _ ≤ ∑ j, eLpNormWkp p U k (fun y ↦ L j (coordL j (f y))) :=
        eLpNormWkp_sum_le (Fact.out : 1 ≤ p)
    _ ≤ ∑ j, ‖L j‖ₑ * ((k + 1 : ℝ≥0∞) * ENNReal.ofReal ‖w i‖) :=
        Finset.sum_le_sum fun j _ ↦ (eLpNormWkp_clm_comp_le (L j)).trans (by gcongr; exact hj j)
    _ ≤ ∑ j, (‖finBasis ℝ F j‖₊ : ℝ≥0∞) * ((k + 1 : ℝ≥0∞) * ENNReal.ofReal ‖w i‖) := by
        gcongr with j
        rw [eNorm_eq_nnNorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm]
        simp [L, ContinuousLinearMap.norm_smulRight_apply]
    _ = ((k + 1 : ℝ≥0) * ∑ j, ‖finBasis ℝ F j‖₊ : ℝ≥0) * ENNReal.ofReal ‖w i‖ := by
        rw [← Finset.sum_mul]
        push_cast
        ring

/-- **Components from a `Cᵏ` reading.** If the chart data in chart `i` of a tuple agree almost
everywhere with a function `f` that is `Cᵏ` on the image of the chart, the norm of the chart-`i`
components is bounded by a constant multiple of the `W^{k,p}` norm of `f` on the image. -/
theorem exists_ofReal_norm_le_eLpNormWkp_of_chartValueL_ae_eq (k : ℕ) :
    ∃ c : ℝ≥0, ∀ {w : C.SobolevData volume p k} {i : Fin C.n} {f : ℂ → F},
      ContDiffOn ℝ k f (C.image i) →
      C.chartValueL volume p k i w =ᵐ[volume.restrict (C.image i)] f →
      ENNReal.ofReal ‖w i‖ ≤ c * eLpNormWkp p (C.image i) k f := by
  refine ⟨∑ j, ‖coordL (F := F) j‖₊, fun {w i f} hf hw ↦ ?_⟩
  set U := C.image i
  have hj (j : Fin (finrank ℝ F)) :
      ENNReal.ofReal ‖w i j‖ ≤ ‖coordL (F := F) j‖ₑ * eLpNormWkp p U k f := by
    have hg : ContDiffOn ℝ k (fun y ↦ coordL j (f y)) U :=
      (coordL j).contDiff.comp_contDiffOn hf
    have hv := C.value_ae_eq_coordL hw j
    refine le_trans ?_ (eLpNormWkp_clm_comp_le (coordL j))
    rw [eLpNormWkp_eq_sum_eLpNorm_iteratedFDeriv U.isOpen k hg]
    refine (ENNReal.ofReal_le_ofReal
      (Wkp.norm_le_sum_lpNorm_iteratedFDeriv_of_contDiffOn k (w i j) hg hv)).trans ?_
    simp only [← toReal_eLpNorm]
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ ENNReal.toReal_nonneg]
    exact Finset.sum_le_sum fun l _ ↦ ENNReal.ofReal_toReal_le
  have hpi : ‖w i‖ ≤ ∑ j, ‖w i j‖ :=
    (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).2 fun j ↦
      Finset.single_le_sum (f := fun j ↦ ‖w i j‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j)
  calc ENNReal.ofReal ‖w i‖ ≤ ENNReal.ofReal (∑ j, ‖w i j‖) := ENNReal.ofReal_le_ofReal hpi
    _ = ∑ j, ENNReal.ofReal ‖w i j‖ :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ norm_nonneg _
    _ ≤ ∑ j, ‖coordL (F := F) j‖ₑ * eLpNormWkp p U k f := Finset.sum_le_sum fun j _ ↦ hj j
    _ = _ := by
        simp [eNorm_eq_nnNorm, ← Finset.sum_mul, U]

end SectionChartData

end TauCeti

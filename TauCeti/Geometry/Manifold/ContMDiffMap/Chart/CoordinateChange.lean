/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Seminorm
import TauCeti.Analysis.Calculus.ContDiff.Bounds

/-!
# Compact chart seminorms under coordinate changes

On a compact set contained in the overlap of two charts of the maximal atlas, the
coordinate derivatives through order `k` in the first chart are bounded by a constant
times any bound on those in the second chart at the transformed points
(`ContMDiffMap.exists_norm_iteratedFDerivWithin_comp_extend_symm_le`). For preferred
charts this says that the compact `C^k` seminorm in either chart is bounded by a constant
times the seminorm in the other chart on a compact set containing the transformed
coordinates. The constant is independent of the vector-valued map. This is the
coordinate-change estimate used in comparing fixed-support smooth test topologies and in
reading strong Whitney neighbourhoods in arbitrary charts; it requires no global bounds
on chart transitions.

Derivatives are taken within extended chart targets. In particular, the estimates
also apply to manifolds with boundary and corners. The compact sets may be empty,
and the coefficient space need not be finite dimensional.

The analytic input is `ContDiffOn.exists_norm_iteratedFDerivWithin_clm_apply_comp_le`,
the compact Leibniz/Faà di Bruno estimate, applied with the identity fibre map.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.1.
-/

public section

open Set Filter Topology IsManifold
open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} [IsManifold I n M]

omit [ChartedSpace H M] [IsManifold I n M] in
/-- On the overlap of two charts, a coordinate derivative in the first chart can be computed
after changing coordinates to the second chart and restricting the derivative domain to the
overlap. No smoothness of the map or of the charts is needed. -/
theorem _root_.TauCeti.iteratedFDerivWithin_comp_extend_symm_eq_extendCoordChange (g : M → F)
    {e e' : OpenPartialHomeomorph M H} {z : E} (hz : z ∈ (I.extendCoordChange e e').source)
    (m : ℕ) :
    iteratedFDerivWithin 𝕜 m (g ∘ (e.extend I).symm) (e.extend I).target z =
      iteratedFDerivWithin 𝕜 m ((g ∘ (e'.extend I).symm) ∘ I.extendCoordChange e e')
        (I.extendCoordChange e e').source z := by
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source, e'.extend_source] at hz ⊢
  -- The overlap is a relative neighborhood, so restricting to it preserves derivatives.
  have hmem : (e.extend I).symm ⁻¹' e'.source ∈ 𝓝[(e.extend I).target] z :=
    (e.continuousOn_extend_symm (I := I) z hz.1).preimage_mem_nhdsWithin
      (e'.open_source.mem_nhds hz.2)
  rw [iteratedFDerivWithin_inter' hmem]
  refine (Filter.EventuallyEq.iteratedFDerivWithin_eq ?_ ?_ m).symm
  · filter_upwards [hmem] with w hw
    exact congrArg g (e'.extend_left_inv hw)
  · exact congrArg g (e'.extend_left_inv hz.2)

/-- On a chart overlap, a coordinate derivative can be computed after changing coordinates
and restricting the derivative domain to the overlap. -/
theorem chartIteratedFDeriv_eq_iteratedFDerivWithin_coordChange
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (x y : M) (m : ℕ) (hm : m ≤ n)
    (z : (extChartAt I x).target)
    (hz : (extChartAt I x).symm z ∈ (extChartAt I y).source) :
    chartIteratedFDeriv f x m hm z =
      iteratedFDerivWithin 𝕜 m
        ((f ∘ (extChartAt I y).symm) ∘ ((extChartAt I x).symm ≫ extChartAt I y))
        ((extChartAt I x).symm ≫ extChartAt I y).source z := by
  rw [chartIteratedFDeriv_self_target_apply]
  simp only [extChartAt] at hz ⊢
  refine TauCeti.iteratedFDerivWithin_comp_extend_symm_eq_extendCoordChange f ?_ m
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
  exact ⟨z.2, hz⟩

omit [IsManifold I n M] in
/-- On a compact subset of the overlap of two charts of the maximal atlas, the coordinate
derivatives through order `k` of a map in the first chart are bounded by a constant multiple of
any common bound on its coordinate derivatives through order `k` in the second chart, taken at
the transformed points. The constant does not depend on the map. -/
theorem exists_norm_iteratedFDerivWithin_comp_extend_symm_le
    {e e' : OpenPartialHomeomorph M H} (he : e ∈ maximalAtlas I n M)
    (he' : e' ∈ maximalAtlas I n M) {K : Set E} (hK : IsCompact K)
    (hKs : K ⊆ (I.extendCoordChange e e').source) (k : ℕ) (hk : k ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (δ : ℝ),
      (∀ i ≤ k, ∀ z ∈ K, ‖iteratedFDerivWithin 𝕜 i (f ∘ (e'.extend I).symm)
        (e'.extend I).target (I.extendCoordChange e e' z)‖ ≤ δ) →
      ∀ i ≤ k, ∀ z ∈ K,
        ‖iteratedFDerivWithin 𝕜 i (f ∘ (e.extend I).symm) (e.extend I).target z‖ ≤ C * δ := by
  set τ := I.extendCoordChange e e'
  have ht : UniqueDiffOn 𝕜 (e'.extend I).target := by
    rw [e'.extend_target]
    exact I.uniqueDiffOn_preimage e'.open_target
  have hτt : MapsTo τ τ.source (e'.extend I).target := fun z hz ↦ by
    have h := τ.map_source hz
    rw [PartialEquiv.trans_target] at h
    exact h.1
  -- One Leibniz/Faà di Bruno constant for each order, applied with the identity fibre map.
  have hb (i : Fin (k + 1)) := ContDiffOn.exists_norm_iteratedFDerivWithin_clm_apply_comp_le
    (n := i) (contDiffOn_const (c := ContinuousLinearMap.id 𝕜 F))
    ((I.contDiffOn_extendCoordChange he he').of_le
      ((Nat.cast_le.mpr (Nat.le_of_lt_succ i.isLt)).trans hk))
    I.uniqueDiffOn_extendCoordChange_source ht hτt hK hKs
  choose C hC using hb
  refine ⟨∑ i, |C i| + 1, by positivity, fun f δ hδ i hi z hz ↦ ?_⟩
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0 (Nat.zero_le k) z hz)
  have hφ : ContDiffOn 𝕜 i (f ∘ (e'.extend I).symm) (e'.extend I).target :=
    (contDiffOn_comp_extend_symm f he').of_le ((Nat.cast_le.mpr hi).trans hk)
  let i' : Fin (k + 1) := ⟨i, by omega⟩
  rw [TauCeti.iteratedFDerivWithin_comp_extend_symm_eq_extendCoordChange f (hKs hz)]
  calc _ ≤ C i' * δ := hC i' _ hφ δ (fun j hj z hz ↦ hδ j (hj.trans hi) z hz) z hz
    _ ≤ |C i'| * δ := by gcongr; exact le_abs_self _
    _ ≤ (∑ j, |C j| + 1) * δ := by
        gcongr
        exact (Finset.single_le_sum (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ i')).trans
          (le_add_of_nonneg_right zero_le_one)

/-- On a compact chart overlap, changing coordinates bounds the `C^k` seminorm by a
constant multiple of the `C^k` seminorm on any compact set containing the transformed
coordinates. The constant does not depend on the map being measured. -/
theorem exists_chartCkSeminorm_le_coordChange
    (x y : M) (K : TopologicalSpace.Compacts (extChartAt I x).target)
    (L : TopologicalSpace.Compacts (extChartAt I y).target)
    (hoverlap : ∀ z ∈ K, (extChartAt I x).symm z ∈ (extChartAt I y).source)
    (himage : ∀ (z : (extChartAt I x).target) (hz : z ∈ K),
      ⟨extChartAt I y ((extChartAt I x).symm z),
        (extChartAt I y).map_source (hoverlap z hz)⟩ ∈ L)
    (k : ℕ) (hk : k ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : C^n⟮I, M; 𝓘(𝕜, F), F⟯,
      chartCkSeminorm x K k hk f ≤ C * chartCkSeminorm y L k hk f := by
  have hKs : Subtype.val '' (K : Set (extChartAt I x).target) ⊆
      (I.extendCoordChange (chartAt H x) (chartAt H y)).source := by
    rintro _ ⟨z, hz, rfl⟩
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact ⟨z.2, hoverlap z hz⟩
  obtain ⟨C, hCpos, hC⟩ := exists_norm_iteratedFDerivWithin_comp_extend_symm_le (F := F)
    (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas y)
    (K.isCompact.image continuous_subtype_val) hKs k hk
  refine ⟨C, hCpos, fun f ↦ ?_⟩
  have hδ := apply_nonneg (chartCkSeminorm (F := F) y L k hk) f
  refine (chartCkSeminorm_le_iff x K k hk f (mul_nonneg hCpos.le hδ)).mpr fun m hm z hz ↦ ?_
  rw [chartIteratedFDeriv_self_target_apply]
  simp only [extChartAt]
  refine hC f _ (fun i hi w hw ↦ ?_) m hm z ⟨z, hz, rfl⟩
  obtain ⟨w, hwK, rfl⟩ := hw
  have hb := (chartCkSeminorm_le_iff y L k hk f hδ).mp le_rfl i hi _ (himage w hwK)
  rw [chartIteratedFDeriv_self_target_apply] at hb
  simp only [extChartAt] at hb
  -- The change of charts is, by definition, the composite of the two extended charts.
  exact hb

/-- A compact set in a chart overlap has a compact coordinate image in the other chart.
The two compact `C^k` seminorms on this same set of manifold points bound one another,
with positive constants independent of the map. The membership equation specifies the
coordinate image exactly, rather than choosing a larger compact neighborhood. -/
theorem exists_chartCkSeminorm_coordChange
    (x y : M) (K : TopologicalSpace.Compacts (extChartAt I x).target)
    (hoverlap : ∀ z ∈ K, (extChartAt I x).symm z ∈ (extChartAt I y).source)
    (k : ℕ) (hk : k ≤ n) :
    ∃ L : TopologicalSpace.Compacts (extChartAt I y).target,
      (∀ w, w ∈ L ↔ ∃ z ∈ K,
        extChartAt I y ((extChartAt I x).symm z) = (w : E)) ∧
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ f : C^n⟮I, M; 𝓘(𝕜, F), F⟯,
        chartCkSeminorm x K k hk f ≤ C * chartCkSeminorm y L k hk f ∧
        chartCkSeminorm y L k hk f ≤ D * chartCkSeminorm x K k hk f := by
  -- Taking the exact compact image supplies both directions, including for empty K.
  let θ : K → (extChartAt I y).target := fun z ↦
    ⟨extChartAt I y ((extChartAt I x).symm z.val),
      (extChartAt I y).map_source (hoverlap z.val z.property)⟩
  have hθ : Continuous θ := by
    apply Continuous.subtype_mk
    exact (continuousOn_extChartAt y).comp_continuous
      ((continuousOn_extChartAt_symm x).comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val) (fun z ↦ z.val.property))
      (fun z ↦ hoverlap z.val z.property)
  let L : TopologicalSpace.Compacts (extChartAt I y).target :=
    ⟨range θ, isCompact_range hθ⟩
  have hL (w : (extChartAt I y).target) : w ∈ L ↔ ∃ z ∈ K,
      extChartAt I y ((extChartAt I x).symm z) = (w : E) := by
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.val, z.property, rfl⟩
    · rintro ⟨z, hz, hzw⟩
      exact ⟨⟨z, hz⟩, Subtype.ext hzw⟩
  have hinv : ∀ w ∈ L, (extChartAt I y).symm w ∈ (extChartAt I x).source := by
    intro w hw
    obtain ⟨z, hz, hzw⟩ := (hL w).mp hw
    rw [← hzw, (extChartAt I y).left_inv (hoverlap z hz)]
    exact (extChartAt I x).map_target z.property
  have hback : ∀ (w : (extChartAt I y).target) (hw : w ∈ L),
      ⟨extChartAt I x ((extChartAt I y).symm w),
        (extChartAt I x).map_source (hinv w hw)⟩ ∈ K := by
    intro w hw
    obtain ⟨z, hz, hzw⟩ := (hL w).mp hw
    have heq : extChartAt I x ((extChartAt I y).symm w) = (z : E) := by
      rw [← hzw, (extChartAt I y).left_inv (hoverlap z hz),
        (extChartAt I x).right_inv z.property]
    have hsub : (⟨extChartAt I x ((extChartAt I y).symm w),
        (extChartAt I x).map_source (hinv w hw)⟩ : (extChartAt I x).target) = z :=
      Subtype.ext heq
    exact hsub.symm ▸ hz
  obtain ⟨C, hCpos, hC⟩ := exists_chartCkSeminorm_le_coordChange
    (F := F) x y K L hoverlap (fun z hz ↦ (hL _).mpr ⟨z, hz, rfl⟩) k hk
  obtain ⟨D, hDpos, hD⟩ := exists_chartCkSeminorm_le_coordChange
    (F := F) y x L K hinv hback k hk
  exact ⟨L, hL, C, D, hCpos, hDpos, fun f ↦ ⟨hC f, hD f⟩⟩

end ContMDiffMap

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

On a compact set contained in the overlap of two source charts, the compact `C^k`
seminorm in either chart is bounded by a constant times the seminorm in the other
chart on a compact set containing the transformed coordinates. The constant is
independent of the vector-valued map. This is the coordinate-change estimate used
in comparing fixed-support smooth test topologies; it requires no global bounds
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
  let τ := (extChartAt I x).symm ≫ extChartAt I y
  have hτs : τ.source = (extChartAt I x).target ∩
      (extChartAt I x).symm ⁻¹' (extChartAt I y).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
  -- The overlap is a relative neighborhood, so restricting to it preserves derivatives.
  have hmem : (extChartAt I x).symm ⁻¹' (extChartAt I y).source ∈
      𝓝[(extChartAt I x).target] (z : E) :=
    (continuousOn_extChartAt_symm (I := I) x (z : E) z.2).preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source y).mem_nhds hz)
  have hset : iteratedFDerivWithin 𝕜 m (f ∘ (extChartAt I x).symm) τ.source z =
      iteratedFDerivWithin 𝕜 m (f ∘ (extChartAt I x).symm)
        (extChartAt I x).target z := by
    rw [hτs]
    exact iteratedFDerivWithin_inter' hmem
  have heq : (f ∘ (extChartAt I y).symm) ∘ τ =ᶠ[𝓝[τ.source] (z : E)]
      f ∘ (extChartAt I x).symm := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hτs, mem_inter_iff] at hw
    exact congrArg f ((extChartAt I y).left_inv hw.2)
  have heqz : ((f ∘ (extChartAt I y).symm) ∘ τ) z =
      (f ∘ (extChartAt I x).symm) z :=
    congrArg f ((extChartAt I y).left_inv hz)
  rw [chartIteratedFDeriv_self_target_apply, ← hset]
  exact (heq.iteratedFDerivWithin_eq heqz m).symm

private theorem exists_chartDerivativeSeminorm_le_coordChange
    (x y : M) (K : TopologicalSpace.Compacts (extChartAt I x).target)
    (L : TopologicalSpace.Compacts (extChartAt I y).target)
    (hoverlap : ∀ z ∈ K, (extChartAt I x).symm z ∈ (extChartAt I y).source)
    (himage : ∀ (z : (extChartAt I x).target) (hz : z ∈ K),
      ⟨extChartAt I y ((extChartAt I x).symm z),
        (extChartAt I y).map_source (hoverlap z hz)⟩ ∈ L)
    (k : ℕ) (hk : k ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : C^n⟮I, M; 𝓘(𝕜, F), F⟯,
      chartDerivativeSeminorm x K k hk f ≤ C * chartCkSeminorm y L k hk f := by
  -- Work on the actual overlap, where the native transition has unique derivatives.
  let τ := (extChartAt I x).symm ≫ extChartAt I y
  have hτs : τ.source = (extChartAt I x).target ∩
      (extChartAt I x).symm ⁻¹' (extChartAt I y).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
  let K' : Set E := Subtype.val '' (K : Set (extChartAt I x).target)
  have hK' : IsCompact K' := K.isCompact.image continuous_subtype_val
  have hKs : K' ⊆ τ.source := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hτs, mem_inter_iff]
    exact ⟨z.2, hoverlap z hz⟩
  have hτ : ContDiffOn 𝕜 k τ τ.source := by
    simpa only [τ, PartialEquiv.coe_trans] using (contDiffOn_ext_coord_change y x).of_le hk
  have hτt : MapsTo τ τ.source (extChartAt I y).target := by
    intro z hz
    rw [hτs, mem_inter_iff] at hz
    exact (extChartAt I y).map_source hz.2
  have hId : ContDiffOn 𝕜 k (fun _ : E ↦ ContinuousLinearMap.id 𝕜 F) τ.source :=
    contDiffOn_const
  obtain ⟨C, hC⟩ := hId.exists_norm_iteratedFDerivWithin_clm_apply_comp_le hτ
      I.uniqueDiffOn_extendCoordChange_source (uniqueDiffOn_extChartAt_target y) hτt hK' hKs
  refine ⟨|C| + 1, by positivity, fun f ↦ ?_⟩
  set δ := chartCkSeminorm y L k hk f
  have hδ : 0 ≤ δ := apply_nonneg _ _
  have hf : ContDiffOn 𝕜 k (f ∘ (extChartAt I y).symm) (extChartAt I y).target :=
    ((f.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt_symm y)).contDiffOn).of_le hk
  have hbound := hC (f ∘ (extChartAt I y).symm) hf δ (by
    intro i hi z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hb := (chartCkSeminorm_le_iff y L k hk f hδ).mp le_rfl i hi _ (himage w hw)
    rw [chartIteratedFDeriv_self_target_apply] at hb
    simpa only [τ, PartialEquiv.coe_trans, Function.comp_apply] using hb)
  refine (chartDerivativeSeminorm_le_iff x K k hk f (mul_nonneg (by positivity) hδ)).mpr
    fun z hz ↦ ?_
  rw [chartIteratedFDeriv_eq_iteratedFDerivWithin_coordChange f x y k hk z (hoverlap z hz)]
  exact (hbound z ⟨z, hz, rfl⟩).trans (by gcongr; exact (le_abs_self C).trans (by linarith))

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
  have hb (i : Fin (k + 1)) := exists_chartDerivativeSeminorm_le_coordChange
    (F := F) x y K L hoverlap himage i
      ((Nat.cast_le.mpr (Nat.le_of_lt_succ i.isLt)).trans hk)
  choose C hCpos hC using hb
  have hsum : 0 < ∑ i, C i := Finset.sum_pos (fun i _ ↦ hCpos i) Finset.univ_nonempty
  refine ⟨∑ i, C i, hsum, fun f ↦ ?_⟩
  refine (chartCkSeminorm_le_iff x K k hk f
    (mul_nonneg hsum.le (apply_nonneg _ _))).mpr fun m hm z hz ↦ ?_
  let i : Fin (k + 1) := ⟨m, by omega⟩
  have hderiv := (chartDerivativeSeminorm_le_iff x K m _ f
    (mul_nonneg (hCpos i).le (apply_nonneg _ _))).mp (hC i f) z hz
  calc _ ≤ C i * chartCkSeminorm y L m _ f := hderiv
       _ ≤ C i * chartCkSeminorm y L k hk f :=
         mul_le_mul_of_nonneg_left (chartCkSeminorm_le_of_le y L hm hk f) (hCpos i).le
       _ ≤ (∑ j, C j) * chartCkSeminorm y L k hk f :=
         mul_le_mul_of_nonneg_right
           (Finset.single_le_sum (fun j _ ↦ (hCpos j).le) (Finset.mem_univ i))
           (apply_nonneg _ _)

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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Holder.Basic
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.CoordinateChange
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Holder.FaaDiBruno

/-!
# Independence of the Hölder spaces `C^{k,α}(M)` from the atlas

Let `M` be a boundaryless `C^{k+1}` manifold over `ℝ` or `ℂ` and `α ≤ 1`. If the `k`th coordinate
derivatives of a vector-valued `C^k` map are `α`-Hölder on a family of coordinate sets whose
relative interiors cover `M`, then its `k`th coordinate derivative in any chart is `α`-Hölder on
every compact subset of the chart target (`ContMDiffMap.MemChartHolder.of_cover`). Near a point,
this is the Hölder chain rule `TauCeti.exists_holderOnWith_iteratedFDerivWithin_comp` for the
transition map, which is `C^{k+1}`; the local Hölder bounds combine on a compact set by a Lebesgue
number argument (`IsCompact.exists_holderOnWith_thickening_and_norm_le`).

Consequently, two compact chart atlases `A` and `B` of `M` define the same Hölder space: a `C^k`
map belongs to `A.CkHolderSpace k α F` exactly when it belongs to `B.CkHolderSpace k α F`
(`TauCeti.CompactChartAtlas.forall_memChartHolder_iff`), and the identity of underlying maps is a
linear equivalence `TauCeti.CompactChartAtlas.CkHolderSpace.atlasLinearEquiv`. When the model
vector space is locally compact and `F` is complete, both spaces are Banach, and the closed graph
theorem makes this equivalence continuous in both directions
(`TauCeti.CompactChartAtlas.CkHolderSpace.atlasEquiv`): the two `C^{k,α}` norms are equivalent
(`TauCeti.CompactChartAtlas.CkHolderSpace.exists_norm_le_and_norm_le`). Thus `C^{k,α}(M, F)` is
a Banach space determined by `M` up to equivalence of norms.

## References

* M. Taylor, *Partial Differential Equations III*, Chapter 13, for Hölder spaces on compact
  manifolds defined through finitely many charts.
-/

public section

open Set Filter Topology IsManifold
open scoped Manifold NNReal

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {k : ℕ} {α : ℝ≥0} [IsManifold I n M] [IsManifold I (k + 1) M]

/-- **Local change of charts for Hölder derivatives.** If the `k`th coordinate derivative of `f`
in the chart at `y` is `α`-Hölder on `K`, and a point `z₀` of the chart target at `x` corresponds
to a point of the relative interior of `K`, then the `k`th coordinate derivative of `f` in the
chart at `x` is `α`-Hölder on a ball around `z₀`. -/
theorem exists_holderOnWith_chartIteratedFDeriv_ball (hα : α ≤ 1) {hk : k ≤ n}
    {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯} {y : M} {K : Set (extChartAt I y).target}
    (hf : MemChartHolder y K k hk α f) (x : M) (z₀ : (extChartAt I x).target)
    (hz₀ : (extChartAt I x).symm z₀ ∈ (extChartAt I y).source)
    (hK : (⟨extChartAt I y ((extChartAt I x).symm z₀), (extChartAt I y).map_source hz₀⟩ :
      (extChartAt I y).target) ∈ interior K) :
    ∃ r > 0, ∃ L : ℝ≥0,
      HolderOnWith L α (chartIteratedFDeriv f x k hk) (Metric.ball z₀ r) := by
  let := IsRCLikeNormedField.rclike 𝕜
  set τ := (extChartAt I x).symm ≫ extChartAt I y with hτ
  have hsrc : τ.source = (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹'
      (extChartAt I y).source := by
    rw [hτ, PartialEquiv.trans_source, PartialEquiv.symm_source]
  have hsopen : IsOpen τ.source := I.isOpen_extendCoordChange_source
  have hz₀s : (z₀ : E) ∈ τ.source := by
    rw [hsrc]
    exact ⟨z₀.property, hz₀⟩
  have hst : MapsTo τ τ.source (extChartAt I y).target := fun z hz ↦ by
    have h := τ.map_source hz
    rw [hτ, PartialEquiv.trans_target] at h
    exact h.1
  -- The Hölder bound in the chart at `y`, on the image of `K` in the model space.
  have hC := (memChartHolder_iff.mp hf).holderWith
  rw [← chartHolderNorm_def] at hC
  have hH : HolderOnWith (chartHolderNorm y K k hk α f) α
      (iteratedFDerivWithin 𝕜 k (f ∘ (extChartAt I y).symm) (extChartAt I y).target)
      (Subtype.val '' K) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    simpa only [ContinuousMap.restrict_apply, chartIteratedFDeriv_self_target_apply,
      Subtype.edist_eq] using hC ⟨p, hp⟩ ⟨q, hq⟩
  have hK' : Subtype.val '' K ∈ 𝓝 (τ z₀) := by
    rw [hτ, PartialEquiv.trans_apply]
    exact (isOpen_extChartAt_target y).isOpenEmbedding_subtypeVal.image_mem_nhds.mpr
      (mem_interior_iff_mem_nhds.mp hK)
  obtain ⟨r, hr, L, hL⟩ := TauCeti.exists_holderOnWith_iteratedFDerivWithin_comp hα
    (hsopen.mem_nhds hz₀s) (isOpen_extChartAt_target y).uniqueDiffOn
    (I.contDiffOn_extendCoordChange (n := k + 1) (chart_mem_maximalAtlas x)
      (chart_mem_maximalAtlas y))
    ((contDiffOn_comp_extend_symm f (chart_mem_maximalAtlas y)).of_le (by exact_mod_cast hk))
    hst (mem_nhdsWithin_of_mem_nhds hK') hH
  -- On a ball inside the chart overlap, the derivative in the chart at `x` is that of the
  -- composite with the transition map.
  obtain ⟨r₀, hr₀, hr₀s⟩ := Metric.isOpen_iff.mp hsopen _ hz₀s
  refine ⟨min r r₀, lt_min hr hr₀, L, fun p hp q hq ↦ ?_⟩
  have hp' : (p : E) ∈ Metric.ball (z₀ : E) (min r r₀) := by
    simpa only [Metric.mem_ball, Subtype.dist_eq] using hp
  have hq' : (q : E) ∈ Metric.ball (z₀ : E) (min r r₀) := by
    simpa only [Metric.mem_ball, Subtype.dist_eq] using hq
  have hps := hr₀s (Metric.ball_subset_ball (min_le_right _ _) hp')
  have hqs := hr₀s (Metric.ball_subset_ball (min_le_right _ _) hq')
  rw [hsrc] at hps hqs
  rw [chartIteratedFDeriv_eq_iteratedFDerivWithin_coordChange f x y k hk p hps.2,
    chartIteratedFDeriv_eq_iteratedFDerivWithin_coordChange f x y k hk q hqs.2,
    Subtype.edist_eq]
  exact hL _ (Metric.ball_subset_ball (min_le_left _ _) hp') _
    (Metric.ball_subset_ball (min_le_left _ _) hq')

/-- **Hölder derivatives in every chart.** If the `k`th coordinate derivatives of `f` are
`α`-Hölder on coordinate sets whose relative interiors cover `M`, then the `k`th coordinate
derivative of `f` in any chart is `α`-Hölder on every compact subset of the chart target. -/
theorem MemChartHolder.of_cover (hα : α ≤ 1) {ι : Type*} {c : ι → M}
    {K : ∀ i, Set (extChartAt I (c i)).target}
    (hK : ∀ y : M, ∃ i, ∃ hy : y ∈ (extChartAt I (c i)).source,
      (⟨extChartAt I (c i) y, (extChartAt I (c i)).map_source hy⟩ :
        (extChartAt I (c i)).target) ∈ interior (K i))
    {hk : k ≤ n} {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯} (hf : ∀ i, MemChartHolder (c i) (K i) k hk α f)
    (x : M) {L : Set (extChartAt I x).target} (hL : IsCompact L) :
    MemChartHolder x L k hk α f := by
  obtain ⟨δ, hδ, C, -, hC, -⟩ := hL.exists_holderOnWith_thickening_and_norm_le
    (f := chartIteratedFDeriv f x k hk) fun z _ ↦ by
      obtain ⟨i, hy, hyK⟩ := hK ((extChartAt I x).symm z)
      exact exists_holderOnWith_chartIteratedFDeriv_ball hα (hf i) x z hy hyK
  exact .of_holderOnWith (hC.mono (Metric.self_subset_thickening hδ L))

end ContMDiffMap

namespace TauCeti

namespace CompactChartAtlas

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (A B : CompactChartAtlas I M)
  {n : WithTop ℕ∞} {k : ℕ} {α : ℝ≥0} {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [IsManifold I (k + 1) M]

/-- **Atlas independence of Hölder membership.** For `α ≤ 1`, a `C^k` map has `α`-Hölder `k`th
coordinate derivatives on the pieces of one compact chart atlas exactly when it has on the pieces
of another. -/
theorem forall_memChartHolder_iff [IsManifold I n M] (hα : α ≤ 1) {hk : k ≤ n}
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    (∀ i, ContMDiffMap.MemChartHolder (A.center i) (A.piece i) k hk α f) ↔
      ∀ j, ContMDiffMap.MemChartHolder (B.center j) (B.piece j) k hk α f :=
  ⟨fun hf j ↦ .of_cover hα A.interior_cover hf _ (B.piece j).isCompact,
    fun hf i ↦ .of_cover hα B.interior_cover hf _ (A.piece i).isCompact⟩

namespace CkHolderSpace

variable [IsManifold I k M]

/-- The `k`th coordinate derivative of an element of `C^{k,α}(M, F)` in any chart is `α`-Hölder
on every compact subset of the chart target, for `α ≤ 1`. -/
theorem memChartHolder_of_isCompact {A : CompactChartAtlas I M} (hα : α ≤ 1)
    (f : A.CkHolderSpace k α F) (x : M) {L : Set (extChartAt I x).target} (hL : IsCompact L) :
    ContMDiffMap.MemChartHolder x L k le_rfl α (toContMDiffMap A k α F f) :=
  .of_cover hα A.interior_cover (memChartHolder f) x hL

variable (k α F)

/-- **The Hölder spaces of two atlases agree.** For `α ≤ 1`, the Hölder spaces `C^{k,α}(M, F)`
of two compact chart atlases consist of the same maps; this is the identity on underlying maps,
as a linear equivalence. -/
noncomputable def atlasLinearEquiv (hα : α ≤ 1) :
    A.CkHolderSpace k α F ≃ₗ[𝕜] B.CkHolderSpace k α F where
  toFun f := mk (toContMDiffMap A k α F f) fun j ↦
    memChartHolder_of_isCompact hα f _ (B.piece j).isCompact
  invFun f := mk (toContMDiffMap B k α F f) fun i ↦
    memChartHolder_of_isCompact hα f _ (A.piece i).isCompact
  map_add' _ _ := ext fun _ ↦ by simp
  map_smul' _ _ := ext fun _ ↦ by simp
  left_inv _ := ext fun _ ↦ by simp
  right_inv _ := ext fun _ ↦ by simp

variable {k α F}

@[simp]
theorem coe_atlasLinearEquiv (hα : α ≤ 1) (f : A.CkHolderSpace k α F) :
    ⇑(atlasLinearEquiv A B k α F hα f) = f := by
  simp [atlasLinearEquiv]

@[simp]
theorem coe_atlasLinearEquiv_symm (hα : α ≤ 1) (f : B.CkHolderSpace k α F) :
    ⇑((atlasLinearEquiv A B k α F hα).symm f) = f :=
  (coe_atlasLinearEquiv A B hα _).symm.trans
    (congrArg _ ((atlasLinearEquiv A B k α F hα).apply_symm_apply f))

@[simp]
theorem toContMDiffMap_atlasLinearEquiv (hα : α ≤ 1) (f : A.CkHolderSpace k α F) :
    toContMDiffMap B k α F (atlasLinearEquiv A B k α F hα f) = toContMDiffMap A k α F f :=
  ContMDiffMap.ext fun y ↦ by simp

@[simp]
theorem toContMDiffMap_atlasLinearEquiv_symm (hα : α ≤ 1) (f : B.CkHolderSpace k α F) :
    toContMDiffMap A k α F ((atlasLinearEquiv A B k α F hα).symm f) =
      toContMDiffMap B k α F f :=
  ContMDiffMap.ext fun y ↦ by simp

/-- The inverse of the identification of the Hölder spaces of `A` and `B` is the identification
of those of `B` and `A`. -/
theorem atlasLinearEquiv_symm (hα : α ≤ 1) :
    (atlasLinearEquiv A B k α F hα).symm = atlasLinearEquiv B A k α F hα :=
  LinearEquiv.ext fun f ↦ ext fun y ↦ by simp

/-- The identification of the Hölder space of an atlas with itself is the identity. -/
@[simp]
theorem atlasLinearEquiv_refl (hα : α ≤ 1) :
    atlasLinearEquiv A A k α F hα = LinearEquiv.refl 𝕜 _ :=
  LinearEquiv.ext fun f ↦ ext fun y ↦ by simp

/-- The identifications of Hölder spaces compose. -/
@[simp]
theorem atlasLinearEquiv_trans (C : CompactChartAtlas I M) (hα : α ≤ 1) :
    (atlasLinearEquiv A B k α F hα).trans (atlasLinearEquiv B C k α F hα) =
      atlasLinearEquiv A C k α F hα :=
  LinearEquiv.ext fun f ↦ ext fun y ↦ by simp

section Complete

variable [LocallyCompactSpace E] [CompleteSpace F]

/-- For `α ≤ 1`, when the model space is locally compact and `F` is complete, the linear
equivalence identifying the Hölder spaces of two compact chart atlases is continuous. -/
theorem continuous_atlasLinearEquiv (hα : α ≤ 1) :
    Continuous (atlasLinearEquiv A B k α F hα) :=
  continuous_of_coe_eq _ (coe_atlasLinearEquiv A B hα)

variable (k α F)

/-- **The canonical Hölder space `C^{k,α}(M, F)`.** For `α ≤ 1`, the Hölder spaces of two compact
chart atlases are the same space of maps with equivalent norms: the identity on underlying maps
is a continuous linear equivalence. -/
noncomputable def atlasEquiv (hα : α ≤ 1) :
    A.CkHolderSpace k α F ≃L[𝕜] B.CkHolderSpace k α F :=
  (atlasLinearEquiv A B k α F hα).toContinuousLinearEquivOfContinuous
    (continuous_atlasLinearEquiv A B hα)

variable {k α F}

@[simp]
theorem coe_atlasEquiv (hα : α ≤ 1) (f : A.CkHolderSpace k α F) :
    ⇑(atlasEquiv A B k α F hα f) = f := by
  simp [atlasEquiv]

@[simp]
theorem toLinearEquiv_atlasEquiv (hα : α ≤ 1) :
    (atlasEquiv A B k α F hα).toLinearEquiv = atlasLinearEquiv A B k α F hα :=
  LinearEquiv.ext fun f ↦ ext fun y ↦ by simp [atlasEquiv]

@[simp]
theorem coe_atlasEquiv_symm (hα : α ≤ 1) (f : B.CkHolderSpace k α F) :
    ⇑((atlasEquiv A B k α F hα).symm f) = f :=
  (coe_atlasEquiv A B hα _).symm.trans
    (congrArg _ ((atlasEquiv A B k α F hα).apply_symm_apply f))

@[simp]
theorem toContMDiffMap_atlasEquiv (hα : α ≤ 1) (f : A.CkHolderSpace k α F) :
    toContMDiffMap B k α F (atlasEquiv A B k α F hα f) = toContMDiffMap A k α F f :=
  ContMDiffMap.ext fun y ↦ by simp

@[simp]
theorem toContMDiffMap_atlasEquiv_symm (hα : α ≤ 1) (f : B.CkHolderSpace k α F) :
    toContMDiffMap A k α F ((atlasEquiv A B k α F hα).symm f) = toContMDiffMap B k α F f :=
  ContMDiffMap.ext fun y ↦ by simp

/-- The inverse of the continuous identification of the Hölder spaces of `A` and `B` is that of
`B` and `A`. -/
theorem atlasEquiv_symm (hα : α ≤ 1) :
    (atlasEquiv A B k α F hα).symm = atlasEquiv B A k α F hα :=
  ContinuousLinearEquiv.ext <| funext fun f ↦ ext fun y ↦ by simp

/-- The continuous identification of the Hölder space of an atlas with itself is the
identity. -/
@[simp]
theorem atlasEquiv_refl (hα : α ≤ 1) :
    atlasEquiv A A k α F hα = ContinuousLinearEquiv.refl 𝕜 _ :=
  ContinuousLinearEquiv.ext <| funext fun f ↦ ext fun y ↦ by simp

/-- The continuous identifications of Hölder spaces compose. -/
@[simp]
theorem atlasEquiv_trans (C : CompactChartAtlas I M) (hα : α ≤ 1) :
    (atlasEquiv A B k α F hα).trans (atlasEquiv B C k α F hα) = atlasEquiv A C k α F hα :=
  ContinuousLinearEquiv.ext <| funext fun f ↦ ext fun y ↦ by simp

/-- **Equivalence of the `C^{k,α}` norms of two atlases.** For `α ≤ 1`, the Hölder norms of two
compact chart atlases bound each other up to a constant factor. -/
theorem exists_norm_le_and_norm_le (hα : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : A.CkHolderSpace k α F,
      ‖atlasEquiv A B k α F hα f‖ ≤ C * ‖f‖ ∧ ‖f‖ ≤ C * ‖atlasEquiv A B k α F hα f‖ := by
  set e := atlasEquiv A B k α F hα
  refine ⟨‖(e : A.CkHolderSpace k α F →L[𝕜] B.CkHolderSpace k α F)‖ +
    ‖(e.symm : B.CkHolderSpace k α F →L[𝕜] A.CkHolderSpace k α F)‖ + 1, by positivity,
    fun f ↦ ⟨(e.toContinuousLinearMap.le_opNorm f).trans ?_, ?_⟩⟩
  · gcongr
    linarith [norm_nonneg (e.symm : B.CkHolderSpace k α F →L[𝕜] A.CkHolderSpace k α F)]
  · calc ‖f‖ = ‖e.symm (e f)‖ := by rw [e.symm_apply_apply]
      _ ≤ ‖(e.symm : B.CkHolderSpace k α F →L[𝕜] A.CkHolderSpace k α F)‖ * ‖e f‖ :=
          e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ _ := by
          gcongr
          linarith [norm_nonneg (e : A.CkHolderSpace k α F →L[𝕜] B.CkHolderSpace k α F)]

end Complete

end CkHolderSpace

end CompactChartAtlas

end TauCeti

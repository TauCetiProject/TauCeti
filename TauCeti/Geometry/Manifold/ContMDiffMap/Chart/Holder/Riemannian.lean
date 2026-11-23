/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Holder.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# Hölder functions for the Riemannian distance lie in `C^{0,α}` of a compact chart atlas

Let `M` be a boundaryless `C¹` manifold with a continuous Riemannian metric whose distance is the
metric of `M`. On a compact subset `K` of an extended chart target, the inverse chart is Lipschitz
from the norm distance of the model space to the Riemannian distance
(`TauCeti.IsRiemannianManifold.exists_lipschitzOnWith_extChartAt_symm_of_isCompact`): it is
Lipschitz near each point of the open chart target, and a locally Lipschitz map is Lipschitz on a
compact set.

Consequently a function `M → F` that is `α`-Hölder for the Riemannian distance is `α`-Hölder in
the coordinates of every piece of a compact chart atlas `A`, and the Hölder space of the metric
space `M` maps continuously into the atlas Hölder space `C^{0,α}(M, F)`
(`TauCeti.CompactChartAtlas.CkHolderSpace.ofHolderSpaceL`).

## Main results

* `TauCeti.IsRiemannianManifold.exists_lipschitzOnWith_extChartAt_symm_of_isCompact`: the
  inverse of an extended chart is Lipschitz on each compact subset of the chart target.
* `TauCeti.CompactChartAtlas.CkHolderSpace.ofHolderSpaceL`: the continuous linear inclusion
  `HolderSpace α M F → A.CkHolderSpace 0 α F`, with `coe_ofHolderSpaceL` and
  `ofHolderSpaceL_injective`.
-/

public section

open Bundle Manifold Set
open scoped Manifold NNReal Topology

noncomputable section

namespace TauCeti

/-- A charted space is a `C⁰` manifold for the order `0` written as the cast of the natural number
`0`, the form in which `TauCeti.CompactChartAtlas.CkHolderSpace 0` asks for it. -/
theorem isManifold_natCast_zero {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    IsManifold I ((0 : ℕ) : WithTop ℕ∞) M := by
  rw [Nat.cast_zero]
  infer_instance

attribute [local instance] isManifold_natCast_zero

section ZeroJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous map as a `C⁰` map, with the order written as the cast of the natural number
`0`. -/
private def toC0 (f : M → F) (hf : Continuous f) : C^(0 : ℕ)⟮I, M; 𝓘(ℝ, F), F⟯ :=
  ⟨f, by
    rw [Nat.cast_zero]
    exact contMDiff_zero_iff.mpr hf⟩

private theorem coe_toC0 (f : M → F) (hf : Continuous f) : ⇑(toC0 (I := I) f hf) = f :=
  (rfl)

/-- The norm of the `0`th coordinate derivative is that of the map in coordinates. -/
private theorem norm_chartIteratedFDeriv_zero (f : C^(0 : ℕ)⟮I, M; 𝓘(ℝ, F), F⟯) (x : M)
    (z : (extChartAt I x).target) :
    ‖ContMDiffMap.chartIteratedFDeriv f x 0 le_rfl z‖ = ‖f ((extChartAt I x).symm z)‖ := by
  rw [← ContinuousMultilinearMap.fin0_apply_norm (x := Fin.elim0)]
  exact congrArg norm (ContMDiffMap.chartIteratedFDeriv_zero_apply f x z _)

/-- The oscillation of the `0`th coordinate derivative is that of the map in coordinates. -/
private theorem norm_chartIteratedFDeriv_zero_sub (f : C^(0 : ℕ)⟮I, M; 𝓘(ℝ, F), F⟯) (x : M)
    (z w : (extChartAt I x).target) :
    ‖ContMDiffMap.chartIteratedFDeriv f x 0 le_rfl z -
        ContMDiffMap.chartIteratedFDeriv f x 0 le_rfl w‖ =
      ‖f ((extChartAt I x).symm z) - f ((extChartAt I x).symm w)‖ := by
  rw [← ContinuousMultilinearMap.fin0_apply_norm (x := Fin.elim0), sub_apply]
  exact congrArg norm (congrArg₂ _ (ContMDiffMap.chartIteratedFDeriv_zero_apply f x z _)
    (ContMDiffMap.chartIteratedFDeriv_zero_apply f x w _))

end ZeroJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

namespace IsRiemannianManifold

/-- **The inverse chart is Lipschitz on compact sets.** On a boundaryless manifold with a
continuous Riemannian metric, the inverse of the extended chart at `x` is Lipschitz, from the norm
distance of the model space to the Riemannian distance, on every compact subset of the chart
target. -/
theorem exists_lipschitzOnWith_extChartAt_symm_of_isCompact (x : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I x).target) :
    ∃ C : ℝ≥0, LipschitzOnWith C (extChartAt I x).symm K := by
  refine LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK fun z hz ↦ ?_
  have hsmooth : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I x).symm z :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (hKt hz))
  obtain ⟨r, hr, C, hC⟩ := exists_lipschitzOnWith_of_contMDiffAt hsmooth
  exact ⟨C, Metric.ball z r, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hr), hC⟩

end IsRiemannianManifold

namespace CompactChartAtlas

variable (A : CompactChartAtlas I M) (α : ℝ≥0)
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A Lipschitz constant of the inverse chart of the atlas `A` on its `i`th piece, from
`TauCeti.IsRiemannianManifold.exists_lipschitzOnWith_extChartAt_symm_of_isCompact`. -/
def chartSymmLipschitzConst (i : A.ι) : ℝ≥0 :=
  (IsRiemannianManifold.exists_lipschitzOnWith_extChartAt_symm_of_isCompact (A.center i)
    ((A.piece i).isCompact.image continuous_subtypeVal)
    (image_subset_iff.mpr fun z _ ↦ z.property)).choose

/-- The inverse chart of the atlas `A` is Lipschitz on the `i`th piece with constant
`A.chartSymmLipschitzConst i`. -/
theorem lipschitzOnWith_chartSymmLipschitzConst (i : A.ι) :
    LipschitzOnWith (A.chartSymmLipschitzConst i) (extChartAt I (A.center i)).symm
      (Subtype.val '' (A.piece i : Set (extChartAt I (A.center i)).target)) :=
  (IsRiemannianManifold.exists_lipschitzOnWith_extChartAt_symm_of_isCompact (A.center i)
    ((A.piece i).isCompact.image continuous_subtypeVal)
    (image_subset_iff.mpr fun z _ ↦ z.property)).choose_spec

namespace CkHolderSpace

variable {A α F}

omit [NormedSpace ℝ F] in
/-- A function that is `α`-Hölder with constant `C` for the Riemannian distance has, on the
`i`th piece, a coordinate representative whose values oscillate by at most
`C L^α |z - w|^α`, where `L` is the Lipschitz constant of the inverse chart. -/
private theorem norm_sub_le_of_holderWith {f : M → F} {C : ℝ≥0} (hf : HolderWith C α f)
    (i : A.ι) {z w : (extChartAt I (A.center i)).target}
    (hz : z ∈ (A.piece i : Set (extChartAt I (A.center i)).target))
    (hw : w ∈ (A.piece i : Set (extChartAt I (A.center i)).target)) :
    ‖f ((extChartAt I (A.center i)).symm z) - f ((extChartAt I (A.center i)).symm w)‖ ≤
      (C * A.chartSymmLipschitzConst i ^ (α : ℝ) : ℝ≥0) * dist z w ^ (α : ℝ) := by
  rw [← dist_eq_norm]
  refine (hf.dist_le _ _).trans ?_
  have hL := (A.lipschitzOnWith_chartSymmLipschitzConst i).dist_le_mul z ⟨z, hz, rfl⟩ w
    ⟨w, hw, rfl⟩
  rw [NNReal.coe_mul, NNReal.coe_rpow, mul_assoc, ← Real.mul_rpow NNReal.zero_le_coe
    dist_nonneg]
  gcongr
  exact hL

variable (A) in
/-- A function that is `α`-Hölder for the Riemannian distance belongs to the atlas Hölder space
`C^{0,α}(M, F)`. -/
def ofHolderSpace (f : HolderSpace α M F) : A.CkHolderSpace 0 α F :=
  mk (toC0 f f.continuous) fun i ↦
    ContMDiffMap.MemChartHolder.of_norm_sub_le fun z hz w hw ↦ by
      rw [norm_chartIteratedFDeriv_zero_sub, coe_toC0]
      exact norm_sub_le_of_holderWith f.holderWith i hz hw

@[simp]
theorem coe_ofHolderSpace (f : HolderSpace α M F) : ⇑(ofHolderSpace A f) = f :=
  coe_mk _ _

/-- The norm of the atlas Hölder space is bounded by a multiple of the Hölder norm for the
Riemannian distance. -/
theorem norm_ofHolderSpace_le (f : HolderSpace α M F) :
    ‖ofHolderSpace A f‖ ≤
      (1 + ∑ i, (A.chartSymmLipschitzConst i : ℝ) ^ (α : ℝ)) * ‖f‖ := by
  have hf0 : 0 ≤ ‖f‖ := norm_nonneg f
  rw [norm_def, add_mul, one_mul, Finset.sum_mul]
  gcongr with i
  · refine (ContMDiffMap.finiteAtlasSeminorm_le_iff _ _ _ _ _ hf0).mpr fun i m hm z _ ↦ ?_
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    rw [ofHolderSpace, toContMDiffMap_mk, norm_chartIteratedFDeriv_zero, coe_toC0]
    exact HolderSpace.norm_apply_le f _
  · have hC : ContMDiffMap.chartHolderNorm (A.center i) (A.piece i) 0 le_rfl α
        (toContMDiffMap A 0 α F (ofHolderSpace A f)) ≤
        nnHolderNorm α ⇑f * A.chartSymmLipschitzConst i ^ (α : ℝ) :=
      ContMDiffMap.chartHolderNorm_le_of_norm_sub_le fun z hz w hw ↦ by
        rw [ofHolderSpace, toContMDiffMap_mk, norm_chartIteratedFDeriv_zero_sub, coe_toC0]
        exact norm_sub_le_of_holderWith f.holderWith i hz hw
    refine (NNReal.coe_le_coe.mpr hC).trans ?_
    rw [NNReal.coe_mul, NNReal.coe_rpow, mul_comm]
    gcongr
    simpa using HolderSpace.nnHolderNorm_le f

variable (A α F)

/-- **Hölder functions for the Riemannian distance are `C^{0,α}` in charts.** On a boundaryless
`C¹` manifold with a continuous Riemannian metric, the inclusion of the Hölder space of the metric
space `M` into the Hölder space `C^{0,α}(M, F)` of a compact chart atlas, as a continuous linear
map. -/
def ofHolderSpaceL : HolderSpace α M F →L[ℝ] A.CkHolderSpace 0 α F :=
  LinearMap.mkContinuous
    { toFun := ofHolderSpace A
      map_add' f g := CkHolderSpace.ext fun y ↦ by simp
      map_smul' c f := CkHolderSpace.ext fun y ↦ by simp }
    (1 + ∑ i, (A.chartSymmLipschitzConst i : ℝ) ^ (α : ℝ)) norm_ofHolderSpace_le

variable {A α F}

@[simp]
theorem coe_ofHolderSpaceL (f : HolderSpace α M F) : ⇑(ofHolderSpaceL A α F f) = f :=
  coe_ofHolderSpace f

/-- The inclusion of the Hölder space for the Riemannian distance is injective. -/
theorem ofHolderSpaceL_injective : Function.Injective (ofHolderSpaceL A α F) := fun f g h ↦
  HolderSpace.ext fun y ↦ by simpa using DFunLike.congr_fun h y

end CkHolderSpace

end CompactChartAtlas

end TauCeti

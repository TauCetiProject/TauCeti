/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Holder.Basic
public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# Hölder functions for the Riemannian distance lie in `C^{0,α}` of a compact chart atlas

Let `M` be a boundaryless `C¹` manifold with a continuous Riemannian metric whose distance is the
metric of `M`. On a compact subset of an extended chart target, the inverse chart is Lipschitz from
the norm distance of the model space to the Riemannian distance
(`TauCeti.IsRiemannianManifold.exists_lipschitzOnWith_extChartAt_symm_of_isCompact`); this file
fixes such a Lipschitz constant on each piece of a compact chart atlas `A`.

Consequently a function `M → F` that is `α`-Hölder for the Riemannian distance is `α`-Hölder in
the coordinates of every piece of `A`, and the Hölder space of the metric space `M` maps
continuously into the atlas Hölder space `C^{0,α}(M, F)`
(`TauCeti.CompactChartAtlas.CkHolderSpace.ofHolderSpaceL`).

## Main results

* `TauCeti.CompactChartAtlas.lipschitzOnWith_chartSymmLipschitzConst`: the inverse chart of the
  atlas is Lipschitz on each piece with constant `chartSymmLipschitzConst`.
* `TauCeti.CompactChartAtlas.CkHolderSpace.ofHolderSpaceL`: the continuous linear inclusion
  `HolderSpace α M F → A.CkHolderSpace 0 α F`, with `coe_ofHolderSpaceL`,
  `ofHolderSpaceL_injective` and the operator-norm bound `opNorm_ofHolderSpaceL_le`.
-/

public section

open Bundle Manifold Set
open scoped Manifold NNReal Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

namespace CompactChartAtlas

section Lipschitz

variable {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  (A : CompactChartAtlas I M)

private theorem exists_lipschitzOnWith_piece (i : A.ι) :
    ∃ C : ℝ≥0, LipschitzOnWith C (extChartAt I (A.center i)).symm
      (Subtype.val '' (A.piece i : Set (extChartAt I (A.center i)).target)) :=
  IsRiemannianManifold.exists_lipschitzOnWith_extChartAt_symm_of_isCompact (A.center i)
    ((A.piece i).isCompact.image continuous_subtypeVal)
    (image_subset_iff.mpr fun z _ ↦ z.property)

/-- A Lipschitz constant of the inverse chart of the atlas `A` on its `i`th piece, from
`TauCeti.IsRiemannianManifold.exists_lipschitzOnWith_extChartAt_symm_of_isCompact`. -/
def chartSymmLipschitzConst (i : A.ι) : ℝ≥0 :=
  (A.exists_lipschitzOnWith_piece i).choose

/-- The inverse chart of the atlas `A` is Lipschitz on the `i`th piece with constant
`A.chartSymmLipschitzConst i`. -/
theorem lipschitzOnWith_chartSymmLipschitzConst (i : A.ι) :
    LipschitzOnWith (A.chartSymmLipschitzConst i) (extChartAt I (A.center i)).symm
      (Subtype.val '' (A.piece i : Set (extChartAt I (A.center i)).target)) :=
  (A.exists_lipschitzOnWith_piece i).choose_spec

end Lipschitz

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {A : CompactChartAtlas I M} {α : ℝ≥0}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace CkHolderSpace

/-- An element `f` of the Hölder space for the Riemannian distance has, on the `i`th piece, an
order-zero coordinate derivative whose values oscillate by at most `[f]_α L^α |z - w|^α`, where
`L` is the Lipschitz constant of the inverse chart. -/
private theorem norm_chartIteratedFDeriv_ofContinuous_sub_le (f : HolderSpace α M F) (i : A.ι)
    {z w : (extChartAt I (A.center i)).target}
    (hz : z ∈ (A.piece i : Set (extChartAt I (A.center i)).target))
    (hw : w ∈ (A.piece i : Set (extChartAt I (A.center i)).target)) :
    ‖ContMDiffMap.chartIteratedFDeriv (ContMDiffMap.ofContinuous (I := I) (I' := 𝓘(ℝ, F)) f
        f.continuous) (A.center i) 0 le_rfl z -
      ContMDiffMap.chartIteratedFDeriv (ContMDiffMap.ofContinuous (I := I) (I' := 𝓘(ℝ, F)) f
        f.continuous) (A.center i) 0 le_rfl w‖ ≤
      (nnHolderNorm α ⇑f * A.chartSymmLipschitzConst i ^ (α : ℝ) : ℝ≥0) * dist z w ^ (α : ℝ) := by
  rw [ContMDiffMap.norm_chartIteratedFDeriv_zero_sub, ContMDiffMap.coe_ofContinuous,
    ← dist_eq_norm]
  refine (f.holderWith.dist_le _ _).trans ?_
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
  mk (ContMDiffMap.ofContinuous f f.continuous) fun i ↦
    ContMDiffMap.MemChartHolder.of_norm_sub_le fun _ hz _ hw ↦
      norm_chartIteratedFDeriv_ofContinuous_sub_le f i hz hw

@[simp]
theorem toContMDiffMap_ofHolderSpace (f : HolderSpace α M F) :
    toContMDiffMap A 0 α F (ofHolderSpace A f) = ContMDiffMap.ofContinuous f f.continuous :=
  toContMDiffMap_mk _ _

@[simp]
theorem coe_ofHolderSpace (f : HolderSpace α M F) : ⇑(ofHolderSpace A f) = f :=
  (coe_mk _ _).trans (ContMDiffMap.coe_ofContinuous _ _)

/-- The norm of the atlas Hölder space is bounded by a multiple of the Hölder norm for the
Riemannian distance. -/
theorem norm_ofHolderSpace_le (f : HolderSpace α M F) :
    ‖ofHolderSpace A f‖ ≤
      (1 + ∑ i, (A.chartSymmLipschitzConst i : ℝ) ^ (α : ℝ)) * ‖f‖ := by
  have hf0 : 0 ≤ ‖f‖ := norm_nonneg f
  rw [norm_def, add_mul, one_mul, Finset.sum_mul, toContMDiffMap_ofHolderSpace]
  gcongr with i
  · refine (ContMDiffMap.finiteAtlasSeminorm_le_iff _ _ _ _ _ hf0).mpr fun i m hm z _ ↦ ?_
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    rw [ContMDiffMap.norm_chartIteratedFDeriv_zero, ContMDiffMap.coe_ofContinuous]
    exact HolderSpace.norm_apply_le f _
  · have hC := ContMDiffMap.chartHolderNorm_le_of_norm_sub_le fun _ hz _ hw ↦
      norm_chartIteratedFDeriv_ofContinuous_sub_le f i hz hw
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

/-- The operator norm of the inclusion of the Hölder space for the Riemannian distance is at most
`1 + ∑ᵢ Lᵢ^α`, where `Lᵢ` is the Lipschitz constant of the inverse chart on the `i`th piece. -/
theorem opNorm_ofHolderSpaceL_le :
    ‖ofHolderSpaceL A α F‖ ≤ 1 + ∑ i, (A.chartSymmLipschitzConst i : ℝ) ^ (α : ℝ) :=
  LinearMap.mkContinuous_norm_le _
    (add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ ↦ by positivity)) _

@[simp]
theorem coe_ofHolderSpaceL (f : HolderSpace α M F) : ⇑(ofHolderSpaceL A α F f) = f :=
  coe_ofHolderSpace f

/-- The inclusion of the Hölder space for the Riemannian distance is injective. -/
theorem ofHolderSpaceL_injective : Function.Injective (ofHolderSpaceL A α F) := fun f g h ↦
  HolderSpace.ext fun y ↦ by simpa using DFunLike.congr_fun h y

end CkHolderSpace

end CompactChartAtlas

end TauCeti

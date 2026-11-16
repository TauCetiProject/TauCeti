/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.FirstJet.Prolongation
public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Vector-bundle comparison for the nonlinear first-jet bundle

When `V : B → Type*` is a `C^1` vector bundle over `B` (modelled on `IB`) with normed fibre `F`
(equipped with its self model `𝓘(𝕜, F)`), two constructions of the first-jet bundle are available:

* `FiberFirstJetBundle IB 𝓘(𝕜, F) F V`, fibred as an affine bundle over the charted total space
  `ManifoldTotalSpace F V` with model fibre `EB →L[𝕜] F`;
* `TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)`, fibred as a vector bundle directly over
  the base `B` with model fibre `F × (EB →L[𝕜] F)`.

This file compares their coordinate changes
(`FiberFirstJet.coordChange_self_left_eq_firstJetBundle_coordChange_snd`), constructs the canonical
`C^n` diffeomorphism `FiberFirstJetBundle.diffeomorphFirstJetBundle` between their total spaces
(requiring only `C^1` bundle regularity for arbitrary `n : ℕ∞ω`), and proves compatibility with
target/value projections, holonomic prolongation (`jet`), and vertical affine translation
(`+ᵥ` vs `FirstJetBundle.ofDeriv` + `+`).

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*,
  Springer-Verlag, 1993, §§12.16–12.17.
* D. J. Saunders, *The Geometry of Jet Bundles*, Cambridge University Press, 1989, §§4.1–4.2.
* `TauCeti.FirstJetBundle` (`TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic`), the linear
  vector-bundle first-jet construction over `B`.
* `TauCeti.FiberFirstJetBundle` (`TauCeti.Geometry.Manifold.FiberBundle.FirstJet.Prolongation`),
  the nonlinear first-jet bundle and holonomic prolongation over `ManifoldTotalSpace F V`.
-/

public section
noncomputable section

open Bundle Set Filter ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace TauCeti

section VectorBundleComparison

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ b, AddCommGroup (V b)]
  [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F V IB]

namespace FiberFirstJet

omit [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F V IB] in
private theorem eventuallyEq_extChartAt_snd_vectorBundle {i z : ManifoldTotalSpace F V}
    (hi : z ∈ (chartAt (ModelProd HB F) i).source) :
    let v := (trivializationAt F V z.proj ((ManifoldTotalSpace.homeomorph F V).symm z)).2
    (fun q : EB × F ↦ (extChartAt (IB.prod 𝓘(𝕜, F)) i ((extChartAt (IB.prod 𝓘(𝕜, F)) z).symm q)).2)
      =ᶠ[𝓝[range (IB.prod 𝓘(𝕜, F))] (extChartAt IB z.proj z.proj, v)]
    fun q : EB × F ↦ FirstJetBundle.fiberCoordChange IB F V z.proj i.proj
      (extChartAt IB i.proj ((extChartAt IB z.proj).symm q.1)) q.2 := by
  intro v
  have hz_pt : extChartAt (IB.prod 𝓘(𝕜, F)) z z = (extChartAt IB z.proj z.proj, v) :=
    Prod.ext (ManifoldTotalSpace.extChartAt_fst_eq (mem_chart_source _ z))
      (ManifoldTotalSpace.extChartAt_snd_eq IB z z)
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (hz_pt ▸ mem_extChartAt_target z),
    nhdsWithin_le_nhds (hz_pt ▸ extChartAt_preimage_mem_nhds' (mem_extChartAt_source z)
      ((chartAt (ModelProd HB F) i).open_source.mem_nhds hi))] with q hq1 hq2
  set w := (extChartAt (IB.prod 𝓘(𝕜, F)) z).symm q
  have hwb_z := (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source
    ((extChartAt_source (IB.prod 𝓘(𝕜, F)) z) ▸ (extChartAt (IB.prod 𝓘(𝕜, F)) z).map_target hq1)).1
  have hwb_i := ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hq2
  have hwb_i1 := hwb_i.1
  have hq_snd : (trivializationAt F V z.proj ((ManifoldTotalSpace.homeomorph F V).symm w)).2 =
      q.2 := (ManifoldTotalSpace.extChartAt_snd_eq IB z w).symm.trans
    (congrArg Prod.snd ((extChartAt (IB.prod 𝓘(𝕜, F)) z).right_inv hq1))
  rw [ManifoldTotalSpace.extChartAt_snd_eq, FirstJetBundle.fiberCoordChange_apply,
    ← ManifoldTotalSpace.proj_extChartAt_symm z hq1,
    (extChartAt IB i.proj).left_inv ((extChartAt_source IB i.proj).symm ▸ hwb_i.2), ← hq_snd]
  rw [← ManifoldTotalSpace.homeomorph_symm_proj w] at hwb_z hwb_i1 ⊢
  exact (Trivialization.coordChangeL_apply_snd 𝕜 _ _ hwb_z hwb_i1).symm

/-- For a `C^1` vector bundle `V`, the nonlinear first-jet coordinate change from the preferred
chart at `z` to any chart `i` containing `z` agrees with the derivative component (`.2`) of the
linear `FirstJetBundle.coordChange` from `z.proj` to `i.proj`. -/
theorem coordChange_self_left_eq_firstJetBundle_coordChange_snd {i z : ManifoldTotalSpace F V}
    (hi : z ∈ (chartAt (ModelProd HB F) i).source) (A : EB →L[𝕜] F) :
    coordChange (IB := IB) (IF := 𝓘(𝕜, F)) (F := F) (E := V) z i z A =
      (FirstJetBundle.coordChange IB F V z.proj i.proj z.proj
        ((trivializationAt F V z.proj ((ManifoldTotalSpace.homeomorph F V).symm z)).2, A)).2 := by
  set b := z.proj
  set b_i := i.proj
  have hb_ext := mem_extChartAt_source (I := IB) b
  set v := (trivializationAt F V b ((ManifoldTotalSpace.homeomorph F V).symm z)).2
  have hb_i' := ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hi
  have hb_i := (FirstJetBundle.mem_baseSet_iff (H := HB) F V).2 hb_i'
  have hbi_ext : b ∈ (extChartAt IB b_i).source := (extChartAt_source IB b_i).symm ▸ hb_i'.2
  have hz_pt : extChartAt (IB.prod 𝓘(𝕜, F)) z z = (extChartAt IB b b, v) :=
    Prod.ext (ManifoldTotalSpace.extChartAt_fst_eq (mem_chart_source _ z))
      (ManifoldTotalSpace.extChartAt_snd_eq IB z z)
  have hbase_step : HasFDerivWithinAt
      (fun q : EB × F ↦ (extChartAt IB b_i ∘ (extChartAt IB b).symm) q.1)
      ((tangentCoordChange IB b b_i b).comp (ContinuousLinearMap.fst 𝕜 EB F))
      (range (IB.prod 𝓘(𝕜, F))) (extChartAt IB b b, v) :=
    (hasFDerivWithinAt_tangentCoordChange (I := IB) ⟨hb_ext, hbi_ext⟩).comp (extChartAt IB b b, v)
      (hasFDerivAt_fst (𝕜 := 𝕜) (E := EB) (F := F)).hasFDerivWithinAt
      fun q hq ↦ by rw [ModelWithCorners.range_prod] at hq; exact hq.1
  have hpt : (extChartAt IB b_i ∘ (extChartAt IB b).symm) (extChartAt IB b b) =
      extChartAt IB b_i b := by rw [Function.comp_apply, (extChartAt IB b).left_inv hb_ext]
  have hclm := ((hpt ▸ FirstJetBundle.hasFDerivWithinAt_fiberCoordChange (I := IB) (F := F) (V := V)
      (mem_baseSet_trivializationAt F V b) hb_i).comp (extChartAt IB b b, v) hbase_step fun q _ ↦ by
        rw [Function.comp_apply, extChartAt_coe]; exact mem_range_self _).clm_apply
    (hasFDerivAt_snd (𝕜 := 𝕜) (E := EB) (F := F)).hasFDerivWithinAt
  dsimp only [Function.comp_def] at hclm
  rw [(extChartAt IB b).left_inv hb_ext, FirstJetBundle.fiberCoordChange_extChartAt hb_i'.2,
    add_comm] at hclm
  have hT_snd : HasFDerivWithinAt
      (fun q : EB × F ↦ (extChartAt (IB.prod 𝓘(𝕜, F)) i
        ((extChartAt (IB.prod 𝓘(𝕜, F)) z).symm q)).2)
      ((ContinuousLinearMap.snd 𝕜 EB F).comp (tangentCoordChange (IB.prod 𝓘(𝕜, F)) z i z))
      (range (IB.prod 𝓘(𝕜, F))) (extChartAt IB b b, v) :=
    hz_pt ▸ hasFDerivAt_snd.comp_hasFDerivWithinAt _
      (hasFDerivWithinAt_tangentCoordChange ⟨mem_extChartAt_source z,
        (extChartAt_source (IB.prod 𝓘(𝕜, F)) i).symm ▸ hi⟩)
  have hev := eventuallyEq_extChartAt_snd_vectorBundle (IB := IB) hi
  have hrange : (extChartAt IB b b, v) ∈ range (IB.prod 𝓘(𝕜, F)) :=
    hz_pt ▸ extChartAt_target_subset_range z (mem_extChartAt_target z)
  have heq_clm := ((IB.prod 𝓘(𝕜, F)).uniqueDiffOn _ hrange).eq hT_snd
    (hclm.congr_of_eventuallyEq hev (hev.self_of_nhdsWithin hrange))
  ext u
  have hcomp_base : tangentCoordChange IB b b_i b (tangentCoordChange IB b_i b b u) = u := by
    rw [tangentCoordChange_comp ⟨⟨hbi_ext, hb_ext⟩, hbi_ext⟩, tangentCoordChange_self hbi_ext]
  have happ := DFunLike.congr_fun heq_clm
    (tangentCoordChange IB b_i b b u, A (tangentCoordChange IB b_i b b u))
  simp only [comp_apply, add_apply, flip_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', hcomp_base] at happ
  rw [coordChange_apply, FirstJetBundle.coordChange_apply]
  exact happ

end FiberFirstJet

namespace FiberFirstJetBundle

/-- Map from the fibre `FiberFirstJet IB 𝓘(𝕜, F) F V z` over `z` into the linear first-jet fibre
`FirstJetBundle IB F V z.proj`, pairing the fibre coordinate of `z` in `trivializationAt F V z.proj`
with `FiberFirstJet.modelEquivAt z j`. -/
def toFirstJetBundleFiber (z : ManifoldTotalSpace F V)
    (j : FiberFirstJet IB 𝓘(𝕜, F) F V z) : FirstJetBundle IB F V z.proj :=
  ((trivializationAt F V z.proj ⟨z.proj, z.snd⟩).2,
    FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z j)

/-- The value coordinate of `toFirstJetBundleFiber z j` in `FirstJetBundle IB F V z.proj` is the
preferred trivialization coordinate of `z.snd`. -/
@[simp]
theorem toFirstJetBundleFiber_fst (z : ManifoldTotalSpace F V)
    (j : FiberFirstJet IB 𝓘(𝕜, F) F V z) :
    (toFirstJetBundleFiber z j).1 = (trivializationAt F V z.proj ⟨z.proj, z.snd⟩).2 :=
  (rfl)

/-- The derivative coordinate of `toFirstJetBundleFiber z j` in `FirstJetBundle IB F V z.proj` is
`FiberFirstJet.modelEquivAt z j`. -/
@[simp]
theorem toFirstJetBundleFiber_snd (z : ManifoldTotalSpace F V)
    (j : FiberFirstJet IB 𝓘(𝕜, F) F V z) :
    (toFirstJetBundleFiber z j).2 = FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z j :=
  (rfl)

/-- Applying `FirstJetBundle.value` to `toFirstJetBundleFiber z j` recovers the vector `z.snd`. -/
@[simp]
theorem value_toFirstJetBundleFiber (z : ManifoldTotalSpace F V)
    (j : FiberFirstJet IB 𝓘(𝕜, F) F V z) :
    FirstJetBundle.value IB F z.proj (toFirstJetBundleFiber z j) = z.snd := by
  rw [FirstJetBundle.value_apply, toFirstJetBundleFiber_fst]
  exact (trivializationAt F V z.proj).symm_apply_apply_mk
    (mem_baseSet_trivializationAt F V z.proj) z.snd

/-- `toFirstJetBundleFiber` intertwines vertical affine translation by `(verticalLift IB z) ∘L L` on
`FiberFirstJet` with addition of `FirstJetBundle.ofDeriv IB F z.proj L` in `FirstJetBundle`. -/
theorem toFirstJetBundleFiber_vadd [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul 𝕜 (V x)] (z : ManifoldTotalSpace F V)
    (L : TangentSpace IB z.proj →L[𝕜] V z.proj) (j : FiberFirstJet IB 𝓘(𝕜, F) F V z) :
    toFirstJetBundleFiber z
        (((VerticalSpace.verticalLift IB z).toContinuousLinearMap.comp L) +ᵥ j) =
      FirstJetBundle.ofDeriv IB F z.proj L + toFirstJetBundleFiber z j := by
  have hvadd (u : EB) :
      (toFirstJetBundleFiber z
        (((VerticalSpace.verticalLift IB z).toContinuousLinearMap.comp L) +ᵥ j)).2 u =
        (trivializationAt F V z.proj).continuousLinearMapAt 𝕜 z.proj
          (L ((tangentSpaceCastModel IB z.proj).symm u)) +
          FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z j u := by
    simp only [toFirstJetBundleFiber_snd, FiberFirstJet.modelEquivAt_vadd, add_apply, comp_apply,
      ContinuousLinearEquiv.coe_coe, VerticalSpace.modelEquivAt_verticalLift]
  rw [FirstJetBundle.ofDeriv_apply]
  refine Prod.ext (zero_add _).symm (ContinuousLinearMap.ext fun u ↦ (hvadd u).trans ?_)
  exact congrArg
    (fun x ↦ (trivializationAt F V z.proj).continuousLinearMapAt 𝕜 z.proj (L x) +
      FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z j u)
    (Manifold.tangentSpaceCastModel_symm_apply IB z.proj u)

private def toFirstJetBundle (p : FiberFirstJetBundle IB 𝓘(𝕜, F) F V) :
    TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) :=
  ⟨p.proj.proj, toFirstJetBundleFiber p.proj p.2⟩

private def ofFirstJetBundle (q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) :
    FiberFirstJetBundle IB 𝓘(𝕜, F) F V :=
  let z : ManifoldTotalSpace F V :=
    ManifoldTotalSpace.homeomorph F V ⟨q.proj, FirstJetBundle.value IB F q.proj q.2⟩
  ⟨z, (FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z).symm q.2.2⟩

@[simp]
private theorem ofFirstJetBundle_proj (q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) :
    (ofFirstJetBundle q).proj =
      ManifoldTotalSpace.homeomorph F V ⟨q.proj, FirstJetBundle.value IB F q.proj q.2⟩ :=
  (rfl)

private theorem ofFirstJetBundle_proj_proj
    (q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) :
    (ofFirstJetBundle q).proj.proj = q.proj :=
  ManifoldTotalSpace.proj_homeomorph _

private theorem trivializationAt_ofFirstJetBundle_proj_snd
    (q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) :
    (trivializationAt F V (ofFirstJetBundle q).proj.proj
        ⟨(ofFirstJetBundle q).proj.proj, (ofFirstJetBundle q).proj.snd⟩).2 = q.2.1 := by
  have hz_symm : (⟨(ofFirstJetBundle q).proj.proj, (ofFirstJetBundle q).proj.snd⟩ :
      TotalSpace F V) = ⟨q.proj, FirstJetBundle.value IB F q.proj q.2⟩ := by
    rw [← ManifoldTotalSpace.homeomorph_symm_apply, ofFirstJetBundle_proj,
      Homeomorph.symm_apply_apply]
  rw [hz_symm, ofFirstJetBundle_proj_proj, FirstJetBundle.value_apply,
    (trivializationAt F V q.proj).apply_mk_symm (mem_baseSet_trivializationAt F V q.proj)]

@[simp]
private theorem modelEquivAt_ofFirstJetBundle_snd
    (q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) :
    FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) (ofFirstJetBundle q).proj
        (ofFirstJetBundle q).2 = q.2.2 :=
  (FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) (ofFirstJetBundle q).proj).apply_symm_apply
    q.2.2

private theorem ofFirstJetBundle_toFirstJetBundle (p : FiberFirstJetBundle IB 𝓘(𝕜, F) F V) :
    ofFirstJetBundle (toFirstJetBundle p) = p := by
  rw [ofFirstJetBundle, toFirstJetBundle, mk_eq_mk_iff_modelEquivAt]
  dsimp only
  refine ⟨?_, (FiberFirstJet.modelEquivAt (IF := 𝓘(𝕜, F)) _).apply_symm_apply _⟩
  rw [value_toFirstJetBundleFiber, ManifoldTotalSpace.homeomorph_mk_proj_snd]

private theorem toFirstJetBundle_ofFirstJetBundle
    (q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) :
    toFirstJetBundle (ofFirstJetBundle q) = q :=
  TotalSpace.ext (ofFirstJetBundle_proj_proj q) (heq_of_eq (Prod.ext
    (trivializationAt_ofFirstJetBundle_proj_snd q) (modelEquivAt_ofFirstJetBundle_snd q)))

private theorem contMDiff_toFirstJetBundle (n : ℕ∞ω) :
    ContMDiff ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F)) (IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))) n
      (toFirstJetBundle : FiberFirstJetBundle IB 𝓘(𝕜, F) F V →
        TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) := by
  intro p₀
  set z₀ := p₀.proj
  have hp_proj : ContMDiffAt ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F)) (IB.prod 𝓘(𝕜, F)) n
      TotalSpace.proj p₀ := Bundle.contMDiff_proj (FiberFirstJet IB 𝓘(𝕜, F) F V) p₀
  have hbase : ContMDiffAt ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F)) IB n
      (fun p : FiberFirstJetBundle IB 𝓘(𝕜, F) F V ↦ p.proj.proj) p₀ :=
    ManifoldTotalSpace.contMDiffAt_proj.comp p₀ hp_proj
  have hval :=
    (ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB 𝓘(𝕜, F) z₀).comp p₀ hp_proj
  have hsnd : ContMDiffAt ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F)) 𝓘(𝕜, EB →L[𝕜] F) n
      (fun p : FiberFirstJetBundle IB 𝓘(𝕜, F) F V ↦
        (trivializationAt (EB →L[𝕜] F) (FiberFirstJet IB 𝓘(𝕜, F) F V) z₀ p).2) p₀ :=
    (Bundle.contMDiffAt_totalSpace_iff.1 contMDiffAt_id).2
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨hbase,
    (hval.prodMk_space hsnd).congr_of_eventuallyEq ?_⟩
  filter_upwards [hp_proj.continuousAt.preimage_mem_nhds
    ((chartAt (ModelProd HB F) z₀).open_source.mem_nhds (mem_chart_source _ z₀))] with p hp
  rw [FirstJetBundle.trivializationAt_apply_snd, FiberFirstJet.trivializationAt_apply]
  dsimp only [Function.comp_apply, toFirstJetBundle, toFirstJetBundleFiber]
  refine Prod.ext ?_ ?_
  · rw [FirstJetBundle.coordChange_apply]
    dsimp only
    exact Trivialization.coordChangeL_apply_snd 𝕜 _ _
      (mem_baseSet_trivializationAt _ _ _)
      (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hp).1
  · dsimp only
    rw [← ManifoldTotalSpace.homeomorph_symm_apply,
      ← FiberFirstJet.coordChange_self_left_eq_firstJetBundle_coordChange_snd hp,
      ← FiberFirstJet.coordAt_eq_coordChange_modelEquivAt hp]

private theorem contMDiff_ofFirstJetBundle (n : ℕ∞ω) :
    ContMDiff (IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))) ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F)) n
      (ofFirstJetBundle : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) →
        FiberFirstJetBundle IB 𝓘(𝕜, F) F V) := by
  intro q₀
  set z₀ := (ofFirstJetBundle q₀).proj
  have htriv : ContMDiffAt (IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))) 𝓘(𝕜, F × (EB →L[𝕜] F)) n
      (fun q ↦ (trivializationAt (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) q₀.proj q).2) q₀ :=
    (Bundle.contMDiffAt_totalSpace_iff.1 contMDiffAt_id).2
  have hproj_smooth : ContMDiffAt (IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))) (IB.prod 𝓘(𝕜, F)) n
      (fun q ↦ (ofFirstJetBundle q).proj) q₀ := by
    refine ManifoldTotalSpace.contMDiffAt_iff.2 ⟨Bundle.contMDiffAt_proj (FirstJetBundle IB F V),
      ((ContinuousLinearMap.fst 𝕜 F (EB →L[𝕜] F)).contMDiffAt.comp q₀ htriv).congr_of_eventuallyEq
        ?_⟩
    filter_upwards [(FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds
      ((trivializationAt F V q₀.proj).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F V q₀.proj))] with ⟨b, v, A⟩ hq
    have hval_eq : FirstJetBundle.value IB F b (v, A) = (trivializationAt F V b).symm b v :=
      FirstJetBundle.value_apply IB F b (v, A)
    simp only [Function.comp_apply, ContinuousLinearMap.coe_fst', hval_eq,
      FirstJetBundle.trivializationAt_apply_snd, FirstJetBundle.coordChange_apply]
    exact (Trivialization.coordChangeL_apply (R := 𝕜) _ _
      ⟨mem_baseSet_trivializationAt F V b, hq⟩ v).symm
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨hproj_smooth,
    ((ContinuousLinearMap.snd 𝕜 F (EB →L[𝕜] F)).contMDiffAt.comp q₀ htriv).congr_of_eventuallyEq
      ?_⟩
  filter_upwards [hproj_smooth.continuousAt.preimage_mem_nhds
    ((chartAt (ModelProd HB F) z₀).open_source.mem_nhds (mem_chart_source _ z₀))] with q hq
  rcases q with ⟨b, v, A⟩
  simp only [Function.comp_apply, ContinuousLinearMap.coe_snd',
    FiberFirstJet.trivializationAt_apply, FirstJetBundle.trivializationAt_apply_snd]
  rw [FiberFirstJet.coordAt_eq_coordChange_modelEquivAt hq, modelEquivAt_ofFirstJetBundle_snd,
    FiberFirstJet.coordChange_self_left_eq_firstJetBundle_coordChange_snd hq,
    ManifoldTotalSpace.homeomorph_symm_apply, trivializationAt_ofFirstJetBundle_proj_snd,
    ofFirstJetBundle_proj_proj, ofFirstJetBundle_proj_proj q₀]

variable (IB F V) in
/-- **Canonical `C^n` diffeomorphism between `FiberFirstJetBundle` and `FirstJetBundle`** for a
`C^1` vector bundle `V` over `B`. -/
def diffeomorphFirstJetBundle (n : ℕ∞ω) :
    FiberFirstJetBundle IB 𝓘(𝕜, F) F V ≃ₘ^n⟮(IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F),
      IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))⟯
      TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) where
  toFun := toFirstJetBundle
  invFun := ofFirstJetBundle
  left_inv := ofFirstJetBundle_toFirstJetBundle
  right_inv := toFirstJetBundle_ofFirstJetBundle
  contMDiff_toFun := contMDiff_toFirstJetBundle n
  contMDiff_invFun := contMDiff_ofFirstJetBundle n

/-- Evaluating `diffeomorphFirstJetBundle` on `⟨z, j⟩` returns
`⟨z.proj, toFirstJetBundleFiber z j⟩`. -/
@[simp]
theorem diffeomorphFirstJetBundle_mk (n : ℕ∞ω) (z : ManifoldTotalSpace F V)
    (j : FiberFirstJet IB 𝓘(𝕜, F) F V z) :
    diffeomorphFirstJetBundle IB F V n ⟨z, j⟩ = ⟨z.proj, toFirstJetBundleFiber z j⟩ :=
  (rfl)

/-- The base projection of `diffeomorphFirstJetBundle IB F V n p` in `FirstJetBundle` equals
`baseProj p`. -/
@[simp]
theorem diffeomorphFirstJetBundle_proj (n : ℕ∞ω) (p : FiberFirstJetBundle IB 𝓘(𝕜, F) F V) :
    (diffeomorphFirstJetBundle IB F V n p).proj = baseProj p :=
  (baseProj_apply p).symm

/-- The fibre component of `diffeomorphFirstJetBundle IB F V n p` over `p.proj.proj` is
`toFirstJetBundleFiber p.proj p.2`. -/
@[simp]
theorem diffeomorphFirstJetBundle_snd (n : ℕ∞ω) (p : FiberFirstJetBundle IB 𝓘(𝕜, F) F V) :
    (diffeomorphFirstJetBundle IB F V n p).2 = toFirstJetBundleFiber p.proj p.2 :=
  (rfl)

/-- Applying `FirstJetBundle.value` to the image of `p` under `diffeomorphFirstJetBundle` and
casting along `(diffeomorphFirstJetBundle_proj n p).trans (baseProj_apply p)` recovers
`p.proj.snd`. -/
theorem cast_value_diffeomorphFirstJetBundle (n : ℕ∞ω)
    (p : FiberFirstJetBundle IB 𝓘(𝕜, F) F V) :
    cast (congrArg V ((diffeomorphFirstJetBundle_proj n p).trans (baseProj_apply p)))
      (FirstJetBundle.value IB F (diffeomorphFirstJetBundle IB F V n p).proj
        (diffeomorphFirstJetBundle IB F V n p).2) = p.proj.snd :=
  value_toFirstJetBundleFiber p.proj p.2

/-- Evaluating `(diffeomorphFirstJetBundle IB F V n).symm` on `⟨b, j⟩` reconstructs the point over
`homeomorph F V ⟨b, value IB F b j⟩` with model jet coordinate `j.2`. -/
@[simp]
theorem diffeomorphFirstJetBundle_symm_mk (n : ℕ∞ω) (b : B) (j : FirstJetBundle IB F V b) :
    (diffeomorphFirstJetBundle IB F V n).symm ⟨b, j⟩ =
      ⟨ManifoldTotalSpace.homeomorph F V ⟨b, FirstJetBundle.value IB F b j⟩,
        (FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F))
          (ManifoldTotalSpace.homeomorph F V ⟨b, FirstJetBundle.value IB F b j⟩)).symm j.2⟩ :=
  (rfl)

/-- The target projection of `(diffeomorphFirstJetBundle IB F V n).symm q` in
`ManifoldTotalSpace F V` is `homeomorph F V ⟨q.proj, FirstJetBundle.value IB F q.proj q.2⟩`. -/
@[simp]
theorem diffeomorphFirstJetBundle_symm_proj (n : ℕ∞ω)
    (q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) :
    ((diffeomorphFirstJetBundle IB F V n).symm q).proj =
      ManifoldTotalSpace.homeomorph F V ⟨q.proj, FirstJetBundle.value IB F q.proj q.2⟩ :=
  (rfl)

/-- The base projection `baseProj` of `(diffeomorphFirstJetBundle IB F V n).symm q` is `q.proj`. -/
theorem baseProj_diffeomorphFirstJetBundle_symm (n : ℕ∞ω)
    (q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) :
    baseProj ((diffeomorphFirstJetBundle IB F V n).symm q) = q.proj := by
  rw [baseProj_apply, diffeomorphFirstJetBundle_symm_proj, ManifoldTotalSpace.proj_homeomorph]

/-- Reading the jet component of `(diffeomorphFirstJetBundle IB F V n).symm q` in `modelEquivAt`
recovers the derivative coordinate `q.2.2`. -/
@[simp]
theorem modelEquivAt_diffeomorphFirstJetBundle_symm_snd (n : ℕ∞ω)
    (q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) :
    FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F))
        ((diffeomorphFirstJetBundle IB F V n).symm q).proj
        ((diffeomorphFirstJetBundle IB F V n).symm q).2 = q.2.2 :=
  modelEquivAt_ofFirstJetBundle_snd q

/-- For a differentiable section `s : ∀ b, V b` at `x`, `diffeomorphFirstJetBundle` carries the
nonlinear prolongation `jet IB 𝓘(𝕜, F) F s x` to the linear first jet
`⟨x, FirstJetBundle.jet IB F s x⟩`. -/
theorem diffeomorphFirstJetBundle_jet (n : ℕ∞ω) {s : ∀ b, V b} {x : B}
    (hs : MDifferentiableAt IB (IB.prod 𝓘(𝕜, F)) (fun b ↦ TotalSpace.mk' F b (s b)) x) :
    diffeomorphFirstJetBundle IB F V n (jet IB 𝓘(𝕜, F) F s x) =
      ⟨x, FirstJetBundle.jet IB F s x⟩ := by
  set sM : B → ManifoldTotalSpace F V := fun b ↦ ManifoldTotalSpace.homeomorph F V ⟨b, s b⟩
  have hsM : MDifferentiableAt IB (IB.prod 𝓘(𝕜, F)) sM x :=
    ((ManifoldTotalSpace.contMDiff_homeomorph 1 F V IB ⟨x, s x⟩).mdifferentiableAt
      one_ne_zero).comp x hs
  have hproj : (ManifoldTotalSpace.proj ∘ sM) =ᶠ[𝓝 x] id :=
    Eventually.of_forall fun b ↦ ManifoldTotalSpace.proj_homeomorph ⟨b, s b⟩
  have hz_proj : (sM x).proj = x := ManifoldTotalSpace.proj_homeomorph ⟨x, s x⟩
  rw [jet_eq_prolong, prolong_of_mdifferentiableAt hsM hproj, diffeomorphFirstJetBundle_mk]
  have h1 : (toFirstJetBundleFiber (sM x) (FiberFirstJet.prolongAt hsM hproj)).1 =
      (FirstJetBundle.jet IB F s x).1 := by
    rw [toFirstJetBundleFiber_fst, ← ManifoldTotalSpace.homeomorph_symm_apply, hz_proj,
      FirstJetBundle.jet_fst]
    dsimp only [sM]
    rw [Homeomorph.symm_apply_apply]
  have h2 : (toFirstJetBundleFiber (sM x) (FiberFirstJet.prolongAt hsM hproj)).2 =
      (FirstJetBundle.jet IB F s x).2 := by
    rw [toFirstJetBundleFiber_snd, ← FiberFirstJet.coordAt_self,
      FiberFirstJet.coordAt_prolongAt hsM hproj (mem_chart_source _ (sM x)), hz_proj,
      FirstJetBundle.jet_snd]
    have hrep : FiberFirstJet.localRep IB 𝓘(𝕜, F) sM (sM x) = FirstJetBundle.localRep IB F s x := by
      funext u
      rw [FiberFirstJet.localRep_apply, FirstJetBundle.localRep_apply]
      dsimp only [sM]
      rw [ManifoldTotalSpace.proj_homeomorph, ManifoldTotalSpace.extChartAt_homeomorph_apply]
      simp
    rw [hrep]
  exact TotalSpace.ext hz_proj (heq_of_eq (Prod.ext h1 h2))

/-- For a differentiable section `s : ∀ b, V b` at `x`, `(diffeomorphFirstJetBundle IB F V n).symm`
carries the linear first jet `⟨x, FirstJetBundle.jet IB F s x⟩` to `jet IB 𝓘(𝕜, F) F s x`. -/
theorem diffeomorphFirstJetBundle_symm_jet (n : ℕ∞ω) {s : ∀ b, V b} {x : B}
    (hs : MDifferentiableAt IB (IB.prod 𝓘(𝕜, F)) (fun b ↦ TotalSpace.mk' F b (s b)) x) :
    (diffeomorphFirstJetBundle IB F V n).symm ⟨x, FirstJetBundle.jet IB F s x⟩ =
      jet IB 𝓘(𝕜, F) F s x :=
  (diffeomorphFirstJetBundle IB F V n).symm_apply_eq.2 (diffeomorphFirstJetBundle_jet n hs).symm

/-- `diffeomorphFirstJetBundle` intertwines vertical affine translation on `FiberFirstJetBundle`
with addition of `FirstJetBundle.ofDeriv` in `FirstJetBundle`. -/
theorem diffeomorphFirstJetBundle_vadd [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul 𝕜 (V x)] (n : ℕ∞ω) (z : ManifoldTotalSpace F V)
    (L : TangentSpace IB z.proj →L[𝕜] V z.proj) (j : FiberFirstJet IB 𝓘(𝕜, F) F V z) :
    diffeomorphFirstJetBundle IB F V n
        ⟨z, ((VerticalSpace.verticalLift IB z).toContinuousLinearMap.comp L) +ᵥ j⟩ =
      ⟨z.proj, FirstJetBundle.ofDeriv IB F z.proj L + toFirstJetBundleFiber z j⟩ := by
  rw [diffeomorphFirstJetBundle_mk, toFirstJetBundleFiber_vadd]

end FiberFirstJetBundle

end VectorBundleComparison

end TauCeti

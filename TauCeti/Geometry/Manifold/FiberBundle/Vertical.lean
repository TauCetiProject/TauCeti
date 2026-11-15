/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The vertical tangent bundle of a smooth fibre bundle

For a fibre bundle `E` over `B` (modelled on `IB`) with manifold fibre `F` (modelled on `IF`),
`TauCeti.VerticalSpace IB IF F E z` at `z : ManifoldTotalSpace F E` is `ker (mfderiv proj z)`.
Restricting tangent trivializations to `{0} × EF` in `VerticalSpace.vectorPrebundle` gives
`TauCeti.VerticalBundle IB IF F E` a `C^n` vector bundle structure (`contMDiffVectorBundle`) and
`C^n` inclusion `VerticalBundle.toTangentBundle` for `C^(n+1)` data, together with the canonical
equivalence `VerticalSpace.verticalLift` (`hasMFDerivAt_fibre_line`) on vector bundles.

## References
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, 1993, §9.3.
* D. J. Saunders, *The Geometry of Jet Bundles*, Cambridge University Press, 1989, §1.2.
-/

public section
noncomputable section

open Bundle Set Filter ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace TauCeti
section ManifoldFiber

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E]

namespace ManifoldTotalSpace
section CarrierProj
omit [TopologicalSpace B] [ChartedSpace HB B] [TopologicalSpace F] [ChartedSpace HF F]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
/-- The bundle projection on the total space charted through the fibre. -/
def proj (z : ManifoldTotalSpace F E) : B := ((homeomorph F E).symm z).proj
/-- The fibre component of `z : ManifoldTotalSpace F E` over `z.proj`. -/
def snd (z : ManifoldTotalSpace F E) : E z.proj := ((homeomorph F E).symm z).2
@[simp] theorem proj_homeomorph (p : TotalSpace F E) : (homeomorph F E p).proj = p.proj := by
  unfold proj; rw [Homeomorph.symm_apply_apply]
@[simp] theorem homeomorph_symm_proj (z : ManifoldTotalSpace F E) :
    ((homeomorph F E).symm z).proj = z.proj := (rfl)
@[simp] theorem homeomorph_mk_proj_snd (z : ManifoldTotalSpace F E) :
    homeomorph F E ⟨z.proj, z.snd⟩ = z := (homeomorph F E).apply_symm_apply z
end CarrierProj

theorem continuous_proj : Continuous (proj : ManifoldTotalSpace F E → B) :=
  (FiberBundle.continuous_proj F E).comp (homeomorph F E).symm.continuous

theorem proj_mem_of_mem_chartAt_source {z w : ManifoldTotalSpace F E}
    (hw : w ∈ (chartAt (ModelProd HB HF) z).source) :
    w.proj ∈ (trivializationAt F E z.proj).baseSet ∧ w.proj ∈ (chartAt HB z.proj).source := by
  obtain ⟨x, rfl⟩ := (homeomorph F E).surjective z; obtain ⟨y, rfl⟩ := (homeomorph F E).surjective w
  rw [proj_homeomorph, proj_homeomorph]; rw [chartAt_homeomorph] at hw
  simp only [Homeomorph.transOpenPartialHomeomorph_source, mem_preimage,
    Homeomorph.symm_apply_apply, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.prod_source, Trivialization.coe_coe, mem_inter_iff, mem_prod] at hw
  have hyb := (trivializationAt F E x.proj).mem_source.1 hw.1
  exact ⟨hyb, (trivializationAt F E x.proj).coe_fst' hyb ▸ hw.2.1⟩

theorem extChartAt_fst_eq {i z : ManifoldTotalSpace F E}
    (hi : z ∈ (chartAt (ModelProd HB HF) i).source) :
    (extChartAt (IB.prod IF) i z).1 = extChartAt IB i.proj z.proj := by
  have hz_mem := (proj_mem_of_mem_chartAt_source hi).1
  obtain ⟨xi, rfl⟩ := (homeomorph F E).surjective i
  obtain ⟨xz, rfl⟩ := (homeomorph F E).surjective z
  rw [proj_homeomorph, proj_homeomorph] at hz_mem ⊢; rw [extChartAt_homeomorph_apply]
  exact congrArg (extChartAt IB xi.proj) ((trivializationAt F E xi.proj).coe_fst' hz_mem)

theorem proj_extChartAt_symm (z : ManifoldTotalSpace F E) {y : EB × EF}
    (hy : y ∈ (extChartAt (IB.prod IF) z).target) :
    ((extChartAt (IB.prod IF) z).symm y).proj = (extChartAt IB z.proj).symm y.1 := by
  obtain ⟨x, rfl⟩ := (homeomorph F E).surjective z
  have h := extChartAt_proj_extChartAt_symm x hy
  have hsrc := (extChartAt_source (IB.prod IF) (homeomorph F E x)) ▸
    (extChartAt (IB.prod IF) (homeomorph F E x)).map_target hy
  have hmem : ((extChartAt (IB.prod IF) (homeomorph F E x)).symm y).proj ∈
      (extChartAt IB x.proj).source := by
    rw [extChartAt_source]; simpa [proj_homeomorph] using (proj_mem_of_mem_chartAt_source hsrc).2
  rw [proj_homeomorph]; rw [homeomorph_symm_proj] at h
  exact ((extChartAt IB x.proj).left_inv hmem).symm.trans (congrArg (extChartAt IB x.proj).symm h)

variable (IB IF) in
theorem hasMFDerivAt_proj (z : ManifoldTotalSpace F E) :
    HasMFDerivAt (IB.prod IF) IB (proj : ManifoldTotalSpace F E → B) z
      ((tangentSpaceCastModel IB z.proj).symm.toContinuousLinearMap ∘L
        (ContinuousLinearMap.fst 𝕜 EB EF).comp
          (tangentSpaceCastModel (IB.prod IF) z).toContinuousLinearMap) := by
  refine ⟨continuous_proj.continuousAt, ?_⟩; obtain ⟨x, rfl⟩ := (homeomorph F E).surjective z
  have hy := mem_extChartAt_target (I := IB.prod IF) (homeomorph F E x)
  refine (hasFDerivAt_fst (𝕜 := 𝕜) (E := EB) (F := EF)).hasFDerivWithinAt.congr_of_eventuallyEq
    ?_ (by simpa [writtenInExtChartAt] using extChartAt_proj_extChartAt_symm x hy)
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hy] with y hy'
  simpa [writtenInExtChartAt] using extChartAt_proj_extChartAt_symm x hy'

theorem tangentSpaceCastModel_mfderiv_proj (z : ManifoldTotalSpace F E)
    (v : TangentSpace (IB.prod IF) z) :
    tangentSpaceCastModel IB z.proj (mfderiv (IB.prod IF) IB proj z v) =
      (tangentSpaceCastModel (IB.prod IF) z v).1 := by
  rw [(hasMFDerivAt_proj IB IF z).mfderiv]; simp
theorem mfderiv_proj_surjective (z : ManifoldTotalSpace F E) :
    Function.Surjective (mfderiv (IB.prod IF) IB (proj : ManifoldTotalSpace F E → B) z) :=
  fun u ↦ ⟨(tangentSpaceCastModel (IB.prod IF) z).symm (tangentSpaceCastModel IB z.proj u, 0),
    (tangentSpaceCastModel IB z.proj).injective <| by
      rw [tangentSpaceCastModel_mfderiv_proj, ContinuousLinearEquiv.apply_symm_apply]⟩

section TangentCoordChange
variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

theorem fst_comp_tangentCoordChange {i j z : ManifoldTotalSpace F E}
    (hi : z ∈ (chartAt (ModelProd HB HF) i).source)
    (hj : z ∈ (chartAt (ModelProd HB HF) j).source) :
    (ContinuousLinearMap.fst 𝕜 EB EF).comp (tangentCoordChange (IB.prod IF) i j z) =
      (tangentCoordChange IB i.proj j.proj z.proj).comp (ContinuousLinearMap.fst 𝕜 EB EF) := by
  have hi' : z ∈ (extChartAt (IB.prod IF) i).source := (extChartAt_source (IB.prod IF) i).symm ▸ hi
  have hj' : z ∈ (extChartAt (IB.prod IF) j).source := (extChartAt_source (IB.prod IF) j).symm ▸ hj
  have hbi : z.proj ∈ (extChartAt IB i.proj).source :=
    (extChartAt_source IB i.proj).symm ▸ (proj_mem_of_mem_chartAt_source hi).2
  have hbj : z.proj ∈ (extChartAt IB j.proj).source :=
    (extChartAt_source IB j.proj).symm ▸ (proj_mem_of_mem_chartAt_source hj).2
  have hLHS := (hasFDerivAt_fst (𝕜 := 𝕜) (E := EB) (F := EF)).comp_hasFDerivWithinAt _
    (hasFDerivWithinAt_tangentCoordChange (I := IB.prod IF) ⟨hi', hj'⟩)
  have hRHS := ((extChartAt_fst_eq (IB := IB) (IF := IF) hi).symm ▸
      hasFDerivWithinAt_tangentCoordChange (I := IB) ⟨hbi, hbj⟩).comp (extChartAt (IB.prod IF) i z)
    ((hasFDerivAt_fst (𝕜 := 𝕜) (E := EB) (F := EF)).hasFDerivWithinAt (s := range (IB.prod IF)))
    fun y hy ↦ by rw [ModelWithCorners.range_prod] at hy; exact hy.1
  have hrange := extChartAt_target_subset_range i ((extChartAt (IB.prod IF) i).map_source hi')
  have hev : (fun y : EB × EF ↦ (extChartAt (IB.prod IF) j ((extChartAt (IB.prod IF) i).symm y)).1)
      =ᶠ[𝓝[range (IB.prod IF)] (extChartAt (IB.prod IF) i z)]
      fun y : EB × EF ↦ (extChartAt IB j.proj ∘ (extChartAt IB i.proj).symm) y.1 := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem
        ((extChartAt (IB.prod IF) i).map_source hi'),
      nhdsWithin_le_nhds (extChartAt_preimage_mem_nhds' hi'
        ((chartAt (ModelProd HB HF) j).open_source.mem_nhds hj))] with y hyt hyj
    rw [extChartAt_fst_eq hyj, proj_extChartAt_symm i hyt, Function.comp_apply]
  exact (IB.prod IF).uniqueDiffOn.eq hrange hLHS
    (hRHS.congr_of_eventuallyEq hev (hev.self_of_nhdsWithin hrange))

theorem fst_continuousLinearMapAt_tangent {i z : ManifoldTotalSpace F E}
    (hi : z ∈ (chartAt (ModelProd HB HF) i).source) (v : TangentSpace (IB.prod IF) z) :
    ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt 𝕜 z v).1 =
      (trivializationAt EB (TangentSpace IB) i.proj).continuousLinearMapAt 𝕜 z.proj
        (mfderiv (IB.prod IF) IB proj z v) := by
  have hz_self := mem_chart_source (ModelProd HB HF) z
  have hbi := (proj_mem_of_mem_chartAt_source hi).2
  have hv : v = (trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) z).symmL 𝕜 z
      (tangentSpaceCastModel (IB.prod IF) z v) := by
    rw [TauCeti.Manifold.symmL_trivializationAt_self]; rfl
  have hmfd : mfderiv (IB.prod IF) IB proj z v =
      (trivializationAt EB (TangentSpace IB) z.proj).symmL 𝕜 z.proj
        (tangentSpaceCastModel (IB.prod IF) z v).1 := by
    rw [TauCeti.Manifold.symmL_trivializationAt_self]
    exact (tangentSpaceCastModel IB z.proj).injective (tangentSpaceCastModel_mfderiv_proj z v)
  rw [hmfd]; nth_rw 1 [hv]
  rw [TauCeti.Manifold.continuousLinearMapAt_symmL_coordChange hz_self hi,
    TauCeti.Manifold.continuousLinearMapAt_symmL_coordChange (mem_chart_source HB z.proj) hbi]
  exact DFunLike.congr_fun (fst_comp_tangentCoordChange hz_self hi) _
end TangentCoordChange

end ManifoldTotalSpace

variable (IB IF F E) in
/-- Vertical tangent space `ker (mfderiv proj z)` of `E` at `z : ManifoldTotalSpace F E`. -/
structure VerticalSpace (z : ManifoldTotalSpace F E) where
  /-- The underlying tangent vector on `ManifoldTotalSpace F E`. -/
  val : TangentSpace (IB.prod IF) z
  /-- A vertical tangent vector lies in the kernel of `mfderiv proj z`. -/
  mfderiv_proj :
    mfderiv (IB.prod IF) IB (ManifoldTotalSpace.proj : ManifoldTotalSpace F E → B) z val = 0

namespace VerticalSpace
variable {z : ManifoldTotalSpace F E}

theorem val_injective (z : ManifoldTotalSpace F E) :
    Function.Injective (VerticalSpace.val : VerticalSpace IB IF F E z →
      TangentSpace (IB.prod IF) z) := by rintro ⟨_, _⟩ ⟨_, _⟩ ⟨⟩; rfl
instance : Zero (VerticalSpace IB IF F E z) := ⟨⟨0, map_zero _⟩⟩
instance : Add (VerticalSpace IB IF F E z) :=
  ⟨fun v w ↦ ⟨v.val + w.val, by rw [map_add, v.mfderiv_proj, w.mfderiv_proj, add_zero]⟩⟩
instance : Neg (VerticalSpace IB IF F E z) :=
  ⟨fun v ↦ ⟨-v.val, by rw [map_neg, v.mfderiv_proj, neg_zero]⟩⟩
instance : Sub (VerticalSpace IB IF F E z) :=
  ⟨fun v w ↦ ⟨v.val - w.val, by rw [map_sub, v.mfderiv_proj, w.mfderiv_proj, sub_zero]⟩⟩
instance : SMul ℕ (VerticalSpace IB IF F E z) :=
  ⟨fun n v ↦ ⟨n • v.val, by rw [map_nsmul, v.mfderiv_proj, smul_zero]⟩⟩
instance : SMul ℤ (VerticalSpace IB IF F E z) :=
  ⟨fun n v ↦ ⟨n • v.val, by rw [map_zsmul, v.mfderiv_proj, smul_zero]⟩⟩
instance : SMul 𝕜 (VerticalSpace IB IF F E z) :=
  ⟨fun c v ↦ ⟨c • v.val, by rw [map_smul, v.mfderiv_proj, smul_zero]⟩⟩
instance : AddCommGroup (VerticalSpace IB IF F E z) :=
  (val_injective z).addCommGroup VerticalSpace.val rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
instance : Module 𝕜 (VerticalSpace IB IF F E z) :=
  (val_injective z).module 𝕜 ⟨⟨VerticalSpace.val, rfl⟩, fun _ _ ↦ rfl⟩ (fun _ _ ↦ rfl)
instance : TopologicalSpace (VerticalSpace IB IF F E z) :=
  TopologicalSpace.induced VerticalSpace.val inferInstance
instance : IsTopologicalAddGroup (VerticalSpace IB IF F E z) where
  continuous_add := continuous_induced_rng.2 ((continuous_induced_dom.comp continuous_fst).add
    (continuous_induced_dom.comp continuous_snd))
  continuous_neg := continuous_induced_rng.2 continuous_induced_dom.neg
instance : ContinuousSMul 𝕜 (VerticalSpace IB IF F E z) :=
  Topology.IsInducing.continuousSMul ⟨rfl⟩ continuous_id rfl
instance : Inhabited (VerticalSpace IB IF F E z) := ⟨0⟩

/-- The canonical continuous linear inclusion of `VerticalSpace` into `TangentSpace`. -/
def toTangent (z : ManifoldTotalSpace F E) :
    VerticalSpace IB IF F E z →L[𝕜] TangentSpace (IB.prod IF) z where
  toFun := VerticalSpace.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_induced_dom
@[ext] theorem ext {v w : VerticalSpace IB IF F E z} (h : toTangent z v = toTangent z w) : v = w :=
  val_injective z h
theorem toTangent_injective (z : ManifoldTotalSpace F E) :
    Function.Injective (toTangent (IB := IB) (IF := IF) (F := F) (E := E) z) := val_injective z
@[simp] theorem mfderiv_proj_toTangent (z : ManifoldTotalSpace F E)
    (v : VerticalSpace IB IF F E z) :
    mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z (toTangent z v) = 0 := v.mfderiv_proj

/-- Construct a vertical tangent vector from a tangent vector in `ker (mfderiv proj z)`. -/
def ofTangent (v : TangentSpace (IB.prod IF) z)
    (hv : mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z v = 0) :
    VerticalSpace IB IF F E z := ⟨v, hv⟩
@[simp] theorem toTangent_ofTangent (v : TangentSpace (IB.prod IF) z)
    (hv : mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z v = 0) :
    toTangent z (ofTangent v hv) = v := (rfl)

/-- Corestrict a continuous linear map into `ker (mfderiv proj z)` to `VerticalSpace`. -/
def liftCLM {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
    (L : X →L[𝕜] TangentSpace (IB.prod IF) z)
    (hL : ∀ x, mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z (L x) = 0) :
    X →L[𝕜] VerticalSpace IB IF F E z where
  toFun x := ⟨L x, hL x⟩
  map_add' x y := ext (L.map_add x y)
  map_smul' c x := ext (L.map_smul c x)
  cont := continuous_induced_rng.2 L.cont
@[simp] theorem toTangent_liftCLM {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
    (L : X →L[𝕜] TangentSpace (IB.prod IF) z)
    (hL : ∀ x, mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z (L x) = 0) (x : X) :
    toTangent z (liftCLM L hL x) = L x := (rfl)
theorem range_toTangent (z : ManifoldTotalSpace F E) :
    LinearMap.range (toTangent (IB := IB) (IF := IF) (F := F) (E := E) z).toLinearMap =
      LinearMap.ker (mfderiv (IB.prod IF) IB
        (ManifoldTotalSpace.proj : ManifoldTotalSpace F E → B) z).toLinearMap := by
  ext v; exact ⟨by rintro ⟨w, rfl⟩; exact w.mfderiv_proj, fun hv ↦ ⟨⟨v, hv⟩, rfl⟩⟩
@[simp] theorem tangentSpaceCastModel_toTangent_fst (z : ManifoldTotalSpace F E)
    (v : VerticalSpace IB IF F E z) :
    (tangentSpaceCastModel (IB.prod IF) z (toTangent z v)).1 = 0 := by
  rw [← ManifoldTotalSpace.tangentSpaceCastModel_mfderiv_proj, mfderiv_proj_toTangent, map_zero]

/-- Preferred-chart coordinate equivalence `VerticalSpace IB IF F E z ≃L[𝕜] EF`. -/
def modelEquivAt (z : ManifoldTotalSpace F E) : VerticalSpace IB IF F E z ≃L[𝕜] EF where
  toLinearMap := ((ContinuousLinearMap.snd 𝕜 EB EF).comp
    ((tangentSpaceCastModel (IB.prod IF) z).toContinuousLinearMap.comp (toTangent z))).toLinearMap
  invFun w := ofTangent ((tangentSpaceCastModel (IB.prod IF) z).symm (0, w)) <|
    (tangentSpaceCastModel IB z.proj).injective <| by
      rw [ManifoldTotalSpace.tangentSpaceCastModel_mfderiv_proj,
        ContinuousLinearEquiv.apply_symm_apply, map_zero]
  left_inv v := ext <| (tangentSpaceCastModel (IB.prod IF) z).injective <| by
    simp only [toTangent_ofTangent, ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext (tangentSpaceCastModel_toTangent_fst z v).symm rfl
  right_inv w := by simp [toTangent_ofTangent]
  continuous_toFun :=
    continuous_snd.comp ((tangentSpaceCastModel (IB.prod IF) z).continuous.comp (toTangent z).cont)
  continuous_invFun := continuous_induced_rng.2
    ((tangentSpaceCastModel (IB.prod IF) z).symm.continuous.comp
      (continuous_const.prodMk continuous_id))
@[simp] theorem modelEquivAt_apply (z : ManifoldTotalSpace F E) (v : VerticalSpace IB IF F E z) :
    modelEquivAt z v = (tangentSpaceCastModel (IB.prod IF) z (toTangent z v)).2 := (rfl)

section Bundle
variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

theorem continuousLinearMapAt_toTangent_fst {i z : ManifoldTotalSpace F E}
    (hi : z ∈ (chartAt (ModelProd HB HF) i).source) (v : VerticalSpace IB IF F E z) :
    ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt 𝕜 z
      (toTangent z v)).1 = 0 := by
  rw [ManifoldTotalSpace.fst_continuousLinearMapAt_tangent hi, mfderiv_proj_toTangent, map_zero]
theorem mfderiv_proj_symmL_zero {i z : ManifoldTotalSpace F E}
    (hi : z ∈ (chartAt (ModelProd HB HF) i).source) (w : EF) :
    mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z
      ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 z (0, w)) = 0 := by
  have hbi := (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hi).2
  have h := ManifoldTotalSpace.fst_continuousLinearMapAt_tangent hi
    ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 z (0, w))
  rw [(trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt_symmL
    hi] at h
  have h0 := congrArg ((trivializationAt EB (TangentSpace IB) i.proj).symmL 𝕜 z.proj) h.symm
  rwa [(trivializationAt EB (TangentSpace IB) i.proj).symmL_continuousLinearMapAt hbi,
    map_zero] at h0

open Classical in
/-- Local pretrivialization of `VerticalSpace IB IF F E` over the chart domain of `i`. -/
def pretrivializationAt (i : ManifoldTotalSpace F E) :
    Pretrivialization EF (π EF (VerticalSpace IB IF F E)) where
  toFun p := (p.proj, ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF))
    i).continuousLinearMapAt 𝕜 p.proj (toTangent p.proj p.2)).2)
  invFun q := if hq : q.1 ∈ (chartAt (ModelProd HB HF) i).source then
      ⟨q.1, ofTangent ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL
        𝕜 q.1 (0, q.2)) (mfderiv_proj_symmL_zero hq q.2)⟩
    else ⟨q.1, 0⟩
  source := π EF (VerticalSpace IB IF F E) ⁻¹' (chartAt (ModelProd HB HF) i).source
  target := (chartAt (ModelProd HB HF) i).source ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hq := by split_ifs with h; exacts [h, (h hq.1).elim]
  left_inv' := by
    rintro ⟨z, v⟩ (hz : z ∈ (chartAt (ModelProd HB HF) i).source)
    dsimp only; rw [dite_eq_left hz]; congr 1; ext; simp only [toTangent_ofTangent]
    set eT := trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i
    rw [show (0, (eT.continuousLinearMapAt 𝕜 z (toTangent z v)).2) =
        eT.continuousLinearMapAt 𝕜 z (toTangent z v) from
        Prod.ext (continuousLinearMapAt_toTangent_fst hz v).symm rfl,
      eT.symmL_continuousLinearMapAt hz]
  right_inv' := by
    rintro ⟨z, w⟩ ⟨hz : z ∈ (chartAt _ i).source, -⟩; dsimp only; rw [dite_eq_left hz]
    simp [(trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt_symmL hz]
  open_target := (chartAt (ModelProd HB HF) i).open_source.prod isOpen_univ
  baseSet := (chartAt (ModelProd HB HF) i).source
  open_baseSet := (chartAt (ModelProd HB HF) i).open_source
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl
@[simp] theorem pretrivializationAt_apply (i : ManifoldTotalSpace F E)
    (p : TotalSpace EF (VerticalSpace IB IF F E)) :
    pretrivializationAt i p = (p.proj, ((trivializationAt (EB × EF)
      (TangentSpace (IB.prod IF)) i).continuousLinearMapAt 𝕜 p.proj (toTangent p.proj p.2)).2) :=
  (rfl)

omit [NontriviallyNormedField 𝕜] [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  [TopologicalSpace B] [ChartedSpace HB B] [NormedAddCommGroup EF] [NormedSpace 𝕜 EF]
  [TopologicalSpace HF] [TopologicalSpace F] [ChartedSpace HF F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
private theorem cast_snd_of_eq_mk {X : Type*} {Y : X → Type*} {a : TotalSpace EF Y}
    {x : X} {v : Y x} (h : a = ⟨x, v⟩) (hp : a.proj = x) :
    cast (congrArg Y hp) a.2 = v := by subst h; rfl
theorem pretrivializationAt_symm_apply {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (w : EF) :
    (pretrivializationAt (IB := IB) (IF := IF) (F := F) (E := E) i).symm z w =
      ofTangent ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 z (0, w))
        (mfderiv_proj_symmL_zero hz w) := by
  rw [Pretrivialization.symm_apply _ hz]
  exact cast_snd_of_eq_mk (dite_eq_left hz) (congrArg TotalSpace.proj (dite_eq_left hz))
instance pretrivializationAt_isLinear (i : ManifoldTotalSpace F E) :
    (pretrivializationAt (IB := IB) (IF := IF) (F := F) (E := E) i).IsLinear 𝕜 where
  linear z _ := (((ContinuousLinearMap.snd 𝕜 EB EF).comp
    (((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt
      𝕜 z).comp (toTangent z))).isLinear)

/-- Vertical coordinate change from chart `i` to chart `j` at `z`. -/
def coordChange (i j z : ManifoldTotalSpace F E) : EF →L[𝕜] EF :=
  (ContinuousLinearMap.snd 𝕜 EB EF).comp
    ((tangentCoordChange (IB.prod IF) i j z).comp (ContinuousLinearMap.inr 𝕜 EB EF))
@[simp] theorem coordChange_apply (i j z : ManifoldTotalSpace F E) (w : EF) :
    coordChange (IB := IB) (IF := IF) (F := F) (E := E) i j z w =
      (tangentCoordChange (IB.prod IF) i j z (0, w)).2 := (rfl)

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
theorem contMDiffOn_coordChange {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] (i j : ManifoldTotalSpace F E) :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    ContMDiffOn (IB.prod IF) 𝓘(𝕜, EF →L[𝕜] EF) n
      (coordChange (IB := IB) (IF := IF) (F := F) (E := E) i j)
      ((chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) j).source) := by
  have : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
  have : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
  have : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
  have : IsManifold IB n B := .of_le (n := n + 1) le_self_add
  have : IsManifold IF n F := .of_le (n := n + 1) le_self_add
  have : ContMDiffFiberBundle n F E IB IF := .of_le (n := n + 1) le_self_add
  exact contMDiffOn_const.clm_comp (((tangentBundleCore.isContMDiff (I := IB.prod IF)
    (M := ManifoldTotalSpace F E) (n := n)).1 (achart _ i) (achart _ j)).clm_comp contMDiffOn_const)

/-- The `VectorPrebundle` giving `VerticalSpace IB IF F E` its vector bundle structure. -/
def vectorPrebundle : VectorPrebundle 𝕜 EF (VerticalSpace IB IF F E) where
  pretrivializationAtlas := range (pretrivializationAt (IB := IB) (IF := IF) (F := F) (E := E))
  pretrivialization_linear' := by rintro _ ⟨i, rfl⟩; infer_instance
  pretrivializationAt := pretrivializationAt
  mem_base_pretrivializationAt z := mem_chart_source _ z
  pretrivialization_mem_atlas z := ⟨z, rfl⟩
  exists_coordChange := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    have : IsManifold IB (0 + 1) B := (by simpa); have : IsManifold IF (0 + 1) F := by simpa
    have : ContMDiffFiberBundle (0 + 1) F E IB IF := by simpa
    refine ⟨coordChange (IB := IB) (IF := IF) (F := F) (E := E) i j,
      (contMDiffOn_coordChange (IB := IB) (IF := IF) (F := F) (E := E) (n := 0) i j).continuousOn,
      fun z hz w ↦ ?_⟩
    rw [pretrivializationAt_apply, pretrivializationAt_symm_apply hz.1, toTangent_ofTangent,
      TauCeti.Manifold.continuousLinearMapAt_symmL_coordChange hz.1 hz.2, coordChange_apply]
  totalSpaceMk_isInducing z := by
    have hfun : (pretrivializationAt (IB := IB) (IF := IF) (F := F) (E := E) z ∘ TotalSpace.mk z) =
        Prod.mk z ∘ modelEquivAt z := by
      funext v; rw [Function.comp_apply, Function.comp_apply, pretrivializationAt_apply]
      dsimp only; rw [TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self]; rfl
    exact hfun ▸ (isInducing_prodMkRight z).comp (modelEquivAt z).toHomeomorph.isInducing
instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace EF (VerticalSpace IB IF F E)) :=
  (vectorPrebundle (IB := IB) (IF := IF) (F := F) (E := E)).totalSpaceTopology
instance instFiberBundle : FiberBundle EF (VerticalSpace IB IF F E) :=
  (vectorPrebundle (IB := IB) (IF := IF) (F := F) (E := E)).toFiberBundle
instance instVectorBundle : VectorBundle 𝕜 EF (VerticalSpace IB IF F E) :=
  (vectorPrebundle (IB := IB) (IF := IF) (F := F) (E := E)).toVectorBundle
@[simp] theorem trivializationAt_baseSet (i : ManifoldTotalSpace F E) :
    (trivializationAt EF (VerticalSpace IB IF F E) i).baseSet =
      (chartAt (ModelProd HB HF) i).source := (rfl)
@[simp] theorem trivializationAt_apply (i : ManifoldTotalSpace F E)
    (p : TotalSpace EF (VerticalSpace IB IF F E)) :
    trivializationAt EF (VerticalSpace IB IF F E) i p = (p.proj, ((trivializationAt (EB × EF)
      (TangentSpace (IB.prod IF)) i).continuousLinearMapAt 𝕜 p.proj (toTangent p.proj p.2)).2) :=
  (rfl)
@[simp] theorem continuousLinearMapAt_trivializationAt_self (z : ManifoldTotalSpace F E)
    (v : VerticalSpace IB IF F E z) :
    (trivializationAt EF (VerticalSpace IB IF F E) z).continuousLinearMapAt 𝕜 z v =
      modelEquivAt z v := by
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _
      (mem_baseSet_trivializationAt EF (VerticalSpace IB IF F E) z),
    trivializationAt_apply, TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self]; rfl

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
theorem contMDiffVectorBundle {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    ContMDiffVectorBundle n EF (VerticalSpace IB IF F E) (IB.prod IF) := by
  have : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
  have : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
  have : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
  have : (vectorPrebundle (IB := IB) (IF := IF) (F := F) (E := E)).IsContMDiff (IB.prod IF) n := by
    refine ⟨?_⟩; rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    refine ⟨coordChange i j, contMDiffOn_coordChange i j, fun z hz w ↦ ?_⟩
    rw [pretrivializationAt_apply, pretrivializationAt_symm_apply hz.1, toTangent_ofTangent,
      TauCeti.Manifold.continuousLinearMapAt_symmL_coordChange hz.1 hz.2, coordChange_apply]
  exact (vectorPrebundle (IB := IB) (IF := IF) (F := F) (E := E)).contMDiffVectorBundle (IB.prod IF)
omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
instance [IsManifold IB ∞ B] [IsManifold IF ∞ F] [ContMDiffFiberBundle ∞ F E IB IF] :
    ContMDiffVectorBundle ∞ EF (VerticalSpace IB IF F E) (IB.prod IF) := by
  have : IsManifold IB (∞ + 1) B := (by simpa); have : IsManifold IF (∞ + 1) F := by simpa
  have : ContMDiffFiberBundle (∞ + 1) F E IB IF := (by simpa); exact contMDiffVectorBundle
omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
instance [IsManifold IB ω B] [IsManifold IF ω F] [ContMDiffFiberBundle ω F E IB IF] :
    ContMDiffVectorBundle ω EF (VerticalSpace IB IF F E) (IB.prod IF) := by
  have : IsManifold IB (ω + 1) B := (by simpa); have : IsManifold IF (ω + 1) F := by simpa
  have : ContMDiffFiberBundle (ω + 1) F E IB IF := (by simpa); exact contMDiffVectorBundle
end Bundle
end VerticalSpace

variable (IB IF F E) in
/-- The **vertical tangent bundle** `VE` of a smooth fibre bundle `E`. -/
abbrev VerticalBundle := TotalSpace EF (VerticalSpace IB IF F E)

namespace VerticalBundle
/-- The canonical bundle inclusion from `VerticalBundle` into `TangentBundle`. -/
def toTangentBundle (p : VerticalBundle IB IF F E) :
    TangentBundle (IB.prod IF) (ManifoldTotalSpace F E) :=
  ⟨p.proj, VerticalSpace.toTangent p.proj p.2⟩
@[simp] theorem toTangentBundle_proj (p : VerticalBundle IB IF F E) :
    (toTangentBundle p).proj = p.proj := (rfl)
@[simp] theorem toTangentBundle_snd (p : VerticalBundle IB IF F E) :
    (toTangentBundle p).2 = VerticalSpace.toTangent p.proj p.2 := (rfl)
theorem toTangentBundle_injective :
    Function.Injective (toTangentBundle (IB := IB) (IF := IF) (F := F) (E := E)) := by
  rintro ⟨z₁, v₁⟩ ⟨z₂, v₂⟩ h; obtain rfl : z₁ = z₂ := congrArg TotalSpace.proj h
  exact congrArg (TotalSpace.mk' EF z₁) (VerticalSpace.ext (eq_of_heq (TotalSpace.mk.inj h).2))

theorem contMDiff_toTangentBundle {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    ContMDiff ((IB.prod IF).prod 𝓘(𝕜, EF)) ((IB.prod IF).prod 𝓘(𝕜, EB × EF)) n
      (toTangentBundle (IB := IB) (IF := IF) (F := F) (E := E)) := by
  have : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
  have : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
  have : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
  have : IsManifold IB n B := .of_le (n := n + 1) le_self_add
  have : IsManifold IF n F := .of_le (n := n + 1) le_self_add
  have : ContMDiffFiberBundle n F E IB IF := .of_le (n := n + 1) le_self_add
  have := VerticalSpace.contMDiffVectorBundle (IB := IB) (IF := IF) (F := F) (E := E) (n := n)
  intro p₀
  have hproj : ContMDiffAt ((IB.prod IF).prod 𝓘(𝕜, EF)) (IB.prod IF) n
      (fun p : VerticalBundle IB IF F E ↦ p.proj) p₀ :=
    Bundle.contMDiffAt_proj (VerticalSpace IB IF F E)
  have hsnd : ContMDiffAt ((IB.prod IF).prod 𝓘(𝕜, EF)) 𝓘(𝕜, EF) n
      (fun p : VerticalBundle IB IF F E ↦
        (trivializationAt EF (VerticalSpace IB IF F E) p₀.proj p).2) p₀ :=
    (Bundle.contMDiffAt_totalSpace_iff.1 contMDiffAt_id).2
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨hproj,
    ((contMDiffAt_const (c := (0 : EB))).prodMk_space hsnd).congr_of_eventuallyEq ?_⟩
  filter_upwards [hproj.continuousAt.preimage_mem_nhds
    ((chartAt (ModelProd HB HF) p₀.proj).open_source.mem_nhds (mem_chart_source _ p₀.proj))]
    with p hp
  have h1 := VerticalSpace.continuousLinearMapAt_toTangent_fst hp p.2
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _ hp] at h1
  refine Prod.ext h1 ?_; rw [VerticalSpace.trivializationAt_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _ hp]; rfl
end VerticalBundle
end ManifoldFiber

namespace VerticalSpace
variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem hasFDerivAt_fibre_line_coord (u : EB) (y₀ y : F) :
    HasFDerivAt (fun t : 𝕜 ↦ (u, y₀ + t • y))
      (ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) ((0 : EB), y)) 0 := by
  suffices hd : ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) ((0 : EB), y) =
      (0 : 𝕜 →L[𝕜] EB).prod ((ContinuousLinearMap.id 𝕜 𝕜).smulRight y) by
    exact hd ▸ (hasFDerivAt_const (𝕜 := 𝕜) u (0 : 𝕜)).prodMk
      (((hasFDerivAt_id (𝕜 := 𝕜) (0 : 𝕜)).smul_const y).const_add y₀)
  ext <;> simp

variable [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ b, AddCommGroup (V b)]
  [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)] [FiberBundle F V] [VectorBundle 𝕜 F V]

variable (IB) in
/-- Canonical equivalence `V z.proj ≃L[𝕜] VerticalSpace IB 𝓘(𝕜, F) F V z` by fibre translation. -/
def verticalLift (z : ManifoldTotalSpace F V) :
    V z.proj ≃L[𝕜] VerticalSpace IB 𝓘(𝕜, F) F V z :=
  ((trivializationAt F V z.proj).continuousLinearEquivAt 𝕜 z.proj
    (mem_baseSet_trivializationAt F V z.proj)).trans (modelEquivAt z).symm
theorem modelEquivAt_verticalLift (z : ManifoldTotalSpace F V) (w : V z.proj) :
    modelEquivAt z (verticalLift IB z w) =
      (trivializationAt F V z.proj).continuousLinearMapAt 𝕜 z.proj w := by
  rw [verticalLift, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply,
    Trivialization.continuousLinearEquivAt_apply]
  exact ((trivializationAt F V z.proj).continuousLinearMapAt_apply_of_mem (R := 𝕜)
    (mem_baseSet_trivializationAt F V z.proj) w).symm

private theorem extChartAt_fibre_line {i z : ManifoldTotalSpace F V}
    (hbi : z.proj ∈ (trivializationAt F V i.proj).baseSet) (w : V z.proj) (t : 𝕜) :
    extChartAt (IB.prod 𝓘(𝕜, F)) i (ManifoldTotalSpace.homeomorph F V ⟨z.proj, z.snd + t • w⟩) =
      (extChartAt IB i.proj z.proj, (trivializationAt F V i.proj ⟨z.proj, z.snd⟩).2 +
        t • (trivializationAt F V i.proj ⟨z.proj, w⟩).2) := by
  obtain ⟨xi, rfl⟩ := (ManifoldTotalSpace.homeomorph F V).surjective i
  rw [ManifoldTotalSpace.proj_homeomorph] at hbi ⊢
  have hl := (trivializationAt F V xi.proj).linear 𝕜 hbi
  rw [ManifoldTotalSpace.extChartAt_homeomorph_apply,
    (trivializationAt F V xi.proj).coe_fst' (x := ⟨z.proj, z.snd + t • w⟩) hbi, hl.1, hl.2]; simp

theorem hasMFDerivAt_fibre_line (z : ManifoldTotalSpace F V) (w : V z.proj) :
    HasMFDerivAt 𝓘(𝕜) (IB.prod 𝓘(𝕜, F))
      (fun t : 𝕜 ↦ ManifoldTotalSpace.homeomorph F V ⟨z.proj, z.snd + t • w⟩) 0
      (ContinuousLinearMap.smulRight
        (tangentSpaceCastModel 𝓘(𝕜) (0 : 𝕜)).toContinuousLinearMap
        (toTangent z (verticalLift IB z w))) := by
  have hb := mem_baseSet_trivializationAt F V z.proj
  set γ : 𝕜 → ManifoldTotalSpace F V := fun t ↦
    ManifoldTotalSpace.homeomorph F V ⟨z.proj, z.snd + t • w⟩
  have hlin : ∀ t : 𝕜, (trivializationAt F V z.proj ⟨z.proj, z.snd + t • w⟩).2 =
      (trivializationAt F V z.proj ⟨z.proj, z.snd⟩).2 +
        t • (trivializationAt F V z.proj ⟨z.proj, w⟩).2 := fun _ ↦ by
    have hl := (trivializationAt F V z.proj).linear 𝕜 hb; rw [hl.1, hl.2]
  have hcont : ContMDiffAt 𝓘(𝕜) (IB.prod 𝓘(𝕜, F)) 0 γ 0 := by
    refine ManifoldTotalSpace.contMDiffAt_iff.2 ⟨contMDiffAt_const, ?_⟩
    dsimp only [γ]; simp_rw [hlin]
    exact contMDiffAt_const.add (contMDiffAt_id.smul contMDiffAt_const)
  refine ⟨hcont.continuousAt, ?_⟩; have hγ0 : γ 0 = z := by simp [γ]
  have hw_coord : modelEquivAt (IB := IB) z (verticalLift IB z w) =
      (trivializationAt F V z.proj ⟨z.proj, w⟩).2 := by
    rw [modelEquivAt_verticalLift,
      (trivializationAt F V z.proj).continuousLinearMapAt_apply_of_mem (R := 𝕜) hb]
  change HasFDerivWithinAt (writtenInExtChartAt 𝓘(𝕜) (IB.prod 𝓘(𝕜, F)) 0 γ)
    ((tangentSpaceCastModel (IB.prod 𝓘(𝕜, F)) (γ 0)).toContinuousLinearMap ∘L
      ContinuousLinearMap.smulRight (tangentSpaceCastModel 𝓘(𝕜) (0 : 𝕜)).toContinuousLinearMap
        (toTangent z (verticalLift IB z w)) ∘L
      (tangentSpaceCastModel 𝓘(𝕜) (0 : 𝕜)).symm.toContinuousLinearMap)
    (range 𝓘(𝕜)) (extChartAt 𝓘(𝕜) (0 : 𝕜) 0)
  have hmap : ((tangentSpaceCastModel (IB.prod 𝓘(𝕜, F)) z).toContinuousLinearMap ∘L
        ContinuousLinearMap.smulRight (tangentSpaceCastModel 𝓘(𝕜) (0 : 𝕜)).toContinuousLinearMap
          (toTangent z (verticalLift IB z w)) ∘L
        (tangentSpaceCastModel 𝓘(𝕜) (0 : 𝕜)).symm.toContinuousLinearMap) =
      ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜)
        ((0 : EB), (trivializationAt F V z.proj ⟨z.proj, w⟩).2) := by
    ext1; exact Prod.ext (by simp) (by simpa using hw_coord)
  rw [hγ0, hmap, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
  have heq : ∀ t : 𝕜, writtenInExtChartAt 𝓘(𝕜) (IB.prod 𝓘(𝕜, F)) 0 γ t =
      (extChartAt IB z.proj z.proj, (trivializationAt F V z.proj ⟨z.proj, z.snd⟩).2 +
        t • (trivializationAt F V z.proj ⟨z.proj, w⟩).2) := fun t ↦ by
    simpa [writtenInExtChartAt, hγ0, γ] using extChartAt_fibre_line (IB := IB) hb w t
  exact (hasFDerivAt_fibre_line_coord (extChartAt IB z.proj z.proj) _ _).hasFDerivWithinAt
    |>.congr_of_eventuallyEq (.of_forall heq) (heq 0)

theorem continuousLinearMapAt_verticalLift [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F V IB]
    {i z : ManifoldTotalSpace F V} (hi : z ∈ (chartAt (ModelProd HB F) i).source)
    (w : V z.proj) :
    (trivializationAt F (VerticalSpace IB 𝓘(𝕜, F) F V) i).continuousLinearMapAt 𝕜 z
        (verticalLift IB z w) =
      (trivializationAt F V i.proj).continuousLinearMapAt 𝕜 z.proj w := by
  have hbi := (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hi).1
  have h0eq : ManifoldTotalSpace.homeomorph F V ⟨z.proj, z.snd + (0 : 𝕜) • w⟩ = z := by simp
  have hcomp := ((mdifferentiableAt_extChartAt (I := IB.prod 𝓘(𝕜, F))
    (h0eq.symm ▸ hi)).hasMFDerivAt.comp 0 (hasMFDerivAt_fibre_line (IB := IB) z w)).2
  rw [writtenInExtChartAt_model_space, modelWithCornersSelf_coe, range_id,
    extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq, hasFDerivWithinAt_univ] at hcomp
  have hdirect := hasFDerivAt_fibre_line_coord (𝕜 := 𝕜) (extChartAt IB i.proj z.proj)
    (trivializationAt F V i.proj ⟨z.proj, z.snd⟩).2 (trivializationAt F V i.proj ⟨z.proj, w⟩).2
  rw [← funext (extChartAt_fibre_line (IB := IB) hbi w)] at hdirect
  have huniq := DFunLike.congr_fun (hcomp.unique hdirect) (1 : 𝕜)
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] at huniq
  rw [h0eq, ContinuousLinearMap.smulRight_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, one_smul] at huniq
  change mfderiv (IB.prod 𝓘(𝕜, F)) 𝓘(𝕜, EB × F) (extChartAt (IB.prod 𝓘(𝕜, F)) i) z
    (toTangent z (verticalLift IB z w)) = _ at huniq
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hi] at huniq
  rw [(trivializationAt F (VerticalSpace IB 𝓘(𝕜, F) F V) i).continuousLinearMapAt_apply_of_mem
      (R := 𝕜) hi,
    (trivializationAt F V i.proj).continuousLinearMapAt_apply_of_mem (R := 𝕜) hbi,
    trivializationAt_apply]
  exact congrArg Prod.snd huniq
end VerticalSpace
end TauCeti

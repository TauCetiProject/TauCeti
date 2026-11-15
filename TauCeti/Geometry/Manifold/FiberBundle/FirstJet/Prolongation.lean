/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Jet.Section
public import TauCeti.Geometry.Manifold.FiberBundle.FirstJet.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Holonomic prolongation, Cartan contact characterization, and vector-bundle comparison

For a fibre bundle `E` over `B` (modelled on `IB`) with manifold fibre `F` (modelled on `IF`),
this file constructs holonomic prolongations `FiberFirstJet.prolongAt`,
`FiberFirstJetBundle.prolong`, and `FiberFirstJetBundle.jet` (`coordAt_prolongAt`, `prolong_congr`,
`contMDiffOn_prolong`, `contMDiff_jet`), bridges to `TauCeti.FirstJetAt`
(`prolong_eq_iff_firstJetAt_mk_eq`, `exists_contMDiffAt_prolong_eq`), characterizes holonomic
sections via `contactFormAt` (`contactFormAt_comp_mfderiv_eq_zero_iff`,
`prolongAt_quadratic_trivial_eval`), and builds the canonical `C^n` diffeomorphism
`diffeomorphFirstJetBundle` with `TauCeti.FirstJetBundle` for vector bundles.

## References
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, 1993, §12.
* D. J. Saunders, *The Geometry of Jet Bundles*, Cambridge University Press, 1989, §§4.1–4.2.
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

namespace FiberFirstJet
/-- Holonomic prolongation at `x` of `s : B → ManifoldTotalSpace F E` (`(proj ∘ s) =ᶠ[𝓝 x] id`). -/
def prolongAt {s : B → ManifoldTotalSpace F E} {x : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s x)
    (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id) :
    FiberFirstJet IB IF F E (s x) where
  toContinuousLinearMap :=
    (mfderiv IB (IB.prod IF) s x).comp (tangentSpaceCast IB (s x).proj x).toContinuousLinearMap
  mfderiv_proj_comp := by
    rw [← ContinuousLinearMap.comp_assoc,
      ← mfderiv_comp x (ManifoldTotalSpace.hasMFDerivAt_proj IB IF (s x)).mdifferentiableAt hs,
      hproj.mfderiv_eq, mfderiv_id]; ext u; rfl
@[simp] theorem prolongAt_apply {s : B → ManifoldTotalSpace F E} {x : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s x)
    (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id) (u : TangentSpace IB (s x).proj) :
    prolongAt hs hproj u = mfderiv IB (IB.prod IF) s x (tangentSpaceCast IB (s x).proj x u) :=
  (rfl)
theorem modelEquivAt_prolongAt {s : B → ManifoldTotalSpace F E} {x : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s x)
    (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id) :
    modelEquivAt (s x) (prolongAt hs hproj) = (ContinuousLinearMap.snd 𝕜 EB EF).comp
      (fderivWithin 𝕜 (writtenInExtChartAt IB (IB.prod IF) x s) (range IB)
        (extChartAt IB x x)) := by
  ext u; rw [modelEquivAt_apply, prolongAt_apply]
  have hmfd : mfderiv IB (IB.prod IF) s x =
      (tangentSpaceCastModel (IB.prod IF) (s x)).symm.toContinuousLinearMap ∘L
        fderivWithin 𝕜 (writtenInExtChartAt IB (IB.prod IF) x s) (range IB) (extChartAt IB x x) ∘L
        (tangentSpaceCastModel IB x).toContinuousLinearMap := ite_eq_left hs
  rw [hmfd]; rfl

/-- Local coordinate representative of `s : B → ManifoldTotalSpace F E` in chart `i`. -/
def localRep (IB : ModelWithCorners 𝕜 EB HB) (IF : ModelWithCorners 𝕜 EF HF)
    (s : B → ManifoldTotalSpace F E) (i : ManifoldTotalSpace F E) (u : EB) : EF :=
  (extChartAt (IB.prod IF) i (s ((extChartAt IB i.proj).symm u))).2
@[simp] theorem localRep_apply (IB : ModelWithCorners 𝕜 EB HB) (IF : ModelWithCorners 𝕜 EF HF)
    (s : B → ManifoldTotalSpace F E) (i : ManifoldTotalSpace F E) (u : EB) :
    localRep IB IF s i u = (extChartAt (IB.prod IF) i (s ((extChartAt IB i.proj).symm u))).2 :=
  (rfl)
theorem contDiffWithinAt_localRep {n : ℕ∞ω} [IsManifold IB n B] [IsManifold IF n F]
    [ContMDiffFiberBundle n F E IB IF] {s : B → ManifoldTotalSpace F E} {x : B}
    {i : ManifoldTotalSpace F E} (hs : ContMDiffAt IB (IB.prod IF) n s x)
    (hi : s x ∈ (chartAt (ModelProd HB HF) i).source) (hbi : x ∈ (extChartAt IB i.proj).source) :
    ContDiffWithinAt 𝕜 n (localRep IB IF s i) (range IB) (extChartAt IB i.proj x) := by
  have hpt := (extChartAt IB i.proj).left_inv hbi
  exact contMDiffWithinAt_iff_contDiffWithinAt.1
    (((ContinuousLinearMap.snd 𝕜 EB EF).contMDiffAt.comp _
      ((hpt.symm ▸ contMDiffAt_extChartAt' hi).comp _ (hpt.symm ▸ hs))).comp_contMDiffWithinAt _
      (contMDiffWithinAt_extChartAt_symm_range i.proj ((extChartAt IB i.proj).map_source hbi)))

theorem hasFDerivWithinAt_writtenInExtChartAt_of_proj_eventuallyEq
    {s : B → ManifoldTotalSpace F E} {x : B} (hs : MDifferentiableAt IB (IB.prod IF) s x)
    (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id) :
    HasFDerivWithinAt (writtenInExtChartAt IB (IB.prod IF) x s)
      ((ContinuousLinearMap.id 𝕜 EB).prod (modelEquivAt (s x) (prolongAt hs hproj)))
      (range IB) (extChartAt IB x x) := by
  have hx_eq : (s x).proj = x := hproj.eq_of_nhds; have hxx' := mem_extChartAt_source (I := IB) x
  set W := writtenInExtChartAt IB (IB.prod IF) x s
  have hW_fst : (Prod.fst ∘ W) =ᶠ[𝓝[range IB] extChartAt IB x x] id := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := IB) x,
      nhdsWithin_le_nhds (extChartAt_preimage_mem_nhds (hs.continuousAt.preimage_mem_nhds
        ((chartAt (ModelProd HB HF) (s x)).open_source.mem_nhds (mem_chart_source _ (s x))))),
      nhdsWithin_le_nhds (extChartAt_preimage_mem_nhds hproj)] with u hu1 hu2 hu3
    have hu3' : (s ((extChartAt IB x).symm u)).proj = (extChartAt IB x).symm u := hu3
    simp only [W, writtenInExtChartAt, Function.comp_apply, id_eq]
    rw [ManifoldTotalSpace.extChartAt_fst_eq hu2, hx_eq, hu3', (extChartAt IB x).right_inv hu1]
  have hd := hs.hasMFDerivAt.2
  have hfst : (ContinuousLinearMap.fst 𝕜 EB EF).comp
      (fderivWithin 𝕜 W (range IB) (extChartAt IB x x)) = ContinuousLinearMap.id 𝕜 EB :=
    (IB.uniqueDiffOn _ (extChartAt_target_subset_range x
      ((extChartAt IB x).map_source hxx'))).eq
      ((hasFDerivAt_fst (𝕜 := 𝕜) (E := EB) (F := EF)).comp_hasFDerivWithinAt _
        hs.differentiableWithinAt_writtenInExtChartAt.hasFDerivWithinAt)
      ((hasFDerivWithinAt_id (𝕜 := 𝕜) (extChartAt IB x x) (range IB)).congr_of_eventuallyEq
        hW_fst (by
          dsimp only [W, writtenInExtChartAt, Function.comp_apply, id_eq]
          rw [(extChartAt IB x).left_inv hxx',
            ManifoldTotalSpace.extChartAt_fst_eq (mem_chart_source _ (s x)), hx_eq]))
  suffices heq : ((tangentSpaceCastModel (IB.prod IF) (s x)).toContinuousLinearMap ∘L
        mfderiv IB (IB.prod IF) s x ∘L (tangentSpaceCastModel IB x).symm.toContinuousLinearMap) =
      (ContinuousLinearMap.id 𝕜 EB).prod (modelEquivAt (s x) (prolongAt hs hproj)) by rwa [← heq]
  have hmfd : mfderiv IB (IB.prod IF) s x =
      (tangentSpaceCastModel (IB.prod IF) (s x)).symm.toContinuousLinearMap ∘L
        fderivWithin 𝕜 W (range IB) (extChartAt IB x x) ∘L
        (tangentSpaceCastModel IB x).toContinuousLinearMap := ite_eq_left hs
  rw [hmfd, modelEquivAt_prolongAt]
  ext v <;> simp only [W, comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.coe_snd']
  exact DFunLike.congr_fun hfst v

theorem coordAt_prolongAt [IsManifold IB 1 B] [IsManifold IF 1 F]
    [ContMDiffFiberBundle 1 F E IB IF] {s : B → ManifoldTotalSpace F E} {x : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s x) (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id)
    {i : ManifoldTotalSpace F E} (hi : s x ∈ (chartAt (ModelProd HB HF) i).source) :
    coordAt i (prolongAt hs hproj) =
      fderivWithin 𝕜 (localRep IB IF s i) (range IB) (extChartAt IB i.proj x) := by
  have hx_eq : (s x).proj = x := hproj.eq_of_nhds
  have hbi : x ∈ (extChartAt IB i.proj).source :=
    (extChartAt_source IB i.proj).symm ▸ hx_eq ▸
      (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hi).2
  have hi' : s x ∈ (extChartAt (IB.prod IF) i).source :=
    (extChartAt_source (IB.prod IF) i).symm ▸ hi
  have hsx' := mem_extChartAt_source (I := IB.prod IF) (s x)
  have hxx' := mem_extChartAt_source (I := IB) x
  have hcoord : coordAt i (prolongAt hs hproj) = coordChange (IB := IB) (IF := IF) (s x) i (s x)
      (modelEquivAt (s x) (prolongAt hs hproj)) := by
    rw [← coordAt_self (s x) (prolongAt hs hproj),
      ← coordAt_ofCoordAt_eq_coordChange (mem_chart_source _ (s x)) hi, ofCoordAt_coordAt]
  rw [hcoord]; set W := writtenInExtChartAt IB (IB.prod IF) x s
  have hbase : HasFDerivWithinAt (extChartAt IB x ∘ (extChartAt IB i.proj).symm)
      (tangentCoordChange IB i.proj (s x).proj (s x).proj) (range IB) (extChartAt IB i.proj x) := by
    rw [hx_eq]; exact hasFDerivWithinAt_tangentCoordChange ⟨hbi, hxx'⟩
  have hpt1 : (extChartAt IB x ∘ (extChartAt IB i.proj).symm) (extChartAt IB i.proj x) =
      extChartAt IB x x := by rw [Function.comp_apply, (extChartAt IB i.proj).left_inv hbi]
  have hmid := (hpt1 ▸ hasFDerivWithinAt_writtenInExtChartAt_of_proj_eventuallyEq hs hproj).comp _
    hbase fun u _ ↦ by rw [Function.comp_apply, extChartAt_coe]; exact mem_range_self _
  have hpt2 : (W ∘ (extChartAt IB x ∘ (extChartAt IB i.proj).symm)) (extChartAt IB i.proj x) =
      extChartAt (IB.prod IF) (s x) (s x) := by
    dsimp only [W, writtenInExtChartAt, Function.comp_apply]
    rw [(extChartAt IB i.proj).left_inv hbi, (extChartAt IB x).left_inv hxx']
  have htop := hasFDerivAt_snd.comp_hasFDerivWithinAt _
    ((hpt2 ▸ hasFDerivWithinAt_tangentCoordChange (I := IB.prod IF) ⟨hsx', hi'⟩).comp _ hmid
      fun u _ ↦ by
        simp only [W, writtenInExtChartAt, Function.comp_apply, extChartAt_coe]
        exact mem_range_self _)
  have hev : localRep IB IF s i =ᶠ[𝓝[range IB] extChartAt IB i.proj x]
      fun u ↦ ((extChartAt (IB.prod IF) i ∘ (extChartAt (IB.prod IF) (s x)).symm)
        ((W ∘ (extChartAt IB x ∘ (extChartAt IB i.proj).symm)) u)).2 := by
    filter_upwards [nhdsWithin_le_nhds (extChartAt_preimage_mem_nhds' hbi (Filter.inter_mem
      (hs.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (I := IB.prod IF) (s x)).mem_nhds hsx'))
      ((isOpen_extChartAt_source (I := IB) x).mem_nhds hxx')))] with u ⟨hus, hux⟩
    simp only [localRep_apply, W, writtenInExtChartAt, Function.comp_apply]
    rw [(extChartAt IB x).left_inv hux, (extChartAt (IB.prod IF) (s x)).left_inv hus]
  have hpt_eq : localRep IB IF s i (extChartAt IB i.proj x) =
      ((extChartAt (IB.prod IF) i ∘ (extChartAt (IB.prod IF) (s x)).symm)
        ((W ∘ (extChartAt IB x ∘ (extChartAt IB i.proj).symm)) (extChartAt IB i.proj x))).2 := by
    dsimp only [localRep, W, writtenInExtChartAt, Function.comp_apply]
    rw [(extChartAt IB i.proj).left_inv hbi, (extChartAt IB x).left_inv hxx',
      (extChartAt (IB.prod IF) (s x)).left_inv hsx']
  exact (((htop.congr_of_eventuallyEq hev hpt_eq).fderivWithin (IB.uniqueDiffOn _
    (extChartAt_target_subset_range i.proj ((extChartAt IB i.proj).map_source hbi)))).trans
    (by ext u; rw [coordChange_apply]; rfl)).symm
end FiberFirstJet

namespace FiberFirstJetBundle
open Classical in
variable (IB IF) in
/-- **Holonomic prolongation of a local section** `s : B → ManifoldTotalSpace F E`. -/
def prolong (s : B → ManifoldTotalSpace F E) (x : B) : FiberFirstJetBundle IB IF F E :=
  if h : MDifferentiableAt IB (IB.prod IF) s x ∧ (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id then
    ⟨s x, FiberFirstJet.prolongAt h.1 h.2⟩
  else ⟨s x, default⟩
@[simp] theorem proj_prolong (s : B → ManifoldTotalSpace F E) (x : B) :
    (prolong IB IF s x).proj = s x := by simp only [prolong]; split_ifs <;> rfl
theorem prolong_of_mdifferentiableAt {s : B → ManifoldTotalSpace F E} {x : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s x)
    (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id) :
    prolong IB IF s x = ⟨s x, FiberFirstJet.prolongAt hs hproj⟩ := dite_eq_left ⟨hs, hproj⟩

theorem prolong_congr {s₁ s₂ : B → ManifoldTotalSpace F E} {x : B} (h : s₁ =ᶠ[𝓝 x] s₂) :
    prolong IB IF s₁ x = prolong IB IF s₂ x := by
  have hx : s₁ x = s₂ x := h.eq_of_nhds
  by_cases hs₁ : MDifferentiableAt IB (IB.prod IF) s₁ x ∧ (ManifoldTotalSpace.proj ∘ s₁) =ᶠ[𝓝 x] id
  · have hs₂ : MDifferentiableAt IB (IB.prod IF) s₂ x ∧ (ManifoldTotalSpace.proj ∘ s₂) =ᶠ[𝓝 x] id :=
      ⟨hs₁.1.congr_of_eventuallyEq h.symm, (h.symm.fun_comp ManifoldTotalSpace.proj).trans hs₁.2⟩
    rw [prolong_of_mdifferentiableAt hs₁.1 hs₁.2, prolong_of_mdifferentiableAt hs₂.1 hs₂.2,
      mk_eq_mk_iff_modelEquivAt]
    refine ⟨hx, ?_⟩; rw [FiberFirstJet.modelEquivAt_prolongAt, FiberFirstJet.modelEquivAt_prolongAt]
    have hev : writtenInExtChartAt IB (IB.prod IF) x s₁ =ᶠ[𝓝[range IB] extChartAt IB x x]
        writtenInExtChartAt IB (IB.prod IF) x s₂ := by
      filter_upwards [nhdsWithin_le_nhds (extChartAt_preimage_mem_nhds h)] with u hu
      simpa [writtenInExtChartAt, hx] using congrArg (extChartAt (IB.prod IF) (s₂ x)) hu
    rw [hev.fderivWithin_eq (by
      dsimp only [writtenInExtChartAt, Function.comp_apply]
      rw [(extChartAt IB x).left_inv (mem_extChartAt_source x), hx])]
  · have hs₂ : ¬(MDifferentiableAt IB (IB.prod IF) s₂ x ∧
        (ManifoldTotalSpace.proj ∘ s₂) =ᶠ[𝓝 x] id) := fun h₂ ↦
      hs₁ ⟨h₂.1.congr_of_eventuallyEq h, (h.fun_comp ManifoldTotalSpace.proj).trans h₂.2⟩
    simp only [prolong, hs₁, hs₂, ↓reduceDIte]; rw [hx]

variable (IB IF F) in
/-- **Holonomic prolongation of a global section `s : ∀ b, E b`.** -/
def jet (s : ∀ b, E b) (x : B) : FiberFirstJetBundle IB IF F E :=
  prolong IB IF (fun b ↦ ManifoldTotalSpace.homeomorph F E ⟨b, s b⟩) x
@[simp] theorem proj_jet (s : ∀ b, E b) (x : B) :
    (jet IB IF F s x).proj = ManifoldTotalSpace.homeomorph F E ⟨x, s x⟩ := proj_prolong _ x
theorem baseProj_jet (s : ∀ b, E b) (x : B) : baseProj (jet IB IF F s x) = x := by
  rw [baseProj_apply, proj_jet, ManifoldTotalSpace.proj_homeomorph]

theorem contMDiffOn_prolong {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] {s : B → ManifoldTotalSpace F E} {U : Set B}
    (hU : IsOpen U) (hs : ContMDiffOn IB (IB.prod IF) (n + 1) s U)
    (hproj : ∀ x ∈ U, (s x).proj = x) :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    ContMDiffOn IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) n (prolong IB IF s) U := by
  have : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
  have : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
  have : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
  have : IsManifold IB n B := .of_le (n := n + 1) le_self_add
  have : IsManifold IF n F := .of_le (n := n + 1) le_self_add
  have : ContMDiffFiberBundle n F E IB IF := .of_le (n := n + 1) le_self_add
  intro x₀ hx₀
  have hsx₀ : ContMDiffAt IB (IB.prod IF) (n + 1) s x₀ := hs.contMDiffAt (hU.mem_nhds hx₀)
  refine ContMDiffAt.contMDiffWithinAt (Bundle.contMDiffAt_totalSpace_iff.2 ?_)
  simp only [proj_prolong]; refine ⟨hsx₀.of_le le_self_add, ?_⟩; set i := s x₀
  have hx₀_src : x₀ ∈ (extChartAt IB i.proj).source :=
    (hproj x₀ hx₀).symm ▸ mem_extChartAt_source x₀
  have hfd := contMDiffWithinAt_iff_contDiffWithinAt.2
    ((FiberFirstJet.contDiffWithinAt_localRep hsx₀ (mem_chart_source _ i) hx₀_src
      ).fderivWithin_right IB.uniqueDiffOn le_rfl
      (extChartAt_target_subset_range i.proj ((extChartAt IB i.proj).map_source hx₀_src)))
  have hderiv : ContMDiffAt IB 𝓘(𝕜, EB →L[𝕜] EF) n
      (fun x ↦ fderivWithin 𝕜 (FiberFirstJet.localRep IB IF s i) (range IB)
        (extChartAt IB i.proj x)) x₀ := by
    rw [← contMDiffWithinAt_univ]
    exact hfd.comp x₀ (contMDiffAt_extChartAt' (extChartAt_source IB i.proj ▸
      hx₀_src)).contMDiffWithinAt fun x _ ↦ by rw [extChartAt_coe]; exact mem_range_self _
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hx₀, hsx₀.continuousAt.preimage_mem_nhds
    ((chartAt (ModelProd HB HF) i).open_source.mem_nhds (mem_chart_source _ i))] with x hxU hxs
  have hsx := (hs.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
  have hproj_x : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id := by
    filter_upwards [hU.mem_nhds hxU] with y hyU; exact hproj y hyU
  rw [prolong_of_mdifferentiableAt hsx hproj_x, FiberFirstJet.trivializationAt_apply,
    FiberFirstJet.coordAt_prolongAt hsx hproj_x hxs]

theorem contMDiff_jet {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] {s : ∀ b, E b}
    (hs : ContMDiff IB (IB.prod IF) (n + 1) fun b ↦ ManifoldTotalSpace.homeomorph F E ⟨b, s b⟩) :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    ContMDiff IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) n (jet IB IF F s) := by
  have : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
  have : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
  have : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
  rw [← contMDiffOn_univ] at hs ⊢
  exact contMDiffOn_prolong isOpen_univ hs fun b _ ↦ ManifoldTotalSpace.proj_homeomorph ⟨b, s b⟩

theorem prolong_eq_iff_firstJetAt_mk_eq [IsManifold IB ∞ B] [IsManifold IF ∞ F]
    [ContMDiffFiberBundle ∞ F E IB IF] [IB.Boundaryless]
    {s₁ s₂ : B → ManifoldTotalSpace F E} {x : B} {i : ManifoldTotalSpace F E}
    (hs₁ : ContMDiffAt IB (IB.prod IF) ∞ s₁ x) (hs₂ : ContMDiffAt IB (IB.prod IF) ∞ s₂ x)
    (hproj₁ : (ManifoldTotalSpace.proj ∘ s₁) =ᶠ[𝓝 x] id)
    (hproj₂ : (ManifoldTotalSpace.proj ∘ s₂) =ᶠ[𝓝 x] id)
    (hi₁ : s₁ x ∈ (chartAt (ModelProd HB HF) i).source)
    (hi₂ : s₂ x ∈ (chartAt (ModelProd HB HF) i).source) :
    have hbi : x ∈ (extChartAt IB i.proj).source := by
      have hx₁ : (s₁ x).proj = x := hproj₁.eq_of_nhds
      rw [extChartAt_source, ← hx₁]; exact (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hi₁).2
    have hf₁ : ContDiffAt 𝕜 ∞ (FiberFirstJet.localRep IB IF s₁ i) (extChartAt IB i.proj x) :=
      (FiberFirstJet.contDiffWithinAt_localRep hs₁ hi₁ hbi).contDiffAt (IB.range_eq_univ ▸ univ_mem)
    have hf₂ : ContDiffAt 𝕜 ∞ (FiberFirstJet.localRep IB IF s₂ i) (extChartAt IB i.proj x) :=
      (FiberFirstJet.contDiffWithinAt_localRep hs₂ hi₂ hbi).contDiffAt (IB.range_eq_univ ▸ univ_mem)
    prolong IB IF s₁ x = prolong IB IF s₂ x ↔
      FirstJetAt.mk (FiberFirstJet.localRep IB IF s₁ i) hf₁ =
        FirstJetAt.mk (FiberFirstJet.localRep IB IF s₂ i) hf₂ := by
  intro hbi hf₁ hf₂
  have hx₁ : (s₁ x).proj = x := hproj₁.eq_of_nhds; have hx₂ : (s₂ x).proj = x := hproj₂.eq_of_nhds
  have hmd₁ := hs₁.mdifferentiableAt (by simp); have hmd₂ := hs₂.mdifferentiableAt (by simp)
  rw [prolong_of_mdifferentiableAt hmd₁ hproj₁, prolong_of_mdifferentiableAt hmd₂ hproj₂,
    mk_eq_mk_iff_coordAt hi₁, FirstJetAt.mk_eq_mk_iff,
    FiberFirstJet.coordAt_prolongAt hmd₁ hproj₁ hi₁,
    FiberFirstJet.coordAt_prolongAt hmd₂ hproj₂ hi₂,
    IB.range_eq_univ, fderivWithin_univ, fderivWithin_univ,
    FiberFirstJet.localRep_apply, FiberFirstJet.localRep_apply, (extChartAt IB i.proj).left_inv hbi]
  refine and_congr ⟨fun h ↦ by rw [h], fun h ↦ ?_⟩ Iff.rfl
  refine (extChartAt (IB.prod IF) i).injOn ((extChartAt_source (IB.prod IF) i).symm ▸ hi₁)
    ((extChartAt_source (IB.prod IF) i).symm ▸ hi₂) (Prod.ext ?_ h)
  rw [ManifoldTotalSpace.extChartAt_fst_eq hi₁, ManifoldTotalSpace.extChartAt_fst_eq hi₂, hx₁, hx₂]

theorem exists_contMDiffAt_prolong_eq [IsManifold IB ∞ B] [IsManifold IF ∞ F]
    [ContMDiffFiberBundle ∞ F E IB IF] [IB.Boundaryless] [IF.Boundaryless]
    (z : ManifoldTotalSpace F E) (j : FiberFirstJet IB IF F E z) :
    ∃ s : B → ManifoldTotalSpace F E, ContMDiffAt IB (IB.prod IF) ∞ s z.proj ∧ s z.proj = z ∧
      (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 z.proj] id ∧ prolong IB IF s z.proj = ⟨z, j⟩ := by
  set u₀ := extChartAt IB z.proj z.proj; set v₀ := (extChartAt (IB.prod IF) z z).2
  set A := FiberFirstJet.modelEquivAt z j
  have hpt_pair : (u₀, v₀) = extChartAt (IB.prod IF) z z :=
    Prod.ext (ManifoldTotalSpace.extChartAt_fst_eq (mem_chart_source _ z)).symm rfl
  obtain ⟨f, hf_smooth, hf_jet, hf_mem⟩ := FirstJetAt.exists_section_coordinates_mem (v₀, A)
    (isOpen_extChartAt_target z) (by dsimp only; rw [hpt_pair]; exact mem_extChartAt_target z)
  have hf_val : f u₀ = v₀ := congrArg Prod.fst hf_jet
  set s : B → ManifoldTotalSpace F E := fun b ↦
    (extChartAt (IB.prod IF) z).symm (extChartAt IB z.proj b, f (extChartAt IB z.proj b))
  have hs_pt : s z.proj = z := by
    change (extChartAt (IB.prod IF) z).symm (u₀, f u₀) = z
    rw [hf_val, hpt_pair, (extChartAt (IB.prod IF) z).left_inv (mem_extChartAt_source z)]
  have hsymm : ContMDiffAt 𝓘(𝕜, EB × EF) (IB.prod IF) ∞ (extChartAt (IB.prod IF) z).symm
      (u₀, f u₀) := by
    rw [hf_val, hpt_pair, ← contMDiffWithinAt_univ, ← (IB.prod IF).range_eq_univ]
    exact contMDiffWithinAt_extChartAt_symm_range z (mem_extChartAt_target z)
  have hs_smooth : ContMDiffAt IB (IB.prod IF) ∞ s z.proj :=
    hsymm.comp z.proj (contMDiffAt_extChartAt.prodMk_space
      (hf_smooth.contDiffAt.contMDiffAt.comp z.proj contMDiffAt_extChartAt))
  have hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 z.proj] id := by
    filter_upwards [(contMDiffAt_extChartAt (I := IB) (n := ∞) (x := z.proj)
        ).continuousAt.eventually hf_mem,
      (isOpen_extChartAt_source (I := IB) z.proj).mem_nhds (mem_extChartAt_source z.proj)]
      with b hb1 hb2
    rw [Function.comp_apply, ManifoldTotalSpace.proj_extChartAt_symm z hb1,
      (extChartAt IB z.proj).left_inv hb2, id_eq]
  refine ⟨s, hs_smooth, hs_pt, hproj, ?_⟩; have hs_md := hs_smooth.mdifferentiableAt (by simp)
  rw [prolong_of_mdifferentiableAt hs_md hproj, mk_eq_mk_iff_modelEquivAt]
  refine ⟨hs_pt, ?_⟩; rw [FiberFirstJet.modelEquivAt_prolongAt, IB.range_eq_univ, fderivWithin_univ]
  have hev : (Prod.snd ∘ writtenInExtChartAt IB (IB.prod IF) z.proj s) =ᶠ[𝓝 u₀] f := by
    filter_upwards [extChartAt_target_mem_nhds (I := IB) z.proj, hf_mem] with u hu1 hu2
    simp only [writtenInExtChartAt, Function.comp_apply, hs_pt, s]
    rw [(extChartAt IB z.proj).right_inv hu1, (extChartAt (IB.prod IF) z).right_inv hu2]
  have hd := hs_md.hasMFDerivAt.2; rw [IB.range_eq_univ, hasFDerivWithinAt_univ] at hd
  exact (hasFDerivAt_snd.comp u₀ hd.differentiableAt.hasFDerivAt).fderiv.symm.trans
    (hev.fderiv_eq.trans (congrArg Prod.snd hf_jet))

theorem contactFormAt_comp_mfderiv_eq_zero_iff [IsManifold IB 1 B] [IsManifold IF 1 F]
    [ContMDiffFiberBundle 1 F E IB IF] {σ : B → FiberFirstJetBundle IB IF F E} {x : B}
    (hσ : MDifferentiableAt IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) σ x)
    (hbase : (baseProj ∘ σ) =ᶠ[𝓝 x] id) :
    (contactFormAt (σ x)).comp (mfderiv IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) σ x) = 0 ↔
      σ x = prolong IB IF (targetProj ∘ σ) x := by
  rw [targetProj_eq_proj]; set s := TotalSpace.proj ∘ σ
  have hs : MDifferentiableAt IB (IB.prod IF) s x :=
    (Bundle.mdifferentiableAt_proj (FiberFirstJet IB IF F E)).comp x hσ
  have hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id := by
    rwa [baseProj_eq_proj_comp_targetProj, targetProj_eq_proj] at hbase
  have hmfd_s : mfderiv ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) (IB.prod IF) TotalSpace.proj (σ x) ∘L
      mfderiv IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) σ x = mfderiv IB (IB.prod IF) s x :=
    (mfderiv_comp x (Bundle.mdifferentiableAt_proj (FiberFirstJet IB IF F E)) hσ).symm
  have hmfd_base : (mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj (σ x).proj).comp
      (mfderiv IB (IB.prod IF) s x) =
      (tangentSpaceCast IB x (σ x).proj.proj).toContinuousLinearMap := by
    change (mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj (s x)).comp
      (mfderiv IB (IB.prod IF) s x) = (tangentSpaceCast IB x (s x).proj).toContinuousLinearMap
    rw [← mfderiv_comp x (ManifoldTotalSpace.hasMFDerivAt_proj IB IF (s x)).mdifferentiableAt hs,
      hproj.mfderiv_eq, mfderiv_id]; ext v; rfl
  rw [prolong_of_mdifferentiableAt hs hproj]; refine ⟨fun h0 ↦ ?_, fun h_eq ↦ ?_⟩
  · refine TotalSpace.ext rfl (heq_of_eq ?_); ext u
    have htan : VerticalSpace.toTangent (σ x).proj
        (((contactFormAt (σ x)).comp (mfderiv IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) σ x))
          (tangentSpaceCast IB (σ x).proj.proj x u)) = 0 := by rw [h0, zero_apply, map_zero]
    rw [comp_apply, toTangent_contactFormAt, ← comp_apply, hmfd_s, ← comp_apply, hmfd_base,
      sub_eq_zero] at htan; exact htan.symm
  · have hj : (σ x).2 = FiberFirstJet.prolongAt hs hproj := eq_of_heq (TotalSpace.mk.inj h_eq).2
    refine ContinuousLinearMap.ext fun v ↦ VerticalSpace.ext ?_
    rw [zero_apply, map_zero, comp_apply, toTangent_contactFormAt, ← comp_apply, hmfd_s,
      ← comp_apply, hmfd_base, hj, FiberFirstJet.prolongAt_apply]
    exact sub_self (mfderiv IB (IB.prod IF) s x v)

theorem prolongAt_quadratic_trivial_eval :
    let s : ℝ → ManifoldTotalSpace ℝ (Bundle.Trivial ℝ ℝ) :=
      fun x ↦ ManifoldTotalSpace.homeomorph ℝ (Bundle.Trivial ℝ ℝ)
        ⟨x, (x ^ 2 : Bundle.Trivial ℝ ℝ x)⟩
    have hs : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) s 3 :=
      (ManifoldTotalSpace.contMDiffAt_iff.2
        ⟨contMDiffAt_id, (contDiff_id.pow 2).contMDiff.contMDiffAt⟩).mdifferentiableAt one_ne_zero
    have hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 (3 : ℝ)] id :=
      Eventually.of_forall fun x ↦
        ManifoldTotalSpace.proj_homeomorph ⟨x, (x ^ 2 : Bundle.Trivial ℝ ℝ x)⟩
    FiberFirstJet.modelEquivAt (s 3) (FiberFirstJet.prolongAt hs hproj) 1 = 6 ∧
      (FiberFirstJet.prolongAt hs hproj).contactProj
        ((tangentSpaceCastModel (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (s 3)).symm (1, 6)) = 0 := by
  intro s hs hproj
  have hpair : writtenInExtChartAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 3 s = fun x : ℝ ↦ (x, x ^ 2) := by
    funext x; dsimp only [writtenInExtChartAt, s, Function.comp_apply]
    rw [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq,
      ManifoldTotalSpace.extChartAt_homeomorph_apply]; simp
  have hd : HasFDerivAt (writtenInExtChartAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 3 s)
      ((ContinuousLinearMap.id ℝ ℝ).prod
        ((2 • (3 : ℝ) ^ (2 - 1)) • ContinuousLinearMap.id ℝ ℝ)) 3 :=
    hpair ▸ (hasFDerivAt_id (3 : ℝ)).prodMk ((hasFDerivAt_id (3 : ℝ)).pow 2)
  have hval : FiberFirstJet.modelEquivAt (s 3) (FiberFirstJet.prolongAt hs hproj) =
      (6 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
    rw [FiberFirstJet.modelEquivAt_prolongAt]
    simp only [modelWithCornersSelf_coe, range_id, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, id_eq, fderivWithin_univ, hd.fderiv]; ext; norm_num
  refine ⟨by rw [hval]; simp, ?_⟩
  have hvec : (tangentSpaceCastModel (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (s 3)).symm (1, 6) =
      FiberFirstJet.prolongAt hs hproj ((tangentSpaceCastModel 𝓘(ℝ, ℝ) (s 3).proj).symm 1) := by
    apply (tangentSpaceCastModel (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (s 3)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    refine Prod.ext ?_ (by rw [← FiberFirstJet.modelEquivAt_apply, hval]; simp)
    rw [FiberFirstJet.tangentSpaceCastModel_apply_fst, ContinuousLinearEquiv.apply_symm_apply]
  rw [hvec, FiberFirstJet.contactProj_apply_self]
end FiberFirstJetBundle
end ManifoldFiber

namespace FiberFirstJetBundle
variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ b, AddCommGroup (V b)]
  [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F V IB]

omit [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [VectorBundle 𝕜 F V] [IsManifold IB 1 B]
  [ContMDiffVectorBundle 1 F V IB] in
private theorem extChartAt_snd_vectorBundle (i w : ManifoldTotalSpace F V) :
    (extChartAt (IB.prod 𝓘(𝕜, F)) i w).2 =
      (trivializationAt F V i.proj ((ManifoldTotalSpace.homeomorph F V).symm w)).2 := by
  obtain ⟨xi, rfl⟩ := (ManifoldTotalSpace.homeomorph F V).surjective i
  obtain ⟨xw, rfl⟩ := (ManifoldTotalSpace.homeomorph F V).surjective w
  rw [ManifoldTotalSpace.extChartAt_homeomorph_apply]; simp
omit [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F V IB] in
private theorem eventuallyEq_extChartAt_snd_vectorBundle {i z : ManifoldTotalSpace F V}
    (hi : z ∈ (chartAt (ModelProd HB F) i).source) :
    let v := (trivializationAt F V z.proj ((ManifoldTotalSpace.homeomorph F V).symm z)).2
    (fun q : EB × F ↦ (extChartAt (IB.prod 𝓘(𝕜, F)) i ((extChartAt (IB.prod 𝓘(𝕜, F)) z).symm q)).2)
      =ᶠ[𝓝[range (IB.prod 𝓘(𝕜, F))] (extChartAt IB z.proj z.proj, v)]
    fun q : EB × F ↦ FirstJetBundle.fiberCoordChange IB F V z.proj i.proj
      ((extChartAt IB i.proj ∘ (extChartAt IB z.proj).symm) q.1) q.2 := by
  intro v
  have hz_pt : extChartAt (IB.prod 𝓘(𝕜, F)) z z = (extChartAt IB z.proj z.proj, v) :=
    Prod.ext (ManifoldTotalSpace.extChartAt_fst_eq (mem_chart_source _ z))
      (extChartAt_snd_vectorBundle z z)
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (hz_pt ▸ mem_extChartAt_target z),
    nhdsWithin_le_nhds (hz_pt ▸ extChartAt_preimage_mem_nhds' (mem_extChartAt_source z)
      ((chartAt (ModelProd HB F) i).open_source.mem_nhds hi))] with q hq1 hq2
  set w := (extChartAt (IB.prod 𝓘(𝕜, F)) z).symm q
  have hwb_z := (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source
    ((extChartAt_source (IB.prod 𝓘(𝕜, F)) z) ▸ (extChartAt (IB.prod 𝓘(𝕜, F)) z).map_target hq1)).1
  have hwb_i := ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hq2; have hwb_i1 := hwb_i.1
  have hq_snd : (trivializationAt F V z.proj ((ManifoldTotalSpace.homeomorph F V).symm w)).2 =
      q.2 := (extChartAt_snd_vectorBundle (IB := IB) z w).symm.trans
    (congrArg Prod.snd ((extChartAt (IB.prod 𝓘(𝕜, F)) z).right_inv hq1))
  rw [extChartAt_snd_vectorBundle, FirstJetBundle.fiberCoordChange_apply, Function.comp_apply,
    ← ManifoldTotalSpace.proj_extChartAt_symm z hq1,
    (extChartAt IB i.proj).left_inv ((extChartAt_source IB i.proj).symm ▸ hwb_i.2), ← hq_snd]
  rw [← ManifoldTotalSpace.homeomorph_symm_proj w] at hwb_z hwb_i1 ⊢
  exact (Trivialization.coordChangeL_apply_snd 𝕜 _ _ hwb_z hwb_i1).symm

theorem coordChange_self_left_eq_firstJetBundle_coordChange {i z : ManifoldTotalSpace F V}
    (hi : z ∈ (chartAt (ModelProd HB F) i).source) (A : EB →L[𝕜] F) :
    FiberFirstJet.coordChange (IB := IB) (IF := 𝓘(𝕜, F)) (F := F) (E := V) z i z A =
      (FirstJetBundle.coordChange IB F V z.proj i.proj z.proj
        ((trivializationAt F V z.proj ((ManifoldTotalSpace.homeomorph F V).symm z)).2, A)).2 := by
  set b := z.proj; set b_i := i.proj; have hb_ext := mem_extChartAt_source (I := IB) b
  set v := (trivializationAt F V b ((ManifoldTotalSpace.homeomorph F V).symm z)).2
  have hb_i' := ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hi
  have hb_i := (FirstJetBundle.mem_baseSet_iff (H := HB) F V).2 hb_i'
  have hbi_ext : b ∈ (extChartAt IB b_i).source := (extChartAt_source IB b_i).symm ▸ hb_i'.2
  have hz_pt : extChartAt (IB.prod 𝓘(𝕜, F)) z z = (extChartAt IB b b, v) :=
    Prod.ext (ManifoldTotalSpace.extChartAt_fst_eq (mem_chart_source _ z))
      (extChartAt_snd_vectorBundle z z)
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
  change HasFDerivWithinAt (fun q : EB × F ↦ FirstJetBundle.fiberCoordChange IB F V b b_i
      ((extChartAt IB b_i ∘ (extChartAt IB b).symm) q.1) q.2)
    ((FirstJetBundle.fiberCoordChange IB F V b b_i
        ((extChartAt IB b_i ∘ (extChartAt IB b).symm) (extChartAt IB b b))).comp
        (ContinuousLinearMap.snd 𝕜 EB F) + _) _ _ at hclm
  rw [hpt, FirstJetBundle.fiberCoordChange_extChartAt hb_i'.2, add_comm] at hclm
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
  rw [FiberFirstJet.coordChange_apply, FirstJetBundle.coordChange_apply]; exact happ

/-- Map from `FiberFirstJet` over `z` to `FirstJetBundle IB F V z.proj` in preferred coordinates. -/
def toFirstJetBundleFiber (z : ManifoldTotalSpace F V)
    (j : FiberFirstJet IB 𝓘(𝕜, F) F V z) : FirstJetBundle IB F V z.proj :=
  ((trivializationAt F V z.proj ((ManifoldTotalSpace.homeomorph F V).symm z)).2,
    FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z j)
/-- Map from `FiberFirstJetBundle IB 𝓘(𝕜, F) F V` to the total space of `FirstJetBundle IB F V`. -/
def toFirstJetBundle (p : FiberFirstJetBundle IB 𝓘(𝕜, F) F V) :
    TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) :=
  ⟨p.proj.proj, toFirstJetBundleFiber p.proj p.2⟩
/-- Inverse map from the total space of `FirstJetBundle IB F V` to `FiberFirstJetBundle`. -/
def ofFirstJetBundle (q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) :
    FiberFirstJetBundle IB 𝓘(𝕜, F) F V :=
  let z : ManifoldTotalSpace F V :=
    ManifoldTotalSpace.homeomorph F V ⟨q.proj, (trivializationAt F V q.proj).symm q.proj q.2.1⟩
  ⟨z, (FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z).symm q.2.2⟩

theorem ofFirstJetBundle_toFirstJetBundle (p : FiberFirstJetBundle IB 𝓘(𝕜, F) F V) :
    ofFirstJetBundle (toFirstJetBundle p) = p := by
  rw [ofFirstJetBundle, toFirstJetBundle, toFirstJetBundleFiber, mk_eq_mk_iff_modelEquivAt]
  dsimp only; refine ⟨?_, (FiberFirstJet.modelEquivAt (IF := 𝓘(𝕜, F)) _).apply_symm_apply _⟩
  obtain ⟨x, hx⟩ := (ManifoldTotalSpace.homeomorph F V).surjective p.proj
  rw [← hx, ManifoldTotalSpace.proj_homeomorph, Homeomorph.symm_apply_apply]
  exact congrArg (ManifoldTotalSpace.homeomorph F V) (congrArg (TotalSpace.mk' F x.proj)
    ((trivializationAt F V x.proj).symm_apply_apply_mk
      (mem_baseSet_trivializationAt F V x.proj) x.2))
theorem toFirstJetBundle_ofFirstJetBundle
    (q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) :
    toFirstJetBundle (ofFirstJetBundle q) = q := by
  rcases q with ⟨b, v, A⟩; dsimp only [ofFirstJetBundle, toFirstJetBundle, toFirstJetBundleFiber]
  set z := ManifoldTotalSpace.homeomorph F V ⟨b, (trivializationAt F V b).symm b v⟩
  have hz_proj : z.proj = b := ManifoldTotalSpace.proj_homeomorph _
  have h1 : (trivializationAt F V z.proj ((ManifoldTotalSpace.homeomorph F V).symm z)).2 = v := by
    rw [hz_proj]; dsimp only [z]; rw [Homeomorph.symm_apply_apply,
      (trivializationAt F V b).apply_mk_symm (mem_baseSet_trivializationAt F V b) v]
  exact TotalSpace.ext hz_proj (heq_of_eq (Prod.ext h1
    ((FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z).apply_symm_apply A)))

theorem contMDiff_toFirstJetBundle (n : ℕ∞ω) :
    ContMDiff ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F)) (IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))) n
      (toFirstJetBundle : FiberFirstJetBundle IB 𝓘(𝕜, F) F V →
        TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V)) := by
  intro p₀; set z₀ := p₀.proj
  have hp_proj : ContMDiffAt ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F)) (IB.prod 𝓘(𝕜, F)) n
      TotalSpace.proj p₀ := Bundle.contMDiff_proj (FiberFirstJet IB 𝓘(𝕜, F) F V) p₀
  obtain ⟨hbase, hval⟩ := (ManifoldTotalSpace.contMDiffAt_iff
    (f := fun p : FiberFirstJetBundle IB 𝓘(𝕜, F) F V ↦
      (ManifoldTotalSpace.homeomorph F V).symm p.proj)).1
    (hp_proj.congr_of_eventuallyEq (.of_forall fun p ↦
      (ManifoldTotalSpace.homeomorph F V).apply_symm_apply p.proj))
  simp only [ManifoldTotalSpace.homeomorph_symm_proj] at hbase hval
  have hsnd : ContMDiffAt ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F)) 𝓘(𝕜, EB →L[𝕜] F) n
      (fun p : FiberFirstJetBundle IB 𝓘(𝕜, F) F V ↦
        (trivializationAt (EB →L[𝕜] F) (FiberFirstJet IB 𝓘(𝕜, F) F V) z₀ p).2) p₀ :=
    (Bundle.contMDiffAt_totalSpace_iff.1 contMDiffAt_id).2
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨hbase,
    (hval.prodMk_space hsnd).congr_of_eventuallyEq ?_⟩
  filter_upwards [hp_proj.continuousAt.preimage_mem_nhds
    ((chartAt (ModelProd HB F) z₀).open_source.mem_nhds (mem_chart_source _ z₀))] with p hp
  rw [FirstJetBundle.trivializationAt_apply_snd, FiberFirstJet.trivializationAt_apply]
  dsimp only [toFirstJetBundle, toFirstJetBundleFiber]; refine Prod.ext ?_ ?_
  · rw [FirstJetBundle.coordChange_apply]; dsimp only
    rw [← ManifoldTotalSpace.homeomorph_symm_proj p.proj]
    exact Trivialization.coordChangeL_apply_snd 𝕜 _ _
      (by rw [ManifoldTotalSpace.homeomorph_symm_proj]; exact mem_baseSet_trivializationAt _ _ _)
      (by rw [ManifoldTotalSpace.homeomorph_symm_proj]
          exact (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hp).1)
  · rw [← coordChange_self_left_eq_firstJetBundle_coordChange hp, ← FiberFirstJet.coordAt_self,
      ← FiberFirstJet.coordAt_ofCoordAt_eq_coordChange (mem_chart_source _ p.proj) hp,
      FiberFirstJet.ofCoordAt_coordAt]

theorem contMDiff_ofFirstJetBundle (n : ℕ∞ω) :
    ContMDiff (IB.prod 𝓘(𝕜, F × (EB →L[𝕜] F))) ((IB.prod 𝓘(𝕜, F)).prod 𝓘(𝕜, EB →L[𝕜] F)) n
      (ofFirstJetBundle : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) →
        FiberFirstJetBundle IB 𝓘(𝕜, F) F V) := by
  intro q₀; set z₀ := (ofFirstJetBundle q₀).proj
  have hz₀_proj : z₀.proj = q₀.proj := ManifoldTotalSpace.proj_homeomorph _
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
    simpa [FirstJetBundle.trivializationAt_apply_snd, FirstJetBundle.coordChange_apply] using
      (Trivialization.coordChangeL_apply _ _ ⟨mem_baseSet_trivializationAt F V b, hq⟩ v).symm
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨hproj_smooth,
    ((ContinuousLinearMap.snd 𝕜 F (EB →L[𝕜] F)).contMDiffAt.comp q₀ htriv).congr_of_eventuallyEq
      ?_⟩
  filter_upwards [hproj_smooth.continuousAt.preimage_mem_nhds
    ((chartAt (ModelProd HB F) z₀).open_source.mem_nhds (mem_chart_source _ z₀))]
    with ⟨b, v, A⟩ hq
  let q : TotalSpace (F × (EB →L[𝕜] F)) (FirstJetBundle IB F V) := ⟨b, (v, A)⟩
  set z := (ofFirstJetBundle q).proj
  have hz_proj : z.proj = b := ManifoldTotalSpace.proj_homeomorph _
  have hv_eq : (trivializationAt F V z.proj ((ManifoldTotalSpace.homeomorph F V).symm z)).2 =
      v := by
    rw [hz_proj]; dsimp only [z, q, ofFirstJetBundle]; rw [Homeomorph.symm_apply_apply,
      (trivializationAt F V b).apply_mk_symm (mem_baseSet_trivializationAt F V b) v]
  simp only [Function.comp_apply, ContinuousLinearMap.coe_snd',
    FiberFirstJet.trivializationAt_apply, FirstJetBundle.trivializationAt_apply_snd]
  change FiberFirstJet.coordAt z₀
      ((FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z).symm A) =
    (FirstJetBundle.coordChange IB F V b q₀.proj b (v, A)).2
  have hj : FiberFirstJet.coordAt z
      ((FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z).symm A) = A := by
    rw [FiberFirstJet.coordAt_self,
      (FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z).apply_symm_apply]
  rw [← FiberFirstJet.ofCoordAt_coordAt (mem_chart_source _ z)
      ((FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z).symm A),
    hj, FiberFirstJet.coordAt_ofCoordAt_eq_coordChange (mem_chart_source _ z) hq,
    coordChange_self_left_eq_firstJetBundle_coordChange hq, hv_eq, hz_proj, hz₀_proj]

variable (IB F V) in
/-- **Canonical `C^n` diffeomorphism between `FiberFirstJetBundle` and `FirstJetBundle`**. -/
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
@[simp] theorem diffeomorphFirstJetBundle_mk (n : ℕ∞ω) (z : ManifoldTotalSpace F V)
    (j : FiberFirstJet IB 𝓘(𝕜, F) F V z) :
    diffeomorphFirstJetBundle IB F V n ⟨z, j⟩ = ⟨z.proj, toFirstJetBundleFiber z j⟩ := (rfl)
@[simp] theorem diffeomorphFirstJetBundle_proj (n : ℕ∞ω) (p : FiberFirstJetBundle IB 𝓘(𝕜, F) F V) :
    (diffeomorphFirstJetBundle IB F V n p).proj = baseProj p := (baseProj_apply p).symm
@[simp] theorem value_toFirstJetBundleFiber (z : ManifoldTotalSpace F V)
    (j : FiberFirstJet IB 𝓘(𝕜, F) F V z) :
    FirstJetBundle.value IB F z.proj (toFirstJetBundleFiber z j) = z.snd := by
  have hz_symm : (ManifoldTotalSpace.homeomorph F V).symm z = ⟨z.proj, z.snd⟩ :=
    (ManifoldTotalSpace.homeomorph F V).injective
      (by rw [Homeomorph.apply_symm_apply, ManifoldTotalSpace.homeomorph_mk_proj_snd])
  rw [FirstJetBundle.value_apply]; dsimp only [toFirstJetBundleFiber]; rw [hz_symm]
  exact (trivializationAt F V z.proj).symm_apply_apply_mk
    (mem_baseSet_trivializationAt F V z.proj) z.snd
@[simp] theorem value_diffeomorphFirstJetBundle (n : ℕ∞ω)
    (p : FiberFirstJetBundle IB 𝓘(𝕜, F) F V) :
    FirstJetBundle.value IB F p.proj.proj (diffeomorphFirstJetBundle IB F V n p).2 = p.proj.snd :=
  value_toFirstJetBundleFiber p.proj p.2

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
  change toFirstJetBundle (prolong IB 𝓘(𝕜, F) sM x) = ⟨x, FirstJetBundle.jet IB F s x⟩
  rw [prolong_of_mdifferentiableAt hsM hproj]; dsimp only [toFirstJetBundle, toFirstJetBundleFiber]
  have h1 : (trivializationAt F V (sM x).proj
      ((ManifoldTotalSpace.homeomorph F V).symm (sM x))).2 = (FirstJetBundle.jet IB F s x).1 := by
    rw [hz_proj, FirstJetBundle.jet_fst]; dsimp only [sM]; rw [Homeomorph.symm_apply_apply]
  have h2 : FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) (sM x)
      (FiberFirstJet.prolongAt hsM hproj) = (FirstJetBundle.jet IB F s x).2 := by
    rw [← FiberFirstJet.coordAt_self,
      FiberFirstJet.coordAt_prolongAt hsM hproj (mem_chart_source _ (sM x)), hz_proj,
      FirstJetBundle.jet_snd]
    have hrep : FiberFirstJet.localRep IB 𝓘(𝕜, F) sM (sM x) = FirstJetBundle.localRep IB F s x := by
      funext u; rw [FiberFirstJet.localRep_apply, FirstJetBundle.localRep_apply]; dsimp only [sM]
      rw [ManifoldTotalSpace.proj_homeomorph, ManifoldTotalSpace.extChartAt_homeomorph_apply]; simp
    rw [hrep]
  exact TotalSpace.ext hz_proj (heq_of_eq (Prod.ext h1 h2))

theorem toFirstJetBundleFiber_vadd [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul 𝕜 (V x)] (z : ManifoldTotalSpace F V)
    (L : TangentSpace IB z.proj →L[𝕜] V z.proj) (j : FiberFirstJet IB 𝓘(𝕜, F) F V z) :
    toFirstJetBundleFiber z
        (((VerticalSpace.verticalLift IB z).toContinuousLinearMap.comp L) +ᵥ j) =
      FirstJetBundle.ofDeriv IB F z.proj L + toFirstJetBundleFiber z j := by
  rw [FirstJetBundle.ofDeriv_apply]; dsimp only [toFirstJetBundleFiber]
  refine Prod.ext (zero_add _).symm ?_; ext u
  have hvadd : FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z
      (((VerticalSpace.verticalLift IB z).toContinuousLinearMap.comp L) +ᵥ j) u =
      VerticalSpace.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z
        (VerticalSpace.verticalLift IB z (L ((tangentSpaceCastModel IB z.proj).symm u))) +
        FiberFirstJet.modelEquivAt (IB := IB) (IF := 𝓘(𝕜, F)) z j u := by
    simp only [FiberFirstJet.modelEquivAt_apply, FiberFirstJet.vadd_apply, map_add, Prod.snd_add,
      VerticalSpace.modelEquivAt_apply, comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [hvadd, VerticalSpace.modelEquivAt_verticalLift]; rfl
theorem diffeomorphFirstJetBundle_vadd [∀ x, IsTopologicalAddGroup (V x)]
    [∀ x, ContinuousSMul 𝕜 (V x)] (n : ℕ∞ω) (z : ManifoldTotalSpace F V)
    (L : TangentSpace IB z.proj →L[𝕜] V z.proj) (j : FiberFirstJet IB 𝓘(𝕜, F) F V z) :
    diffeomorphFirstJetBundle IB F V n
        ⟨z, ((VerticalSpace.verticalLift IB z).toContinuousLinearMap.comp L) +ᵥ j⟩ =
      ⟨z.proj, FirstJetBundle.ofDeriv IB F z.proj L + toFirstJetBundleFiber z j⟩ := by
  rw [diffeomorphFirstJetBundle_mk, toFirstJetBundleFiber_vadd]
end FiberFirstJetBundle
end TauCeti

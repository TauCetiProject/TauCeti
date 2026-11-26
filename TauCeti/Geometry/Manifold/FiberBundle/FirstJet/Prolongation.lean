/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Jet.Section
public import TauCeti.Geometry.Manifold.FiberBundle.FirstJet.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.ContMDiff.Defs

/-!
# Holonomic prolongation and Cartan contact characterization

For a fibre bundle `E` over a manifold `B` (modelled on `IB`) with manifold fibre `F` (modelled on
`IF`), this file constructs the first holonomic prolongation `j¹s` of sections and characterizes
holonomic sections of `J¹E` via the pointwise Cartan contact map.

## Section conventions and fallback behavior

* **Local sections** are represented as maps `s : B → ManifoldTotalSpace F E` satisfying the local
  right-inverse condition `(ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id`. At a point `x` where `s` is
  manifold-differentiable and locally a section, `FiberFirstJet.prolongAt` packages `mfderiv` of `s`
  (adjusted by `tangentSpaceCast` along `(s x).proj = x`) as an element of `FiberFirstJet`.
  `FiberFirstJetBundle.prolong` extends this to an arbitrary map `s : B → ManifoldTotalSpace F E`
  without hypotheses, returning an arbitrary fallback `⟨s x, Classical.arbitrary _⟩` whenever either
  `MDifferentiableAt` or `(ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id` fails.
* **Global dependent sections** `s : ∀ b, E b` are prolonged by `FiberFirstJetBundle.jet`, defined
  by composing `s` with `ManifoldTotalSpace.homeomorph F E` and applying `prolong` (so `jet`
  likewise falls back to `⟨homeomorph ⟨x, s x⟩, Classical.arbitrary _⟩` where `s` is not
  differentiable).

## Regularity and boundary hypotheses

* Prolongation, coordinate derivative formulas (`FiberFirstJet.hasFDerivWithinAt_localRep`,
  `FiberFirstJet.coordAt_prolongAt`), `C^m` smoothness of `prolong` and `jet` from `C^n` sections
  when `m + 1 ≤ n` (`FiberFirstJetBundle.contMDiffAt_prolong`, `contMDiffOn_prolong`,
  `contMDiff_jet`), local realization of arbitrary 1-jets
  (`FiberFirstJetBundle.exists_contMDiffAt_prolong_eq`, requiring only `[IF.Boundaryless]`), and
  the holonomic contact criterion (`FiberFirstJetBundle.contactFormAt_comp_mfderiv_eq_zero_iff`)
  all work on `C^1` bundles and allow boundary on `B`.
* The germ-quotient bridge `FiberFirstJetBundle.prolong_eq_iff_firstJetAt_mk_eq` requires `∞`
  smoothness and `[IB.Boundaryless]` because `TauCeti.FirstJetAt` is defined as the quotient of
  `C^∞` germs using `fderiv` (rather than `fderivWithin` on `range IB`).

## References

* I. M. Anderson, *The Variational Bicomplex*, Utah State University, 1992, Chapter 1, §A.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*,
  Springer-Verlag, 1993, §12.
* D. J. Saunders, *The Geometry of Jet Bundles*, Cambridge University Press, 1989, §§4.1–4.2.
* `TauCeti.FirstJetAt` (`TauCeti.Analysis.Calculus.Jet.Section`), used for the local `C^∞` germ
  quotient comparison.
* `TauCeti.FirstJetBundle` (`TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic`), adapted for
  preferred-chart local representatives (`localRep`, `contDiffWithinAt_localRep`) and prolongation
  smoothness.
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

/-- Holonomic prolongation at `x` of a map `s : B → ManifoldTotalSpace F E` that is differentiable
at `x` and locally a section (`(ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id`). -/
def prolongAt {s : B → ManifoldTotalSpace F E} {x : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s x)
    (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id) :
    FiberFirstJet IB IF F E (s x) where
  toContinuousLinearMap :=
    (mfderiv IB (IB.prod IF) s x).comp (tangentSpaceCast IB (s x).proj x).toContinuousLinearMap
  mfderiv_proj_comp := by
    rw [← ContinuousLinearMap.comp_assoc,
      ← mfderiv_comp x (ManifoldTotalSpace.hasMFDerivAt_proj IB IF (s x)).mdifferentiableAt hs,
      hproj.mfderiv_eq, mfderiv_id, ContinuousLinearMap.comp_id]
    ext u
    dsimp only [Function.comp_apply, id_eq]
    rw [comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
      ← Manifold.tangentSpaceCast_symm IB x (s x).proj, ContinuousLinearEquiv.apply_symm_apply,
      id_apply]

/-- Applying `prolongAt hs hproj` to a base tangent vector transports it along `(s x).proj = x` and
applies `mfderiv IB (IB.prod IF) s x`. -/
@[simp]
theorem prolongAt_apply {s : B → ManifoldTotalSpace F E} {x : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s x)
    (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id) (u : TangentSpace IB (s x).proj) :
    prolongAt hs hproj u = mfderiv IB (IB.prod IF) s x (tangentSpaceCast IB (s x).proj x u) :=
  (rfl)

/-- In the preferred model coordinates at `s x`, `prolongAt hs hproj` is the vertical component of
the chart derivative `fderivWithin` of `writtenInExtChartAt IB (IB.prod IF) x s`. -/
theorem modelEquivAt_prolongAt {s : B → ManifoldTotalSpace F E} {x : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s x)
    (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id) :
    modelEquivAt (s x) (prolongAt hs hproj) = (ContinuousLinearMap.snd 𝕜 EB EF).comp
      (fderivWithin 𝕜 (writtenInExtChartAt IB (IB.prod IF) x s) (range IB)
        (extChartAt IB x x)) := by
  ext u
  rw [modelEquivAt_apply, prolongAt_apply, Manifold.tangentSpaceCast_tangentSpaceCastModel_symm,
    hs.mfderiv]
  simp

/-- Local fibre-coordinate representative of `s : B → ManifoldTotalSpace F E` in the preferred
bundle chart at `i`. -/
def localRep (IB : ModelWithCorners 𝕜 EB HB) (IF : ModelWithCorners 𝕜 EF HF)
    (s : B → ManifoldTotalSpace F E) (i : ManifoldTotalSpace F E) (u : EB) : EF :=
  (extChartAt (IB.prod IF) i (s ((extChartAt IB i.proj).symm u))).2

/-- Pointwise formula for `localRep` in the preferred bundle chart at `i`. -/
@[simp]
theorem localRep_apply (IB : ModelWithCorners 𝕜 EB HB) (IF : ModelWithCorners 𝕜 EF HF)
    (s : B → ManifoldTotalSpace F E) (i : ManifoldTotalSpace F E) (u : EB) :
    localRep IB IF s i u = (extChartAt (IB.prod IF) i (s ((extChartAt IB i.proj).symm u))).2 :=
  (rfl)

/-- For a `C^n` map `s` into a `C^n` fibre bundle, the local representative `localRep IB IF s i` is
`C^n` within `range IB` at `extChartAt IB i.proj x`. -/
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

/-- Over a boundaryless base model `IB`, the local representative `localRep IB IF s i` of a `C^n`
local section at `x` is `C^n` on an open neighbourhood (`ContDiffAt`) of
`extChartAt IB i.proj x`. -/
theorem contDiffAt_localRep {n : ℕ∞ω} [IsManifold IB n B] [IsManifold IF n F]
    [ContMDiffFiberBundle n F E IB IF] [IB.Boundaryless]
    {s : B → ManifoldTotalSpace F E} {x : B} {i : ManifoldTotalSpace F E}
    (hs : ContMDiffAt IB (IB.prod IF) n s x)
    (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id)
    (hi : s x ∈ (chartAt (ModelProd HB HF) i).source) :
    ContDiffAt 𝕜 n (localRep IB IF s i) (extChartAt IB i.proj x) := by
  have hx : (s x).proj = x := hproj.eq_of_nhds
  have hbi : x ∈ (extChartAt IB i.proj).source :=
    hx ▸ ManifoldTotalSpace.proj_mem_extChartAt_source_of_mem_chartAt_source hi
  exact (contDiffWithinAt_localRep hs hi hbi).contDiffAt (IB.range_eq_univ ▸ univ_mem)

/-- For a differentiable local section `s` at `x`, `writtenInExtChartAt IB (IB.prod IF) x s` has
chart derivative `(id, modelEquivAt (s x) (prolongAt hs hproj))` within `range IB`. -/
theorem hasFDerivWithinAt_writtenInExtChartAt_of_proj_eventuallyEq
    {s : B → ManifoldTotalSpace F E} {x : B} (hs : MDifferentiableAt IB (IB.prod IF) s x)
    (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id) :
    HasFDerivWithinAt (writtenInExtChartAt IB (IB.prod IF) x s)
      ((ContinuousLinearMap.id 𝕜 EB).prod (modelEquivAt (s x) (prolongAt hs hproj)))
      (range IB) (extChartAt IB x x) := by
  have hx_eq : (s x).proj = x := hproj.eq_of_nhds
  have hxx' := mem_extChartAt_source (I := IB) x
  have hrange : extChartAt IB x x ∈ range IB :=
    extChartAt_target_subset_range x ((extChartAt IB x).map_source hxx')
  set W := writtenInExtChartAt IB (IB.prod IF) x s
  -- Stage 1: in preferred charts around `x` and `s x`, the base coordinate of `W` is locally `id`.
  have hW_fst : (Prod.fst ∘ W) =ᶠ[𝓝[range IB] extChartAt IB x x] id := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := IB) x,
      nhdsWithin_le_nhds (extChartAt_preimage_mem_nhds (hs.continuousAt.preimage_mem_nhds
        ((chartAt (ModelProd HB HF) (s x)).open_source.mem_nhds (mem_chart_source _ (s x))))),
      nhdsWithin_le_nhds (extChartAt_preimage_mem_nhds hproj)] with u hu1 hu2 hu3
    have hu3' : (s ((extChartAt IB x).symm u)).proj = (extChartAt IB x).symm u := hu3
    simp only [W, writtenInExtChartAt, Function.comp_apply, id_eq]
    rw [ManifoldTotalSpace.extChartAt_fst_eq hu2, hx_eq, hu3', (extChartAt IB x).right_inv hu1]
  -- Stage 2: identify the horizontal derivative component via uniqueness on `range IB`.
  have hW_fd := hs.differentiableWithinAt_writtenInExtChartAt.hasFDerivWithinAt
  have hfst : (ContinuousLinearMap.fst 𝕜 EB EF).comp
      (fderivWithin 𝕜 W (range IB) (extChartAt IB x x)) = ContinuousLinearMap.id 𝕜 EB :=
    (IB.uniqueDiffOn _ hrange).eq
      ((hasFDerivAt_fst (𝕜 := 𝕜) (E := EB) (F := EF)).comp_hasFDerivWithinAt _ hW_fd)
      ((hasFDerivWithinAt_id (𝕜 := 𝕜) (extChartAt IB x x) (range IB)).congr_of_eventuallyEq
        hW_fst (hW_fst.self_of_nhdsWithin hrange))
  have hderiv_eq : fderivWithin 𝕜 W (range IB) (extChartAt IB x x) =
      (ContinuousLinearMap.id 𝕜 EB).prod (modelEquivAt (s x) (prolongAt hs hproj)) := by
    rw [modelEquivAt_prolongAt]
    ext v <;> simp only [W, comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.coe_snd']
    exact DFunLike.congr_fun hfst v
  rwa [← hderiv_eq]

/-- Near `extChartAt IB i.proj x`, the local fibre representative `localRep IB IF s i` factors
through `writtenInExtChartAt IB (IB.prod IF) x s` sandwiched between the base and ambient chart
transitions. -/
private theorem localRep_eventuallyEq_writtenInExtChartAt {s : B → ManifoldTotalSpace F E} {x : B}
    {i : ManifoldTotalSpace F E} (hs : ContinuousAt s x)
    (hbi : x ∈ (extChartAt IB i.proj).source) :
    localRep IB IF s i =ᶠ[𝓝[range IB] extChartAt IB i.proj x]
      fun u ↦ ((extChartAt (IB.prod IF) i ∘ (extChartAt (IB.prod IF) (s x)).symm)
        ((writtenInExtChartAt IB (IB.prod IF) x s ∘
          (extChartAt IB x ∘ (extChartAt IB i.proj).symm)) u)).2 := by
  have hsx' := mem_extChartAt_source (I := IB.prod IF) (s x)
  have hxx' := mem_extChartAt_source (I := IB) x
  filter_upwards [nhdsWithin_le_nhds (extChartAt_preimage_mem_nhds' hbi (Filter.inter_mem
    (hs.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := IB.prod IF) (s x)).mem_nhds hsx'))
    ((isOpen_extChartAt_source (I := IB) x).mem_nhds hxx')))] with u ⟨hus, hux⟩
  simp only [localRep_apply, writtenInExtChartAt, Function.comp_apply]
  rw [(extChartAt IB x).left_inv hux, (extChartAt (IB.prod IF) (s x)).left_inv hus]

/-- For a differentiable local section `s` at `x` into a `C^1` fibre bundle, the local
representative `localRep IB IF s i` in any preferred bundle chart `i` containing `s x` has
Fréchet derivative `coordAt i (prolongAt hs hproj)` within `range IB` at
`extChartAt IB i.proj x`. -/
theorem hasFDerivWithinAt_localRep [IsManifold IB 1 B] [IsManifold IF 1 F]
    [ContMDiffFiberBundle 1 F E IB IF] {s : B → ManifoldTotalSpace F E} {x : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s x)
    (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id)
    {i : ManifoldTotalSpace F E} (hi : s x ∈ (chartAt (ModelProd HB HF) i).source) :
    HasFDerivWithinAt (localRep IB IF s i) (coordAt i (prolongAt hs hproj))
      (range IB) (extChartAt IB i.proj x) := by
  have hx_eq : (s x).proj = x := hproj.eq_of_nhds
  have hbi : x ∈ (extChartAt IB i.proj).source :=
    hx_eq ▸ ManifoldTotalSpace.proj_mem_extChartAt_source_of_mem_chartAt_source hi
  have hi' : s x ∈ (extChartAt (IB.prod IF) i).source :=
    (extChartAt_source (IB.prod IF) i).symm ▸ hi
  have hsx' := mem_extChartAt_source (I := IB.prod IF) (s x)
  have hxx' := mem_extChartAt_source (I := IB) x
  have hrange : extChartAt IB i.proj x ∈ range IB :=
    extChartAt_target_subset_range i.proj ((extChartAt IB i.proj).map_source hbi)
  -- Stage 1: differentiate the base chart transition, then compose with `writtenInExtChartAt`.
  set W := writtenInExtChartAt IB (IB.prod IF) x s
  have hbase : HasFDerivWithinAt (extChartAt IB x ∘ (extChartAt IB i.proj).symm)
      (tangentCoordChange IB i.proj (s x).proj (s x).proj) (range IB) (extChartAt IB i.proj x) := by
    rw [hx_eq]; exact hasFDerivWithinAt_tangentCoordChange ⟨hbi, hxx'⟩
  have hpt1 : (extChartAt IB x ∘ (extChartAt IB i.proj).symm) (extChartAt IB i.proj x) =
      extChartAt IB x x := by rw [Function.comp_apply, (extChartAt IB i.proj).left_inv hbi]
  have hmid := (hpt1 ▸ hasFDerivWithinAt_writtenInExtChartAt_of_proj_eventuallyEq hs hproj).comp _
    hbase fun u _ ↦ by rw [Function.comp_apply, extChartAt_coe]; exact mem_range_self _
  -- Stage 2: compose with the ambient chart transition and project onto the fibre factor.
  have hpt2 : (W ∘ (extChartAt IB x ∘ (extChartAt IB i.proj).symm)) (extChartAt IB i.proj x) =
      extChartAt (IB.prod IF) (s x) (s x) := by
    dsimp only [W, writtenInExtChartAt, Function.comp_apply]
    rw [(extChartAt IB i.proj).left_inv hbi, (extChartAt IB x).left_inv hxx']
  have htop := hasFDerivAt_snd.comp_hasFDerivWithinAt _
    ((hpt2 ▸ hasFDerivWithinAt_tangentCoordChange (I := IB.prod IF) ⟨hsx', hi'⟩).comp _ hmid
      fun u _ ↦ by
        simp only [W, writtenInExtChartAt, Function.comp_apply, extChartAt_coe]
        exact mem_range_self _)
  -- Stage 3: transfer along the eventual equality with `localRep IB IF s i`.
  have hev := localRep_eventuallyEq_writtenInExtChartAt (IB := IB) (IF := IF) hs.continuousAt hbi
  rw [coordAt_eq_coordChange_modelEquivAt hi]
  exact (htop.congr_of_eventuallyEq hev (hev.self_of_nhdsWithin hrange)).congr_fderiv
    (by ext u; simp only [coordChange_apply, comp_apply, ContinuousLinearMap.prod_apply,
      id_apply, coe_snd'])

/-- In any preferred bundle chart `i` containing `s x`, the jet coordinate `coordAt i` of
`prolongAt hs hproj` is the derivative `fderivWithin` of `localRep IB IF s i` within `range IB`. -/
theorem coordAt_prolongAt [IsManifold IB 1 B] [IsManifold IF 1 F]
    [ContMDiffFiberBundle 1 F E IB IF] {s : B → ManifoldTotalSpace F E} {x : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s x) (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id)
    {i : ManifoldTotalSpace F E} (hi : s x ∈ (chartAt (ModelProd HB HF) i).source) :
    coordAt i (prolongAt hs hproj) =
      fderivWithin 𝕜 (localRep IB IF s i) (range IB) (extChartAt IB i.proj x) := by
  have hx_eq : (s x).proj = x := hproj.eq_of_nhds
  have hbi : x ∈ (extChartAt IB i.proj).source :=
    hx_eq ▸ ManifoldTotalSpace.proj_mem_extChartAt_source_of_mem_chartAt_source hi
  exact ((hasFDerivWithinAt_localRep hs hproj hi).fderivWithin
    (IB.uniqueDiffOn _ (extChartAt_target_subset_range i.proj
      ((extChartAt IB i.proj).map_source hbi)))).symm

end FiberFirstJet

namespace FiberFirstJetBundle

open Classical in
variable (IB IF) in
/-- **Holonomic prolongation of a local section** `s : B → ManifoldTotalSpace F E` at `x`.
Evaluates to `⟨s x, FiberFirstJet.prolongAt hs hproj⟩` when `s` is differentiable at `x` and
satisfies `(ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id`, and falls back to
`⟨s x, Classical.arbitrary _⟩` otherwise. -/
def prolong (s : B → ManifoldTotalSpace F E) (x : B) : FiberFirstJetBundle IB IF F E :=
  if h : MDifferentiableAt IB (IB.prod IF) s x ∧ (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id then
    ⟨s x, FiberFirstJet.prolongAt h.1 h.2⟩
  else ⟨s x, Classical.arbitrary _⟩

/-- The target-bundle projection of `prolong IB IF s x` is `s x`. -/
@[simp]
theorem proj_prolong (s : B → ManifoldTotalSpace F E) (x : B) :
    (prolong IB IF s x).proj = s x := by
  simp only [prolong]; split_ifs <;> rfl

/-- The source (base) projection of `prolong IB IF s x` is `(s x).proj`. -/
@[simp]
theorem baseProj_prolong (s : B → ManifoldTotalSpace F E) (x : B) :
    baseProj (prolong IB IF s x) = (s x).proj := by
  rw [baseProj_apply, proj_prolong]

/-- When `s` is differentiable at `x` and locally a section near `x`, `prolong IB IF s x` evaluates
to `⟨s x, FiberFirstJet.prolongAt hs hproj⟩`. -/
theorem prolong_of_mdifferentiableAt {s : B → ManifoldTotalSpace F E} {x : B}
    (hs : MDifferentiableAt IB (IB.prod IF) s x)
    (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x] id) :
    prolong IB IF s x = ⟨s x, FiberFirstJet.prolongAt hs hproj⟩ :=
  dite_eq_left ⟨hs, hproj⟩

/-- Holonomic prolongation at `x` depends only on the germ of `s` at `x`. -/
theorem prolong_congr {s₁ s₂ : B → ManifoldTotalSpace F E} {x : B} (h : s₁ =ᶠ[𝓝 x] s₂) :
    prolong IB IF s₁ x = prolong IB IF s₂ x := by
  have hx : s₁ x = s₂ x := h.eq_of_nhds
  by_cases hs₁ : MDifferentiableAt IB (IB.prod IF) s₁ x ∧ (ManifoldTotalSpace.proj ∘ s₁) =ᶠ[𝓝 x] id
  · have hs₂ : MDifferentiableAt IB (IB.prod IF) s₂ x ∧ (ManifoldTotalSpace.proj ∘ s₂) =ᶠ[𝓝 x] id :=
      ⟨hs₁.1.congr_of_eventuallyEq h.symm, (h.symm.fun_comp ManifoldTotalSpace.proj).trans hs₁.2⟩
    rw [prolong_of_mdifferentiableAt hs₁.1 hs₁.2, prolong_of_mdifferentiableAt hs₂.1 hs₂.2,
      mk_eq_mk_iff_modelEquivAt]
    refine ⟨hx, ?_⟩
    ext u
    rw [FiberFirstJet.modelEquivAt_apply, FiberFirstJet.modelEquivAt_apply,
      FiberFirstJet.prolongAt_apply, FiberFirstJet.prolongAt_apply,
      Manifold.tangentSpaceCast_tangentSpaceCastModel_symm,
      Manifold.tangentSpaceCast_tangentSpaceCastModel_symm, h.symm.mfderiv_eq]
    simp
  · have hs₂ : ¬(MDifferentiableAt IB (IB.prod IF) s₂ x ∧
        (ManifoldTotalSpace.proj ∘ s₂) =ᶠ[𝓝 x] id) := fun h₂ ↦
      hs₁ ⟨h₂.1.congr_of_eventuallyEq h, (h.fun_comp ManifoldTotalSpace.proj).trans h₂.2⟩
    simp only [prolong, hs₁, hs₂, ↓reduceDIte]
    exact congrArg (fun z ↦ (⟨z, Classical.arbitrary _⟩ : FiberFirstJetBundle IB IF F E)) hx

variable (IB IF F) in
/-- **Holonomic prolongation of a global dependent section** `s : ∀ b, E b` at `x`.
Defined as `prolong IB IF (fun b ↦ ManifoldTotalSpace.homeomorph F E ⟨b, s b⟩) x`: it evaluates to
`FiberFirstJet.prolongAt` when `b ↦ homeomorph F E ⟨b, s b⟩` is differentiable at `x`, and falls
back to `⟨homeomorph F E ⟨x, s x⟩, Classical.arbitrary _⟩` otherwise. -/
def jet (s : ∀ b, E b) (x : B) : FiberFirstJetBundle IB IF F E :=
  prolong IB IF (fun b ↦ ManifoldTotalSpace.homeomorph F E ⟨b, s b⟩) x

/-- `jet IB IF F s x` is defined as `prolong` of `b ↦ homeomorph F E ⟨b, s b⟩` at `x`. -/
theorem jet_eq_prolong (s : ∀ b, E b) (x : B) :
    jet IB IF F s x = prolong IB IF (fun b ↦ ManifoldTotalSpace.homeomorph F E ⟨b, s b⟩) x :=
  (rfl)

/-- The target projection of `jet IB IF F s x` in `ManifoldTotalSpace F E` is
`homeomorph F E ⟨x, s x⟩`. -/
@[simp]
theorem proj_jet (s : ∀ b, E b) (x : B) :
    (jet IB IF F s x).proj = ManifoldTotalSpace.homeomorph F E ⟨x, s x⟩ :=
  proj_prolong _ x

/-- The base projection of `jet IB IF F s x` is `x`. -/
@[simp]
theorem baseProj_jet (s : ∀ b, E b) (x : B) : baseProj (jet IB IF F s x) = x := by
  rw [baseProj_apply, proj_jet, ManifoldTotalSpace.proj_homeomorph]

/-- **Pointwise regularity of holonomic prolongation**: if `s` is `C^n` at `x₀` with `m + 1 ≤ n`
and locally a section near `x₀`, then `prolong IB IF s` is `C^m` at `x₀` (assuming only `C^1`
bundle regularity). -/
theorem contMDiffAt_prolong {m n : ℕ∞ω} [IsManifold IB 1 B] [IsManifold IF 1 F]
    [ContMDiffFiberBundle 1 F E IB IF] {s : B → ManifoldTotalSpace F E} {x₀ : B}
    (hs : ContMDiffAt IB (IB.prod IF) n s x₀) (hmn : m + 1 ≤ n)
    (hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x₀] id) :
    ContMDiffAt IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) m (prolong IB IF s) x₀ := by
  refine Bundle.contMDiffAt_totalSpace_iff.2 ?_
  simp only [proj_prolong]
  refine ⟨hs.of_le (le_trans le_self_add hmn), ?_⟩
  set i := s x₀
  have hx₀_eq : i.proj = x₀ := hproj.eq_of_nhds
  have hx₀_src : x₀ ∈ (extChartAt IB i.proj).source := hx₀_eq.symm ▸ mem_extChartAt_source x₀
  -- Stage 1: show the local fibre representative is `C^n` within `range IB`, so its `fderivWithin`
  -- is `C^m` on `range IB` and composes with `extChartAt IB i.proj`.
  have hrep : ContDiffWithinAt 𝕜 n (FiberFirstJet.localRep IB IF s i) (range IB)
      (extChartAt IB i.proj x₀) := by
    have hfn : FiberFirstJet.localRep IB IF s i =
        (ContinuousLinearMap.snd 𝕜 EB EF) ∘
          (extChartAt (IB.prod IF) (s x₀) ∘ s ∘ (extChartAt IB x₀).symm) := by
      ext u
      simp [FiberFirstJet.localRep_apply, i, hx₀_eq]
    rw [hfn, hx₀_eq]
    exact (ContinuousLinearMap.snd 𝕜 EB EF).contDiff.comp_contDiffWithinAt (contMDiffAt_iff.1 hs).2
  have hfd := contMDiffWithinAt_iff_contDiffWithinAt.2
    (hrep.fderivWithin_right IB.uniqueDiffOn hmn
      (extChartAt_target_subset_range i.proj ((extChartAt IB i.proj).map_source hx₀_src)))
  have hext : ContMDiffAt IB 𝓘(𝕜, EB) m (extChartAt IB i.proj) x₀ :=
    hx₀_eq.symm ▸ (contMDiffAt_extChartAt (I := IB) (n := m) (x := x₀))
  have hderiv : ContMDiffAt IB 𝓘(𝕜, EB →L[𝕜] EF) m
      (fun x ↦ fderivWithin 𝕜 (FiberFirstJet.localRep IB IF s i) (range IB)
        (extChartAt IB i.proj x)) x₀ := by
    rw [← contMDiffWithinAt_univ]
    exact hfd.comp x₀ hext.contMDiffWithinAt fun x _ ↦ by
      rw [extChartAt_coe]; exact mem_range_self _
  -- Stage 2: transfer `C^m` regularity to the trivialization coordinate of `prolong IB IF s` via
  -- `FiberFirstJet.coordAt_prolongAt` on a neighbourhood of `x₀`.
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [(hs.of_le (le_trans le_add_self hmn)).eventually_mdifferentiableAt one_ne_zero,
    eventually_eventually_nhds.2 hproj,
    hs.continuousAt.preimage_mem_nhds
      ((chartAt (ModelProd HB HF) i).open_source.mem_nhds (mem_chart_source _ i))]
    with x hsx hproj_x hxs
  rw [prolong_of_mdifferentiableAt hsx hproj_x, FiberFirstJet.trivializationAt_apply,
    FiberFirstJet.coordAt_prolongAt hsx hproj_x hxs]

/-- On an open set `U`, the holonomic prolongation of a `C^n` local section is `C^m` whenever
`m + 1 ≤ n`. -/
theorem contMDiffOn_prolong {m n : ℕ∞ω} [IsManifold IB 1 B] [IsManifold IF 1 F]
    [ContMDiffFiberBundle 1 F E IB IF] {s : B → ManifoldTotalSpace F E} {U : Set B}
    (hU : IsOpen U) (hs : ContMDiffOn IB (IB.prod IF) n s U) (hmn : m + 1 ≤ n)
    (hproj : ∀ x ∈ U, (s x).proj = x) :
    ContMDiffOn IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) m (prolong IB IF s) U := by
  intro x₀ hx₀
  have hproj_nhds : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 x₀] id := by
    filter_upwards [hU.mem_nhds hx₀] with x hx using hproj x hx
  exact (contMDiffAt_prolong (hs.contMDiffAt (hU.mem_nhds hx₀)) hmn hproj_nhds).contMDiffWithinAt

/-- If a dependent section `s : ∀ b, E b` is `C^n` at `x₀` with `m + 1 ≤ n`, then `jet IB IF F s`
is `C^m` at `x₀`. -/
theorem contMDiffAt_jet {m n : ℕ∞ω} [IsManifold IB 1 B] [IsManifold IF 1 F]
    [ContMDiffFiberBundle 1 F E IB IF] {s : ∀ b, E b} {x₀ : B}
    (hs : ContMDiffAt IB (IB.prod IF) n (fun b ↦ ManifoldTotalSpace.homeomorph F E ⟨b, s b⟩) x₀)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) m (jet IB IF F s) x₀ :=
  contMDiffAt_prolong hs hmn
    (Eventually.of_forall fun b ↦ ManifoldTotalSpace.proj_homeomorph ⟨b, s b⟩)

/-- On an open set `U`, the first jet `jet IB IF F s` of a `C^n` dependent section is `C^m`
whenever `m + 1 ≤ n`. -/
theorem contMDiffOn_jet {m n : ℕ∞ω} [IsManifold IB 1 B] [IsManifold IF 1 F]
    [ContMDiffFiberBundle 1 F E IB IF] {s : ∀ b, E b} {U : Set B} (hU : IsOpen U)
    (hs : ContMDiffOn IB (IB.prod IF) n (fun b ↦ ManifoldTotalSpace.homeomorph F E ⟨b, s b⟩) U)
    (hmn : m + 1 ≤ n) :
    ContMDiffOn IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) m (jet IB IF F s) U :=
  contMDiffOn_prolong hU hs hmn fun b _ ↦ ManifoldTotalSpace.proj_homeomorph ⟨b, s b⟩

/-- The first jet `jet IB IF F s` of a globally `C^n` dependent section is `C^m` whenever
`m + 1 ≤ n`. -/
theorem contMDiff_jet {m n : ℕ∞ω} [IsManifold IB 1 B] [IsManifold IF 1 F]
    [ContMDiffFiberBundle 1 F E IB IF] {s : ∀ b, E b}
    (hs : ContMDiff IB (IB.prod IF) n fun b ↦ ManifoldTotalSpace.homeomorph F E ⟨b, s b⟩)
    (hmn : m + 1 ≤ n) :
    ContMDiff IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) m (jet IB IF F s) :=
  fun x ↦ contMDiffAt_jet (hs x) hmn

/-- **Bridge to the `C^∞` local germ quotient `FirstJetAt`**: over a boundaryless base model `IB`,
two `C^∞` local sections through a common bundle chart `i` have equal 1-jet prolongations at `x`
iff their local coordinate representatives define the same class in `FirstJetAt`. -/
theorem prolong_eq_iff_firstJetAt_mk_eq [IsManifold IB ∞ B] [IsManifold IF ∞ F]
    [ContMDiffFiberBundle ∞ F E IB IF] [IB.Boundaryless]
    {s₁ s₂ : B → ManifoldTotalSpace F E} {x : B} {i : ManifoldTotalSpace F E}
    (hs₁ : ContMDiffAt IB (IB.prod IF) ∞ s₁ x) (hs₂ : ContMDiffAt IB (IB.prod IF) ∞ s₂ x)
    (hproj₁ : (ManifoldTotalSpace.proj ∘ s₁) =ᶠ[𝓝 x] id)
    (hproj₂ : (ManifoldTotalSpace.proj ∘ s₂) =ᶠ[𝓝 x] id)
    (hi₁ : s₁ x ∈ (chartAt (ModelProd HB HF) i).source)
    (hi₂ : s₂ x ∈ (chartAt (ModelProd HB HF) i).source) :
    prolong IB IF s₁ x = prolong IB IF s₂ x ↔
      FirstJetAt.mk (FiberFirstJet.localRep IB IF s₁ i)
          (FiberFirstJet.contDiffAt_localRep hs₁ hproj₁ hi₁) =
        FirstJetAt.mk (FiberFirstJet.localRep IB IF s₂ i)
          (FiberFirstJet.contDiffAt_localRep hs₂ hproj₂ hi₂) := by
  have hx₁ : (s₁ x).proj = x := hproj₁.eq_of_nhds
  have hx₂ : (s₂ x).proj = x := hproj₂.eq_of_nhds
  have hbi : x ∈ (extChartAt IB i.proj).source :=
    hx₁ ▸ ManifoldTotalSpace.proj_mem_extChartAt_source_of_mem_chartAt_source hi₁
  have hmd₁ := hs₁.mdifferentiableAt (by simp)
  have hmd₂ := hs₂.mdifferentiableAt (by simp)
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

/-- Affine chart-model lift `(u, v₀ + A (u - u₀))` around `z : ManifoldTotalSpace F E` with
slope `A : EB →L[𝕜] EF`. -/
private def localAffineCoord (IB : ModelWithCorners 𝕜 EB HB) (IF : ModelWithCorners 𝕜 EF HF)
    (z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) (b : B) : EB × EF :=
  (extChartAt IB z.proj b,
    (extChartAt (IB.prod IF) z z).2 + A (extChartAt IB z.proj b - extChartAt IB z.proj z.proj))

/-- Local section witness near `z.proj` obtained by pulling back `localAffineCoord` along
`(extChartAt (IB.prod IF) z).symm`. -/
private def localAffineSection (IB : ModelWithCorners 𝕜 EB HB) (IF : ModelWithCorners 𝕜 EF HF)
    (z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) (b : B) : ManifoldTotalSpace F E :=
  (extChartAt (IB.prod IF) z).symm (localAffineCoord IB IF z A b)

private theorem localAffineCoord_self (z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) :
    localAffineCoord IB IF z A z.proj = extChartAt (IB.prod IF) z z := by
  simp only [localAffineCoord, sub_self, map_zero, add_zero]
  exact Prod.ext (ManifoldTotalSpace.extChartAt_fst_eq (mem_chart_source _ z)).symm rfl

private theorem localAffineSection_self (z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) :
    localAffineSection IB IF z A z.proj = z := by
  rw [localAffineSection, localAffineCoord_self,
    (extChartAt (IB.prod IF) z).left_inv (mem_extChartAt_source z)]

private theorem localAffineCoord_mem_range [IF.Boundaryless]
    (z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) (b : B) :
    localAffineCoord IB IF z A b ∈ range (IB.prod IF) := by
  rw [ModelWithCorners.range_prod, IF.range_eq_univ]
  exact ⟨by dsimp only [localAffineCoord]; rw [extChartAt_coe]; exact mem_range_self _, mem_univ _⟩

private theorem contMDiffAt_localAffineCoord (z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) :
    ContMDiffAt IB 𝓘(𝕜, EB × EF) ω (localAffineCoord IB IF z A) z.proj :=
  have hf : ContDiff 𝕜 ω fun u : EB ↦
      (extChartAt (IB.prod IF) z z).2 + A (u - extChartAt IB z.proj z.proj) :=
    contDiff_const.add (A.contDiff.comp (contDiff_id.sub contDiff_const))
  contMDiffAt_extChartAt.prodMk_space
    (hf.contDiffAt.contMDiffAt.comp z.proj contMDiffAt_extChartAt)

private theorem contMDiffAt_localAffineSection [IF.Boundaryless]
    (z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) :
    ContMDiffAt IB (IB.prod IF) ω (localAffineSection IB IF z A) z.proj := by
  rw [← contMDiffWithinAt_univ]
  exact ((localAffineCoord_self (IB := IB) (IF := IF) z A).symm ▸
    contMDiffWithinAt_extChartAt_symm_range_self z).comp z.proj
    (contMDiffAt_localAffineCoord (IB := IB) (IF := IF) z A).contMDiffWithinAt
    fun b _ ↦ localAffineCoord_mem_range z A b

private theorem proj_comp_localAffineSection_eventuallyEq [IF.Boundaryless]
    (z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) :
    (ManifoldTotalSpace.proj ∘ localAffineSection IB IF z A) =ᶠ[𝓝 z.proj] id := by
  have hu_open : IsOpen ((IB.prod IF).symm ⁻¹' (chartAt (ModelProd HB HF) z).target) :=
    (chartAt (ModelProd HB HF) z).open_target.preimage (IB.prod IF).continuous_symm
  have hu_mem : localAffineCoord IB IF z A z.proj ∈
      (IB.prod IF).symm ⁻¹' (chartAt (ModelProd HB HF) z).target := by
    rw [localAffineCoord_self]
    exact ((extChartAt_target (I := IB.prod IF) z) ▸ mem_extChartAt_target z).1
  have hg_mem : ∀ᶠ b in 𝓝 z.proj,
      localAffineCoord IB IF z A b ∈ (extChartAt (IB.prod IF) z).target := by
    filter_upwards [(contMDiffAt_localAffineCoord (IB := IB) (IF := IF) z A).continuousAt.eventually
      (hu_open.mem_nhds hu_mem)] with b hb
    rw [extChartAt_target]
    exact ⟨hb, localAffineCoord_mem_range z A b⟩
  filter_upwards [hg_mem,
    (isOpen_extChartAt_source (I := IB) z.proj).mem_nhds (mem_extChartAt_source z.proj)]
    with b hb1 hb2
  dsimp only [Function.comp_apply, localAffineSection, id_eq]
  rw [ManifoldTotalSpace.proj_extChartAt_symm z hb1]
  exact (extChartAt IB z.proj).left_inv hb2

private theorem writtenInExtChartAt_localAffineSection_eventuallyEq [IF.Boundaryless]
    (z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) :
    writtenInExtChartAt IB (IB.prod IF) z.proj (localAffineSection IB IF z A) =ᶠ[
      𝓝[range IB] extChartAt IB z.proj z.proj]
      fun u ↦ (u, (extChartAt (IB.prod IF) z z).2 + A (u - extChartAt IB z.proj z.proj)) := by
  set u₀ := extChartAt IB z.proj z.proj with hu₀
  set v₀ := (extChartAt (IB.prod IF) z z).2
  let f : EB → EF := fun u ↦ v₀ + A (u - u₀)
  have hf_cont : Continuous f :=
    continuous_const.add (A.continuous.comp (continuous_id.sub continuous_const))
  have hu_open : IsOpen ((IB.prod IF).symm ⁻¹' (chartAt (ModelProd HB HF) z).target) :=
    (chartAt (ModelProd HB HF) z).open_target.preimage (IB.prod IF).continuous_symm
  have hu₀_mem : (u₀, f u₀) ∈ (IB.prod IF).symm ⁻¹' (chartAt (ModelProd HB HF) z).target := by
    have hf₀ : (u₀, f u₀) = extChartAt (IB.prod IF) z z :=
      localAffineCoord_self (IB := IB) (IF := IF) z A
    rw [hf₀]
    exact ((extChartAt_target (I := IB.prod IF) z) ▸ mem_extChartAt_target z).1
  filter_upwards [hu₀ ▸ extChartAt_target_mem_nhdsWithin (I := IB) z.proj,
    nhdsWithin_le_nhds ((continuousAt_id.prodMk hf_cont.continuousAt).eventually
      (hu_open.mem_nhds hu₀_mem))] with u hu1 hu2
  have hmem : (u, f u) ∈ (extChartAt (IB.prod IF) z).target := by
    rw [extChartAt_target, ModelWithCorners.range_prod, IF.range_eq_univ]
    exact ⟨hu2, extChartAt_target_subset_range z.proj hu1, mem_univ _⟩
  dsimp only [writtenInExtChartAt, Function.comp_apply]
  rw [localAffineSection_self]
  dsimp only [localAffineSection, localAffineCoord]
  rw [(extChartAt IB z.proj).right_inv hu1]
  exact (extChartAt (IB.prod IF) z).right_inv hmem

private theorem fderivWithin_writtenInExtChartAt_localAffineSection [IF.Boundaryless]
    (z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) :
    fderivWithin 𝕜 (writtenInExtChartAt IB (IB.prod IF) z.proj (localAffineSection IB IF z A))
        (range IB) (extChartAt IB z.proj z.proj) =
      (ContinuousLinearMap.id 𝕜 EB).prod A := by
  set u₀ := extChartAt IB z.proj z.proj with hu₀
  set v₀ := (extChartAt (IB.prod IF) z z).2
  have hf_deriv : HasFDerivAt (fun u ↦ v₀ + A (u - u₀)) A u₀ := by
    simpa using (A.hasFDerivAt.comp u₀ (hasFDerivAt_sub_const u₀)).const_add v₀
  have hrange : u₀ ∈ range IB :=
    hu₀ ▸ extChartAt_target_subset_range z.proj (mem_extChartAt_target z.proj)
  have hev := writtenInExtChartAt_localAffineSection_eventuallyEq (IB := IB) (IF := IF) z A
  exact (((hasFDerivAt_id u₀).prodMk hf_deriv).hasFDerivWithinAt (s := range IB)
    |>.congr_of_eventuallyEq hev (hev.self_of_nhdsWithin hrange)).fderivWithin
    (IB.uniqueDiffOn u₀ hrange)

/-- **Every 1-jet over a boundaryless fibre is realized by a local `C^n` section**: for any `z` and
`j : FiberFirstJet IB IF F E z`, there exists a map `s : B → ManifoldTotalSpace F E` that is `C^n`
at `z.proj`, satisfies `s z.proj = z` and `(ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 z.proj] id`, and has
prolongation `prolong IB IF s z.proj = ⟨z, j⟩`. -/
theorem exists_contMDiffAt_prolong_eq {n : ℕ∞ω} [IF.Boundaryless]
    (z : ManifoldTotalSpace F E) (j : FiberFirstJet IB IF F E z) :
    ∃ s : B → ManifoldTotalSpace F E, ContMDiffAt IB (IB.prod IF) n s z.proj ∧ s z.proj = z ∧
      (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 z.proj] id ∧ prolong IB IF s z.proj = ⟨z, j⟩ := by
  set A := FiberFirstJet.modelEquivAt z j
  set s := localAffineSection IB IF z A
  -- Stage 1: value, `C^ω` regularity, and local section property of the affine chart lift `s`.
  have hs_pt : s z.proj = z := localAffineSection_self z A
  have hs_top : ContMDiffAt IB (IB.prod IF) ω s z.proj := contMDiffAt_localAffineSection z A
  have hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 z.proj] id :=
    proj_comp_localAffineSection_eventuallyEq z A
  refine ⟨s, hs_top.of_le le_top, hs_pt, hproj, ?_⟩
  -- Stage 2: identify the prolongation in preferred model coordinates via the chart derivative.
  have hs_md := hs_top.mdifferentiableAt (by simp)
  rw [prolong_of_mdifferentiableAt hs_md hproj, mk_eq_mk_iff_modelEquivAt]
  refine ⟨hs_pt, ?_⟩
  rw [FiberFirstJet.modelEquivAt_prolongAt, fderivWithin_writtenInExtChartAt_localAffineSection]
  ext v
  simp only [A, comp_apply, ContinuousLinearMap.prod_apply, coe_snd']

/-- **Cartan contact characterization of holonomic sections**: for a differentiable local section
`σ : B → FiberFirstJetBundle IB IF F E` over `B` (`(baseProj ∘ σ) =ᶠ[𝓝 x] id`), the pullback of the
pointwise contact map `contactFormAt (σ x)` along `mfderiv _ _ σ x` vanishes iff `σ x` equals the
holonomic prolongation of its underlying bundle section `TotalSpace.proj ∘ σ` at `x`. -/
theorem contactFormAt_comp_mfderiv_eq_zero_iff [IsManifold IB 1 B] [IsManifold IF 1 F]
    [ContMDiffFiberBundle 1 F E IB IF] {σ : B → FiberFirstJetBundle IB IF F E} {x : B}
    (hσ : MDifferentiableAt IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) σ x)
    (hbase : (baseProj ∘ σ) =ᶠ[𝓝 x] id) :
    (contactFormAt (σ x)).comp (mfderiv IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) σ x) = 0 ↔
      σ x = prolong IB IF (TotalSpace.proj ∘ σ) x := by
  -- Stage 1: relate `mfderiv` of `σ`, the projected section `TotalSpace.proj ∘ σ`, and `prolongAt`.
  have hs : MDifferentiableAt IB (IB.prod IF) (TotalSpace.proj ∘ σ) x :=
    (Bundle.mdifferentiableAt_proj (FiberFirstJet IB IF F E)).comp x hσ
  have hproj : (ManifoldTotalSpace.proj ∘ (TotalSpace.proj ∘ σ)) =ᶠ[𝓝 x] id := by
    rwa [baseProj_eq_proj_comp_proj] at hbase
  have hmfd_s (v : TangentSpace IB x) :
      mfderiv ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) (IB.prod IF) TotalSpace.proj (σ x)
        (mfderiv IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) σ x v) =
        mfderiv IB (IB.prod IF) (TotalSpace.proj ∘ σ) x v :=
    DFunLike.congr_fun
      (mfderiv_comp x (Bundle.mdifferentiableAt_proj (FiberFirstJet IB IF F E)) hσ).symm v
  have hprolong (v : TangentSpace IB x) :
      FiberFirstJet.prolongAt hs hproj (tangentSpaceCast IB x (σ x).proj.proj v) =
        mfderiv IB (IB.prod IF) (TotalSpace.proj ∘ σ) x v := by
    rw [FiberFirstJet.prolongAt_apply]
    dsimp only [Function.comp_apply]
    rw [← Manifold.tangentSpaceCast_symm IB x (σ x).proj.proj,
      ContinuousLinearEquiv.symm_apply_apply]
  have hmfd_base (v : TangentSpace IB x) :
      mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj (σ x).proj
        (mfderiv IB (IB.prod IF) (TotalSpace.proj ∘ σ) x v) =
        tangentSpaceCast IB x (σ x).proj.proj v := by
    rw [← hprolong v]
    exact (FiberFirstJet.prolongAt hs hproj).mfderiv_proj_apply _
  -- Stage 2: expand `contactFormAt` in ambient tangent coordinates for both implications.
  rw [prolong_of_mdifferentiableAt hs hproj]
  refine ⟨fun h0 ↦ ?_, fun h_eq ↦ ?_⟩
  · refine TotalSpace.ext rfl (heq_of_eq ?_)
    ext u
    have htan :
        ((((contactFormAt (σ x)).comp (mfderiv IB ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) σ x))
          (tangentSpaceCast IB (σ x).proj.proj x u) :
          VerticalSpace IB IF F E (σ x).proj) : TangentSpace (IB.prod IF) (σ x).proj) = 0 := by
      rw [h0, zero_apply, VerticalSpace.coe_zero]
    rw [comp_apply, coe_contactFormAt, hmfd_s, hmfd_base,
      ← Manifold.tangentSpaceCast_symm IB x (σ x).proj.proj, ContinuousLinearEquiv.apply_symm_apply,
      Manifold.tangentSpaceCast_symm, sub_eq_zero] at htan
    rw [FiberFirstJet.prolongAt_apply]
    dsimp only [Function.comp_apply]
    exact htan.symm
  · have hj : (σ x).snd = FiberFirstJet.prolongAt hs hproj := eq_of_heq (TotalSpace.mk.inj h_eq).2
    refine ContinuousLinearMap.ext fun v ↦ VerticalSpace.ext ?_
    rw [zero_apply, VerticalSpace.coe_zero, comp_apply, coe_contactFormAt, hmfd_s, hmfd_base, hj,
      hprolong, sub_self]

-- Sanity check: prolonging `x ↦ (x, x * x)` on `ℝ × ℝ` at `x = 3` gives derivative `6` and
-- annihilates the holonomic tangent vector `(1, 6)` under `contactProj`.
example :
    let s : ℝ → ManifoldTotalSpace ℝ (Bundle.Trivial ℝ ℝ) :=
      fun x ↦ ManifoldTotalSpace.homeomorph ℝ (Bundle.Trivial ℝ ℝ)
        ⟨x, (x * x : Bundle.Trivial ℝ ℝ x)⟩
    have hs : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) s 3 :=
      (ManifoldTotalSpace.contMDiffAt_iff.2
        ⟨contMDiffAt_id, (contDiff_id.mul contDiff_id).contMDiff.contMDiffAt⟩).mdifferentiableAt
        one_ne_zero
    have hproj : (ManifoldTotalSpace.proj ∘ s) =ᶠ[𝓝 (3 : ℝ)] id :=
      Eventually.of_forall fun x ↦
        ManifoldTotalSpace.proj_homeomorph
          (⟨x, (x * x : Bundle.Trivial ℝ ℝ x)⟩ : TotalSpace ℝ (Bundle.Trivial ℝ ℝ))
    FiberFirstJet.modelEquivAt (s 3) (FiberFirstJet.prolongAt hs hproj) 1 = 6 ∧
      (FiberFirstJet.prolongAt hs hproj).contactProj
        ((tangentSpaceCastModel (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (s 3)).symm (1, 6)) = 0 := by
  intro s hs hproj
  have hpair : writtenInExtChartAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 3 s =
      fun x : ℝ ↦ (x, x * x) := by
    funext x
    dsimp only [writtenInExtChartAt, s, Function.comp_apply]
    rw [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq,
      ManifoldTotalSpace.extChartAt_homeomorph_apply]
    simp
  have hd : HasFDerivAt (writtenInExtChartAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 3 s)
      ((ContinuousLinearMap.id ℝ ℝ).prod
        ((3 : ℝ) • ContinuousLinearMap.id ℝ ℝ + (3 : ℝ) • ContinuousLinearMap.id ℝ ℝ)) 3 :=
    hpair ▸ (hasFDerivAt_id (3 : ℝ)).prodMk ((hasFDerivAt_id (3 : ℝ)).mul (hasFDerivAt_id (3 : ℝ)))
  have hval : FiberFirstJet.modelEquivAt (s 3) (FiberFirstJet.prolongAt hs hproj) =
      (6 : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
    rw [FiberFirstJet.modelEquivAt_prolongAt]
    simp only [modelWithCornersSelf_coe, range_id, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, id_eq, fderivWithin_univ, hd.fderiv]
    ext
    norm_num
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
end TauCeti

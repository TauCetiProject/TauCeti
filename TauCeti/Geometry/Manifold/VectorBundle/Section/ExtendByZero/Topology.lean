/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.ExtendByZero
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmulLeft
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map.Basic
public import TauCeti.Topology.Algebra.Module.Spaces.CompactConvergenceCLM
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Open extension of native bundle tests

Extension by zero is continuous on fixed compact-support stages and for their native final
locally convex topology. The construction works for all supported regularities on the raw
section carriers. On native smooth bundle tests it gives continuous linear extension maps,
compact-convergence transposes, nested-open laws and the universal-open equivalence.
-/

public noncomputable section

open Bundle Set TopologicalSpace Topology ContMDiffSection
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney CompactConvergenceCLM

namespace ContMDiffSection

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LocallyCompactSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞ω}
  [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {U D : Opens M} (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
  (hD : (D : Set M) ⊆ e.baseSet)
  {P : Type*} [TopologicalSpace P]

/-- A fixed compact support lets pulled-back frame continuity extend across the boundary by zero. -/
theorem continuous_extended_frame_of_fixed_support
    (K : Compacts U)
    (s : P → compactlySupported I F n
      ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V))
    (hK : ∀ p, (s p).val.tsupport ⊆ K) :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let DU := Opens.comap c D
    let hDU : (DU : Set U) ⊆ (e.pullback c).baseSet := fun _ hx ↦ hD hx
    Continuous (fun p ↦ (e.pullback c).frameCoordinates hDU (s p).val) →
      Continuous (fun p ↦ e.frameCoordinates hD (extendByZero (s p))) := by
  intro c DU hDU hs
  have hL : IsClosed (Subtype.val '' (K : Set U) : Set M) :=
    (K.isCompact.image continuous_subtypeVal).isClosed
  let d : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  let W : Bool → Opens D := fun b ↦
    bif b then Opens.comap d U else Opens.comap d ⟨(Subtype.val '' (K : Set U))ᶜ, hL.isOpen_compl⟩
  have hW : ∀ x : D, ∃ b, x ∈ W b := by
    intro x
    by_cases hx : (x : M) ∈ U
    · exact ⟨true, hx⟩
    · exact ⟨false, fun ⟨y, _, hyx⟩ ↦ hx (hyx ▸ y.property : d x ∈ U)⟩
  apply ContMDiffMap.continuous_of_forall_continuous_restrict W hW
  intro b
  cases b with
  | false =>
    convert continuous_const (y := (0 : C^n⟮I, W false; 𝓘(ℝ, F), F⟯)) using 1
    funext p
    ext x
    have hx : ((x : D) : M) ∉ (extendByZero (s p)).tsupport := by
      rw [tsupport_extendByZero]
      exact fun hm ↦ x.property (image_mono (hK p) hm)
    rw [ContMDiffMap.restrict_apply, Trivialization.frameCoordinates_apply,
      eq_zero_of_notMem_tsupport _ hx,
      ← e.continuousLinearMapAt_apply_of_mem (R := ℝ) (hD (x : D).property), map_zero]
    simp
  | true =>
    let j : C^n⟮I, W true; I, DU⟯ :=
      ⟨fun x ↦ ⟨⟨((x : D) : M), x.property⟩, (x : D).property⟩,
        (TauCeti.ContMDiff.subtypeVal_comp_iff DU _).mp
          ((TauCeti.ContMDiff.subtypeVal_comp_iff U _).mp (by
            -- The composite with both subtype projections is the double inclusion into `M`.
            change ContMDiff I I n (fun x : W true ↦ ((x : D) : M))
            exact contMDiff_subtypeVal.comp contMDiff_subtypeVal))⟩
    have h := ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
      (hs.prodMk (continuous_const (y := j)))
    apply h.congr
    intro p
    ext x
    simp only [Function.comp_apply, ContMDiffMap.restrict_apply,
      ContMDiffMap.comp_apply, Trivialization.frameCoordinates_apply]
    erw [Trivialization.pullback_apply, extendByZero_apply_of_mem (s p)
      (⟨((x : D) : M), x.property⟩ : U)]
    rfl

variable {ι : Type*} (es : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (es i)] (A : ι → Opens M)
  (hA : ∀ i, (A i : Set M) ⊆ (es i).baseSet)

/-- Extension by zero is continuous from each fixed-support stage in a covering frame family. -/
theorem continuous_extendByZero_ofSupportedIn (K : Compacts U) :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let eU := fun i ↦ (es i).pullback c
    let AU := fun i ↦ Opens.comap c (A i)
    let hAU : ∀ i, (AU i : Set U) ⊆ (eU i).baseSet := fun i _ hx ↦ hA i hx
    letI := frameTopology (I := I) (n := n) eU AU hAU
    letI := frameTopology (I := I) (n := n) es A hA
    Continuous (fun s : supportedIn I F n (c *ᵖ V) K ↦
      extendByZero (ofSupportedIn K s)) := by
  let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  let eU := fun i ↦ (es i).pullback c
  let AU := fun i ↦ Opens.comap c (A i)
  let hAU : ∀ i, (AU i : Set U) ⊆ (eU i).baseSet := fun i _ hx ↦ hA i hx
  let := frameTopology (I := I) (n := n) eU AU hAU
  let := frameTopology (I := I) (n := n) es A hA
  apply (continuous_frameTopology_iff_frameCoordinates es A hA).2
  intro i
  apply continuous_extended_frame_of_fixed_support (es i) (hA i) K
    (fun s ↦ ofSupportedIn K s) (fun s ↦ by
      rw [ofSupportedIn_apply]
      exact mem_supportedIn.mp s.property)
  have hc : Continuous (fun s : supportedIn I F n (c *ᵖ V) K ↦
      (ofSupportedIn K s).val) := by
    simpa only [ofSupportedIn_apply] using
      (continuous_subtypeVal : Continuous (fun s : supportedIn I F n (c *ᵖ V) K ↦ s.val))
  exact (continuous_frameCoordinates eU AU hAU i).comp hc

/-- Extension by zero is continuous for the final locally convex topologies of covering frames. -/
theorem continuous_extendByZero_compactlySupported :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let eU := fun i ↦ (es i).pullback c
    let AU := fun i ↦ Opens.comap c (A i)
    let hAU : ∀ i, (AU i : Set U) ⊆ (eU i).baseSet := fun i _ hx ↦ hA i hx
    letI := compactlySupportedTopology (I := I) (n := n) eU AU hAU
    letI := compactlySupportedTopology (I := I) (n := n) es A hA
    Continuous (extendByZeroLinearMap (I := I) (F := F) (n := n) (V := V) (U := U)) := by
  let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  let eU := fun i ↦ (es i).pullback c
  let AU := fun i ↦ Opens.comap c (A i)
  let hAU : ∀ i, (AU i : Set U) ⊆ (eU i).baseSet := fun i _ hx ↦ hA i hx
  let := frameTopology (I := I) (n := n) eU AU hAU
  let := frameTopology (I := I) (n := n) es A hA
  let := compactlySupportedTopology (I := I) (n := n) eU AU hAU
  let := compactlySupportedTopology (I := I) (n := n) es A hA
  let := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := n) es A hA
  let := continuousSMul_compactlySupportedTopology (I := I) (n := n) es A hA
  let := locallyConvexSpace_compactlySupportedTopology (I := I) (n := n) es A hA
  apply (continuous_compactlySupportedTopology_iff eU AU hAU
    (extendByZeroLinearMap (I := I) (F := F) (n := n) (V := V) (U := U))).2
  intro K
  let L : Compacts M := K.map Subtype.val continuous_subtypeVal
  let g : supportedIn I F n (c *ᵖ V) K → supportedIn I F n V L := fun s ↦
    ⟨extendByZero (ofSupportedIn K s), by
      rw [mem_supportedIn, tsupport_extendByZero, ofSupportedIn_apply]
      exact image_mono (mem_supportedIn.mp s.property)⟩
  have hg : Continuous g :=
    (continuous_extendByZero_ofSupportedIn es A hA K).subtype_mk _
  convert (continuous_ofSupportedIn (I := I) (n := n) es A hA L).comp hg using 1
  funext s
  apply Subtype.ext
  simp only [Function.comp_apply, ofSupportedIn_apply]
  -- Read the fixed-support inclusion through its underlying compactly supported section.
  change (extendByZeroLinearMap (ofSupportedIn K s)).val = _
  erw [extendByZeroLinearMap_apply]

end ContMDiffSection

namespace TauCeti.BundleTest

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LocallyCompactSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M] {U D : Opens M}

/-- Continuous linear extension by zero on native smooth bundle tests. -/
def extendByZeroCLM :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    TauCeti.BundleTest I F (c *ᵖ V) →L[ℝ] TauCeti.BundleTest I F V := by
  let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  let L : TauCeti.BundleTest I F (c *ᵖ V) →ₗ[ℝ] TauCeti.BundleTest I F V :=
    (TauCeti.BundleTest.ofCompactlySupported I F V).toLinearMap.comp
      ((extendByZeroLinearMap (I := I) (F := F) (n := ∞) (V := V) (U := U)).comp
        (TauCeti.BundleTest.ofCompactlySupported I F (c *ᵖ V)).symm.toLinearMap)
  refine ⟨L, ?_⟩
  let e : M → Trivialization F (π F V) := fun x ↦ trivializationAt F V x
  let A : M → Opens M := fun x ↦ ⟨(e x).baseSet, (e x).open_baseSet⟩
  let hA : ∀ i, (A i : Set M) ⊆ (e i).baseSet := fun _ ↦ subset_rfl
  let eU := fun i ↦ (e i).pullback c
  let AU := fun i ↦ Opens.comap c (A i)
  let hAU : ∀ i, (AU i : Set U) ⊆ (eU i).baseSet := fun i _ hx ↦ hA i hx
  have hcover : ∀ x : U, ∃ i, x ∈ AU i :=
    fun x ↦ ⟨(x : M), mem_baseSet_trivializationAt F V (x : M)⟩
  erw [TauCeti.BundleTest.instTopologicalSpace_eq_compactlySupportedTopology eU AU hAU hcover]
  exact continuous_extendByZero_compactlySupported (I := I) (n := ∞) e A hA

/-- Native extension commutes with the compactly supported section representation. -/
theorem extendByZeroCLM_ofCompactlySupported :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ s : compactlySupported I F ∞ (c *ᵖ V),
      extendByZeroCLM (I := I) (F := F) (V := V) (ofCompactlySupported I F (c *ᵖ V) s) =
        ofCompactlySupported I F V (extendByZeroLinearMap s) := by
  intros
  rfl

/-- Extension on native tests agrees with extension on compactly supported sections. -/
theorem extendByZeroCLM_apply :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ (s : TauCeti.BundleTest I F (c *ᵖ V)) (x : M),
      extendByZeroCLM (I := I) (F := F) (V := V) s x =
        extendByZero ((TauCeti.BundleTest.ofCompactlySupported I F (c *ᵖ V)).symm s) x := by
  intro c s x
  -- The native/raw equivalence changes only the test wrapper, not its section value.
  change (extendByZeroLinearMap ((ofCompactlySupported I F (c *ᵖ V)).symm s)).val x = _
  erw [extendByZeroLinearMap_apply]

/-- Extension vanishes outside the open subset. -/
@[simp]
theorem extendByZeroCLM_apply_of_notMem :
    dsimp% only [ContinuousMap.coe_mk] (
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ (s : TauCeti.BundleTest I F (c *ᵖ V)) {x : M}, x ∉ U →
      extendByZeroCLM (I := I) (F := F) (V := V) s x = 0) := by
  intro s x hx
  rw [extendByZeroCLM_apply]
  exact extendByZero_apply_of_notMem _ hx

/-- Extension on the open subset is the original test, viewed in the ambient fibre. -/
@[simp]
theorem extendByZeroCLM_apply_of_mem :
    dsimp% only [ContinuousMap.coe_mk] (
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ (s : TauCeti.BundleTest I F (c *ᵖ V)) (x : U),
      extendByZeroCLM (I := I) (F := F) (V := V) s (x : M) =
        (Pullback.lift c (TotalSpace.mk' F x (s x))).snd) := by
  intro s x
  rw [extendByZeroCLM_apply]
  erw [extendByZero_apply_of_mem _ x]
  rfl

/-- The closed support of the extension is the image of the original closed support. -/
theorem tsupport_extendByZeroCLM :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ (s : TauCeti.BundleTest I F (c *ᵖ V)),
      closure {x : M | extendByZeroCLM (I := I) (F := F) (V := V) s x ≠ 0} =
        Subtype.val '' closure {x : U | s x ≠ 0} := by
  intro c s
  simp only [extendByZeroCLM_apply]
  simpa only [tsupport_def] using
    (tsupport_extendByZero ((ofCompactlySupported I F (c *ᵖ V)).symm s))

/-- Extension commutes with multiplication by an ambient smooth scalar function. -/
theorem extendByZeroCLM_smulLeftCLM :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ (f : C^∞⟮I, M; ℝ⟯) (s : TauCeti.BundleTest I F (c *ᵖ V)),
      extendByZeroCLM (I := I) (F := F) (V := V)
        (TauCeti.BundleTest.smulLeftCLM (f.restrict U) s) =
      TauCeti.BundleTest.smulLeftCLM f (extendByZeroCLM (I := I) (F := F) (V := V) s) := by
  intro c f s
  apply TauCeti.BundleTest.ext
  intro x
  rw [TauCeti.BundleTest.smulLeftCLM_apply]
  by_cases hx : x ∈ U
  · erw [extendByZeroCLM_apply_of_mem _ (⟨x, hx⟩ : U),
      extendByZeroCLM_apply_of_mem s (⟨x, hx⟩ : U),
      TauCeti.BundleTest.smulLeftCLM_apply (I := I) (F := F) (V := c *ᵖ V)]
    erw [ContMDiffMap.restrict_apply]
    rfl
  · rw [extendByZeroCLM_apply_of_notMem _ hx, extendByZeroCLM_apply_of_notMem _ hx,
      smul_zero]

section Dual
variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousConstSMul ℝ W]

/-- Restriction on compact-convergence duals, transposed from test extension. -/
def restrictDualCLM :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    (TauCeti.BundleTest I F V →L_c[ℝ] W) →L[ℝ]
      TauCeti.BundleTest I F (c *ᵖ V) →L_c[ℝ] W := by
  let _c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  exact (extendByZeroCLM (I := I) (F := F) (V := V) (U := U)).precompCompactConvergenceCLM W

/-- Dual restriction pairs with a test by pairing against its extension. -/
@[simp]
theorem restrictDualCLM_apply :
    dsimp% only [ContinuousMap.coe_mk] (
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ (T : TauCeti.BundleTest I F V →L_c[ℝ] W) (s : TauCeti.BundleTest I F (c *ᵖ V)),
      restrictDualCLM T s = T (extendByZeroCLM (I := I) (F := F) (V := V) s)) := by
  intros
  rfl

/-- Restriction of a point mass outside the open subset is zero. -/
theorem restrictDualCLM_delta_of_notMem :
    let _c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ (x : M) (ℓ : V x →L[ℝ] W), x ∉ U →
      restrictDualCLM (I := I) (F := F) (V := V) (U := U) (TauCeti.BundleTest.delta x ℓ) = 0 := by
  intro _c x ℓ hx
  apply ContinuousLinearMap.ext
  intro s
  erw [restrictDualCLM_apply, TauCeti.BundleTest.delta_apply,
    extendByZeroCLM_apply_of_notMem s hx, map_zero]
  rfl

/-- Restriction of a point mass inside the open subset is the corresponding point mass. -/
theorem restrictDualCLM_delta_of_mem :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ (x : U) (ℓ : V (x : M) →L[ℝ] W),
      restrictDualCLM (I := I) (F := F) (V := V) (U := U) (TauCeti.BundleTest.delta (x : M) ℓ) =
        TauCeti.BundleTest.delta (I := I) (F := F) x (show (c *ᵖ V) x →L[ℝ] W from ℓ) := by
  intro c x ℓ
  apply ContinuousLinearMap.ext
  intro s
  erw [restrictDualCLM_apply, TauCeti.BundleTest.delta_apply,
    extendByZeroCLM_apply_of_mem s x, TauCeti.BundleTest.delta_apply]
  rfl

/-- Dual restriction commutes with multiplication by smooth functions. -/
theorem restrictDualCLM_smulLeftDualCLM :
    let _c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ (f : C^∞⟮I, M; ℝ⟯) (T : TauCeti.BundleTest I F V →L_c[ℝ] W),
      restrictDualCLM (I := I) (F := F) (V := V) (U := U)
        (TauCeti.BundleTest.smulLeftDualCLM f T) =
      TauCeti.BundleTest.smulLeftDualCLM (f.restrict U)
        (restrictDualCLM (I := I) (F := F) (V := V) (U := U) T) := by
  intro _c f T
  apply ContinuousLinearMap.ext
  intro s
  calc
    _ = TauCeti.BundleTest.smulLeftDualCLM f T
        (extendByZeroCLM (I := I) (F := F) (V := V) s) := restrictDualCLM_apply _ _
    _ = T (TauCeti.BundleTest.smulLeftCLM f
        (extendByZeroCLM (I := I) (F := F) (V := V) s)) := smulLeftDualCLM_apply _ _ _
    _ = T (extendByZeroCLM (I := I) (F := F) (V := V)
        (TauCeti.BundleTest.smulLeftCLM (f.restrict U) s)) :=
      congrArg T (extendByZeroCLM_smulLeftCLM (I := I) (F := F) (V := V) f s).symm
    _ = restrictDualCLM (I := I) (F := F) (V := V) T (smulLeftCLM (f.restrict U) s) :=
      (restrictDualCLM_apply _ _).symm
    _ = _ := (smulLeftDualCLM_apply _ _ _).symm

end Dual

section Localization
variable {N G : Type*} [TopologicalSpace N] [ChartedSpace H N] [T2Space N]
  [IsManifold I ∞ N] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {Z : N → Type*} [∀ x, AddCommGroup (Z x)] [∀ x, Module ℝ (Z x)]
  [∀ x, TopologicalSpace (Z x)] [TopologicalSpace (TotalSpace G Z)]
  [FiberBundle G Z] [VectorBundle ℝ G Z] [ContMDiffVectorBundle ∞ G Z I]
  (T : TauCeti.BundleTest I G Z →L[ℝ] TauCeti.BundleTest I F V) (q : C(N, U))
  (hT : ∀ s, closure {x : M | T s x ≠ 0} ⊆
    Subtype.val '' q '' closure {x : N | s x ≠ 0})

private def relocalizeLinearMap : TauCeti.BundleTest I G Z →ₗ[ℝ]
    compactlySupported I F ∞ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) := by
  let L := (restrictLinearMap I F ∞ V U).comp
    ((compactlySupported I F ∞ V).subtype.comp
      ((TauCeti.BundleTest.ofCompactlySupported I F V).symm.toLinearMap.comp T.toLinearMap))
  refine L.codRestrict _ ?_
  intro s
  -- codRestrict changes only the support certificate; its section carrier is ordinary restriction.
  change (restrictLinearMap I F ∞ V U)
    ((TauCeti.BundleTest.ofCompactlySupported I F V).symm (T s)).val ∈ _
  erw [restrictLinearMap_apply]
  apply restrict_mem_compactlySupported ((TauCeti.BundleTest.ofCompactlySupported I F V).symm (T s))
  rw [tsupport_def]
  rintro x hx
  rcases hT s hx with ⟨u, ⟨y, _, rfl⟩, rfl⟩
  exact (q y).property

omit [LocallyCompactSpace E] [T2Space M] [T2Space N] in
private theorem relocalizeLinearMap_val (s : TauCeti.BundleTest I G Z) :
    (relocalizeLinearMap T q hT s).val =
      ((TauCeti.BundleTest.ofCompactlySupported I F V).symm (T s)).val.restrict U := by
  simp only [relocalizeLinearMap, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, LinearEquiv.coe_toLinearMap, ContinuousLinearMap.coe_coe]
  erw [restrictLinearMap_apply]

private def relocalizeStageLinearMap (K : Compacts N) : supportedIn I G ∞ Z K →ₗ[ℝ]
    supportedIn I F ∞ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)
      (K.map q q.continuous) := by
  let L := (relocalizeLinearMap T q hT).comp
    ((TauCeti.BundleTest.ofCompactlySupported I G Z).toLinearMap.comp (ofSupportedIn K))
  let A := (compactlySupported I F ∞
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)).subtype.comp L
  refine A.codRestrict _ ?_
  intro s
  rw [mem_supportedIn]
  -- Evaluate the supported-stage carrier through its named value law before forgetting support.
  change (relocalizeLinearMap T q hT
    (TauCeti.BundleTest.ofCompactlySupported I G Z (ofSupportedIn K s))).val.tsupport ⊆ _
  rw [relocalizeLinearMap_val, tsupport_restrict, tsupport_def]
  intro u hu
  rcases hT (TauCeti.BundleTest.ofCompactlySupported I G Z (ofSupportedIn K s)) hu with
    ⟨u', ⟨y, hy, rfl⟩, heq⟩
  refine ⟨y, (mem_supportedIn.mp s.property) ?_, Subtype.ext heq⟩
  simpa only [LinearEquiv.symm_apply_apply, ofSupportedIn_apply, tsupport_def] using hy

omit [LocallyCompactSpace E] [T2Space M] [T2Space N] in
private theorem relocalizeStageLinearMap_val (K : Compacts N)
    (s : supportedIn I G ∞ Z K) :
    (relocalizeStageLinearMap T q hT K s).val =
      (relocalizeLinearMap T q hT
        (TauCeti.BundleTest.ofCompactlySupported I G Z (ofSupportedIn K s))).val := by
  simp only [relocalizeStageLinearMap, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, LinearEquiv.coe_toLinearMap]

omit [T2Space M] [T2Space N] in
private theorem continuous_relocalizeStageLinearMap (K : Compacts N) :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let eU := fun x : M ↦ (trivializationAt F V x).pullback c
    let AU := fun x : M ↦ Opens.comap c ⟨(trivializationAt F V x).baseSet,
      (trivializationAt F V x).open_baseSet⟩
    let hAU : ∀ x, (AU x : Set U) ⊆ (eU x).baseSet := fun _ ↦ subset_rfl
    let eN := fun x : N ↦ trivializationAt G Z x
    let AN := fun x : N ↦ (⟨(eN x).baseSet, (eN x).open_baseSet⟩ : Opens N)
    let hAN : ∀ x, (AN x : Set N) ⊆ (eN x).baseSet := fun _ ↦ subset_rfl
    letI := frameTopology (I := I) (n := ∞) eN AN hAN
    letI := frameTopology (I := I) (n := ∞) eU AU hAU
    Continuous (relocalizeStageLinearMap T q hT K) := by
  intro c eU AU hAU eN AN hAN
  let := frameTopology (I := I) (n := ∞) eN AN hAN
  let := frameTopology (I := I) (n := ∞) eU AU hAU
  let eM := fun x : M ↦ trivializationAt F V x
  let AM := fun x : M ↦ (⟨(eM x).baseSet, (eM x).open_baseSet⟩ : Opens M)
  let hAM : ∀ x, (AM x : Set M) ⊆ (eM x).baseSet := fun _ ↦ subset_rfl
  let := frameTopology (I := I) (n := ∞) eM AM hAM
  have hf : Continuous (fun t : TauCeti.BundleTest I F V ↦
      ((TauCeti.BundleTest.ofCompactlySupported I F V).symm t).val) :=
    continuous_val_compactlySupportedTopology eM AM hAM
  have hh := (continuous_restrict_frameTopology eM AM hAM U).comp
    (hf.comp (T.continuous.comp
      (TauCeti.BundleTest.continuous_ofSupportedIn (I := I) (F := G) (V := Z) K)))
  have hv : Continuous (fun s : supportedIn I G ∞ Z K ↦
      (relocalizeStageLinearMap T q hT K s).val) := by
    apply hh.congr
    intro s
    exact ((relocalizeStageLinearMap_val T q hT K s).trans
      (relocalizeLinearMap_val T q hT _)).symm
  exact hv.subtype_mk _

omit [T2Space M] [T2Space N] in
/-- Localize a continuous native test operator whose supports lie in a controlled open image. -/
def localizeCLM :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    TauCeti.BundleTest I G Z →L[ℝ] TauCeti.BundleTest I F (c *ᵖ V) := by
  intro c
  let L := (TauCeti.BundleTest.ofCompactlySupported I F (c *ᵖ V)).toLinearMap.comp
    (relocalizeLinearMap T q hT)
  refine ⟨L, ?_⟩
  let eN := fun x : N ↦ trivializationAt G Z x
  let AN := fun x : N ↦ (⟨(eN x).baseSet, (eN x).open_baseSet⟩ : Opens N)
  let hAN : ∀ x, (AN x : Set N) ⊆ (eN x).baseSet := fun _ ↦ subset_rfl
  let eM := fun x : M ↦ trivializationAt F V x
  let AM := fun x : M ↦ (⟨(eM x).baseSet, (eM x).open_baseSet⟩ : Opens M)
  let eU := fun x : M ↦ (eM x).pullback c
  let AU := fun x : M ↦ Opens.comap c (AM x)
  let hAU : ∀ x, (AU x : Set U) ⊆ (eU x).baseSet := fun _ ↦ subset_rfl
  let := frameTopology (I := I) (n := ∞) eN AN hAN
  let := frameTopology (I := I) (n := ∞) eU AU hAU
  have hcover : ∀ x : U, ∃ i, x ∈ AU i := fun x ↦ ⟨x.val, mem_baseSet_trivializationAt F V x.val⟩
  apply (TauCeti.BundleTest.continuous_iff_continuous_comp (I := I) (F := G) (V := Z) L).2
  intro K
  have hi : Continuous (TauCeti.BundleTest.ofCompactlySupported I F (c *ᵖ V) ∘
      ofSupportedIn (I := I) (F := F) (n := ∞) (V := c *ᵖ V) (K.map q q.continuous)) := by
    erw [TauCeti.BundleTest.instTopologicalSpace_eq_compactlySupportedTopology eU AU hAU hcover]
    exact ContMDiffSection.continuous_ofSupportedIn (I := I) (n := ∞) eU AU hAU _
  convert hi.comp (continuous_relocalizeStageLinearMap T q hT K) using 1
  funext s
  apply TauCeti.BundleTest.ext
  intro u
  -- Evaluate the supported-stage carrier through its named value law before forgetting support.
  change (relocalizeLinearMap T q hT
    (TauCeti.BundleTest.ofCompactlySupported I G Z (ofSupportedIn K s))).val u = _
  erw [ofSupportedIn_apply, relocalizeStageLinearMap_val]

omit [T2Space M] [T2Space N] in
/-- Localization agrees with the original operator at every point of the open subset. -/
@[simp]
theorem localizeCLM_apply :
    dsimp% only [ContinuousMap.coe_mk] (
    ∀ (s : TauCeti.BundleTest I G Z) (u : U), localizeCLM T q hT s u = T s (u : M)) := by
  intro s u
  -- The final topology adds continuity to this same algebraic localization carrier.
  change (relocalizeLinearMap T q hT s).val u = _
  erw [relocalizeLinearMap_val, ContMDiffSection.restrict_apply]

omit [T2Space N] in
/-- Re-extending a controlled localization recovers the original native test operator. -/
theorem extendByZeroCLM_localizeCLM :
    ∀ s : TauCeti.BundleTest I G Z,
      extendByZeroCLM (I := I) (F := F) (V := V) (U := U) (localizeCLM T q hT s) = T s := by
  intro s
  apply TauCeti.BundleTest.ext
  intro x
  by_cases hx : x ∈ U
  · erw [extendByZeroCLM_apply_of_mem _ ⟨x, hx⟩, localizeCLM_apply]
    -- Both evaluations lie in the original ambient fibre; only the subtype index differs.
    rfl
  · rw [extendByZeroCLM_apply_of_notMem _ hx]
    symm
    by_contra hne
    rcases hT s (subset_closure hne) with ⟨u, _, rfl⟩
    exact hx u.property

end Localization

/-- Continuous linear extension of native tests to a larger open subset. -/
def inclusionCLM (h : U ≤ D) :
    let cU : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    TauCeti.BundleTest I F (cU *ᵖ V) →L[ℝ] TauCeti.BundleTest I F (cD *ᵖ V) := by
  let q : C(U, D) := ⟨Opens.inclusion h, continuous_subtypeVal.subtype_mk _⟩
  refine localizeCLM (I := I) (F := F) (V := V) (U := D)
    (extendByZeroCLM (I := I) (F := F) (V := V) (U := U)) q ?_
  intro s
  rw [tsupport_extendByZeroCLM]
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨q u, ⟨u, hu, rfl⟩, rfl⟩

/-- Intermediate extension evaluates by the already-defined ambient extension operator. -/
theorem inclusionCLM_apply (h : U ≤ D) :
    dsimp% only [ContinuousMap.coe_mk] (
    let cU : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let _cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ (s : TauCeti.BundleTest I F (cU *ᵖ V)) (x : D),
      inclusionCLM (I := I) (F := F) (V := V) h s x =
        extendByZeroCLM (I := I) (F := F) (V := V) s (x : M)) := by
  intro s x
  simp only [inclusionCLM, localizeCLM_apply]
  rfl

/-- Native intermediate extension agrees with raw compact-support extension. -/
theorem inclusionCLM_ofCompactlySupported (h : U ≤ D)
    (s : compactlySupported I F ∞ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)) :
    inclusionCLM (I := I) (F := F) (V := V) h
      (TauCeti.BundleTest.ofCompactlySupported I F _ s) =
      TauCeti.BundleTest.ofCompactlySupported I F _ (extendByZeroToOpenLinearMap h s) := by
  apply TauCeti.BundleTest.ext
  intro x
  erw [inclusionCLM_apply, extendByZeroCLM_apply]
  erw [extendByZeroToOpenLinearMap_val, ContMDiffSection.restrict_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rfl

/-- The closed support of native intermediate extension is the inclusion image. -/
theorem tsupport_inclusionCLM (h : U ≤ D) :
    let cU : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ s : TauCeti.BundleTest I F (cU *ᵖ V),
      closure {x : D | inclusionCLM (I := I) (F := F) (V := V) h s x ≠ 0} =
        (Opens.inclusion h) '' closure {x : U | s x ≠ 0} := by
  intro cU s
  obtain ⟨t, rfl⟩ := (ofCompactlySupported I F (cU *ᵖ V)).surjective s
  erw [inclusionCLM_ofCompactlySupported]
  -- The public raw support law computes the same pointwise section through this wrapper.
  change closure {x : D | (extendByZeroToOpenLinearMap h t).val x ≠ 0} = _
  rw [← ContMDiffSection.tsupport_def, tsupport_extendByZeroToOpenLinearMap,
    ContMDiffSection.tsupport_def]
  rfl

/-- Native test extension along the identity inclusion is the identity. -/
theorem inclusionCLM_refl :
    let _cU : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    inclusionCLM (I := I) (F := F) (V := V) (U := U) le_rfl =
      ContinuousLinearMap.id ℝ _ := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro s
  obtain ⟨t, rfl⟩ := (TauCeti.BundleTest.ofCompactlySupported I F
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)).surjective s
  erw [inclusionCLM_ofCompactlySupported, extendByZeroToOpenLinearMap_refl]
  rfl

/-- Native test extension through nested opens composes. -/
theorem inclusionCLM_comp {D' : Opens M} (h : U ≤ D) (h' : D ≤ D') :
    let _cU : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let _cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let _cDprime : C(D', M) := ⟨Subtype.val, continuous_subtypeVal⟩
    (inclusionCLM (I := I) (F := F) (V := V) h').comp
      (inclusionCLM (I := I) (F := F) (V := V) h) =
      inclusionCLM (I := I) (F := F) (V := V) (h.trans h') := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro s
  obtain ⟨t, rfl⟩ := (TauCeti.BundleTest.ofCompactlySupported I F
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)).surjective s
  -- The public representation law transports both native operators to the same raw carrier.
  erw [ContinuousLinearMap.comp_apply, inclusionCLM_ofCompactlySupported h t,
    inclusionCLM_ofCompactlySupported h' (extendByZeroToOpenLinearMap h t),
    inclusionCLM_ofCompactlySupported (h.trans h') t]
  exact congrArg (TauCeti.BundleTest.ofCompactlySupported I F _)
    (extendByZeroToOpenLinearMap_comp h h' t)

/-- Ambient extension is unchanged by inserting an intermediate open subset. -/
theorem extendByZeroCLM_inclusionCLM (h : U ≤ D) :
    let _cU : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let _cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    (extendByZeroCLM (I := I) (F := F) (V := V) (U := D)).comp
      (inclusionCLM (I := I) (F := F) (V := V) h) =
      extendByZeroCLM (I := I) (F := F) (V := V) (U := U) := by
  dsimp only
  apply ContinuousLinearMap.ext
  intro s
  obtain ⟨t, rfl⟩ := (TauCeti.BundleTest.ofCompactlySupported I F
    ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)).surjective s
  erw [ContinuousLinearMap.comp_apply, inclusionCLM_ofCompactlySupported]
  -- The ambient native wrapper is the common codomain of both raw section maps.
  change TauCeti.BundleTest.ofCompactlySupported I F V
    (extendByZeroLinearMap (extendByZeroToOpenLinearMap h t)) =
      TauCeti.BundleTest.ofCompactlySupported I F V (extendByZeroLinearMap t)
  congr 1
  apply Subtype.ext
  erw [extendByZeroLinearMap_apply, extendByZeroLinearMap_apply]
  exact extendByZero_extendByZeroToOpenLinearMap h t

section NestedDual
variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousConstSMul ℝ W]

/-- The compact-convergence transpose of intermediate native test extension. -/
def restrictDualToOpenCLM (h : U ≤ D) :
    let cU : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    (TauCeti.BundleTest I F (cD *ᵖ V) →L_c[ℝ] W) →L[ℝ]
      (TauCeti.BundleTest I F (cU *ᵖ V) →L_c[ℝ] W) := by
  dsimp only
  exact (inclusionCLM (I := I) (F := F) (V := V) h).precompCompactConvergenceCLM W

/-- Intermediate dual restriction evaluates against intermediate test extension. -/
@[simp]
theorem restrictDualToOpenCLM_apply (h : U ≤ D) :
    dsimp% only [ContinuousMap.coe_mk] (
    let cU : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ (T : TauCeti.BundleTest I F (cD *ᵖ V) →L_c[ℝ] W)
      (s : TauCeti.BundleTest I F (cU *ᵖ V)),
      restrictDualToOpenCLM (I := I) (F := F) (V := V) h T s =
        T (inclusionCLM (I := I) (F := F) (V := V) h s)) := by
  intro T s
  exact ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply
    (inclusionCLM (I := I) (F := F) (V := V) h) T s

/-- Dual restriction along the identity inclusion is the identity. -/
theorem restrictDualToOpenCLM_refl :
    let cU : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ μ : TauCeti.BundleTest I F (cU *ᵖ V) →L_c[ℝ] W,
      restrictDualToOpenCLM (I := I) (F := F) (V := V) le_rfl μ = μ := by
  dsimp only
  intro μ
  apply ContinuousLinearMap.ext
  intro s
  erw [restrictDualToOpenCLM_apply]
  exact congrArg μ (congrArg (fun L ↦ L s)
    (inclusionCLM_refl (I := I) (F := F) (V := V) (U := U)))

/-- Dual restriction through nested opens composes. -/
theorem restrictDualToOpenCLM_comp {D' : Opens M} (h : U ≤ D) (h' : D ≤ D') :
    let _cU : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let _cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let cDprime : C(D', M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ μ : TauCeti.BundleTest I F (cDprime *ᵖ V) →L_c[ℝ] W,
      restrictDualToOpenCLM (I := I) (F := F) (V := V) h
        (restrictDualToOpenCLM (I := I) (F := F) (V := V) h' μ) =
      restrictDualToOpenCLM (I := I) (F := F) (V := V) (h.trans h') μ := by
  dsimp only
  intro μ
  apply ContinuousLinearMap.ext
  intro s
  erw [restrictDualToOpenCLM_apply, restrictDualToOpenCLM_apply,
    restrictDualToOpenCLM_apply]
  exact congrArg μ (congrArg (fun L ↦ L s) (inclusionCLM_comp (I := I) (F := F) (V := V) h h'))

end NestedDual

omit [T2Space M] in
/-- Continuous linear restriction of native tests to the universal open subset. -/
def restrictUnivCLM :
    let U : Opens M := ⊤
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    TauCeti.BundleTest I F V →L[ℝ] TauCeti.BundleTest I F (c *ᵖ V) := by
  intro U _c
  let q : C(M, U) := ⟨fun x ↦ ⟨x, Set.mem_univ x⟩, continuous_id.subtype_mk _⟩
  refine localizeCLM (I := I) (F := F) (V := V) (U := U)
    (ContinuousLinearMap.id ℝ _) q ?_
  intro s x hx
  exact ⟨q x, ⟨x, hx, rfl⟩, rfl⟩

omit [T2Space M] in
/-- Universal-open restriction preserves every pointwise fibre value. -/
@[simp]
theorem restrictUnivCLM_apply (s : TauCeti.BundleTest I F V) (x : (⊤ : Opens M)) :
    dsimp% only [ContinuousMap.coe_mk] (
    restrictUnivCLM (I := I) (F := F) (V := V) s x = s (x : M)) := by
  -- The identity operator is localized; its public evaluation law retains the ambient value.
  exact localizeCLM_apply (I := I) (F := F) (V := V) (U := (⊤ : Opens M))
    (ContinuousLinearMap.id ℝ (TauCeti.BundleTest I F V)) _ _ s x

omit [T2Space M] in
/-- Universal-open restriction commutes with the compact-support representation. -/
theorem restrictUnivCLM_ofCompactlySupported :
    let U : Opens M := ⊤
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ s : compactlySupported I F ∞ V,
      restrictUnivCLM (I := I) (F := F) (V := V) (ofCompactlySupported I F V s) =
        ofCompactlySupported I F (c *ᵖ V) (restrictUnivLinearMap s) := by
  intro U c s
  apply TauCeti.BundleTest.ext
  intro x
  erw [restrictUnivCLM_apply]
  -- Both native wrappers have the values specified by the raw universal restriction law.
  change s.val (x : M) = (restrictUnivLinearMap s).val x
  erw [restrictUnivLinearMap_val, ContMDiffSection.restrict_apply]

/-- Extension and restriction identify native tests on the universal open with ambient tests. -/
def univCLE :
    let U : Opens M := ⊤
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    TauCeti.BundleTest I F (c *ᵖ V) ≃L[ℝ] TauCeti.BundleTest I F V := by
  intro U c
  refine
    { toLinearEquiv :=
        { toLinearMap := (extendByZeroCLM (I := I) (F := F) (V := V) (U := U)).toLinearMap
          invFun := restrictUnivCLM (I := I) (F := F) (V := V)
          left_inv := ?_
          right_inv := ?_ }
      continuous_toFun := (extendByZeroCLM (I := I) (F := F) (V := V) (U := U)).continuous
      continuous_invFun := (restrictUnivCLM (I := I) (F := F) (V := V)).continuous }
  · intro s
    apply TauCeti.BundleTest.ext
    intro x
    erw [restrictUnivCLM_apply, extendByZeroCLM_apply_of_mem _ x]
    -- The pullback lift retains the same fibre element over the underlying point.
    rfl
  · intro s
    apply TauCeti.BundleTest.ext
    intro x
    erw [extendByZeroCLM_apply_of_mem _ ⟨x, Set.mem_univ x⟩, restrictUnivCLM_apply]
    rfl

/-- The universal-open test equivalence evaluates by the unique subtype lift. -/
@[simp]
theorem univCLE_apply
    (s : TauCeti.BundleTest I F
      ((⟨Subtype.val, continuous_subtypeVal⟩ : C((⊤ : Opens M), M)) *ᵖ V)) (x : M) :
    dsimp% only [ContinuousMap.coe_mk] (
    univCLE (I := I) (F := F) (V := V) s x = s ⟨x, Set.mem_univ x⟩) := by
  exact extendByZeroCLM_apply_of_mem s ⟨x, Set.mem_univ x⟩

/-- The inverse universal-open test equivalence preserves pointwise values. -/
@[simp]
theorem univCLE_symm_apply (s : TauCeti.BundleTest I F V) (x : (⊤ : Opens M)) :
    dsimp% only [ContinuousMap.coe_mk] (
    (univCLE (I := I) (F := F) (V := V)).symm s x = s (x : M)) := by
  exact restrictUnivCLM_apply s x

/-- The universal-open equivalence extends native tests by zero. -/
theorem univCLE_toContinuousLinearMap :
    (univCLE (I := I) (F := F) (V := V)).toContinuousLinearMap =
      extendByZeroCLM (I := I) (F := F) (V := V) (U := ⊤) := by
  rfl

/-- Intermediate extension evaluates to the original test at points of the smaller open. -/
@[simp]
theorem inclusionCLM_apply_of_mem (h : U ≤ D) :
    dsimp% only [ContinuousMap.coe_mk] (
    let cU : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    let _cD : C(D, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ (s : TauCeti.BundleTest I F (cU *ᵖ V)) (u : U),
      inclusionCLM (I := I) (F := F) (V := V) h s (Opens.inclusion h u) =
        (Pullback.lift cU (TotalSpace.mk' F u (s u))).snd) := by
  intro s u
  -- Evaluate localization by the ambient operator, then use its public inclusion-point law.
  erw [inclusionCLM_apply, extendByZeroCLM_apply_of_mem s u]


end TauCeti.BundleTest

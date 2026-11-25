/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.CompactSupport.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Density
public import TauCeti.Analysis.Distribution.TestFunction.DualEquiv
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Map
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Bundle test sections and distributions on manifolds

Let `V → M` be a smooth real vector bundle over a smooth manifold. Its **bundle tests**
`TauCeti.BundleTest I F V` are the compactly supported smooth sections of `V`, with the final
locally convex topology of their fixed-compact support stages
(`ContMDiffSection.compactlySupportedTopology`), computed in the preferred trivializations
`trivializationAt F V x`. Every covering family of smooth frames gives the same topology
(`TauCeti.BundleTest.instTopologicalSpace_eq_compactlySupportedTopology`), so this choice is
only a normalization. The topology is Hausdorff.

A smooth bundle map whose expression in the preferred frames at each point is a constant model map
transports bundle tests continuously
(`TauCeti.BundleTest.continuous_map_of_inCoordinates_eq_const`): in frame coordinates it acts by a
fixed continuous linear map, so it is continuous on each fixed-compact support stage. Canonical
identifications of bundles, such as double-dual evaluation, have this form.

A continuous linear functional `T : BundleTest I F V →L_c[ℝ] ℝ` is a distribution paired with
`V`-valued tests; the space of these functionals carries the topology of uniform convergence on
compact sets of tests, as Mathlib's `Distribution` does. In particular the distributional sections
of a bundle `V` are the functionals on the tests with values in `V* ⊗ |Λ|`, the bundle of
`V`-dual densities, realized as the bundle of continuous linear maps from `V` to the density line
`TauCeti.DensityBundle I M`: this is `TauCeti.BundleDistribution I M F V`. The density factor is
what lets a section `u` of `V` act on such a test `s` without a choice of measure on `M`: the
pairing of `u` with `s` is the density `x ↦ s x (u x)`, to be integrated over `M`.

In a coordinate chart `c` whose source lies over the base set of a trivialization `t` of `V`, a
functional `T` with values in a normed space `W` is read as a native distribution on the chart
target, with values in `F →L[ℝ] W` (`Bundle.Trivialization.chartDistributionCLM`); for real
functionals this is the dual of the model fibre. A real test function `φ` on the chart target
and a vector `v : F` are paired as `T (φ • v)`, where `φ • v` is extended to a bundle test through
the chart and the frame (`Bundle.Trivialization.chartTestCLM`). This is the local representative
through which regularity of distributions on manifolds, for instance local Sobolev regularity, is
defined chart by chart from the Euclidean theory. Since bundle tests are finite sums of such
extended tests (`ContMDiffSection.span_iUnion_range_chartTestSection_eq_top`), a functional is
determined by its local representatives (`TauCeti.BundleTest.ext_chartDistributionCLM`).

The point mass `δ_x ℓ : s ↦ ℓ (s x)` at `x : M`, for a covector `ℓ` on the fibre `V x` or more
generally a continuous linear map `ℓ : V x →L[ℝ] W` (`TauCeti.BundleTest.delta`), vanishes only
when `ℓ` does. Its local representative is the Euclidean point mass at `c x`, with value `ℓ` read
in the frame (`Bundle.Trivialization.chartDistributionCLM_delta_of_mem`), and it is invisible in
charts whose source does not contain `x`
(`Bundle.Trivialization.chartDistributionCLM_delta_of_notMem`).

## Main definitions

* `TauCeti.BundleTest I F V`: the compactly supported smooth sections of `V`, with their test
  topology.
* `TauCeti.BundleTest.continuous_map_of_inCoordinates_eq_const`: transport of bundle tests along a
  bundle map that is constant in frames is continuous.
* `Bundle.Trivialization.chartTestCLM`: extension of native test functions on a chart target to
  bundle tests, as a continuous linear map.
* `Bundle.Trivialization.chartDistributionCLM`: the local representative of a functional on bundle
  tests, a distribution on the chart target with values in `F →L[ℝ] W`.
* `TauCeti.BundleTest.ext_chartDistributionCLM`: functionals on bundle tests are determined by
  their local representatives.
* `TauCeti.BundleTest.delta`: the point mass at a point with a covector on the fibre.
* `TauCeti.DualDensityTest I M F V`: the bundle tests with values in `V →L[ℝ] |Λ|`.
* `TauCeti.BundleDistribution I M F V`: the distributional sections of `V`, the continuous linear
  functionals on the tests with values in `V →L[ℝ] |Λ|`.

## References

* L. Schwartz, *Théorie des distributions*, Hermann, 1966, Chapter III (distributions as
  continuous linear functionals on test functions, and their localization).
* J. J. Duistermaat, J. A. C. Kolk, *Distributions: Theory and Applications*, Birkhäuser, 2010,
  §§16, 19 (distributions on manifolds and densities).
-/

-- The carrier, its instances, `ofCompactlySupported` and the test topology are exposed: the
-- characterizing lemmas below are proved by unfolding them to compactly supported sections, and
-- without exposure their bodies could not be unfolded in those proofs.
@[expose] public noncomputable section

open Bundle Set TopologicalSpace ContMDiffSection
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-! ### Bundle tests -/

variable (I F V) in
/-- The **bundle tests** of a smooth vector bundle `V`: its compactly supported smooth sections.
This type synonym of `ContMDiffSection.compactlySupported I F ∞ V` carries the test topology, the
final locally convex topology of the fixed-compact support stages. -/
def BundleTest : Type _ :=
  ContMDiffSection.compactlySupported I F ∞ V

namespace BundleTest

instance : AddCommGroup (BundleTest I F V) :=
  inferInstanceAs (AddCommGroup (ContMDiffSection.compactlySupported I F ∞ V))

instance : Module ℝ (BundleTest I F V) :=
  inferInstanceAs (Module ℝ (ContMDiffSection.compactlySupported I F ∞ V))

variable (I F V) in
/-- A compactly supported smooth section as a bundle test. -/
def ofCompactlySupported :
    ContMDiffSection.compactlySupported I F ∞ V ≃ₗ[ℝ] BundleTest I F V :=
  LinearEquiv.refl ℝ _

instance : CoeFun (BundleTest I F V) fun _ ↦ (x : M) → V x :=
  ⟨fun s ↦ ((ofCompactlySupported I F V).symm s).val⟩

variable [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]

/-- The test topology, computed in the preferred trivializations `trivializationAt F V x` over
their base sets. Every covering family of smooth frames gives the same topology
(`TauCeti.BundleTest.instTopologicalSpace_eq_compactlySupportedTopology`). -/
instance instTopologicalSpace : TopologicalSpace (BundleTest I F V) :=
  compactlySupportedTopology (I := I) (n := ∞) (fun x : M ↦ trivializationAt F V x)
    (fun x ↦ ⟨_, (trivializationAt F V x).open_baseSet⟩) fun _ ↦ subset_rfl

end BundleTest

end TauCeti

end

public noncomputable section

open Bundle Set TopologicalSpace ContMDiffSection ContinuousLinearMap
open scoped ContDiff Manifold Distributions CompactConvergenceCLM

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

namespace BundleTest

@[simp]
theorem coe_ofCompactlySupported (s : ContMDiffSection.compactlySupported I F ∞ V) :
    ⇑(ofCompactlySupported I F V s) = s.val :=
  rfl

/-- A bundle test is a smooth section. -/
theorem contMDiff (s : BundleTest I F V) :
    ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ fun x ↦ TotalSpace.mk' F x (s x) :=
  ((ofCompactlySupported I F V).symm s).val.contMDiff

/-- A bundle test has compact support. -/
theorem isCompact_tsupport (s : BundleTest I F V) : IsCompact (closure {x | s x ≠ 0}) :=
  (tsupport_def ((ofCompactlySupported I F V).symm s).val).symm ▸
    mem_compactlySupported.1 ((ofCompactlySupported I F V).symm s).property

/-- Bundle tests are determined by their values. -/
@[ext]
theorem ext {s t : BundleTest I F V} (h : ∀ x, s x = t x) : s = t :=
  (ofCompactlySupported I F V).symm.injective <| Subtype.ext <| ContMDiffSection.ext h

@[simp]
theorem add_apply (s t : BundleTest I F V) (x : M) : (s + t) x = s x + t x :=
  rfl

@[simp]
theorem smul_apply (a : ℝ) (s : BundleTest I F V) (x : M) : (a • s) x = a • s x :=
  rfl

@[simp]
theorem zero_apply (x : M) : (0 : BundleTest I F V) x = 0 :=
  rfl

@[simp]
theorem neg_apply (s : BundleTest I F V) (x : M) : (-s) x = -s x :=
  rfl

@[simp]
theorem sub_apply (s t : BundleTest I F V) (x : M) : (s - t) x = s x - t x :=
  rfl

variable [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]

/-- The topology on bundle tests is the test topology of any covering family of smooth frames
`e i` over open sets `U i` contained in their base sets: it does not depend on the frames. -/
theorem instTopologicalSpace_eq_compactlySupportedTopology [LocallyCompactSpace E] {ι : Type*}
    (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover : ∀ x : M, ∃ i, x ∈ U i) :
    instTopologicalSpace = compactlySupportedTopology (I := I) (n := ∞) e U hU :=
  compactlySupportedTopology_eq_of_covers _ _ _ (fun x ↦ ⟨x, mem_baseSet_trivializationAt F V x⟩)
    e U hU hcover

instance : T2Space (BundleTest I F V) :=
  t2Space_compactlySupportedTopology (I := I) (n := ∞) _ _ _
    fun x ↦ ⟨x, mem_baseSet_trivializationAt F V x⟩

/-- Evaluation of bundle tests at a point is continuous. -/
theorem continuous_eval_const (x : M) : Continuous fun s : BundleTest I F V ↦ s x := by
  let := frameTopology (I := I) (n := ∞) (fun x : M ↦ trivializationAt F V x)
    (fun x ↦ ⟨_, (trivializationAt F V x).open_baseSet⟩) fun _ ↦ subset_rfl
  exact (ContMDiffSection.continuous_eval_const _ _ _
    (fun x ↦ ⟨x, mem_baseSet_trivializationAt F V x⟩) x).comp
    (continuous_val_compactlySupportedTopology (I := I) (n := ∞) _ _ _)

/-- Every fixed-compact support stage includes continuously into the bundle tests. -/
theorem continuous_ofSupportedIn (K : Compacts M) :
    letI := frameTopology (I := I) (n := ∞) (fun x : M ↦ trivializationAt F V x)
      (fun x ↦ ⟨_, (trivializationAt F V x).open_baseSet⟩) fun _ ↦ subset_rfl
    Continuous (ofCompactlySupported I F V ∘ ofSupportedIn (I := I) (F := F) (V := V) K) :=
  ContMDiffSection.continuous_ofSupportedIn _ _ _ K

variable {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G]

/-- The universal property of the test topology: a linear map from bundle tests to a locally
convex real topological vector space is continuous exactly when it is continuous on every
fixed-compact support stage. -/
theorem continuous_iff_continuous_comp (g : BundleTest I F V →ₗ[ℝ] G) :
    letI := frameTopology (I := I) (n := ∞) (fun x : M ↦ trivializationAt F V x)
      (fun x ↦ ⟨_, (trivializationAt F V x).open_baseSet⟩) fun _ ↦ subset_rfl
    Continuous g ↔ ∀ K : Compacts M,
      Continuous (g ∘ ofCompactlySupported I F V ∘ ofSupportedIn (I := I) (F := F) (V := V) K) :=
  continuous_compactlySupportedTopology_iff _ _ _
    (g ∘ₗ (ofCompactlySupported I F V).toLinearMap)

/-! ### Point masses -/

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]

/-- The **point mass** `δ_x ℓ` at `x : M` with a continuous linear map `ℓ : V x →L[ℝ] W` on the
fibre `V x`, for instance a covector: the functional `s ↦ ℓ (s x)` on bundle tests. -/
def delta (x : M) (ℓ : V x →L[ℝ] W) : BundleTest I F V →L_c[ℝ] W where
  toFun s := ℓ (s x)
  map_add' s t := by simp
  map_smul' a s := by simp
  cont := ℓ.continuous.comp (continuous_eval_const x)

@[simp]
theorem delta_apply (x : M) (ℓ : V x →L[ℝ] W) (s : BundleTest I F V) :
    delta x ℓ s = ℓ (s x) :=
  (rfl)

@[simp]
theorem delta_zero [IsTopologicalAddGroup W] (x : M) :
    delta (I := I) (F := F) (V := V) x (0 : V x →L[ℝ] W) = 0 := by
  ext s
  simp

theorem delta_add [IsTopologicalAddGroup W] (x : M) (ℓ ℓ' : V x →L[ℝ] W) :
    delta (I := I) (F := F) x (ℓ + ℓ') = delta x ℓ + delta x ℓ' := by
  ext s
  simp

theorem delta_smul [ContinuousConstSMul ℝ W] (x : M) (a : ℝ) (ℓ : V x →L[ℝ] W) :
    delta (I := I) (F := F) x (a • ℓ) = a • delta x ℓ := by
  ext s
  simp

/-- Every vector of a fibre is the value of a bundle test. -/
theorem exists_apply_eq [FiniteDimensional ℝ E] [T2Space M] (x : M) (v : V x) :
    ∃ s : BundleTest I F V, s x = v := by
  obtain ⟨s, hsx, hs, -⟩ := ContMDiffSection.exists_apply_eq_isCompact_tsupport_subset
    (I := I) (F := F) (n := ∞) x v Filter.univ_mem
  exact ⟨ofCompactlySupported I F V ⟨s, ContMDiffSection.mem_compactlySupported.2 hs⟩, hsx⟩

/-- A point mass vanishes exactly when its map on the fibre does. -/
theorem delta_eq_zero_iff [FiniteDimensional ℝ E] [T2Space M] [IsTopologicalAddGroup W] {x : M}
    {ℓ : V x →L[ℝ] W} :
    delta (I := I) (F := F) x ℓ = 0 ↔ ℓ = 0 := by
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨s, rfl⟩ := exists_apply_eq (I := I) (F := F) x v
    simpa using congr($h s)
  · ext s
    simp [h]

end BundleTest

end TauCeti

/-! ### Transport along bundle maps -/

namespace TauCeti.BundleTest

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {V₁ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle ∞ F₂ V₂ I]

/-- A smooth bundle map whose expression in the preferred frames at each point is a constant model
map transports bundle tests continuously: in frame coordinates on the common frame domains it
is a fixed continuous linear map, so it is continuous on every fixed-compact support stage. -/
theorem continuous_map_of_inCoordinates_eq_const (ϕ : ∀ x, V₁ x →L[ℝ] V₂ x)
    (hϕ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) ∞
      (fun p : TotalSpace F₁ V₁ ↦ (⟨p.proj, ϕ p.proj p.snd⟩ : TotalSpace F₂ V₂)))
    {c : M → F₁ →L[ℝ] F₂}
    (hc : ∀ a x, x ∈ (trivializationAt F₁ V₁ a).baseSet →
      x ∈ (trivializationAt F₂ V₂ a).baseSet →
      ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ a x a x (ϕ x) = c a) :
    Continuous fun s : BundleTest I F₁ V₁ ↦ ofCompactlySupported I F₂ V₂
      (mapCompactlySupported (fun x ↦ (ϕ x : V₁ x →ₗ[ℝ] V₂ x)) hϕ
        ((ofCompactlySupported I F₁ V₁).symm s)) := by
  -- Work in the frames of both bundles at each point, over the intersection of their domains.
  let e₁ : M → Trivialization F₁ (π F₁ V₁) := fun a ↦ trivializationAt F₁ V₁ a
  let e₂ : M → Trivialization F₂ (π F₂ V₂) := fun a ↦ trivializationAt F₂ V₂ a
  let U : M → Opens M := fun a ↦
    ⟨(e₁ a).baseSet ∩ (e₂ a).baseSet, (e₁ a).open_baseSet.inter (e₂ a).open_baseSet⟩
  have hU₁ : ∀ a, (U a : Set M) ⊆ (e₁ a).baseSet := fun _ _ h ↦ h.1
  have hU₂ : ∀ a, (U a : Set M) ⊆ (e₂ a).baseSet := fun _ _ h ↦ h.2
  have hcov : ∀ x : M, ∃ a, x ∈ U a :=
    fun x ↦ ⟨x, mem_baseSet_trivializationAt F₁ V₁ x, mem_baseSet_trivializationAt F₂ V₂ x⟩
  let ϕ' : ∀ x, V₁ x →ₗ[ℝ] V₂ x := fun x ↦ ϕ x
  -- In frame coordinates the map is the constant model map `c a`.
  have hΦ : letI := frameTopology (I := I) (n := ∞) e₁ U hU₁
      letI := frameTopology (I := I) (n := ∞) e₂ U hU₂
      Continuous (mapLinearMap ϕ' hϕ) := by
    refine continuous_frameTopology_of_frameCoordinates_eq_clm_apply e₁ U hU₁ e₂ hU₂ c ?_
    intro a s x
    have hx₁ := hU₁ a x.property
    have hx₂ := hU₂ a x.property
    rw [← hc a x hx₁ hx₂, ContinuousLinearMap.inCoordinates_eq hx₁ hx₂]
    simp [ϕ', e₁, e₂, Trivialization.frameCoordinates_apply, hx₁]
  let := frameTopology (I := I) (n := ∞) e₁ U hU₁
  let := frameTopology (I := I) (n := ∞) e₂ U hU₂
  let := compactlySupportedTopology (I := I) (n := ∞) e₂ U hU₂
  let := isTopologicalAddGroup_compactlySupportedTopology (I := I) (n := ∞) e₂ U hU₂
  let := continuousSMul_compactlySupportedTopology (I := I) (n := ∞) e₂ U hU₂
  let := locallyConvexSpace_compactlySupportedTopology (I := I) (n := ∞) e₂ U hU₂
  rw [instTopologicalSpace_eq_compactlySupportedTopology e₁ U hU₁ hcov,
    instTopologicalSpace_eq_compactlySupportedTopology e₂ U hU₂ hcov]
  refine (continuous_compactlySupportedTopology_iff e₁ U hU₁
    (mapCompactlySupported ϕ' hϕ)).2 fun K ↦ ?_
  -- On a fixed-compact stage the map stays in the same stage of the target.
  have hK : Continuous (mapSupportedIn ϕ' hϕ K) :=
    ((hΦ.comp continuous_subtypeVal).subtype_mk fun s ↦
      mapLinearMap_mem_supportedIn ϕ' hϕ s.property).congr fun s ↦
        Subtype.ext (coe_mapSupportedIn ϕ' hϕ K s).symm
  exact ((ContMDiffSection.continuous_ofSupportedIn e₂ U hU₂ K).comp hK).congr fun s ↦
    Subtype.ext (by simp)

end TauCeti.BundleTest

/-! ### Local representatives in charts -/

namespace Bundle.Trivialization

open TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  (c : OpenPartialHomeomorph M E)
  (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hct : c.source ⊆ t.baseSet)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Extending native test functions on the target of a smooth chart `c` to bundle tests through a
bundle frame `t`, by zero outside the chart source (`Bundle.Trivialization.chartTestSection`), as
a continuous linear map for the test topologies. -/
def chartTestCLM : 𝓓(⟨c.target, c.open_target⟩, F) →L[ℝ] BundleTest I F V where
  toLinearMap := (BundleTest.ofCompactlySupported I F V).toLinearMap ∘ₗ
    t.chartTestSection (n := ⊤) c hc hct
  cont := continuous_chartTestSection (n := ⊤) t c hc hct _ _ _

@[simp]
theorem coe_chartTestCLM (φ : 𝓓(⟨c.target, c.open_target⟩, F)) :
    ⇑(t.chartTestCLM c hc hct φ) = (t.chartTestSection (n := ⊤) c hc hct φ).val :=
  (rfl)

/-- On the chart source, the extended test is the inverse frame applied to the value of the test
function in coordinates. -/
theorem chartTestCLM_apply_of_mem (φ : 𝓓(⟨c.target, c.open_target⟩, F)) {x : M}
    (hx : x ∈ c.source) : t.chartTestCLM c hc hct φ x = t.symmL ℝ x (φ (c x)) :=
  t.chartTestSection_apply_of_mem (n := ⊤) c hc hct φ hx

/-- The extended test vanishes outside the chart source. -/
theorem chartTestCLM_apply_of_notMem (φ : 𝓓(⟨c.target, c.open_target⟩, F)) {x : M}
    (hx : x ∉ c.source) : t.chartTestCLM c hc hct φ x = 0 :=
  t.chartTestSection_apply_of_notMem (n := ⊤) c hc hct φ hx

/-- Native test functions on the chart target are determined by their extended bundle tests. -/
theorem chartTestCLM_injective : Function.Injective (t.chartTestCLM c hc hct) :=
  (BundleTest.ofCompactlySupported I F V).injective.comp
    (t.chartTestSection_injective (n := ⊤) c hc hct)

variable [FiniteDimensional ℝ F]

/-- The **local representative** of a functional `T` on bundle tests in a smooth chart `c` and a
bundle frame `t` over its source: the distribution on the chart target, with values in the maps
`F →L[ℝ] W` on the model fibre, that pairs a real test function `φ` with `v : F` as `T (φ • v)`,
the test function `φ • v` being extended to a bundle test through the chart and the frame. -/
def chartDistributionCLM :
    (BundleTest I F V →L_c[ℝ] W) →L[ℝ] 𝓓'(⟨c.target, c.open_target⟩, F →L[ℝ] W) :=
  (TestFunction.dualEquivDistribution : _ ≃L[ℝ] 𝓓'(⟨c.target, c.open_target⟩, F →L[ℝ] W)) ∘L
    (t.chartTestCLM c hc hct).precompCompactConvergenceCLM W

@[simp]
theorem chartDistributionCLM_apply_apply (T : BundleTest I F V →L_c[ℝ] W)
    (φ : 𝓓(⟨c.target, c.open_target⟩, ℝ)) (v : F) :
    t.chartDistributionCLM c hc hct T φ v =
      T (t.chartTestCLM c hc hct (TestFunction.postcompCLM (toSpanSingleton ℝ v) φ)) := by
  simp only [chartDistributionCLM, coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    TestFunction.dualEquivDistribution_apply_apply]
  -- Precomposition is evaluated through the `→L_c` type synonym.
  rfl

/-- In a chart whose source contains `x`, the local representative of the point mass `δ_x ℓ` is
the point mass at `c x` with value the map `ℓ` read in the frame. -/
theorem chartDistributionCLM_delta_of_mem {x : M} (hx : x ∈ c.source) (ℓ : V x →L[ℝ] W) :
    t.chartDistributionCLM c hc hct (BundleTest.delta x ℓ) =
      Distribution.mapCLM (toSpanSingleton ℝ (ℓ ∘L t.symmL ℝ x)) (Distribution.delta (c x)) := by
  ext φ v
  simp [t.chartTestCLM_apply_of_mem c hc hct _ hx]

/-- In a chart whose source does not contain `x`, the local representative of a point mass at `x`
vanishes. -/
theorem chartDistributionCLM_delta_of_notMem {x : M} (hx : x ∉ c.source) (ℓ : V x →L[ℝ] W) :
    t.chartDistributionCLM c hc hct (BundleTest.delta x ℓ) = 0 := by
  ext φ v
  simp [t.chartTestCLM_apply_of_notMem c hc hct _ hx]

end Bundle.Trivialization

/-! ### Functionals are determined by their local representatives -/

namespace TauCeti.BundleTest

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Functionals on bundle tests are determined by their local representatives.** On a
boundaryless Hausdorff `σ`-compact manifold with finite-dimensional model, two functionals agree
once their local representatives agree in every smooth chart lying over the base set of a
trivialization of the bundle atlas: bundle tests are finite sums of chart extensions of native
test functions (`ContMDiffSection.span_iUnion_range_chartTestSection_eq_top`). -/
theorem ext_chartDistributionCLM {T T' : BundleTest I F V →L_c[ℝ] W}
    (h : ∀ (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
      (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
      (hct : c.source ⊆ t.baseSet),
      t.chartDistributionCLM c hc hct T = t.chartDistributionCLM c hc hct T') :
    T = T' := by
  -- The chart extensions span the bundle tests.
  have hspan := congrArg (Submodule.map (ofCompactlySupported I F V).toLinearMap)
    (span_iUnion_range_chartTestSection_eq_top (I := I) (F := F) (V := V) (n := ⊤))
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at hspan
  refine ContinuousLinearMap.coe_injective (LinearMap.ext_on hspan ?_)
  rintro _ ⟨_, ⟨_, ⟨p, rfl⟩, φ, rfl⟩, rfl⟩
  let := p.memTrivializationAtlas
  have hp := TestFunction.dualEquivDistribution.injective
    (h p.trivialization p.chart p.contMDiffOn_chart p.source_subset)
  rw [ChartTestData.chartTestSection_def]
  -- Evaluation of the precomposition through the `→L_c` type synonym is evaluation of `T` and
  -- `T'` at the extended test.
  exact DFunLike.congr_fun hp φ

/-- Functionals on bundle tests agree exactly when all their local representatives agree. -/
theorem ext_chartDistributionCLM_iff {T T' : BundleTest I F V →L_c[ℝ] W} :
    T = T' ↔ ∀ (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
      (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
      (hct : c.source ⊆ t.baseSet),
      t.chartDistributionCLM c hc hct T = t.chartDistributionCLM c hc hct T' :=
  ⟨fun h _ _ _ _ _ ↦ h ▸ rfl, ext_chartDistributionCLM⟩

end TauCeti.BundleTest

/-! ### Distributional sections -/

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

/-- The bundle tests with values in the **`V`-dual densities**, the bundle of continuous linear
maps from `V` to the density line `TauCeti.DensityBundle I M`. These are the tests on which the
distributional sections of `V` act. -/
abbrev DualDensityTest :=
  BundleTest I (F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] DensityBundle I M x)

/-- The **distributional sections** of a smooth vector bundle `V`: the continuous linear
functionals on the bundle tests with values in the `V`-dual densities, the bundle of continuous
linear maps from `V` to the density line `TauCeti.DensityBundle I M`. The density factor is what
lets a section `u` of `V` act on such a test `s` without a choice of measure on `M`, through the
integral of the density `x ↦ s x (u x)`. -/
abbrev BundleDistribution :=
  DualDensityTest I M F V →L_c[ℝ] ℝ

end TauCeti

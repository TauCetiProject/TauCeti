/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Gluing
public import Mathlib.Topology.ContinuousMap.LocallyConvex
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# The compact derivative topology on bundle sections

Fix open frame domains in a smooth vector bundle. `ContMDiffSection.frameTopology` is the
topology of uniform convergence on compact coordinate sets of every available derivative of
the frame coefficients. It is a topological vector space, locally convex over the reals.
The convergence criterion `ContMDiffSection.tendsto_frameTopology_iff` uses the existing
`Bundle.Trivialization.chartDerivativeSeminorm`, applied to differences of sections.

For a cover, the coefficient map `TauCeti.Manifold.sectionFrameCoordinates` is a closed
embedding into the product of weak Whitney coefficient spaces. Its image consists exactly
of tuples satisfying the actual bundle transition law, as proved in `Section.Gluing`.
Thus this topology retains the gluing equations when taking coefficient limits.
Point evaluation is continuous, and the section space is Hausdorff.

The topology is supplied explicitly, rather than installed globally, since the frame domains
are parameters. The results here concern a specified family of frame domains. Cover comparison
and continuity of open restriction are proved in `Section.FrameCover`; completeness is separate.
Neither compactness nor finite dimensionality is needed, and chart derivatives allow corners.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, for compact derivative topologies.

The construction uses the native chart jets and frame coordinates, and the closed-image
gluing theorem `TauCeti.Manifold.isClosed_range_sectionFrameCoordinates`.
-/

public section

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- All source-chart derivatives of the local frame coefficients, as a linear map into
the product of compact-open continuous-map spaces. -/
-- Use the simp normal form of the target so `frameJet_apply` can rewrite this dependent coercion.
def frameJet : Cₛ^n⟮I; F, V⟯ →ₗ[𝕜]
    ∀ (i : ι) (x : U i) (m : {m : ℕ // m ≤ n}),
      C(↥(I.target ∩ I.symm ⁻¹' (chartAt H x).target), E [×(m : ℕ)]→L[𝕜] F) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun x ↦ LinearMap.pi fun m ↦
    (ContMDiffMap.chartIteratedFDerivLinearMap x m m.2).comp
      ((e i).frameCoordinates (hU i))

/-- The frame jet is the native chart derivative of the frame-coordinate function. -/
-- Normalize the dependent coercion's chart target, as required by simp normal form.
@[simp]
theorem frameJet_apply (s : Cₛ^n⟮I; F, V⟯) (i : ι) (x : U i)
    (m : {m : ℕ // m ≤ n}) :
    DFunLike.coe (F := Cₛ^n⟮I; F, V⟯ →ₗ[𝕜]
      ∀ (i : ι) (x : U i) (m : {m : ℕ // m ≤ n}),
        C(↥(I.target ∩ I.symm ⁻¹' (chartAt H x).target), E [×(m : ℕ)]→L[𝕜] F))
      (frameJet e U hU) s i x m =
      ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) s) x m m.2 :=
  ContMDiffMap.chartIteratedFDerivLinearMap_apply _ _ _ _

/-- The topology of compact convergence of all available coordinate derivatives in the
specified frame domains. For smooth sections, all finite derivative orders are included. -/
@[instance_reducible]
def frameTopology : TopologicalSpace Cₛ^n⟮I; F, V⟯ :=
  .induced (frameJet (I := I) e U hU) inferInstance

/-- A section family is continuous exactly when all its frame-coordinate chart jets are
continuous in the compact-open topology. -/
theorem continuous_frameTopology_iff {P : Type*} [TopologicalSpace P]
    {s : P → Cₛ^n⟮I; F, V⟯} :
    let _ := frameTopology (I := I) (n := n) e U hU
    Continuous s ↔ ∀ (i : ι) (x : U i) (m : ℕ) (hm : m ≤ n),
      Continuous (fun p ↦
        ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) (s p)) x m hm) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  simp only [continuous_induced_rng, continuous_pi_iff, Function.comp_def,
    frameJet_apply]
  refine forall_congr' fun i ↦ forall_congr' fun x ↦ ?_
  simp only [Subtype.forall]
  -- `extChartAt` is a simp definition. Reconcile its native chart-jet target with the
  -- expanded target required for the dependent coercion in `frameJet_apply` to be simp-normal.
  convert! Iff.rfl

/-- A chosen frame-coordinate jet depends continuously on the section. -/
theorem continuous_frameJet_apply (i : ι) (x : U i) (m : ℕ) (hm : m ≤ n) :
    let _ := frameTopology (I := I) (n := n) e U hU
    Continuous (fun s : Cₛ^n⟮I; F, V⟯ ↦
      ContMDiffMap.chartIteratedFDeriv ((e i).frameCoordinates (hU i) s) x m hm) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  exact (continuous_frameTopology_iff (I := I) (n := n) e U hU).mp continuous_id i x m hm

/-- Addition and subtraction are continuous for the frame topology. -/
theorem isTopologicalAddGroup_frameTopology :
    let _ := frameTopology (I := I) (n := n) e U hU
    IsTopologicalAddGroup Cₛ^n⟮I; F, V⟯ :=
  isTopologicalAddGroup_induced (frameJet (I := I) e U hU)

/-- Joint scalar multiplication is continuous for the frame topology. -/
theorem continuousSMul_frameTopology :
    let _ := frameTopology (I := I) (n := n) e U hU
    ContinuousSMul 𝕜 Cₛ^n⟮I; F, V⟯ :=
  continuousSMul_induced (frameJet (I := I) e U hU)

section Coefficients

open scoped TauCeti.ManifoldWeakWhitney

/-- Frame coefficients depend continuously on the section in the weak Whitney topology. -/
theorem continuous_frameCoordinates (i : ι) :
    let _ := frameTopology (I := I) (n := n) e U hU
    Continuous ((e i).frameCoordinates (I := I) (n := n) (hU i)) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  apply ContMDiffMap.continuous_manifoldWeakWhitney_iff.mpr
  intro x y m hm K hK W hW
  rw [ContMDiffMap.chartJetSet_self_target x y m hm K W]
  exact (ContinuousMap.isOpen_setOfPred_mapsTo hK hW).preimage
    (continuous_frameJet_apply e U hU i x m hm)

/-- Continuity into the frame topology can be checked on the weak Whitney spaces of
coefficient functions. -/
theorem continuous_frameTopology_iff_frameCoordinates {P : Type*} [TopologicalSpace P]
    {s : P → Cₛ^n⟮I; F, V⟯} :
    let _ := frameTopology (I := I) (n := n) e U hU
    Continuous s ↔ ∀ i, Continuous (fun p ↦ (e i).frameCoordinates (hU i) (s p)) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  constructor
  · intro hs i
    exact (continuous_frameCoordinates e U hU i).comp hs
  · intro hs
    apply (continuous_frameTopology_iff e U hU).mpr
    intro i x m hm
    exact (ContMDiffMap.continuous_chartIteratedFDeriv x m hm).comp (hs i)

/-- The topology on sections is induced by their tuple of weak Whitney frame coefficients,
as well as by their coordinate jets. -/
theorem isInducing_sectionFrameCoordinates :
    let _ := frameTopology (I := I) (n := n) e U hU
    IsInducing (TauCeti.Manifold.sectionFrameCoordinates (I := I) (n := n) e U hU) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let J : (∀ i, C^n⟮I, U i; 𝓘(𝕜, F), F⟯) →
      ∀ (i : ι) (x : U i) (m : {m : ℕ // m ≤ n}),
        C((extChartAt I x).target, E [×(m : ℕ)]→L[𝕜] F) :=
    fun f i x m ↦ ContMDiffMap.chartIteratedFDeriv (f i) x m m.2
  have hJ : Continuous J := continuous_pi fun i ↦ continuous_pi fun x ↦
    continuous_pi fun m ↦
      (ContMDiffMap.continuous_chartIteratedFDeriv x m m.2).comp (continuous_apply i)
  have hcomp : J ∘ TauCeti.Manifold.sectionFrameCoordinates (I := I) e U hU =
      frameJet e U hU := by
    funext s i x m
    dsimp only [Function.comp_apply, J]
    rw [frameJet_apply]
    -- The exported coefficient maps agree pointwise by their evaluation lemmas;
    -- neither map's definition needs to be unfolded.
    congr 1
    ext y
    simp
  have hc : Continuous (TauCeti.Manifold.sectionFrameCoordinates (I := I) (n := n) e U hU) := by
    apply continuous_pi
    intro i
    refine (continuous_frameCoordinates e U hU i).congr fun s ↦ ?_
    ext y
    simp
  apply IsInducing.of_comp hc hJ
  rw [hcomp]
  exact .induced _

/-- For a frame cover, sections form a closed subspace of the product of weak Whitney
coefficient spaces. The image is characterized by the bundle transition equations in
`TauCeti.Manifold.mem_range_sectionFrameCoordinates_iff`. -/
theorem isClosedEmbedding_sectionFrameCoordinates (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology (I := I) (n := n) e U hU
    IsClosedEmbedding (TauCeti.Manifold.sectionFrameCoordinates (I := I) (n := n) e U hU) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  exact ⟨⟨isInducing_sectionFrameCoordinates e U hU,
    TauCeti.Manifold.sectionFrameCoordinates_injective e U hU hcover⟩,
    TauCeti.Manifold.isClosed_range_sectionFrameCoordinates e U hU hcover⟩

/-- A frame cover gives a Hausdorff topology on sections. -/
theorem t2Space_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology (I := I) (n := n) e U hU
    T2Space Cₛ^n⟮I; F, V⟯ := by
  let _ := frameTopology (I := I) (n := n) e U hU
  exact (isClosedEmbedding_sectionFrameCoordinates (I := I) (n := n)
    e U hU hcover).isEmbedding.t2Space

/-- Evaluation at a point lying in one of the frame domains is continuous. -/
theorem continuous_eval_const_of_mem (i : ι) {x : M} (hx : x ∈ U i) :
    let _ := frameTopology (I := I) (n := n) e U hU
    Continuous (fun s : Cₛ^n⟮I; F, V⟯ ↦ s x) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  have hc := (ContMDiffMap.continuous_eval_const_manifoldWeakWhitney
    (I := I) (J := 𝓘(𝕜, F)) (n := n) (⟨x, hx⟩ : U i)).comp
      (continuous_frameCoordinates e U hU i)
  have h := ((e i).continuousLinearEquivAt 𝕜 x (hU i hx)).symm.continuous.comp hc
  exact h.congr fun s ↦ by
    simp only [Function.comp_apply, Trivialization.frameCoordinates_apply,
      Trivialization.continuousLinearEquivAt_symm_apply,
      (e i).symm_apply_apply_mk (hU i hx)]

/-- Point evaluation is continuous when the chosen frame domains cover the base. -/
theorem continuous_eval_const (hcover : ∀ x, ∃ i, x ∈ U i) (x : M) :
    let _ := frameTopology (I := I) (n := n) e U hU
    Continuous (fun s : Cₛ^n⟮I; F, V⟯ ↦ s x) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  obtain ⟨i, hi⟩ := hcover x
  exact continuous_eval_const_of_mem e U hU i hi

end Coefficients

/-- Convergence of sections is exactly compact convergence of every frame-coordinate chart
derivative, expressed by the existing derivative seminorms on differences of sections. -/
theorem tendsto_frameTopology_iff {P : Type*} {l : Filter P}
    {s : P → Cₛ^n⟮I; F, V⟯} {s₀ : Cₛ^n⟮I; F, V⟯} :
    let _ := frameTopology (I := I) (n := n) e U hU
    Tendsto s l (𝓝 s₀) ↔ ∀ (i : ι) (x : U i)
      (K : Compacts (extChartAt I x).target) (m : ℕ) (hm : m ≤ n),
      Tendsto (fun p ↦ (e i).chartDerivativeSeminorm (hU i) x K m hm (s p - s₀))
        l (𝓝 0) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  simp only [nhds_induced, tendsto_comap_iff, tendsto_pi_nhds, Function.comp_def,
    frameJet_apply]
  refine forall_congr' fun i ↦ forall_congr' fun x ↦ ?_
  simp only [Subtype.forall]
  constructor
  · intro h K m hm
    apply tendsto_order.mpr
    constructor
    · intro r hr
      exact Eventually.of_forall fun p ↦ hr.trans_le (apply_nonneg _ _)
    · intro ε hε
      have hu := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
        (h m hm) K K.isCompact
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with p hp
      apply ((e i).chartDerivativeSeminorm_lt_iff (hU i) x K m hm _ hε).mpr
      intro z hz
      simpa only [map_sub, ContMDiffMap.chartIteratedFDeriv_sub,
        ContinuousMap.sub_apply, dist_eq_norm, norm_sub_rev] using hp z hz
  · intro h m hm
    apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
    intro K hK
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(h ⟨K, hK⟩ m hm).eventually (gt_mem_nhds hε)] with p hp
    have hb := ((e i).chartDerivativeSeminorm_lt_iff (hU i) x ⟨K, hK⟩ m hm _ hε).mp hp
    intro z hz
    simpa only [map_sub, ContMDiffMap.chartIteratedFDeriv_sub,
      ContinuousMap.sub_apply, dist_eq_norm, norm_sub_rev] using hb z hz

/-- A compact frame-coordinate derivative seminorm is continuous in the section topology. -/
theorem continuous_chartDerivativeSeminorm (i : ι) (x : U i)
    (K : Compacts (extChartAt I x).target) (m : ℕ) (hm : m ≤ n) :
    let _ := frameTopology (I := I) (n := n) e U hU
    Continuous ((e i).chartDerivativeSeminorm (hU i) x K m hm) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  have hjet := (ContinuousMap.continuous_restrict (K : Set (extChartAt I x).target)).comp
    (continuous_frameJet_apply e U hU i x m hm)
  exact ((continuous_norm (E := C(K, E [×m]→L[𝕜] F))).comp hjet).congr fun s ↦
    ((e i).chartDerivativeSeminorm_apply (hU i) x K m hm s).symm

/-- Compact frame derivative tolerance balls are open in the section topology. -/
theorem isOpen_ball_chartDerivativeSeminorm (i : ι) (x : U i)
    (K : Compacts (extChartAt I x).target) (m : ℕ) (hm : m ≤ n)
    (s : Cₛ^n⟮I; F, V⟯) (r : ℝ) :
    let _ := frameTopology (I := I) (n := n) e U hU
    IsOpen (((e i).chartDerivativeSeminorm (hU i) x K m hm).ball s r) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := isTopologicalAddGroup_frameTopology (I := I) (n := n) e U hU
  exact isOpen_lt ((continuous_chartDerivativeSeminorm e U hU i x K m hm).comp
    (continuous_id.sub continuous_const)) continuous_const

/-- Compact frame `C^k` tolerance balls are open in the section topology. -/
theorem isOpen_ball_chartCkSeminorm (i : ι) (x : U i)
    (K : Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n)
    (s : Cₛ^n⟮I; F, V⟯) (r : ℝ) :
    let _ := frameTopology (I := I) (n := n) e U hU
    IsOpen (((e i).chartCkSeminorm (hU i) x K k hk).ball s r) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := ContMDiffMap.manifoldWeakWhitneyTopology (I := I) (M := U i)
    (J := 𝓘(𝕜, F)) (N := F) (n := n)
  have h := (ContMDiffMap.isOpen_ball_chartCkSeminorm x K k hk
    ((e i).frameCoordinates (hU i) s) r).preimage (continuous_frameCoordinates e U hU i)
  by_cases hr : 0 < r
  · convert h using 1
    ext t
    exact ((e i).mem_ball_chartCkSeminorm_iff (hU i) x K k hk s t hr).trans
      (ContMDiffMap.mem_ball_chartCkSeminorm_iff x K k hk
        ((e i).frameCoordinates (hU i) s) ((e i).frameCoordinates (hU i) t) hr).symm
  · rw [Seminorm.ball_eq_emptyset _ (le_of_not_gt hr)]
    exact isOpen_empty

/-- Every positive compact frame `C^k` tolerance gives a section neighborhood. -/
theorem ball_chartCkSeminorm_mem_nhds (i : ι) (x : U i)
    (K : Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n)
    (s : Cₛ^n⟮I; F, V⟯) {r : ℝ} (hr : 0 < r) :
    let _ := frameTopology (I := I) (n := n) e U hU
    ((e i).chartCkSeminorm (hU i) x K k hk).ball s r ∈ 𝓝 s := by
  let _ := frameTopology (I := I) (n := n) e U hU
  exact (isOpen_ball_chartCkSeminorm e U hU i x K k hk s r).mem_nhds (by simpa using hr)

/-- A compact frame `C^k` seminorm is continuous in the section topology. -/
theorem continuous_chartCkSeminorm (i : ι) (x : U i)
    (K : Compacts (extChartAt I x).target) (k : ℕ) (hk : k ≤ n) :
    let _ := frameTopology (I := I) (n := n) e U hU
    Continuous ((e i).chartCkSeminorm (hU i) x K k hk) := by
  let _ := frameTopology (I := I) (n := n) e U hU
  let _ := isTopologicalAddGroup_frameTopology (I := I) (n := n) e U hU
  exact Seminorm.continuous_of_forall fun r hr ↦
    ball_chartCkSeminorm_mem_nhds e U hU i x K k hk 0 hr

end ContMDiffSection

namespace ContMDiffSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- The compact derivative topology on real bundle sections is locally convex. -/
theorem locallyConvexSpace_frameTopology :
    let _ := frameTopology (I := I) (n := n) e U hU
    LocallyConvexSpace ℝ Cₛ^n⟮I; F, V⟯ :=
  .induced (frameJet (I := I) (n := n) e U hU)

end ContMDiffSection

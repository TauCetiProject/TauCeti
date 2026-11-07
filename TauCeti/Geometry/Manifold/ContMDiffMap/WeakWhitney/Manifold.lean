/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.WithSeminorms
public import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney.Open
public import TauCeti.Topology.ContinuousMap.UniformGroup

/-!
# Completeness of vector-valued weak Whitney map spaces

On a boundaryless manifold with locally compact model, the chart jet realizes the native
space of finite-order or smooth vector-valued maps as a closed subspace of the product of
compact-open derivative spaces. The zeroth coefficients of a limiting jet agree on overlaps;
the local Taylor-series limit theorem then recovers a smooth map with precisely that jet.
For a complete target, this proves completeness for the additive uniformity of the existing
weak Whitney topology. No compactness or countability of the manifold is required.

This provides the coefficient-space completeness needed to reconstruct smooth bundle sections
from compatible local limits. Analytic regularity is excluded.

## References

* M. Hirsch, *Differential Topology*, Chapter 2, §1, for the weak Whitney topology.
* The local reconstruction reuses `ContMDiffMap.exists_openWeakWhitneyJet_eq_of_tendsto`,
  which is based on Mathlib's Taylor-series derivative-limit theorem.
-/

public section

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω} [IsManifold I n M]

/-- All source-chart derivatives of a vector-valued map, with compact-open topology in each
component. Unlike the compact chart jet, a component is defined on the entire chart target. -/
def chartJet : C^n⟮I, M; 𝓘(𝕜, F), F⟯ →ₗ[𝕜]
    ∀ (x : M) (m : {m : ℕ // m ≤ n}),
      C(↥(I.target ∩ I.symm ⁻¹' (chartAt H x).target), E [×(m : ℕ)]→L[𝕜] F) :=
  LinearMap.pi fun x ↦ LinearMap.pi fun m ↦ chartIteratedFDerivLinearMap x m m.2

/-- Each component of the chart jet is the native chart derivative. -/
@[simp]
-- Normalize the dependent coercion's chart target, as for `chartIteratedFDerivLinearMap_apply`.
theorem chartJet_apply (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (x : M) (m : {m : ℕ // m ≤ n}) :
    DFunLike.coe (F := C^n⟮I, M; 𝓘(𝕜, F), F⟯ →ₗ[𝕜]
      ∀ (x : M) (m : {m : ℕ // m ≤ n}),
        C(↥(I.target ∩ I.symm ⁻¹' (chartAt H x).target), E [×(m : ℕ)]→L[𝕜] F))
      chartJet f x m = chartIteratedFDeriv f x m m.2 :=
  chartIteratedFDerivLinearMap_apply _ _ _ _

/-- The chart jet induces exactly the existing manifold weak Whitney topology. -/
theorem isInducing_chartJet :
    IsInducing (chartJet (I := I) (M := M) (F := F) (n := n)) := by
  refine ⟨le_antisymm ?_ ?_⟩
  · apply continuous_iff_le_induced.mp
    exact continuous_pi fun x ↦ continuous_pi fun m ↦
      (continuous_chartIteratedFDeriv x m m.2).congr fun f ↦ (chartJet_apply f x m).symm
  · rw [← continuous_id_iff_le]
    let _ := TopologicalSpace.induced (chartJet (I := I) (M := M) (F := F) (n := n))
      inferInstance
    apply continuous_manifoldWeakWhitney_iff_chartIteratedFDeriv.mpr
    intro x m hm
    exact (((continuous_apply (⟨m, hm⟩ : {m : ℕ // m ≤ n})).comp
      ((continuous_apply x).comp
        (continuous_induced_dom (f := chartJet (I := I) (M := M) (F := F) (n := n))))).congr
      fun f ↦ chartJet_apply f x ⟨m, hm⟩)

/-- Chart derivatives determine a vector-valued map, already through their zeroth entries. -/
theorem chartJet_injective :
    Function.Injective (chartJet (I := I) (M := M) (F := F) (n := n)) := by
  intro f g h
  ext x
  have hx := congrArg (fun j ↦ j x ⟨0, by simp⟩ ⟨extChartAt I x x,
    mem_extChartAt_target x⟩ 0) h
  rw [chartJet_apply f x ⟨0, by simp⟩, chartJet_apply g x ⟨0, by simp⟩] at hx
  let z : (extChartAt I x).target := ⟨extChartAt I x x, mem_extChartAt_target x⟩
  have hf := chartIteratedFDeriv_zero_apply f x z 0
  have hg := chartIteratedFDeriv_zero_apply g x z 0
  simpa only [z, extChartAt_to_inv] using hf.symm.trans (hx.trans hg)

section Limits

variable [IsRCLikeNormedField 𝕜] [LocallyCompactSpace E] [I.Boundaryless]
  {r : ℕ∞} [IsManifold I (r : ℕ∞ω) M]

/-- Recover a chart representative of a limiting chart jet using open-domain completeness. -/
private theorem contDiffOn_chartJet_limit
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → C^(r : ℕ∞ω)⟮I, M; 𝓘(𝕜, F), F⟯}
    {g : ∀ (x : M) (m : {m : ℕ // m ≤ (r : ℕ∞ω)}),
      C((extChartAt I x).target, E [×(m : ℕ)]→L[𝕜] F)}
    (hg : Tendsto (fun i ↦ chartJet (f i)) l (𝓝 g))
    {h : M → F} (hpoint : ∀ y, Tendsto (fun i ↦ f i y) l (𝓝 (h y))) (x : M) :
    ContDiffOn 𝕜 (r : ℕ∞ω) (h ∘ (extChartAt I x).symm) (extChartAt I x).target ∧
      ∀ (m : ℕ) (hm : m ≤ (r : ℕ∞ω)) (z : (extChartAt I x).target),
        iteratedFDerivWithin 𝕜 m (h ∘ (extChartAt I x).symm)
          (extChartAt I x).target z = g x ⟨m, hm⟩ z := by
  let U : TopologicalSpace.Opens E := ⟨_, isOpen_extChartAt_target (I := I) x⟩
  let fc (i : ι) : C^(r : ℕ∞ω)⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯ :=
    ⟨fun z ↦ f i ((extChartAt I x).symm z), fun z ↦ by
      apply (contMDiffAt_subtype_iff (U := U)
        (f := f i ∘ (extChartAt I x).symm)).mpr
      have hf := contDiffOn_comp_extend_symm (f i) (IsManifold.chart_mem_maximalAtlas x)
      exact ((hf z z.2).contDiffAt (U.isOpen.mem_nhds z.2)).contMDiffAt⟩
  have hjet (i : ι) : openWeakWhitneyJet U (fc i) = fun m ↦ chartJet (f i) x m := by
    funext m
    apply ContinuousMap.ext
    intro z
    rw [openWeakWhitneyJet_apply, openIteratedFDerivContinuousMap_apply,
      chartJet_apply (f i) x m, chartIteratedFDeriv_self_target_apply]
    apply iteratedFDerivWithin_congr _ z.2
    intro y hy
    exact Subtype.val_injective.extend_apply (fc i) (fun _ ↦ 0) ⟨y, hy⟩
  have hconv : Tendsto (fun i ↦ openWeakWhitneyJet U (fc i)) l (𝓝 (g x)) := by
    -- The open source and extended chart target have the same underlying set; their
    -- dependent continuous-map types need to be reconciled before comparing the jets.
    convert! (tendsto_pi_nhds.1 hg) x using 1
    exact funext hjet
  obtain ⟨H, hH⟩ := exists_openWeakWhitneyJet_eq_of_tendsto U hconv
  have heq : EqOn (Function.extend Subtype.val H (fun _ ↦ 0))
      (h ∘ (extChartAt I x).symm) U := by
    intro y hy
    have hc : Tendsto fc l (𝓝 H) :=
      (isEmbedding_openWeakWhitneyJet U).isInducing.tendsto_nhds_iff.mpr
        (by simpa only [Function.comp_def, hH] using hconv)
    have hv := (continuous_eval_const_manifoldWeakWhitney
      (I := 𝓘(𝕜, E)) (J := 𝓘(𝕜, F)) (⟨y, hy⟩ : U)).tendsto H |>.comp hc
    have hv' : H ⟨y, hy⟩ = h ((extChartAt I x).symm y) :=
      tendsto_nhds_unique hv (hpoint _)
    exact (Subtype.val_injective.extend_apply H (fun _ ↦ 0) ⟨y, hy⟩).trans hv'
  refine ⟨(contDiffOn_extend U H (fun _ ↦ 0)).congr heq.symm, fun m hm z ↦ ?_⟩
  have hz : iteratedFDerivWithin 𝕜 m (Function.extend Subtype.val H (fun _ ↦ 0)) U z =
      g x ⟨m, hm⟩ z := by
    simpa only [openWeakWhitneyJet_apply, openIteratedFDerivContinuousMap_apply] using
      congrArg (fun j ↦ j ⟨m, hm⟩ z) hH
  simpa only [U, TopologicalSpace.Opens.coe_mk] using
    (iteratedFDerivWithin_congr (𝕜 := 𝕜) (n := m) heq z.2).symm.trans hz

/-- A limit of chart jets comes from a native map. Finite and smooth regularity are allowed,
and no target completeness is needed when the coefficient limits are supplied. -/
theorem exists_chartJet_eq_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → C^(r : ℕ∞ω)⟮I, M; 𝓘(𝕜, F), F⟯}
    {g : ∀ (x : M) (m : {m : ℕ // m ≤ (r : ℕ∞ω)}),
      C((extChartAt I x).target, E [×(m : ℕ)]→L[𝕜] F)}
    (hg : Tendsto (fun i ↦ chartJet (f i)) l (𝓝 g)) :
    ∃ h : C^(r : ℕ∞ω)⟮I, M; 𝓘(𝕜, F), F⟯, chartJet h = g := by
  classical
  let h : M → F := fun x ↦ g x ⟨0, by simp⟩ ⟨extChartAt I x x,
    mem_extChartAt_target x⟩ 0
  have hpoint (x : M) : Tendsto (fun i ↦ f i x) l (𝓝 (h x)) := by
    have ht := (((continuous_eval_const (0 : Fin 0 → E)).tendsto _).comp
      ((continuous_eval_const ⟨extChartAt I x x,
        mem_extChartAt_target x⟩).tendsto _)).comp
          ((tendsto_pi_nhds.1 ((tendsto_pi_nhds.1 hg) x)) ⟨0, by simp⟩)
    refine ht.congr' (Eventually.of_forall fun i ↦ ?_)
    simp only [Function.comp_def]
    rw [chartJet_apply (f i) x ⟨0, by simp⟩]
    -- Reconcile the normalized jet target with the native chart-derivative target.
    convert! chartIteratedFDeriv_zero_apply (f i) x
      ⟨extChartAt I x x, mem_extChartAt_target x⟩ 0 using 1
    exact (congrArg (f i) (extChartAt_to_inv x)).symm
  have hchart := contDiffOn_chartJet_limit hg hpoint
  have hsmooth : ContMDiff I 𝓘(𝕜, F) (r : ℕ∞ω) h := by
    intro x
    have hc := (hchart x).1
    have heq : h =ᶠ[𝓝 x] (h ∘ (extChartAt I x).symm) ∘ extChartAt I x := by
      filter_upwards [extChartAt_source_mem_nhds (I := I) x] with y hy
      simp only [Function.comp_apply, (extChartAt I x).left_inv hy]
    apply ContMDiffAt.congr_of_eventuallyEq _ heq
    exact ((hc _ (mem_extChartAt_target x)).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).contMDiffAt.comp x
        contMDiffAt_extChartAt
  let H : C^(r : ℕ∞ω)⟮I, M; 𝓘(𝕜, F), F⟯ := ⟨h, hsmooth⟩
  refine ⟨H, funext fun x ↦ funext fun m ↦ ContinuousMap.ext fun z ↦ ?_⟩
  exact (congrArg (fun j ↦ j z) (chartJet_apply H x m)).trans
    ((chartIteratedFDeriv_self_target_apply H x m m.2 z).trans ((hchart x).2 m m.2 z))

/-- The chart jet has closed image in the product of its compact-open derivative spaces. -/
theorem isClosedEmbedding_chartJet :
    IsClosedEmbedding (chartJet (I := I) (M := M) (F := F) (n := (r : ℕ∞ω))) := by
  refine ⟨⟨isInducing_chartJet, chartJet_injective⟩,
    isClosed_of_closure_subset fun g hg ↦ ?_⟩
  let l := Filter.comap (Subtype.val : range (chartJet (I := I) (M := M)
    (F := F) (n := (r : ℕ∞ω))) → _) (𝓝 g)
  have : l.NeBot := mem_closure_iff_comap_neBot.1 hg
  let f := fun z : range (chartJet (I := I) (M := M) (F := F) (n := (r : ℕ∞ω))) ↦
    Classical.choose z.property
  have hf : (fun z ↦ chartJet (f z)) = Subtype.val :=
    funext fun z ↦ Classical.choose_spec z.property
  exact exists_chartJet_eq_of_tendsto (l := l) (f := f) (by rw [hf]; exact tendsto_comap)

/-- Completeness for the additive uniformity of the native weak Whitney topology, for any
finite or smooth regularity and complete vector target. -/
theorem completeSpace_manifoldWeakWhitney [CompleteSpace F] :
    let _ := IsTopologicalAddGroup.rightUniformSpace C^(r : ℕ∞ω)⟮I, M; 𝓘(𝕜, F), F⟯
    CompleteSpace C^(r : ℕ∞ω)⟮I, M; 𝓘(𝕜, F), F⟯ := by
  let _ := IsTopologicalAddGroup.rightUniformSpace C^(r : ℕ∞ω)⟮I, M; 𝓘(𝕜, F), F⟯
  let _ : IsUniformAddGroup C^(r : ℕ∞ω)⟮I, M; 𝓘(𝕜, F), F⟯ := isUniformAddGroup_of_addCommGroup
  let _ (x : M) : LocallyCompactSpace (extChartAt I x).target :=
    (isOpen_extChartAt_target x).locallyCompactSpace
  have (x : M) (m : ℕ) :
      CompleteSpace C(↥(I.target ∩ I.symm ⁻¹' (chartAt H x).target), E [×m]→L[𝕜] F) := by
    infer_instance
  have hj := AddMonoidHom.isUniformInducing_of_isInducing
    (f := (chartJet (I := I) (M := M) (F := F) (n := (r : ℕ∞ω))).toAddMonoidHom)
    (isInducing_chartJet (I := I) (M := M) (F := F) (n := (r : ℕ∞ω)))
  exact (completeSpace_iff_isComplete_range hj).2
    (isClosedEmbedding_chartJet (I := I) (M := M) (F := F) (r := r)).isClosed_range.isComplete

end Limits

end ContMDiffMap

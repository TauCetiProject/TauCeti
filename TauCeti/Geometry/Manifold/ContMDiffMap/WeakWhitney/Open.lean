/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
public import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
public import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney.Complete
public import TauCeti.Geometry.Manifold.ExtChartAt
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# Weak Whitney jets on open subsets of normed spaces

The native manifold map carrier on an open subset records derivatives in its inherited
charts. These jets can equivalently be read on the open subset itself, using an arbitrary
extension to the ambient normed space and differentiating within the open subset. The open-source
jet induces precisely the existing manifold weak Whitney topology, including when the source is
empty. Its induced uniformity is compatible with that topology.

For real or complex coefficients and a locally compact ambient source, locally uniform limits
of Taylor coefficients give a closed jet image. The map space is therefore complete when the
target is complete, for finite and smooth regularity; analytic regularity is excluded. With an
explicit sigma-compactness hypothesis on the open source, the derivative uniformity is countably
generated and the native topology is metrizable. No finite-dimensionality or separability of
the target is needed.

This supplies open coefficient-map spaces used in local bundle frames. Cover independence,
completeness of spaces of global sections, and Montel properties require further bundle gluing.

The topology convention follows M. Hirsch, *Differential Topology*, Chapter 2, §1; the
closed-jet argument uses Mathlib's derivative-limit theorem on open sets.
-/

public section

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped Uniformity ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω} (U : Opens E)

/-- The derivative of a native map on an open source, bundled as a continuous map on that source.
The arbitrary values of the chosen extension outside the source do not affect its derivatives. -/
def openIteratedFDerivContinuousMap (f : C^n⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯)
    (m : ℕ) (hm : m ≤ n) : C(U, E [×m]→L[𝕜] F) :=
  ⟨fun x ↦ iteratedFDerivWithin 𝕜 m (Function.extend Subtype.val f (fun _ ↦ 0)) U x,
    ((contDiffOn_extend U f (fun _ ↦ 0)).continuousOn_iteratedFDerivWithin hm
      U.isOpen.uniqueDiffOn).domRestrict⟩

/-- Evaluation of the open-source derivative map. -/
@[simp]
theorem openIteratedFDerivContinuousMap_apply
    (f : C^n⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯) (m : ℕ) (hm : m ≤ n) (z : U) :
    openIteratedFDerivContinuousMap U f m hm z =
      iteratedFDerivWithin 𝕜 m (Function.extend Subtype.val f (fun _ ↦ 0)) U z := by
  rfl

/-- Open-source jets agree with the native inherited chart jets. -/
theorem chartIteratedFDeriv_opens_apply
    (f : C^n⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯) (x : U) (m : ℕ) (hm : m ≤ n)
    (z : (extChartAt 𝓘(𝕜, E) x).target) :
    chartIteratedFDeriv f x m hm z = openIteratedFDerivContinuousMap U f m hm
      ⟨z, by
        -- Opens uses a membership carrier; expose its underlying set for the target equality.
        change (z : E) ∈ (U : Set E)
        rw [← Opens.extChartAt_opens_target (𝕜 := 𝕜) U x]
        exact z.2⟩ := by
  rw [chartIteratedFDeriv_self_target_apply, openIteratedFDerivContinuousMap_apply]
  simp only [Opens.extChartAt_opens_target]
  apply iteratedFDerivWithin_congr _ (by
        rw [← Opens.extChartAt_opens_target (𝕜 := 𝕜) U x]
        exact z.2)
  intro y hy
  have hc : ((extChartAt 𝓘(𝕜, E) x).symm y : E) = y := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, id_eq] using
      U.coe_extChartAt_symm_apply (I := 𝓘(𝕜, E)) x
        (by simpa only [Opens.extChartAt_opens_target] using hy)
  have he : (extChartAt 𝓘(𝕜, E) x).symm y = (⟨y, hy⟩ : U) := Subtype.ext hc
  simp only [Function.comp_apply, he]
  exact (Subtype.val_injective.extend_apply f (fun _ ↦ 0) ⟨y, hy⟩).symm

/-- The family of all open-source derivatives through the prescribed regularity. -/
def openWeakWhitneyJet (f : C^n⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯) :
    (m : {m : ℕ // m ≤ n}) → C(U, E [×(m : ℕ)]→L[𝕜] F) :=
  fun m ↦ openIteratedFDerivContinuousMap U f m m.2

/-- Evaluation of the family of open-source derivatives. -/
@[simp]
theorem openWeakWhitneyJet_apply (f : C^n⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯)
    (m : {m : ℕ // m ≤ n}) :
    openWeakWhitneyJet U f m = openIteratedFDerivContinuousMap U f m m.2 := by
  rfl

/-- Every native chart-derivative map is open-source differentiation followed by restriction
along the canonical chart-target homeomorphism. -/
theorem chartIteratedFDeriv_opens_eq
    (f : C^n⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯) (x : U) (m : ℕ) (hm : m ≤ n) :
    chartIteratedFDeriv f x m hm = (openIteratedFDerivContinuousMap U f m hm).comp
      ⟨Opens.openChartTargetHomeomorph (𝕜 := 𝕜) U x,
        (Opens.openChartTargetHomeomorph (𝕜 := 𝕜) U x).continuous⟩ := by
  apply ContinuousMap.ext
  intro z
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  convert chartIteratedFDeriv_opens_apply U f x m hm z using 1
  congr 1
  apply Subtype.ext
  exact Opens.coe_openChartTargetHomeomorph_apply (𝕜 := 𝕜) U x z

/-- Conversely, any one inherited chart records every open-source derivative. -/
theorem openIteratedFDerivContinuousMap_eq
    (f : C^n⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯) (x : U) (m : ℕ) (hm : m ≤ n) :
    openIteratedFDerivContinuousMap U f m hm = (chartIteratedFDeriv f x m hm).comp
      ⟨(Opens.openChartTargetHomeomorph (𝕜 := 𝕜) U x).symm,
        (Opens.openChartTargetHomeomorph (𝕜 := 𝕜) U x).symm.continuous⟩ := by
  rw [chartIteratedFDeriv_opens_eq]
  apply ContinuousMap.ext
  intro z
  exact congrArg (openIteratedFDerivContinuousMap U f m hm)
    ((Opens.openChartTargetHomeomorph (𝕜 := 𝕜) U x).apply_symm_apply z).symm

/-- The full open-source jet is injective, since its zeroth coefficient recovers the values. -/
theorem openWeakWhitneyJet_injective :
    Function.Injective (openWeakWhitneyJet (𝕜 := 𝕜) (F := F) (n := n) U) := by
  intro f g h
  ext x
  have hx := congrArg (fun z ↦ z ⟨0, by simp⟩ x (0 : Fin 0 → E)) h
  simpa only [openWeakWhitneyJet, openIteratedFDerivContinuousMap_apply,
    iteratedFDerivWithin_zero_apply, Subtype.val_injective.extend_apply] using hx

/-- The open-source jet is continuous for the existing manifold weak Whitney topology. -/
theorem continuous_openWeakWhitneyJet :
    Continuous (openWeakWhitneyJet (𝕜 := 𝕜) (F := F) (n := n) U) := by
  classical
  rcases isEmpty_or_nonempty U with hU | hU
  · have := hU
    have heq : openWeakWhitneyJet (𝕜 := 𝕜) (F := F) (n := n) U = fun _ ↦ 0 :=
      funext fun _ ↦ Subsingleton.elim _ _
    rw [heq]
    exact continuous_const
  · obtain ⟨x⟩ := hU
    apply continuous_pi
    intro m
    let toTarget : C(U, (extChartAt 𝓘(𝕜, E) x).target) :=
      ⟨(Opens.openChartTargetHomeomorph (𝕜 := 𝕜) U x).symm,
        (Opens.openChartTargetHomeomorph (𝕜 := 𝕜) U x).symm.continuous⟩
    exact ((ContinuousMap.continuous_precomp toTarget).comp
      (continuous_chartIteratedFDeriv x m m.2)).congr fun f ↦
        (openIteratedFDerivContinuousMap_eq U f x m m.2).symm

/-- The open-source jet induces precisely the native manifold weak Whitney topology. -/
theorem isInducing_openWeakWhitneyJet :
    IsInducing (openWeakWhitneyJet (𝕜 := 𝕜) (F := F) (n := n) U) := by
  constructor
  apply le_antisymm
  · exact (continuous_openWeakWhitneyJet U).le_induced
  · rw [← continuous_id_iff_le]
    -- Test continuity with the jet-induced topology on the domain, retaining the native topology
    -- on the codomain. Every inherited chart jet is a precomposition of an open-source jet.
    let _ : TopologicalSpace C^n⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯ :=
      TopologicalSpace.induced (openWeakWhitneyJet (𝕜 := 𝕜) (F := F) (n := n) U) inferInstance
    apply continuous_manifoldWeakWhitney_iff_compact_chartIteratedFDeriv.mpr
    intro x m hm K
    let toSource : C((extChartAt 𝓘(𝕜, E) x).target, U) :=
      ⟨Opens.openChartTargetHomeomorph (𝕜 := 𝕜) U x,
        (Opens.openChartTargetHomeomorph (𝕜 := 𝕜) U x).continuous⟩
    have h := (ContinuousMap.continuous_restrict (K : Set _)).comp
      ((ContinuousMap.continuous_precomp toSource).comp
        ((continuous_apply (⟨m, hm⟩ : {m : ℕ // m ≤ n})).comp
          (continuous_induced_dom : Continuous
            (openWeakWhitneyJet (𝕜 := 𝕜) (F := F) (n := n) U))))
    exact h.congr fun f ↦ congrArg (fun g ↦ g.restrict (K : Set _))
      (chartIteratedFDeriv_opens_eq U f x m hm).symm

/-- The open-source jet embeds the existing weak Whitney map space. -/
theorem isEmbedding_openWeakWhitneyJet :
    IsEmbedding (openWeakWhitneyJet (𝕜 := 𝕜) (F := F) (n := n) U) :=
  ⟨isInducing_openWeakWhitneyJet U, openWeakWhitneyJet_injective U⟩

/-- The compact-open derivative uniformity is compatible with the existing weak Whitney topology
on native maps from an open source. -/
@[instance_reducible]
def instUniformSpaceOpenWeakWhitney : UniformSpace C^n⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯ :=
  (isEmbedding_openWeakWhitneyJet U).comapUniformSpace (openWeakWhitneyJet U)

scoped[TauCeti.ManifoldWeakWhitney] attribute [instance]
  ContMDiffMap.instUniformSpaceOpenWeakWhitney

/-- The open-source jet is a uniform embedding for the compatible derivative uniformity. -/
theorem isUniformEmbedding_openWeakWhitneyJet :
    IsUniformEmbedding (openWeakWhitneyJet (𝕜 := 𝕜) (F := F) (n := n) U) :=
  Embedding.to_isUniformEmbedding _ (isEmbedding_openWeakWhitneyJet U)

/-- A sigma-compact open source gives a countably generated derivative uniformity. Sigma-compactness
of the source is assumed explicitly; no countability of the target as a set is required. -/
theorem isCountablyGenerated_openWeakWhitney [LocallyCompactSpace E] [SigmaCompactSpace U] :
    IsCountablyGenerated (𝓤 C^n⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯) := by
  have : LocallyCompactSpace U := by
    simpa only [← SetLike.coe_sort_coe] using U.isOpen.locallyCompactSpace
  rw [← (isUniformEmbedding_openWeakWhitneyJet U).isUniformInducing.comap_uniformity]
  infer_instance

/-- For a sigma-compact open source, the native weak Whitney topology is metrizable. -/
theorem metrizableSpace_openWeakWhitney [LocallyCompactSpace E] [SigmaCompactSpace U] :
    MetrizableSpace C^n⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯ := by
  have := isCountablyGenerated_openWeakWhitney (𝕜 := 𝕜) (F := F) (n := n) U
  infer_instance

scoped[TauCeti.ManifoldWeakWhitney] attribute [instance]
  ContMDiffMap.isCountablyGenerated_openWeakWhitney ContMDiffMap.metrizableSpace_openWeakWhitney

section Complete

variable [IsRCLikeNormedField 𝕜] [LocallyCompactSpace E] {r : ℕ∞}

/-- A compact-open limit of open-source jets is the jet of a native map. This includes finite
and smooth regularity, excludes analytic regularity, and permits an empty source. -/
theorem exists_openWeakWhitneyJet_eq_of_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → C^(r : ℕ∞ω)⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯}
    {g : (m : {m : ℕ // m ≤ (r : ℕ∞ω)}) → C(U, E [×(m : ℕ)]→L[𝕜] F)}
    (hg : Tendsto (fun i ↦ openWeakWhitneyJet U (f i)) l (𝓝 g)) :
    ∃ h : C^(r : ℕ∞ω)⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯, openWeakWhitneyJet U h = g := by
  classical
  have : LocallyCompactSpace U := by
    simpa only [← SetLike.coe_sort_coe] using U.isOpen.locallyCompactSpace
  let p : E → FormalMultilinearSeries 𝕜 E F := fun x m ↦
    if hm : (m : ℕ∞ω) ≤ r then Function.extend Subtype.val (g ⟨m, hm⟩) (fun _ ↦ 0) x else 0
  have hp (m : ℕ) (hm : (m : ℕ∞ω) ≤ r) (x : U) : p x m = g ⟨m, hm⟩ x := by
    simp only [p, dite_eq_left hm, Subtype.val_injective.extend_apply]
  have hlim (m : ℕ) (hm : (m : ℕ∞ω) ≤ r) :
      TendstoLocallyUniformlyOn
        (fun i x ↦ ftaylorSeriesWithin 𝕜 (Function.extend Subtype.val (f i) (fun _ ↦ 0)) U x m)
        (fun x ↦ p x m) l U := by
    apply tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr
    have ht := (tendsto_pi_nhds.1 hg) ⟨m, hm⟩
    have ht' := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 ht
    simp only [openWeakWhitneyJet, openIteratedFDerivContinuousMap_apply] at ht'
    simpa only [← SetLike.coe_sort_coe, Function.comp_def, hp m hm, ftaylorSeriesWithin] using ht'
  let h : E → F := fun x ↦ (p x 0).curry0
  have hh : HasFTaylorSeriesUpToOn (r : ℕ∞ω) h p U :=
    HasFTaylorSeriesUpToOn.of_tendstoLocallyUniformlyOn U.isOpen
      (fun i ↦ (contDiffOn_extend U (f i) (fun _ ↦ 0)).ftaylorSeriesWithin
        U.isOpen.uniqueDiffOn) hlim fun x hx ↦ by
      have ht := ((continuousMultilinearCurryFin0 𝕜 E F).continuous.tendsto (p x 0)).comp
        ((hlim 0 (by simp)).tendsto_at hx)
      simpa only [h, ftaylorSeriesWithin, Function.comp_def,
        iteratedFDerivWithin_zero_eq_comp, continuousMultilinearCurryFin0_apply,
        ContinuousMultilinearMap.curry0_apply, continuousMultilinearCurryFin0_symm_apply_apply]
        using ht
  let H : C^(r : ℕ∞ω)⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯ :=
    ⟨fun x ↦ h x, fun x ↦ contMDiffAt_subtype_iff.mpr
      ((hh.contDiffOn x x.2).contDiffAt (U.isOpen.mem_nhds x.2)).contMDiffAt⟩
  refine ⟨H, funext fun m ↦ ?_⟩
  apply ContinuousMap.ext
  intro x
  rw [openWeakWhitneyJet, openIteratedFDerivContinuousMap_apply]
  have heq : EqOn (Function.extend Subtype.val H (fun _ ↦ 0)) h U := by
    intro y hy
    exact Subtype.val_injective.extend_apply H (fun _ ↦ 0) ⟨y, hy⟩
  rw [iteratedFDerivWithin_congr heq x.2]
  exact (hh.eq_iteratedFDerivWithin_of_uniqueDiffOn m.2 U.isOpen.uniqueDiffOn x.2).symm.trans
    (hp m m.2 x)

/-- The native weak Whitney map space on an open source is the closed image of its derivative jet.
No completeness of the target is required for this closed-image statement. -/
theorem isClosedEmbedding_openWeakWhitneyJet :
    IsClosedEmbedding (openWeakWhitneyJet (𝕜 := 𝕜) (F := F) (n := (r : ℕ∞ω)) U) := by
  refine ⟨isEmbedding_openWeakWhitneyJet U, isClosed_of_closure_subset fun g hg ↦ ?_⟩
  let l := Filter.comap (Subtype.val : range (openWeakWhitneyJet (𝕜 := 𝕜)
    (F := F) (n := (r : ℕ∞ω)) U) → _) (𝓝 g)
  have : l.NeBot := mem_closure_iff_comap_neBot.1 hg
  let f := fun z : range (openWeakWhitneyJet (𝕜 := 𝕜) (F := F) (n := (r : ℕ∞ω)) U) ↦
    Classical.choose z.property
  have hf : (fun z ↦ openWeakWhitneyJet U (f z)) = Subtype.val :=
    funext fun z ↦ Classical.choose_spec z.property
  exact exists_openWeakWhitneyJet_eq_of_tendsto U (l := l) (f := f)
    (by rw [hf]; exact tendsto_comap)

/-- For a complete target, native finite-order and smooth maps on an open source form a complete
space in their existing weak Whitney topology and its compatible derivative uniformity. -/
theorem completeSpace_openWeakWhitney [CompleteSpace F] :
    CompleteSpace C^(r : ℕ∞ω)⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯ := by
  have : LocallyCompactSpace U := by
    simpa only [← SetLike.coe_sort_coe] using U.isOpen.locallyCompactSpace
  exact (completeSpace_iff_isComplete_range
    (isUniformEmbedding_openWeakWhitneyJet U).isUniformInducing).2
      (isClosedEmbedding_openWeakWhitneyJet U).isClosed_range.isComplete

/-- Completeness at every finite or smooth exponent, with the native `LEInfty` class excluding
analytic regularity. -/
theorem instCompleteSpaceOpenWeakWhitney [CompleteSpace F] [hn : ENat.LEInfty n] :
    CompleteSpace C^n⟮𝓘(𝕜, E), U; 𝓘(𝕜, F), F⟯ := by
  obtain ⟨q, rfl⟩ := WithTop.ne_top_iff_exists.1
    (ne_top_of_le_ne_top (by simp : (∞ : ℕ∞ω) ≠ ⊤) hn.out)
  exact completeSpace_openWeakWhitney U (r := q)

scoped[TauCeti.ManifoldWeakWhitney] attribute [instance]
  ContMDiffMap.instCompleteSpaceOpenWeakWhitney

end Complete

end ContMDiffMap

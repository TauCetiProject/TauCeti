/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation

/-!
# Pairing maps in the manifold weak Whitney topology

Pairing `C^n⟮I, M; J, N⟯ × C^n⟮I, M; J', N'⟯ → C^n⟮I, M; J.prod J', N × N'⟯`, `(f, g) ↦ (f, g)`,
is continuous for the weak Whitney topologies. No local compactness is needed.

A chart of `N × N'` at a pair of points is the product of the charts of the factors, and a
coordinate derivative of a pair is the pair of the coordinate derivatives
(`ContMDiffMap.iteratedFDerivWithin_extChartAt_prodMk`). On the compact set of a derivative test,
the coordinate derivatives of maps near `f₀` converge uniformly to those of `f₀`
(`ContMDiffMap.tendstoUniformlyOn_iteratedFDerivWithin_extChartAt`), and the coordinate
derivatives of the pair of `f₀` and `g₀` stay in a compact subset of the open set of the test,
which gives continuity.
Together with composition (`ContMDiffMap.continuous_comp_manifoldWeakWhitney`, when the models
of the source and of all the variables are locally compact, or
`ContMDiffMap.continuous_postcomp_manifoldWeakWhitney`, when the outer map is fixed and the
source model is locally compact), this makes the pointwise application of a fixed smooth map of
several variables continuous. For instance, pointwise division of maps into a Lie group, and
subtraction of maps into an additive Lie group, are continuous.

## Main results

* `ContMDiffMap.iteratedFDerivWithin_extChartAt_prodMk`: a coordinate derivative of a pair of maps,
  read in the product chart, is the pair of the coordinate derivatives.
* `ContMDiffMap.continuous_prodMk_manifoldWeakWhitney`: pairing is jointly continuous.
* `ContMDiffMap.continuous_div_manifoldWeakWhitney_of_lieGroup`,
  `ContMDiffMap.continuous_sub_manifoldWeakWhitney_of_lieAddGroup`: pointwise division of maps
  into a Lie group, and subtraction of maps into an additive Lie group, are jointly continuous.

The weak topology is treated in M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1.
-/

public section

open Set Filter Topology
open scoped Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']

variable [IsManifold I n M] [IsManifold J n N] [IsManifold J' n N']

/-- A coordinate derivative of a pair of maps, read in a product chart, is the pair of the
coordinate derivatives of the two maps. -/
theorem iteratedFDerivWithin_extChartAt_prodMk (f : C^n⟮I, M; J, N⟯) (g : C^n⟮I, M; J', N'⟯)
    {x : M} {y : N × N'} {w : E} (hw : w ∈ (extChartAt I x).target)
    (hf : f ((extChartAt I x).symm w) ∈ (extChartAt J y.1).source)
    (hg : g ((extChartAt I x).symm w) ∈ (extChartAt J' y.2).source) {m : ℕ} (hm : m ≤ n) :
    iteratedFDerivWithin 𝕜 m (extChartAt (J.prod J') y ∘ f.prodMk g ∘ (extChartAt I x).symm)
        (extChartAt I x).target w =
      (iteratedFDerivWithin 𝕜 m (extChartAt J y.1 ∘ f ∘ (extChartAt I x).symm)
          (extChartAt I x).target w).prod
        (iteratedFDerivWithin 𝕜 m (extChartAt J' y.2 ∘ g ∘ (extChartAt I x).symm)
          (extChartAt I x).target w) := by
  have h : extChartAt (J.prod J') y ∘ f.prodMk g ∘ (extChartAt I x).symm =
      fun v ↦ ((extChartAt J y.1 ∘ f ∘ (extChartAt I x).symm) v,
        (extChartAt J' y.2 ∘ g ∘ (extChartAt I x).symm) v) := by
    funext v
    simp only [extChartAt_prod, Function.comp_apply, PartialEquiv.prod_coe, prodMk_apply]
  rw [h]
  exact iteratedFDerivWithin_prodMk (f.contDiffWithinAt_extChartAt hw hf)
    (g.contDiffWithinAt_extChartAt hw hg) (uniqueDiffOn_extChartAt_target x) hw hm

/-- If `f₀` is visible in a target chart on a compact set `K` of a source chart target, then
every map near `f₀` is visible there on `K`, with `m`-th coordinate derivatives uniformly
`δ`-close to those of `f₀` on `K`. -/
private theorem eventually_forall_mem_source_and_dist_iteratedFDerivWithin_lt
    {f₀ : C^n⟮I, M; J, N⟯} {x : M} {y : N} {K : Set (extChartAt I x).target} (hK : IsCompact K)
    (hK₀ : ∀ w ∈ K, f₀ ((extChartAt I x).symm w) ∈ (extChartAt J y).source) {m : ℕ} (hm : m ≤ n)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ f : C^n⟮I, M; J, N⟯ in 𝓝 f₀, ∀ w ∈ K, f ((extChartAt I x).symm w) ∈ (extChartAt J y).source ∧
      dist (iteratedFDerivWithin 𝕜 m (extChartAt J y ∘ f ∘ (extChartAt I x).symm)
          (extChartAt I x).target w)
        (iteratedFDerivWithin 𝕜 m (extChartAt J y ∘ f₀ ∘ (extChartAt I x).symm)
          (extChartAt I x).target w) < δ := by
  have hU := Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_iteratedFDerivWithin_extChartAt
    (hK.image continuous_subtypeVal) (image_subset_iff.mpr fun w _ ↦ w.property)
    (by rintro _ ⟨w, hw, rfl⟩; exact hK₀ w hw) hm) δ hδ
  have hT := (isOpen_chartJetSet (J := J) x y 0 (by simp) hK isOpen_univ).mem_nhds
    (mem_chartJetSet.mpr fun w hw ↦ ⟨hK₀ w hw, mem_univ _⟩)
  filter_upwards [hT, hU] with f hf hf' w hw
  rw [dist_comm]
  exact ⟨((mem_chartJetSet.mp hf) w hw).1, hf' w (mem_image_of_mem _ hw)⟩

/-- Pairing of `C^n` maps is jointly continuous for the manifold weak Whitney topologies. -/
theorem continuous_prodMk_manifoldWeakWhitney :
    Continuous (fun p : C^n⟮I, M; J, N⟯ × C^n⟮I, M; J', N'⟯ ↦ p.1.prodMk p.2) := by
  refine continuous_iff_continuousAt.mpr fun ⟨f₀, g₀⟩ ↦ ?_
  refine tendsto_manifoldWeakWhitney_iff.mpr fun x y m hm K hK V hV h₀ ↦ ?_
  have hsrc (w : (extChartAt I x).target) (hw : w ∈ K) :
      f₀ ((extChartAt I x).symm w) ∈ (extChartAt J y.1).source ∧
        g₀ ((extChartAt I x).symm w) ∈ (extChartAt J' y.2).source := by
    simpa only [extChartAt_prod, PartialEquiv.prod_source, prodMk_apply, mem_prod] using
      ((mem_chartJetSet.mp h₀) w hw).1
  let D (w : (extChartAt I x).target) := iteratedFDerivWithin 𝕜 m
    (extChartAt (J.prod J') y ∘ f₀.prodMk g₀ ∘ (extChartAt I x).symm) (extChartAt I x).target w
  -- On `K`, the coordinate derivative of `(f₀, g₀)` stays in a compact subset of the open set of
  -- the test, so a uniform neighbourhood of it stays in that open set.
  have hS : IsCompact (D '' K) :=
    hK.image_of_continuousOn fun w hw ↦ ((((f₀.prodMk g₀).contDiffWithinAt_extChartAt w.property
      ((mem_chartJetSet.mp h₀) w hw).1).continuousWithinAt_iteratedFDerivWithin
        (uniqueDiffOn_extChartAt_target x) hm w.property).comp
          continuous_subtypeVal.continuousWithinAt fun v _ ↦ v.property)
  have hSV : D '' K ⊆ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact ((mem_chartJetSet.mp h₀) w hw).2
  obtain ⟨δ, hδ, hδV⟩ := hS.exists_thickening_subset_open hV hSV
  -- Nearby maps stay visible in the factor charts on `K` and have nearby coordinate derivatives.
  rw [nhds_prod_eq]
  filter_upwards [(eventually_forall_mem_source_and_dist_iteratedFDerivWithin_lt hK
    (fun w hw ↦ (hsrc w hw).1) hm hδ).prod_mk
      (eventually_forall_mem_source_and_dist_iteratedFDerivWithin_lt hK
        (fun w hw ↦ (hsrc w hw).2) hm hδ)] with ⟨f, g⟩ ⟨hf, hg⟩
  refine mem_chartJetSet.mpr fun w hw ↦
    ⟨by simpa only [extChartAt_prod, PartialEquiv.prod_source, prodMk_apply, mem_prod] using
        And.intro (hf w hw).1 (hg w hw).1,
      hδV (Metric.mem_thickening_iff.mpr ⟨_, mem_image_of_mem D hw, ?_⟩)⟩
  dsimp only [D]
  rw [iteratedFDerivWithin_extChartAt_prodMk f g w.property (hf w hw).1 (hg w hw).1 hm,
    iteratedFDerivWithin_extChartAt_prodMk f₀ g₀ w.property (hsrc w hw).1 (hsrc w hw).2 hm]
  -- `ContinuousMultilinearMap.prodL` is an isometry, so the distance of the pairs is the larger
  -- of the distances of the components.
  exact (((ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin m ↦ E) F F').dist_map (_, _) (_, _)).trans
    Prod.dist_eq).trans_lt (max_lt (hf w hw).2 (hg w hw).2)


/-- Pointwise division of `C^n` maps into a Lie group is jointly continuous for the manifold weak
Whitney topologies, provided the models of the source and of the Lie group are locally compact:
it is pairing followed by composition with the division `ContMDiffMap.fst / ContMDiffMap.snd`.
For vector-valued maps, `ContMDiffMap.continuous_sub_manifoldWeakWhitney` needs no local
compactness. -/
@[to_additive
/-- Pointwise subtraction of `C^n` maps into an additive Lie group is jointly continuous for the
manifold weak Whitney topologies, provided the models of the source and of the Lie group are
locally compact: it is pairing followed by composition with the subtraction
`ContMDiffMap.fst - ContMDiffMap.snd`. For vector-valued maps,
`ContMDiffMap.continuous_sub_manifoldWeakWhitney` needs no local compactness. -/]
theorem continuous_div_manifoldWeakWhitney_of_lieGroup [LocallyCompactSpace E]
    [LocallyCompactSpace F] {L : Type*} [TopologicalSpace L] [ChartedSpace G L] [Group L]
    [LieGroup J n L] :
    Continuous (fun p : C^n⟮I, M; J, L⟯ × C^n⟮I, M; J, L⟯ ↦ p.1 / p.2) := by
  refine (continuous_comp_manifoldWeakWhitney.comp
    ((continuous_const (y := (fst / snd : C^n⟮J.prod J, L × L; J, L⟯))).prodMk
      continuous_prodMk_manifoldWeakWhitney)).congr fun p ↦
      ContMDiffMap.ext fun x ↦ ?_
  simp

end ContMDiffMap

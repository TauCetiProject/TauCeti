/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation

/-!
# Pairing maps in the manifold weak Whitney topology

Pairing `C^n⟮I, M; J, N⟯ × C^n⟮I, M; J', N'⟯ → C^n⟮I, M; J.prod J', N × N'⟯`, `(f, g) ↦ (f, g)`,
is continuous for the weak Whitney topologies. No local compactness is needed.

A chart of `N × N'` at a pair of points is the product of the charts of the factors, and a
coordinate derivative of a pair is the pair of the coordinate derivatives
(`ContMDiffMap.iteratedFDerivWithin_extChartAt_prodMk`). On the compact set of a derivative test,
the coordinate derivatives of maps near `f₀` converge uniformly to those of `f₀`
(`ContMDiffMap.tendstoUniformlyOn_iteratedFDerivWithin_extChartAt`), and the pair of derivatives
of `f₀` and `g₀` stays in a compact subset of the open set of the test, which gives continuity.
Together with composition (`ContMDiffMap.continuous_comp_manifoldWeakWhitney`, when the models
of the source and of all the variables are locally compact, or
`ContMDiffMap.continuous_postcomp_manifoldWeakWhitney`, when the outer map is fixed and the
source model is locally compact), this makes the pointwise application of a fixed smooth map of
several variables continuous.
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

/-- The pair of two `C^n` maps evaluates to the pair of their values. -/
@[simp]
theorem prodMk_apply (f : C^n⟮I, M; J, N⟯) (g : C^n⟮I, M; J', N'⟯) (x : M) :
    f.prodMk g x = (f x, g x) := rfl

/-- A pair of maps is visible in a product chart exactly when each map is visible in the
corresponding factor chart. -/
theorem prodMk_mem_extChartAt_prod_source_iff (f : C^n⟮I, M; J, N⟯) (g : C^n⟮I, M; J', N'⟯)
    {y : N × N'} {x : M} :
    f.prodMk g x ∈ (extChartAt (J.prod J') y).source ↔
      f x ∈ (extChartAt J y.1).source ∧ g x ∈ (extChartAt J' y.2).source := by
  simp only [extChartAt_prod, PartialEquiv.prod_source, prodMk_apply, mem_prod]

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

/-- Pairing of `C^n` maps is jointly continuous for the manifold weak Whitney topologies. -/
theorem continuous_prodMk_manifoldWeakWhitney :
    Continuous (fun p : C^n⟮I, M; J, N⟯ × C^n⟮I, M; J', N'⟯ ↦ p.1.prodMk p.2) := by
  refine continuous_iff_continuousAt.mpr fun ⟨f₀, g₀⟩ ↦ ?_
  refine tendsto_manifoldWeakWhitney_iff.mpr fun x y m hm K hK V hV h₀ ↦ ?_
  set ψ₁ := extChartAt J y.1
  set ψ₂ := extChartAt J' y.2
  have hsrc (w : (extChartAt I x).target) (hw : w ∈ K) :
      f₀ ((extChartAt I x).symm w) ∈ ψ₁.source ∧ g₀ ((extChartAt I x).symm w) ∈ ψ₂.source := by
    exact (prodMk_mem_extChartAt_prod_source_iff f₀ g₀).mp ((mem_chartJetSet.mp h₀) w hw).1
  set C : Set E := Subtype.val '' K
  have hC : IsCompact C := hK.image continuous_subtype_val
  have hCx : C ⊆ (extChartAt I x).target := image_subset_iff.mpr fun w _ ↦ w.2
  have hCy₁ : ∀ w ∈ C, f₀ ((extChartAt I x).symm w) ∈ ψ₁.source := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hsrc w hw).1
  have hCy₂ : ∀ w ∈ C, g₀ ((extChartAt I x).symm w) ∈ ψ₂.source := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hsrc w hw).2
  let D₁ : C^n⟮I, M; J, N⟯ → E → E [×m]→L[𝕜] F := fun f w ↦
    iteratedFDerivWithin 𝕜 m (ψ₁ ∘ f ∘ (extChartAt I x).symm) (extChartAt I x).target w
  let D₂ : C^n⟮I, M; J', N'⟯ → E → E [×m]→L[𝕜] F' := fun g w ↦
    iteratedFDerivWithin 𝕜 m (ψ₂ ∘ g ∘ (extChartAt I x).symm) (extChartAt I x).target w
  -- On `C`, the pair of the coordinate derivatives of `f₀` and `g₀` stays in a compact subset of
  -- the open set of the test, so a uniform neighbourhood of it stays in that open set.
  let L := ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin m ↦ E) F F'
  have hS : IsCompact ((fun w ↦ (D₁ f₀ w, D₂ g₀ w)) '' C) := by
    refine hC.image_of_continuousOn (ContinuousOn.prodMk (fun w hw ↦ ?_) (fun w hw ↦ ?_))
    · exact ((f₀.contDiffWithinAt_extChartAt (hCx hw) (hCy₁ w hw)
        ).continuousWithinAt_iteratedFDerivWithin (uniqueDiffOn_extChartAt_target x) hm
          (hCx hw)).mono hCx
    · exact ((g₀.contDiffWithinAt_extChartAt (hCx hw) (hCy₂ w hw)
        ).continuousWithinAt_iteratedFDerivWithin (uniqueDiffOn_extChartAt_target x) hm
          (hCx hw)).mono hCx
  have hSV : (fun w ↦ (D₁ f₀ w, D₂ g₀ w)) '' C ⊆ L ⁻¹' V := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have h := ((mem_chartJetSet.mp h₀) w hw).2
    rw [iteratedFDerivWithin_extChartAt_prodMk f₀ g₀ w.2 (hsrc w hw).1 (hsrc w hw).2 hm] at h
    exact h
  obtain ⟨δ, hδ, hδV⟩ := hS.exists_thickening_subset_open (hV.preimage L.continuous) hSV
  -- Nearby maps stay visible in the factor charts on `K` and have nearby coordinate derivatives.
  have hT₁ : ∀ᶠ f in 𝓝 f₀, f ∈ chartJetSet (J := J) (n := n) x y.1 0 K univ :=
    (isOpen_chartJetSet x y.1 0 (by simp) hK isOpen_univ).mem_nhds
      (mem_chartJetSet.mpr fun w hw ↦ ⟨(hsrc w hw).1, mem_univ _⟩)
  have hT₂ : ∀ᶠ g in 𝓝 g₀, g ∈ chartJetSet (J := J') (n := n) x y.2 0 K univ :=
    (isOpen_chartJetSet x y.2 0 (by simp) hK isOpen_univ).mem_nhds
      (mem_chartJetSet.mpr fun w hw ↦ ⟨(hsrc w hw).2, mem_univ _⟩)
  have hU₁ := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_iteratedFDerivWithin_extChartAt hC hCx hCy₁ hm) δ hδ
  have hU₂ := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_iteratedFDerivWithin_extChartAt hC hCx hCy₂ hm) δ hδ
  rw [nhds_prod_eq]
  filter_upwards [(hT₁.and hU₁).prod_mk (hT₂.and hU₂)] with ⟨f, g⟩ ⟨⟨hf, hf'⟩, hg, hg'⟩
  refine mem_chartJetSet.mpr fun w hw ↦ ?_
  have h₁ := ((mem_chartJetSet.mp hf) w hw).1
  have h₂ := ((mem_chartJetSet.mp hg) w hw).1
  have hwC : (w : E) ∈ C := mem_image_of_mem _ hw
  refine ⟨?_, ?_⟩
  · exact (prodMk_mem_extChartAt_prod_source_iff f g).mpr ⟨h₁, h₂⟩
  · rw [iteratedFDerivWithin_extChartAt_prodMk f g w.2 h₁ h₂ hm]
    have hfg : (D₁ f w, D₂ g w) ∈ Metric.thickening δ ((fun w ↦ (D₁ f₀ w, D₂ g₀ w)) '' C) :=
      Metric.mem_thickening_iff.mpr ⟨_, mem_image_of_mem _ hwC, by
        rw [Prod.dist_eq, max_lt_iff, dist_comm (D₁ f w), dist_comm (D₂ g w)]
        exact ⟨hf' w hwC, hg' w hwC⟩⟩
    exact hδV hfg

end ContMDiffMap

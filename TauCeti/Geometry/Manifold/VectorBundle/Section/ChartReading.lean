/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Schwartz
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
public import TauCeti.Geometry.Manifold.VectorBundle.Section.CutoffFrame
import TauCeti.Analysis.Distribution.SchwartzSpace.SupportedIn

/-!
# Chart readings of chart extensions and chart localizations

Let `c` be a chart of the maximal atlas of a manifold modelled on `ℝⁿ` whose source lies in the
base set of a trivialization `t` of a complex vector bundle. This file reads, in charts, the
sections built from test functions by `c` and `t` and the test functions built from sections:

* `Bundle.Trivialization.ofReal_cutoffPullback_smul_chartTestSection`: multiplying the extension
  `Bundle.Trivialization.chartTestSection` of a test function supported in `L` by a cutoff equal
  to `1` on `L`, read on the manifold, does not change it;
* `Bundle.Trivialization.cutoffPushforwardSchwartz_cutoffFrameCoeff_chartTestSection`: read in
  `c`, a cut-off frame coefficient `ρ ℓ(t ·)` of the extension of a test function `φ` is `ℓ ∘ φ`;
* `Bundle.Trivialization.apply_chartLocalization_eq_cutoffPushforwardSchwartz`: a coordinate
  `ℓ` of the chart localization `Bundle.Trivialization.chartLocalization` of a section is the
  chart reading `OpenPartialHomeomorph.cutoffPushforwardSchwartz` of a cut-off frame coefficient.

These turn estimates on chart readings of cut-off frame coefficients into estimates on chart
localizations of sections.
-/

public section

noncomputable section

open Bundle Set TopologicalSpace TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap

namespace Bundle.Trivialization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]

section ChartTestSection

variable {c : OpenPartialHomeomorph M (CoordinateSpace n)}
  (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (t : Trivialization V (π V E)) [MemTrivializationAtlas t] (hct : c.source ⊆ t.baseSet)
  {L : Compacts (CoordinateSpace n)} (hL : (L : Set (CoordinateSpace n)) ⊆ c.target)
  {ψ : 𝓓(⟨c.target, c.open_target⟩, ℝ)} (hψ : ∀ y ∈ (L : Set (CoordinateSpace n)), ψ y = 1)

include hψ in
/-- Multiplying the extension through `c` and `t` of a test function supported in `L` by a cutoff
in the chart equal to `1` on `L`, read on `M`, does not change it. -/
theorem ofReal_cutoffPullback_smul_chartTestSection (φ : 𝓓_{L}(CoordinateSpace n, V)) :
    ContMDiffMap.ofReal (c.cutoffPullback hc ψ 1) •
        (t.chartTestSection c (contMDiffOn_of_mem_maximalAtlas hc) hct
          (TestFunction.ofSupportedIn (Ω := ⟨c.target, c.open_target⟩) hL φ)).val =
      (t.chartTestSection c (contMDiffOn_of_mem_maximalAtlas hc) hct
        (TestFunction.ofSupportedIn (Ω := ⟨c.target, c.open_target⟩) hL φ)).val := by
  refine ContMDiffSection.ext fun x ↦ ?_
  rw [ContMDiffSection.smul_apply_of_normedAlgebra]
  by_cases hx : x ∈ c.source
  · rw [ContMDiffMap.ofReal_apply, c.cutoffPullback_one_apply_of_mem hc ψ hx]
    by_cases hφ : φ (c x) = 0
    · simp [t.chartTestSection_apply_of_mem c _ hct _ hx, hφ]
    · simp [hψ _ (φ.support_subset hφ)]
  · simp [t.chartTestSection_apply_of_notMem c _ hct _ hx]

include hψ in
/-- Read in the chart `c` through a cutoff equal to `1` on `L`, a cut-off frame coefficient
`ρ ℓ(t ·)` of the extension of a test function `φ` supported in `L` is `ℓ ∘ φ`, when `ρ` is `1` on
the chart preimage of the support of the cutoff. -/
theorem cutoffPushforwardSchwartz_cutoffFrameCoeff_chartTestSection
    (ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρ : tsupport ρ ⊆ t.baseSet)
    (hρψ : ∀ y ∈ tsupport ψ, ρ (c.symm y) = 1) (ℓ : V →L[ℂ] ℂ)
    (φ : 𝓓_{L}(CoordinateSpace n, V)) :
    c.cutoffPushforwardSchwartz hc ψ (t.cutoffFrameCoeff ρ hρ ℓ
        (t.chartTestSection c (contMDiffOn_of_mem_maximalAtlas hc) hct
          (TestFunction.ofSupportedIn (Ω := ⟨c.target, c.open_target⟩) hL φ)).val) =
      ContDiffMapSupportedIn.toSchwartzMapCLM ℂ (ContDiffMapSupportedIn.postcompCLM ℓ φ) := by
  ext y
  rw [c.cutoffPushforwardSchwartz_apply, ContDiffMapSupportedIn.toSchwartzMapCLM_apply,
    ContDiffMapSupportedIn.postcompCLM_apply, Function.comp_apply,
    Bundle.Trivialization.cutoffFrameCoeff_apply]
  by_cases hy : y ∈ c.target
  · have hxs : c.symm y ∈ c.source := c.map_target hy
    have hb := hct hxs
    rw [t.chartTestSection_apply_of_mem c _ hct _ hxs, c.right_inv hy,
      t.continuousLinearMapAt_apply_of_mem (R := ℂ) hb, t.symmL_apply hb, t.apply_mk_symm hb]
    by_cases hφ : φ y = 0
    · simp [hφ]
    · have hyL : y ∈ (L : Set (CoordinateSpace n)) := φ.support_subset hφ
      simp [hψ y hyL, hρψ y (subset_tsupport _ (by simp [hψ y hyL]))]
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hy (ψ.tsupport_subset h)]
    simp [φ.zero_on_compl fun h ↦ hy (hL h)]

end ChartTestSection

omit [T2Space M] in
/-- Read in a chart `c` through a cutoff `ψ`, the coordinate `ℓ` of the chart localization of a
section `s` is the chart reading of its cut-off frame coefficient `χ ℓ(t s)`, when `χ` is `1` on
the support of `ψ`. -/
theorem apply_chartLocalization_eq_cutoffPushforwardSchwartz
    {c : OpenPartialHomeomorph M (CoordinateSpace n)}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t] (hct : c.source ⊆ t.baseSet)
    (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (L : Compacts (CoordinateSpace n))
    (hL : (L : Set (CoordinateSpace n)) ⊆ c.target) (hψ : MapsTo c (tsupport ψ) L)
    {ψ' : 𝓓(⟨c.target, c.open_target⟩, ℝ)} (hψ' : ∀ x ∈ c.source, ψ' (c x) = ψ x)
    (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet)
    (hχψ : ∀ x ∈ tsupport ψ, χ x = 1) (ℓ : V →L[ℂ] ℂ) (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    (fun y ↦ ℓ (t.chartLocalization c (contMDiffOn_symm_of_mem_maximalAtlas hc) hct ψ L hL
        hψ s y)) =
      ⇑(c.cutoffPushforwardSchwartz hc ψ' (t.cutoffFrameCoeff χ hχ ℓ s)) := by
  funext y
  rw [c.cutoffPushforwardSchwartz_apply hc, Bundle.Trivialization.cutoffFrameCoeff_apply]
  by_cases hy : y ∈ c.target
  · have hxs : c.symm y ∈ c.source := c.map_target hy
    rw [t.chartLocalization_apply_of_mem c _ hct ψ L hL hψ _ hy, ← c.right_inv hy,
      hψ' _ hxs, c.left_inv hxs]
    by_cases hψy : ψ (c.symm y) = 0
    · simp [hψy]
    · rw [hχψ _ (subset_tsupport _ hψy), t.continuousLinearMapAt_apply_of_mem (R := ℂ) (hct hxs)]
      simp
  · rw [t.chartLocalization_apply_of_notMem c _ hct ψ L hL hψ _ hy, map_zero,
      image_eq_zero_of_notMem_tsupport fun h ↦ hy (ψ'.tsupport_subset h), zero_smul]

end Bundle.Trivialization

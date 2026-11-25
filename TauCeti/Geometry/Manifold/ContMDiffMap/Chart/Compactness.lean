/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.CountableSeminorms
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Montel
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Topology.Compactness.Compact

/-!
# Compactness from eventual bounds for coordinate derivatives

On a smooth sigma-compact boundaryless manifold with finite-dimensional real model and target,
eventual bounds on every derivative on compact subsets of each chart give one smoothly convergent
subsequence. The tail on which a bound holds
may depend on the chart, the compact set and the order. The extraction also works for
unbundled functions that are eventually smooth near each compact set, assuming additionally that
the source is Hausdorff.

The proofs use `ContMDiffMap.isVonNBounded_iff_forall_exists_norm_chartIteratedFDeriv_le`,
`ContMDiffMap.tendsto_manifoldWeakWhitney_iff_chartIteratedFDeriv`, and the metrizable Montel
structure supplied by `ContMDiffMap.montelSpace_manifoldWeakWhitney` and
`ContMDiffMap.metrizableSpace_manifoldWeakWhitney_of_sigmaCompact`.
-/

public section

open Bornology ContMDiffMap Filter Manifold Set TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- On a smooth sigma-compact boundaryless manifold with finite-dimensional real model, smooth
maps to a finite-dimensional real normed space have one smoothly convergent subsequence if their
coordinate derivatives are eventually bounded on compact sets. -/
theorem exists_strictMono_tendsto_of_eventually_norm_iteratedFDeriv_le
    (f : ℕ → C^∞⟮I, M; 𝓘(ℝ, F), F⟯)
    (hb : ∀ (x : M) (K : Set E), IsCompact K → K ⊆ (extChartAt I x).target →
      ∀ m : ℕ, ∃ R : ℝ, ∀ᶠ i in atTop, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ m (f i ∘ (extChartAt I x).symm) y‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯,
      Tendsto (f ∘ φ) atTop (𝓝 g) := by
  have := metrizableSpace_manifoldWeakWhitney_of_sigmaCompact (I := I) (M := M) (F := F) (n := ∞)
  have h := isVonNBounded_range_of_eventually_norm_iteratedFDerivWithin_le f
    (fun x K hK hKT m _ ↦ by
      obtain ⟨R, hR⟩ := hb x K hK hKT m
      refine ⟨R, hR.mono fun i hi y hy ↦ ?_⟩
      rw [iteratedFDerivWithin_of_isOpen m (isOpen_extChartAt_target x) (hKT hy)]
      exact hi y hy)
  have hc := MontelSpace.isCompact_of_isClosed_of_isVonNBounded ℝ isClosed_closure h.closure
  obtain ⟨g, _, φ, hφ, hg⟩ := hc.tendsto_subseq (fun i ↦ subset_closure (mem_range_self i))
  exact ⟨φ, hφ, g, hg⟩

/-- Eventual smoothness near compact sets and eventual bounds for the derivatives in charts give
a smooth global limit of a single subsequence on a Hausdorff smooth sigma-compact boundaryless
manifold with finite-dimensional real model and target. The input functions can take arbitrary
values away from their current smooth domains. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv_of_eventually_contMDiffAt
    [T2Space M]
    (f : ℕ → M → F)
    (hs : ∀ K : Set M, IsCompact K → ∀ᶠ i in atTop, ∀ x ∈ K, ContMDiffAt I 𝓘(ℝ, F) ∞ (f i) x)
    (hb : ∀ (x : M) (K : Set E), IsCompact K → K ⊆ (extChartAt I x).target →
      ∀ m : ℕ, ∃ R : ℝ, ∀ᶠ i in atTop, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ m (f i ∘ (extChartAt I x).symm) y‖ ≤ R) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯, ∀ (x : M) (m : ℕ),
      TendstoLocallyUniformlyOn (fun i ↦ iteratedFDeriv ℝ m (f (σ i) ∘ (extChartAt I x).symm))
        (iteratedFDeriv ℝ m (g ∘ (extChartAt I x).symm)) atTop (extChartAt I x).target := by
  obtain ⟨a, -, ha⟩ := exists_contMDiffMap_eventuallyEq_nhdsSet_of_eventually_contMDiffAt f hs
  have he (x : M) {K : Set E} (hK : IsCompact K) (hKT : K ⊆ (extChartAt I x).target) (m : ℕ) :
      ∀ᶠ i in atTop, EqOn (iteratedFDeriv ℝ m (a i ∘ (extChartAt I x).symm))
        (iteratedFDeriv ℝ m (f i ∘ (extChartAt I x).symm)) K := by
    apply Filter.Eventually.mono
      (hK.eventually_eventuallyEq_nhdsWithin_comp (continuousOn_extChartAt_symm x) hKT ha)
    intro i hi y hy
    have he := (hi y hy).iteratedFDerivWithin_eq (𝕜 := ℝ)
      ((hi y hy).eq_of_nhdsWithin (hKT hy)) m
    simpa only [iteratedFDerivWithin_of_isOpen m (isOpen_extChartAt_target x) (hKT hy)]
      using he
  obtain ⟨ψ, hψ, g, hg⟩ := exists_strictMono_tendsto_of_eventually_norm_iteratedFDeriv_le a
    (fun x K hK hKT m ↦ by
      obtain ⟨R, hR⟩ := hb x K hK hKT m
      refine ⟨R, ?_⟩
      filter_upwards [hR, he x hK hKT m] with i hi h y hy
      rw [h hy]
      exact hi y hy)
  refine ⟨ψ, hψ, g, fun x m ↦ ?_⟩
  have hT := isOpen_extChartAt_target (I := I) x
  have hl := tendsto_manifoldWeakWhitney_iff_tendstoLocallyUniformlyOn_iteratedFDerivWithin.mp
    hg x m (by simp)
  have heq (u : M → F) :
      EqOn (iteratedFDerivWithin ℝ m (u ∘ (extChartAt I x).symm) (extChartAt I x).target)
        (iteratedFDeriv ℝ m (u ∘ (extChartAt I x).symm)) (extChartAt I x).target :=
    fun _ hy ↦ iteratedFDerivWithin_of_isOpen m hT hy
  have hl' := (hl.congr (fun i ↦ heq (a (ψ i)))).congr_right (heq g)
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hT] at hl' ⊢
  exact fun K hKT hK ↦ (hl' K hKT hK).congr (hψ.tendsto_atTop.eventually (he x hK hKT m))

end TauCeti

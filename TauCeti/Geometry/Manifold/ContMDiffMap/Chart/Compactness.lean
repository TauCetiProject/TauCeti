/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.CountableSeminorms
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Montel
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# Compactness from eventual bounds for coordinate derivatives

On a sigma-compact boundaryless manifold, eventual bounds on every derivative on compact
subsets of each chart give one smoothly convergent subsequence. The tail on which a bound holds
may depend on the chart, the compact set and the order. The extraction also works for
unbundled functions that are eventually smooth near each compact set. The chart criterion for
weak Whitney convergence uses within derivatives and also applies at corners.
-/

public section

open Bornology Filter Manifold Set TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney Topology

namespace ContMDiffMap

section ChartDerivatives

variable {𝕜 E H M F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω} [IsManifold I n M]

/-- Eventual bounds for the coordinate derivatives on compact subsets of chart targets imply that
the range of the sequence is bounded in the weak Whitney topology. -/
theorem isVonNBounded_range_of_eventually_norm_iteratedFDerivWithin_le
    (f : ℕ → C^n⟮I, M; 𝓘(𝕜, F), F⟯)
    (hb : ∀ (x : M) (K : Set E), IsCompact K → K ⊆ (extChartAt I x).target →
      ∀ m : ℕ, m ≤ n → ∃ R : ℝ, ∀ᶠ i in atTop, ∀ y ∈ K,
        ‖iteratedFDerivWithin 𝕜 m (f i ∘ (extChartAt I x).symm) (extChartAt I x).target y‖ ≤ R) :
    IsVonNBounded 𝕜 (range f) := by
  apply isVonNBounded_iff_forall_exists_norm_chartIteratedFDeriv_le.2
  intro x m hm K
  let T := (extChartAt I x).target
  let K' := Subtype.val '' (K : Set T)
  have hK' : IsCompact K' := K.isCompact.image continuous_subtypeVal
  obtain ⟨R, hR⟩ := hb x K' hK' (image_val_subset (γ := (K : Set T))) m hm
  let p (i : ℕ) := ‖(chartIteratedFDeriv (f i) x m hm).restrict (K : Set T)‖
  have hp : IsBoundedUnder (· ≤ ·) atTop p := by
    refine ⟨max 0 R, hR.mono fun i hi ↦ (ContinuousMap.norm_le _ (le_max_left ..)).2 fun y ↦ ?_⟩
    rw [ContinuousMap.restrict_apply, chartIteratedFDeriv_self_target_apply]
    exact (hi y.val ⟨y.val, y.property, rfl⟩).trans (le_max_right ..)
  obtain ⟨C, hC⟩ := hp.bddAbove_range
  refine ⟨C, ?_⟩
  rintro _ ⟨i, rfl⟩ y hy
  exact (ContinuousMap.norm_coe_le_norm
    ((chartIteratedFDeriv (f i) x m hm).restrict (K : Set T)) ⟨y, hy⟩).trans
    (hC (mem_range_self i))

/-- For a locally compact model, weak Whitney convergence is equivalent to locally uniform
convergence of every coordinate derivative on its chart target. This uses within derivatives
so the criterion applies to manifolds with corners. -/
theorem tendsto_manifoldWeakWhitney_iff_tendstoLocallyUniformlyOn_iteratedFDerivWithin
    [LocallyCompactSpace E] {ι : Type*} {l : Filter ι}
    {f : ι → C^n⟮I, M; 𝓘(𝕜, F), F⟯} {g : C^n⟮I, M; 𝓘(𝕜, F), F⟯} :
    Tendsto f l (𝓝 g) ↔ ∀ (x : M) (m : ℕ), m ≤ n →
      TendstoLocallyUniformlyOn
        (fun i ↦ iteratedFDerivWithin 𝕜 m (f i ∘ (extChartAt I x).symm) (extChartAt I x).target)
        (iteratedFDerivWithin 𝕜 m (g ∘ (extChartAt I x).symm) (extChartAt I x).target)
        l (extChartAt I x).target := by
  rw [tendsto_manifoldWeakWhitney_iff_chartIteratedFDeriv]
  congr! 4 with x m hm
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  have heq (a : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
      ⇑(chartIteratedFDeriv a x m hm) =
        iteratedFDerivWithin 𝕜 m (a ∘ (extChartAt I x).symm) (extChartAt I x).target ∘
          Subtype.val :=
    funext (chartIteratedFDeriv_self_target_apply a x m hm)
  simp only [heq, Function.comp_def]

end ChartDerivatives

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Smooth maps to a finite-dimensional normed space have one smoothly convergent subsequence
on the whole manifold if their coordinate derivatives are eventually bounded on compact sets. -/
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

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [FiniteDimensional ℝ F] in
private theorem eventually_eqOn_iteratedFDeriv_comp_extChartAt_symm
    {ι : Type*} {l : Filter ι} {a b : ι → M → F}
    (h : ∀ K : Set M, IsCompact K → ∀ᶠ i in l, a i =ᶠ[𝓝ˢ K] b i)
    (x : M) {K : Set E} (hK : IsCompact K) (hKT : K ⊆ (extChartAt I x).target) (m : ℕ) :
    ∀ᶠ i in l, EqOn (iteratedFDeriv ℝ m (a i ∘ (extChartAt I x).symm))
      (iteratedFDeriv ℝ m (b i ∘ (extChartAt I x).symm)) K := by
  have hc := (continuousOn_extChartAt_symm (I := I) x).mono hKT
  filter_upwards [h _ (hK.image_of_continuousOn hc)] with i hi y hy
  have he : a i =ᶠ[𝓝 ((extChartAt I x).symm y)] b i :=
    (eventually_nhdsSet_iff_forall.mp hi) _ (mem_image_of_mem _ hy)
  have ht := ((continuousOn_extChartAt_symm (I := I) x).continuousAt
    ((isOpen_extChartAt_target x).mem_nhds (hKT hy))).tendsto
  exact ((he.comp_tendsto ht).iteratedFDeriv ℝ m).self_of_nhds

/-- Eventual smoothness near compact sets and eventual bounds for the derivatives in charts give
a smooth global limit of a single subsequence. The input functions can take arbitrary values
away from their current smooth domains. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv_of_locally_smooth [T2Space M]
    (f : ℕ → M → F)
    (hs : ∀ K : Set M, IsCompact K → ∀ᶠ i in atTop, ∀ x ∈ K, ContMDiffAt I 𝓘(ℝ, F) ∞ (f i) x)
    (hb : ∀ (x : M) (K : Set E), IsCompact K → K ⊆ (extChartAt I x).target →
      ∀ m : ℕ, ∃ R : ℝ, ∀ᶠ i in atTop, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ m (f i ∘ (extChartAt I x).symm) y‖ ≤ R) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯, ∀ (x : M) (m : ℕ),
      TendstoLocallyUniformlyOn (fun i ↦ iteratedFDeriv ℝ m (f (σ i) ∘ (extChartAt I x).symm))
        (iteratedFDeriv ℝ m (g ∘ (extChartAt I x).symm)) atTop (extChartAt I x).target := by
  obtain ⟨a, -, ha⟩ := exists_contMDiffMap_eventuallyEq_nhdsSet_of_eventually_contMDiffAt f hs
  have he (x : M) {K : Set E} (hK : IsCompact K) (hKT : K ⊆ (extChartAt I x).target) (m : ℕ) :=
    eventually_eqOn_iteratedFDeriv_comp_extChartAt_symm ha x hK hKT m
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

end ContMDiffMap

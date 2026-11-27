/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Sobolev
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartCutoffs
public import TauCeti.Geometry.Manifold.VectorBundle.Section.LocalOperator
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basis
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding.Schwartz
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartReading

/-!
# Pseudodifferential operators between bundles on bundle tests and their duals

Let `M` be a σ-compact manifold modelled on `ℝⁿ`, let `E`, `F` be smooth complex vector bundles
over `M` with finite-dimensional model fibres `V` and `W`, and let `P : Γ(E) → Γ(F)` be a classical
pseudodifferential operator of order `m` (`TauCeti.sectionClassicalPseudodifferentialOperators`).
Since `P` is properly supported, it sends compactly supported smooth sections of `E` to compactly
supported smooth sections of `F`. This file proves that it does so continuously for the test
topologies, so that `P` acts on the bundle tests `TauCeti.BundleTest` as a continuous linear map
(`TauCeti.BundleTest.pseudodifferentialCLM`). Its transpose, the precomposition `T ↦ T ∘ P`, then
acts on continuous linear functionals on the bundle tests of `F`
(`TauCeti.BundleTest.pseudodifferentialDualCLM`). For a differential operator, which is local, the
same transpose is `TauCeti.BundleTest.localOperatorDualCLM`
(`TauCeti.BundleTest.pseudodifferentialDualCLM_eq_localOperatorDualCLM`).

## The argument

The test topology is the final locally convex topology of its fixed-compact support stages
(`TauCeti.BundleTest.continuous_iff_continuous_comp`). On the stage of a compact set `K`, a test is
the sum of the extensions, through charts `c` of the maximal atlas and frames `t`, of its chart
localizations, test functions supported in fixed compact subsets `L` of the chart targets
(`TauCeti.ChartCutoffs.sum_chartTestCLM_localize`). So it suffices that `φ ↦ P (ext φ)` is
continuous from `𝓓_L(ℝⁿ, V)` to the bundle tests of `F`. Proper support puts all these outputs in
one compact set `K'`, on which they are again sums of chart extensions of their localizations, and
it suffices that each localization `φ ↦ loc (P (ext φ))`, with values in `𝓓_{L'}(ℝⁿ, W)`, is
continuous.

This is an estimate. In a basis of `W`, the coordinates of `loc (P (ext φ))` are chart readings
of cut-off frame coefficients of `P (ext φ)`, so by the Sobolev embedding their derivatives of order
`i` are bounded by their `H^r` norms for `r > i + n / 2`. The Sobolev estimate between two charts
(`TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_smul_le`)
bounds these by the `H^{r + m}` norms of the coordinates of `φ`, which depend continuously on `φ`.

## Main declarations

* `TauCeti.BundleTest.pseudodifferentialCLM`: the action of `P` on bundle tests, as a continuous
  linear map, with `TauCeti.BundleTest.pseudodifferentialCLM_apply`, the identity, addition and
  composition rules `TauCeti.BundleTest.pseudodifferentialCLM_id`,
  `TauCeti.BundleTest.pseudodifferentialCLM_add` and
  `TauCeti.BundleTest.pseudodifferentialCLM_comp`, and the comparison
  `TauCeti.BundleTest.pseudodifferentialCLM_eq_localOperatorCLM`.
* `TauCeti.BundleTest.pseudodifferentialDualCLM`: its transpose on functionals on bundle tests,
  with `TauCeti.BundleTest.pseudodifferentialDualCLM_apply`, the identity, addition and
  composition rules `TauCeti.BundleTest.pseudodifferentialDualCLM_id`,
  `TauCeti.BundleTest.pseudodifferentialDualCLM_add` and
  `TauCeti.BundleTest.pseudodifferentialDualCLM_comp` (composites in the reverse order), and the
  comparison `TauCeti.BundleTest.pseudodifferentialDualCLM_eq_localOperatorDualCLM`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §6.3 (distributions on manifolds).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985, §18.1
  (properly supported pseudodifferential operators on manifolds and their action on
  distributions).
-/

public section

noncomputable section

open Bundle Set Filter Topology TopologicalSpace ContMDiffSection MeasureTheory
open scoped ContDiff Manifold Distributions SchwartzMap BesselPotentialSpace CompactConvergenceCLM

namespace TauCeti

variable {n : ℕ}

section ChartCutoffs

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M] [T2Space M]
  [SigmaCompactSpace M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {V : Type*} [TopologicalSpace V] {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace V E)] [FiberBundle V E]
  {W : Type*} [TopologicalSpace W] {F : M → Type*} [∀ x, TopologicalSpace (F x)]
  [TopologicalSpace (TotalSpace W F)] [FiberBundle W F]

/-- Chart cutoffs whose charts lie in the maximal atlas, with sources inside the base sets of the
trivializations of `E` and of `F` at their points. -/
private theorem exists_chartCutoffs :
    ∃ A : ChartCutoffs 𝓘(ℝ, CoordinateSpace n) M ⊤ M,
      (∀ x, A.chart x ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M) ∧
      (∀ x, (A.chart x).source ⊆ (trivializationAt V E x).baseSet) ∧
      ∀ x, (A.chart x).source ⊆ (trivializationAt W F x).baseSet := by
  choose c hc hxc hcE hcF using fun x : M ↦
    exists_mem_maximalAtlas_source_subset_baseSet V 𝓘(ℝ, CoordinateSpace n) (n := ∞) E W F x
  obtain ⟨A, rfl⟩ := ChartCutoffs.exists_chart_eq (n := ⊤) c
    (fun x ↦ contMDiffOn_of_mem_maximalAtlas (hc x))
    (fun x ↦ contMDiffOn_symm_of_mem_maximalAtlas (hc x)) hxc
  exact ⟨A, hc, hcE, hcF⟩

end ChartCutoffs

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [∀ x, TopologicalSpace (E x)] [FiberBundle V E] [VectorBundle ℝ V E] [VectorBundle ℂ V E]
  [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, IsScalarTower ℝ ℂ (F x)]
  [∀ x, TopologicalSpace (F x)] [FiberBundle W F] [VectorBundle ℝ W F] [VectorBundle ℂ W F]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯} {m : ℝ}

omit [∀ x, IsScalarTower ℝ ℂ (E x)] [∀ x, IsScalarTower ℝ ℂ (F x)] in
/-- **The core estimate.** Let `c` and `c'` be charts of the maximal atlas over which `E` and `F`
are trivialized by `t` and `t'`. Extend a test function `φ` supported in a compact subset `L` of
the target of `c` through `c` and `t`, apply `P`, and localize the result through `c'`, `t'` and a
cutoff `ψ`. The derivatives of order `i` of this localization are bounded by the `H^{r + m}` norms
of the coordinates of `φ`, for `r = i + n + 1`. -/
private theorem exists_seminorm_chartLocalization_apply_chartTestSection_le
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    {c : OpenPartialHomeomorph M (CoordinateSpace n)}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t] (hct : c.source ⊆ t.baseSet)
    {L : Compacts (CoordinateSpace n)} (hL : (L : Set (CoordinateSpace n)) ⊆ c.target)
    {c' : OpenPartialHomeomorph M (CoordinateSpace n)}
    (hc' : c' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t'] (hct' : c'.source ⊆ t'.baseSet)
    (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ c'.source) (L' : Compacts (CoordinateSpace n))
    (hL' : (L' : Set (CoordinateSpace n)) ⊆ c'.target) (hψ : MapsTo c' (tsupport ψ) L') (i : ℕ) :
    ∃ A, 0 ≤ A ∧ ∀ φ : 𝓓_{L}(CoordinateSpace n, V),
      ContDiffMapSupportedIn.seminorm ℝ (CoordinateSpace n) W ⊤ L' i
        (t'.chartLocalization c' (contMDiffOn_symm_of_mem_maximalAtlas hc') hct' ψ L' hL' hψ
          (P (t.chartTestSection c (contMDiffOn_of_mem_maximalAtlas hc) hct
            (TestFunction.ofSupportedIn (Ω := ⟨c.target, c.open_target⟩) hL φ)).val)) ≤
      A * ∑ k, ‖SchwartzMap.toBesselPotentialSpaceCLM (i + n + 1 + m) 2
        (ContDiffMapSupportedIn.toSchwartzMapCLM ℂ (ContDiffMapSupportedIn.postcompCLM
          ((Module.finBasis ℂ V).coord k).toContinuousLinearMap φ))‖ := by
  -- Cutoffs: `ψin = 1` near `L` in the chart `c`, `ρ = 1` on `c⁻¹ (supp ψin)` inside the base set
  -- of `t`, the reading `ψ'` of `ψ` in `c'`, and `χ = 1` on `supp ψ` inside the base set of `t'`.
  obtain ⟨ψin, hψin, -⟩ := TestFunction.exists_eventually_eq_one
    (Ω := ⟨c.target, c.open_target⟩) (n := ⊤) L.isCompact hL
  obtain ⟨ρ, hρs, hρ1, -, hρt, -⟩ :=
    (c.isCompact_symm_image_tsupport ψin).exists_contMDiff_one_nhds_tsupport_subset
      𝓘(ℝ, CoordinateSpace n) t.open_baseSet (image_subset_iff.2 fun y hy ↦
        hct (c.map_target (ψin.tsupport_subset hy)))
  obtain ⟨ψ', -, hψ'⟩ := c'.exists_testFunction_apply_eq
    (contMDiffOn_symm_of_mem_maximalAtlas hc') hψc hψs
  obtain ⟨χ, hχs, hχ1, -, hχt, -⟩ := hψc.isCompact.exists_contMDiff_one_nhds_tsupport_subset
    𝓘(ℝ, CoordinateSpace n) t'.open_baseSet (hψs.trans hct')
  have hψin1 (y : CoordinateSpace n) (hy : y ∈ (L : Set (CoordinateSpace n))) : ψin y = 1 :=
    hψin.self_of_nhdsSet y hy
  set ρ' : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ := ⟨ρ, hρs⟩
  have hρψ (y : CoordinateSpace n) (hy : y ∈ tsupport ψin) : ρ' (c.symm y) = 1 :=
    hρ1.self_of_nhdsSet _ (mem_image_of_mem _ hy)
  set r : ℝ := i + n + 1
  -- The Sobolev embedding in `c'`, and the Sobolev estimate between the charts `c` and `c'`.
  obtain ⟨Cemb, hCemb0, hCemb⟩ :=
    SchwartzMap.exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpaceCLM
      (E := CoordinateSpace n) (F := ℂ) (s := r) (k := i)
      (by simp only [r, finrank_euclideanSpace_fin]; linarith)
  choose C hC using fun l ↦
    exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_cutoffFrameCoeff_smul_le hP hc'
      hc ψ' t' ⟨χ, hχs⟩ hχt ((Module.finBasis ℂ W).coord l).toContinuousLinearMap ψin t ρ' hρt
    hρψ (Module.finBasis ℂ V) (r + m)
  refine ⟨∑ l, ‖Module.finBasis ℂ W l‖ * (Cemb * |C l|), by positivity, fun φ ↦ ?_⟩
  refine (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (by positivity) i _).2 fun x _ ↦
    ((Module.finBasis ℂ W).norm_iteratedFDeriv_le_sum
      ((ContDiffMapSupportedIn.contDiff _).of_le (mod_cast le_top)) x).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ ↦ ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h := hC l (t.chartTestSection c (contMDiffOn_of_mem_maximalAtlas hc) hct
    (TestFunction.ofSupportedIn (Ω := ⟨c.target, c.open_target⟩) hL φ)).val
  rw [t.ofReal_cutoffPullback_smul_chartTestSection hc hct hL hψin1, add_sub_cancel_right] at h
  simp_rw [t.cutoffPushforwardSchwartz_cutoffFrameCoeff_chartTestSection hc hct hL hψin1 _ hρt
    hρψ] at h
  simp_rw [← LinearMap.coe_toContinuousLinearMap' ((Module.finBasis ℂ W).coord l),
    t'.apply_chartLocalization_eq_cutoffPushforwardSchwartz hc' hct' ψ L' hL' hψ hψ' ⟨χ, hχs⟩ hχt
      (fun x hx ↦ hχ1.self_of_nhdsSet x hx)]
  refine (hCemb _ i le_rfl x).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
    (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))) hCemb0

omit [∀ x, IsScalarTower ℝ ℂ (E x)] [∀ x, IsScalarTower ℝ ℂ (F x)] in
/-- Extending a test function `φ` supported in a compact subset `L` of the target of a chart `c`
through `c` and `t`, applying `P` and localizing the result through a chart `c'`, a
trivialization `t'` and a cutoff `ψ`, is continuous in `φ`. -/
private theorem continuous_chartLocalization_apply_chartTestSection
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    {c : OpenPartialHomeomorph M (CoordinateSpace n)}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t] (hct : c.source ⊆ t.baseSet)
    {L : Compacts (CoordinateSpace n)} (hL : (L : Set (CoordinateSpace n)) ⊆ c.target)
    {c' : OpenPartialHomeomorph M (CoordinateSpace n)}
    (hc' : c' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t'] (hct' : c'.source ⊆ t'.baseSet)
    (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ c'.source) (L' : Compacts (CoordinateSpace n))
    (hL' : (L' : Set (CoordinateSpace n)) ⊆ c'.target) (hψ : MapsTo c' (tsupport ψ) L') :
    Continuous fun φ : 𝓓_{L}(CoordinateSpace n, V) ↦
      t'.chartLocalization c' (contMDiffOn_symm_of_mem_maximalAtlas hc') hct' ψ L' hL' hψ
        (P (t.chartTestSection c (contMDiffOn_of_mem_maximalAtlas hc) hct
          (TestFunction.ofSupportedIn (Ω := ⟨c.target, c.open_target⟩) hL φ)).val) := by
  -- The map is additive, and by the core estimate its seminorms are bounded by functions of `φ`
  -- that are continuous and vanish at `0`; so it is continuous at `0`.
  let g : 𝓓_{L}(CoordinateSpace n, V) →+ 𝓓_{L'}(CoordinateSpace n, W) :=
    { toFun := fun φ ↦ t'.chartLocalization c' (contMDiffOn_symm_of_mem_maximalAtlas hc') hct' ψ
        L' hL' hψ (P (t.chartTestSection c (contMDiffOn_of_mem_maximalAtlas hc) hct
          (TestFunction.ofSupportedInCLM ℝ (Ω := ⟨c.target, c.open_target⟩) hL φ)).val)
      map_zero' := by simp only [map_zero, ZeroMemClass.coe_zero]
      map_add' := fun _ _ ↦ by simp only [map_add, Submodule.coe_add] }
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt,
    (ContDiffMapSupportedIn.withSeminorms ℝ (CoordinateSpace n) W ⊤ L').tendsto_nhds g (g 0)]
  intro i ε hε
  obtain ⟨A, -, hAg⟩ := exists_seminorm_chartLocalization_apply_chartTestSection_le hP hc t hct
    hL hc' t' hct' ψ hψc hψs L' hL' hψ i
  set Q : 𝓓_{L}(CoordinateSpace n, V) → ℝ := fun φ ↦ ∑ k,
    ‖SchwartzMap.toBesselPotentialSpaceCLM (i + n + 1 + m) 2
      (ContDiffMapSupportedIn.toSchwartzMapCLM ℂ (ContDiffMapSupportedIn.postcompCLM
        ((Module.finBasis ℂ V).coord k).toContinuousLinearMap φ))‖ with hQ
  have hQc : Continuous Q := continuous_finsetSum _ fun _ _ ↦ by fun_prop
  have ht : Tendsto (fun φ ↦ (A + 1) * Q φ) (𝓝 0) (𝓝 0) := by
    simpa [hQ] using (hQc.tendsto 0).const_mul (A + 1)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with φ hφ
  rw [map_zero, sub_zero]
  exact (hAg φ).trans_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith)
    (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)) hφ)

/-! ### The action on bundle tests -/

/-- The linear map underlying `TauCeti.BundleTest.pseudodifferentialCLM`: a properly supported
operator sends compactly supported sections to compactly supported sections. -/
private def testLinearMap (hP : IsSectionProperlySupported P) :
    BundleTest 𝓘(ℝ, CoordinateSpace n) V E →ₗ[ℝ] BundleTest 𝓘(ℝ, CoordinateSpace n) W F :=
  (BundleTest.ofCompactlySupported _ W F).toLinearMap ∘ₗ
    ((P.restrictScalars ℝ).restrict fun s hs ↦ by
      obtain ⟨K', hK', hPK, -⟩ :=
        isSectionProperlySupported_iff.1 hP _ (mem_compactlySupported.1 hs)
      exact mem_compactlySupported.2
        (hK'.of_isClosed_subset (P s).isClosed_tsupport (hPK _ subset_rfl))) ∘ₗ
    (BundleTest.ofCompactlySupported _ V E).symm.toLinearMap

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [FiniteDimensional ℂ V]
  [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)] [FiniteDimensional ℂ W]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)] in
private theorem val_symm_testLinearMap (hP : IsSectionProperlySupported P)
    (Φ : BundleTest 𝓘(ℝ, CoordinateSpace n) V E) :
    ((BundleTest.ofCompactlySupported _ W F).symm (testLinearMap hP Φ)).val =
      P ((BundleTest.ofCompactlySupported _ V E).symm Φ).val := by
  simp [testLinearMap, LinearMap.restrict_apply]

/-- Extending test functions supported in a compact subset `L` of the target of a chart `c` of the
maximal atlas through `c` and a trivialization `t`, and then applying `P`, is continuous. -/
private theorem continuous_testLinearMap_chartTestCLM
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (A : ChartCutoffs 𝓘(ℝ, CoordinateSpace n) M ⊤ M)
    (hA : ∀ x, A.chart x ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (hAF : ∀ x, (A.chart x).source ⊆ (trivializationAt W F x).baseSet)
    {c : OpenPartialHomeomorph M (CoordinateSpace n)}
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t] (hct : c.source ⊆ t.baseSet)
    {L : Compacts (CoordinateSpace n)} (hL : (L : Set (CoordinateSpace n)) ⊆ c.target) :
    Continuous fun φ : 𝓓_{L}(CoordinateSpace n, V) ↦
      testLinearMap (mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).1
        (t.chartTestCLM c (contMDiffOn_of_mem_maximalAtlas hc) hct
          (TestFunction.ofSupportedIn (Ω := ⟨c.target, c.open_target⟩) hL φ)) := by
  set hP' := (mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).1
  -- The outputs are supported in a fixed compact set `K'`.
  have hK : IsCompact (c.symm '' L) :=
    L.isCompact.image_of_continuousOn (c.continuousOn_symm.mono hL)
  obtain ⟨K', hK', hPK, -⟩ := isSectionProperlySupported_iff.1 hP' _ hK
  have hsupp (φ : 𝓓_{L}(CoordinateSpace n, V)) :
      closure {x | testLinearMap hP' (t.chartTestCLM c (contMDiffOn_of_mem_maximalAtlas hc) hct
        (TestFunction.ofSupportedIn (Ω := ⟨c.target, c.open_target⟩) hL φ)) x ≠ 0} ⊆ K' := by
    have h := hPK (t.chartTestSection c (contMDiffOn_of_mem_maximalAtlas hc) hct
      (TestFunction.ofSupportedIn (Ω := ⟨c.target, c.open_target⟩) hL φ)).val (by
        rw [Bundle.Trivialization.tsupport_chartTestSection]
        exact image_mono φ.tsupport_subset)
    rwa [← ContMDiffSection.tsupport_def, val_symm_testLinearMap, t.val_symm_chartTestCLM]
  -- Decompose the outputs along the chart cutoffs meeting `K'`.
  have heq := funext fun φ ↦ (A.sum_chartTestCLM_localize (fun y ↦ trivializationAt W F y) hAF
    hK' (hsupp φ)).symm
  rw [heq]
  refine continuous_finsetSum _ fun y _ ↦ (ContinuousLinearMap.continuous _).comp ?_
  refine ((TestFunction.ofSupportedInCLM ℝ (A.chartSupport_subset_target y)).continuous.comp
    (continuous_chartLocalization_apply_chartTestSection hP hc t hct hL (hA y)
      (trivializationAt W F y) (hAF y) (A.cutoff y) (A.isCompact_tsupport y) (A.tsupport_subset y)
      (A.chartSupport y) (A.chartSupport_subset_target y) (A.mapsTo_chartSupport y))).congr
    fun φ ↦ ?_
  rw [A.localize_apply, Function.comp_apply, TestFunction.coe_ofSupportedInCLM,
    val_symm_testLinearMap, t.val_symm_chartTestCLM]

variable [SigmaCompactSpace M]

/-- A properly supported classical pseudodifferential operator acts continuously on bundle
tests. -/
private theorem continuous_testLinearMap (hP : P ∈ sectionClassicalPseudodifferentialOperators m) :
    Continuous (testLinearMap (mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).1) := by
  obtain ⟨A, hA, hAE, hAF⟩ :=
    exists_chartCutoffs (n := n) (M := M) (V := V) (E := E) (W := W) (F := F)
  set hP' := (mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).1
  let := frameTopology (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞)
    (fun x : M ↦ trivializationAt V E x) (fun x ↦ ⟨_, (trivializationAt V E x).open_baseSet⟩)
    fun _ ↦ subset_rfl
  refine (BundleTest.continuous_iff_continuous_comp _).2 fun K ↦ ?_
  -- On the stage of `K`, a test is the sum of the chart extensions of its localizations.
  have heq := funext fun σ ↦ congrArg (testLinearMap hP')
    (A.sum_chartTestCLM_localize (fun x ↦ trivializationAt V E x) hAE K.isCompact
      (BundleTest.tsupport_ofSupportedIn_subset K σ)).symm
  refine (Continuous.congr ?_ fun σ ↦ (congrFun heq σ).symm)
  simp_rw [map_sum]
  refine continuous_finsetSum _ fun x _ ↦ ?_
  refine ((continuous_testLinearMap_chartTestCLM hP A hA hAF (hA x) (trivializationAt V E x)
    (hAE x) (A.chartSupport_subset_target x)).comp
      (((trivializationAt V E x).chartLocalizationCLM (A.chart x) (A.contMDiffOn_chart_symm x)
        (hAE x) (A.cutoff x) (A.chartSupport x) (A.chartSupport_subset_target x)
        (A.mapsTo_chartSupport x)).continuous.comp (BundleTest.continuous_ofSupportedIn K))).congr
    fun σ ↦ ?_
  simp only [Function.comp_apply, A.localize_apply,
    Bundle.Trivialization.chartLocalizationCLM_apply]

namespace BundleTest

variable (P) in
/-- **Pseudodifferential operators act on bundle tests.** A classical pseudodifferential operator
`P : Γ(E) → Γ(F)` between bundles is properly supported, so it sends compactly supported smooth
sections of `E` to compactly supported smooth sections of `F`, and it does so continuously for the
test topologies. -/
def pseudodifferentialCLM (hP : P ∈ sectionClassicalPseudodifferentialOperators m) :
    BundleTest 𝓘(ℝ, CoordinateSpace n) V E →L[ℝ] BundleTest 𝓘(ℝ, CoordinateSpace n) W F where
  toLinearMap := testLinearMap (mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).1
  cont := continuous_testLinearMap hP

/-- The action of `P` on a bundle test is the action of `P` on its underlying section. -/
@[simp]
theorem pseudodifferentialCLM_apply (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (Φ : BundleTest 𝓘(ℝ, CoordinateSpace n) V E) (x : M) :
    pseudodifferentialCLM P hP Φ x = P ((ofCompactlySupported _ V E).symm Φ).val x := by
  exact congrArg (fun s ↦ s x)
    (val_symm_testLinearMap (mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).1 Φ)

/-- For a local operator, such as a differential operator, the action on bundle tests is the
action of local operators, `TauCeti.BundleTest.localOperatorCLM`. -/
theorem pseudodifferentialCLM_eq_localOperatorCLM
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hloc : ∀ (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) →
      P s x = 0) :
    pseudodifferentialCLM P hP = localOperatorCLM (P.restrictScalars ℝ) hloc :=
  ContinuousLinearMap.ext fun _ ↦ BundleTest.ext fun _ ↦ by
    rw [pseudodifferentialCLM_apply]
    exact (localOperatorCLM_apply (P := P.restrictScalars ℝ) hloc _ _).symm

/-- The identity acts on bundle tests as the identity. -/
@[simp]
theorem pseudodifferentialCLM_id
    (hP : (LinearMap.id : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ]
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) ∈ sectionClassicalPseudodifferentialOperators 0 :=
      id_mem_sectionClassicalPseudodifferentialOperators) :
    pseudodifferentialCLM LinearMap.id hP =
      ContinuousLinearMap.id ℝ (BundleTest 𝓘(ℝ, CoordinateSpace n) V E) := by
  ext
  simp

/-- The action on bundle tests of a sum is the sum of the actions. -/
theorem pseudodifferentialCLM_add
    {P' : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hP' : P' ∈ sectionClassicalPseudodifferentialOperators m)
    (hPP' : P + P' ∈ sectionClassicalPseudodifferentialOperators m := add_mem hP hP') :
    pseudodifferentialCLM (P + P') hPP' =
      pseudodifferentialCLM P hP + pseudodifferentialCLM P' hP' := by
  ext
  simp

/-- The action on bundle tests of a composite is the composite of the actions. -/
theorem pseudodifferentialCLM_comp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
    {G : M → Type*} [TopologicalSpace (TotalSpace U G)] [∀ x, AddCommGroup (G x)]
    [∀ x, Module ℝ (G x)] [∀ x, Module ℂ (G x)] [∀ x, IsScalarTower ℝ ℂ (G x)]
    [∀ x, TopologicalSpace (G x)] [FiberBundle U G] [VectorBundle ℝ U G] [VectorBundle ℂ U G]
    [ContMDiffVectorBundle ∞ U G 𝓘(ℝ, CoordinateSpace n)] [FiniteDimensional ℂ U] {m' : ℝ}
    {R : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); U, G⟯}
    (hR : R ∈ sectionClassicalPseudodifferentialOperators m')
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hRP : R ∘ₗ P ∈ sectionClassicalPseudodifferentialOperators (m' + m) :=
      comp_mem_sectionClassicalPseudodifferentialOperators (P := P) (R := R) hR hP) :
    pseudodifferentialCLM (R ∘ₗ P) hRP =
      (pseudodifferentialCLM R hR).comp (pseudodifferentialCLM P hP) := by
  ext
  simp [pseudodifferentialCLM, val_symm_testLinearMap]

section Dual

variable {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul ℝ G]

variable (P) in
/-- **The transpose of a pseudodifferential operator** on functionals on bundle tests: a continuous
linear functional `T` on the bundle tests of `F` is sent to `T ∘ P`, a functional on the bundle
tests of `E`, as a continuous linear map for the topologies of uniform convergence on compact sets
of tests. -/
def pseudodifferentialDualCLM (hP : P ∈ sectionClassicalPseudodifferentialOperators m) :
    (BundleTest 𝓘(ℝ, CoordinateSpace n) W F →L_c[ℝ] G) →L[ℝ]
      BundleTest 𝓘(ℝ, CoordinateSpace n) V E →L_c[ℝ] G :=
  (pseudodifferentialCLM P hP).precompCompactConvergenceCLM G

@[simp]
theorem pseudodifferentialDualCLM_apply (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (T : BundleTest 𝓘(ℝ, CoordinateSpace n) W F →L_c[ℝ] G)
    (Φ : BundleTest 𝓘(ℝ, CoordinateSpace n) V E) :
    pseudodifferentialDualCLM (G := G) P hP T Φ = T (pseudodifferentialCLM P hP Φ) :=
  ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply _ _ _

/-- For a local operator, such as a differential operator, the transpose is the transpose of
local operators, `TauCeti.BundleTest.localOperatorDualCLM`. -/
theorem pseudodifferentialDualCLM_eq_localOperatorDualCLM
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hloc : ∀ (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) →
      P s x = 0) :
    pseudodifferentialDualCLM (G := G) P hP = localOperatorDualCLM (P.restrictScalars ℝ) hloc := by
  ext T Φ
  rw [pseudodifferentialDualCLM_apply, pseudodifferentialCLM_eq_localOperatorCLM hP hloc]
  exact (localOperatorDualCLM_apply hloc T Φ).symm

/-- The transpose of the identity is the identity. -/
@[simp]
theorem pseudodifferentialDualCLM_id
    (hP : (LinearMap.id : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ]
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) ∈ sectionClassicalPseudodifferentialOperators 0 :=
      id_mem_sectionClassicalPseudodifferentialOperators) :
    pseudodifferentialDualCLM (G := G) LinearMap.id hP =
      ContinuousLinearMap.id ℝ (BundleTest 𝓘(ℝ, CoordinateSpace n) V E →L_c[ℝ] G) := by
  ext
  simp

/-- The transpose of a sum is the sum of the transposes. -/
theorem pseudodifferentialDualCLM_add
    {P' : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hP' : P' ∈ sectionClassicalPseudodifferentialOperators m)
    (hPP' : P + P' ∈ sectionClassicalPseudodifferentialOperators m := add_mem hP hP') :
    pseudodifferentialDualCLM (G := G) (P + P') hPP' =
      pseudodifferentialDualCLM P hP + pseudodifferentialDualCLM P' hP' := by
  ext
  simp [pseudodifferentialCLM_add hP hP']

/-- The transpose of a composite is the composite of the transposes, in the reverse order. -/
theorem pseudodifferentialDualCLM_comp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
    {H : M → Type*} [TopologicalSpace (TotalSpace U H)] [∀ x, AddCommGroup (H x)]
    [∀ x, Module ℝ (H x)] [∀ x, Module ℂ (H x)] [∀ x, IsScalarTower ℝ ℂ (H x)]
    [∀ x, TopologicalSpace (H x)] [FiberBundle U H] [VectorBundle ℝ U H] [VectorBundle ℂ U H]
    [ContMDiffVectorBundle ∞ U H 𝓘(ℝ, CoordinateSpace n)] [FiniteDimensional ℂ U] {m' : ℝ}
    {R : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); U, H⟯}
    (hR : R ∈ sectionClassicalPseudodifferentialOperators m')
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hRP : R ∘ₗ P ∈ sectionClassicalPseudodifferentialOperators (m' + m) :=
      comp_mem_sectionClassicalPseudodifferentialOperators (P := P) (R := R) hR hP) :
    pseudodifferentialDualCLM (G := G) (R ∘ₗ P) hRP =
      (pseudodifferentialDualCLM (G := G) P hP).comp (pseudodifferentialDualCLM (G := G) R hR) := by
  ext T Φ
  simp [pseudodifferentialCLM_comp hR hP hRP]

end Dual

end BundleTest

end TauCeti

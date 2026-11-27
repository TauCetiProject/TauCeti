/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Composition
public import TauCeti.Analysis.Pseudodifferential.Manifold.PatchedQuantization
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial.BundleTest
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
import TauCeti.Analysis.Pseudodifferential.Symbol.Map
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
import TauCeti.Topology.Algebra.Module.Spaces.CompactConvergenceCLM

/-!
# Pseudodifferential operators on test functions of a compact manifold

Let `M` be a compact manifold modelled on `ℝⁿ`. Its complex test functions are the bundle tests
`TauCeti.BundleTest` of the trivial bundle with fibre `ℂ`: on a compact manifold these are all the
complex-valued smooth functions on `M` (`TauCeti.BundleTest.contMDiffMapEquiv`), now with the test
topology. This file shows that a classical pseudodifferential operator `P` of order `m` on `M`
(`TauCeti.classicalPseudodifferentialOperators`) acts **continuously** on the test functions
(`TauCeti.BundleTest.pseudodifferentialCLM`). Hence its transpose `T ↦ T ∘ P` acts continuously on
the continuous linear functionals on test functions, the distribution densities on `M`
(`TauCeti.BundleTest.pseudodifferentialDualCLM`): this is how a pseudodifferential operator acts,
by transposition, on distributions on a manifold. It is the counterpart for pseudodifferential
operators of the action of differential operators (`TauCeti.BundleTest.localOperatorCLM`,
`TauCeti.BundleTest.localOperatorDualCLM`), which are local and hence continuous by Peetre's
theorem.

## The argument

On a compact manifold of positive dimension, `P` is a finite sum of chart quantizations
(`TauCeti.exists_eq_sum_chartQuantization`), the operators

`u ↦ (φ · Op(a) (ψ · (u ∘ e⁻¹))) ∘ e`

for a chart `e` of the maximal atlas, cutoffs `φ`, `ψ` in its target and a classical symbol `a`
(`OpenPartialHomeomorph.chartQuantization`). Each of them is a composite of continuous linear maps
(`OpenPartialHomeomorph.continuous_chartQuantization_bundleTest`):

* the chart localization `u ↦ ψ · (u ∘ e⁻¹)` of bundle tests
  (`Bundle.Trivialization.chartLocalizationCLM`), read as a Schwartz function
  (`ContDiffMapSupportedIn.toSchwartzMapCLM`);
* the quantization `Op(χ a)` of the symbol `a` cut off by a test function `χ` equal to `1` near the
  support of `φ`, whose estimates are uniform in the position, so that it is continuous on Schwartz
  space (`TauCeti.Symbol.quantizeUniformCLM`); since `φ χ = φ`, it gives `φ · Op(a)` after the
  cutoff by `φ`;
* the cutoff `w ↦ φ · w` of Schwartz functions to test functions on the chart target
  (`TestFunction.smulSchwartzMapCLM`), extended to the manifold through the chart
  (`Bundle.Trivialization.chartTestCLM`).

In dimension zero a compact manifold is a finite set, so its test functions form a
finite-dimensional space, on which every linear operator is continuous.

## Main declarations

* `OpenPartialHomeomorph.continuous_chartQuantization_bundleTest`: a chart quantization is
  continuous on the test functions.
* `TauCeti.BundleTest.pseudodifferentialCLM`: a classical pseudodifferential operator acting on
  the test functions of a compact manifold, as a continuous linear map, with
  `TauCeti.BundleTest.pseudodifferentialCLM_apply`. It sends the identity to the identity,
  composites to composites and sums to sums.
* `TauCeti.BundleTest.pseudodifferentialDualCLM`: its transpose `T ↦ T ∘ P` on the continuous
  linear functionals on test functions, as a continuous linear map, with the same algebraic API,
  composites in the reverse order.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 (pseudodifferential operators on manifolds act continuously on test functions and, by
  transposition, on distributions).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open Set Filter Bundle TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap Topology CompactConvergenceCLM

/-! ### Chart quantizations on test functions -/

namespace OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [CompactSpace M]
  {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M) {m : ℝ}

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [CompactSpace M] in
/-- The cutoff `ψ` read on `M` is supported over the support of `ψ`. -/
private theorem mapsTo_tsupport_cutoffPullback (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    MapsTo e (tsupport (e.cutoffPullback he ψ 1))
      (⟨tsupport ψ, ψ.hasCompactSupport.isCompact⟩ : TopologicalSpace.Compacts _) := by
  rintro _ hx
  obtain ⟨y, hy, rfl⟩ := e.tsupport_cutoffPullback_subset he ψ 1 hx
  rwa [e.right_inv (ψ.tsupport_subset hy)]

/-- The chart localization of a test function `u` by the cutoff `ψ`, read on `M` through the
chart, is `ψ · (u ∘ e⁻¹)`. -/
private theorem chartLocalizationCLM_cutoffPullback_apply
    [MemTrivializationAtlas (Bundle.Trivial.trivialization M ℂ)]
    (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (u : BundleTest 𝓘(ℝ, CoordinateSpace n) ℂ (Bundle.Trivial M ℂ)) (y : CoordinateSpace n) :
    (Bundle.Trivial.trivialization M ℂ).chartLocalizationCLM e
      (contMDiffOn_symm_of_mem_maximalAtlas he) (by simp) (e.cutoffPullback he ψ 1) _
      ψ.tsupport_subset (e.mapsTo_tsupport_cutoffPullback he ψ) u y =
      ψ y • BundleTest.contMDiffMapEquiv _ M ℂ u (e.symm y) := by
  rw [Bundle.Trivialization.chartLocalizationCLM_apply]
  by_cases hy : y ∈ e.target
  · rw [(Bundle.Trivial.trivialization M ℂ).chartLocalization_apply_of_mem (hy := hy)]
    simp [e.cutoffPullback_one_apply_of_mem he _ (e.map_target hy), e.right_inv hy]
  · rw [(Bundle.Trivial.trivialization M ℂ).chartLocalization_apply_of_notMem (hy := hy),
      image_eq_zero_of_notMem_tsupport fun h ↦ hy (ψ.tsupport_subset h), zero_smul]

/-- **Chart quantizations are continuous on test functions.** On a compact manifold, the chart
quantization `u ↦ (φ · Op(a) (ψ · (u ∘ e⁻¹))) ∘ e` of a classical symbol `a` is continuous for
the test topology. -/
theorem continuous_chartQuantization_bundleTest (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n ℂ ℂ m) :
    Continuous fun u : BundleTest 𝓘(ℝ, CoordinateSpace n) ℂ (Bundle.Trivial M ℂ) ↦
      (BundleTest.contMDiffMapEquiv _ M ℂ).symm
        (e.chartQuantization he φ ψ a (BundleTest.contMDiffMapEquiv _ M ℂ u)) := by
  -- Read test functions in the trivialization of the trivial bundle, which is its whole atlas.
  have : MemTrivializationAtlas (Bundle.Trivial.trivialization M ℂ) := ⟨mem_singleton _⟩
  -- A cutoff `χ` equal to `1` near the support of `φ` makes the symbol uniform without changing
  -- `φ · Op(a)`.
  obtain ⟨χ, hχ1, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤)
    φ.hasCompactSupport.isCompact φ.tsupport_subset
  have hχ : ContDiff ℝ ∞ fun y ↦ (χ y : ℂ) := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hχa : (Symbol.smulLeft hχ a.toSymbol).IsUniform :=
    (Symbol.hasCompactSpatialSupport_smulLeft hχ
      (χ.hasCompactSupport.comp_left Complex.ofReal_zero) a.toSymbol).isUniform
  let L := (Bundle.Trivial.trivialization M ℂ).chartLocalizationCLM e
    (contMDiffOn_symm_of_mem_maximalAtlas he) (by simp) (e.cutoffPullback he ψ 1) _
    ψ.tsupport_subset (e.mapsTo_tsupport_cutoffPullback he ψ)
  let G := (Bundle.Trivial.trivialization M ℂ).chartTestCLM e
      (contMDiffOn_of_mem_maximalAtlas he) (by simp) ∘L
    TestFunction.smulSchwartzMapCLM φ ∘L (Symbol.quantizeUniformCLM _ hχa).restrictScalars ℝ ∘L
    ContDiffMapSupportedIn.toSchwartzMapCLM ℝ ∘L L
  refine G.continuous.congr fun u ↦ BundleTest.ext fun p ↦ ?_
  have hv (y : CoordinateSpace n) : ContDiffMapSupportedIn.toSchwartzMapCLM ℝ (L u) y =
      ψ y • BundleTest.contMDiffMapEquiv _ M ℂ u (e.symm y) := by
    rw [ContDiffMapSupportedIn.coe_toSchwartzMapCLM]
    exact e.chartLocalizationCLM_cutoffPullback_apply he ψ u y
  by_cases hp : p ∈ e.source
  · simp only [G, ContinuousLinearMap.coe_comp, Function.comp_apply,
      Bundle.Trivialization.chartTestCLM_apply_of_mem _ _ _ _ _ hp,
      Bundle.Trivial.symmL_trivialization, ContinuousLinearMap.id_apply,
      TestFunction.smulSchwartzMapCLM_apply, ContinuousLinearMap.coe_restrictScalars',
      Symbol.quantizeUniformCLM_apply, Symbol.quantizeSchwartzValue_smulLeft,
      BundleTest.contMDiffMapEquiv_symm_apply, e.chartQuantization_apply_of_mem he φ ψ a _ hv hp]
    -- `φ χ = φ`, since `χ = 1` on the support of `φ`.
    rcases eq_or_ne (φ (e p)) 0 with h0 | h0
    · simp [h0]
    · rw [hχ1.self_of_nhdsSet (e p) (subset_tsupport _ (Function.mem_support.2 h0)),
        Complex.ofReal_one, one_smul]
  · simp only [G, ContinuousLinearMap.coe_comp, Function.comp_apply,
      BundleTest.contMDiffMapEquiv_symm_apply, e.chartQuantization_apply_of_notMem he _ _ _ _ hp,
      Bundle.Trivialization.chartTestCLM_apply_of_notMem _ _ _ _ _ hp]

end OpenPartialHomeomorph

/-! ### Pseudodifferential operators on test functions and distributions -/

namespace TauCeti.BundleTest

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [CompactSpace M]
  {m m' : ℝ} {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

omit [T2Space M] in
/-- In dimension zero a compact manifold is a finite set, so its test functions form a
finite-dimensional space and every linear operator on them is continuous. -/
private theorem continuous_of_dim_eq_zero (hn : n = 0)
    (L : BundleTest 𝓘(ℝ, CoordinateSpace n) ℂ (Bundle.Trivial M ℂ) →ₗ[ℝ]
      BundleTest 𝓘(ℝ, CoordinateSpace n) ℂ (Bundle.Trivial M ℂ)) : Continuous L := by
  subst hn
  have : DiscreteTopology M := ChartedSpace.discreteTopology (CoordinateSpace 0) M
  have : Finite M := finite_of_compact_of_discrete
  -- A test function is determined by its values at the finitely many points of `M`.
  let ev : BundleTest 𝓘(ℝ, CoordinateSpace 0) ℂ (Bundle.Trivial M ℂ) →ₗ[ℝ] M → ℂ :=
    { toFun u x := u x
      map_add' u v := funext (BundleTest.add_apply u v)
      map_smul' c u := funext (BundleTest.smul_apply c u) }
  have : FiniteDimensional ℝ (BundleTest 𝓘(ℝ, CoordinateSpace 0) ℂ (Bundle.Trivial M ℂ)) :=
    Module.Finite.of_injective ev fun u v huv ↦ BundleTest.ext (congrFun huv)
  exact L.continuous_of_finiteDimensional

/-- **Pseudodifferential operators act continuously on test functions.** On a compact manifold
`M` modelled on `ℝⁿ`, a classical pseudodifferential operator `P` of order `m` acting
on the test functions of `M`, the bundle tests of the trivial bundle with fibre `ℂ`, as a
continuous linear map for the test topology. -/
def pseudodifferentialCLM (hP : P ∈ classicalPseudodifferentialOperators m) :
    BundleTest 𝓘(ℝ, CoordinateSpace n) ℂ (Bundle.Trivial M ℂ) →L[ℝ]
      BundleTest 𝓘(ℝ, CoordinateSpace n) ℂ (Bundle.Trivial M ℂ) where
  toLinearMap := (contMDiffMapEquiv _ M ℂ).symm.toLinearMap ∘ₗ P.restrictScalars ℝ ∘ₗ
    (contMDiffMapEquiv _ M ℂ).toLinearMap
  cont := by
    rcases eq_or_ne n 0 with hn | hn
    · exact continuous_of_dim_eq_zero hn _
    have : NeZero n := ⟨hn⟩
    obtain ⟨k, e, he, φ, ψ, a, rfl⟩ := exists_eq_sum_chartQuantization hP
    refine (continuous_finsetSum Finset.univ fun i _ ↦
      (e i).continuous_chartQuantization_bundleTest (he i) (φ i) (ψ i) (a i)).congr fun u ↦ ?_
    simp

/-- Read as a smooth function, `P` acting on a test function `u` is `P u`. -/
@[simp]
theorem contMDiffMapEquiv_pseudodifferentialCLM (hP : P ∈ classicalPseudodifferentialOperators m)
    (u : BundleTest 𝓘(ℝ, CoordinateSpace n) ℂ (Bundle.Trivial M ℂ)) :
    contMDiffMapEquiv _ M ℂ (pseudodifferentialCLM hP u) = P (contMDiffMapEquiv _ M ℂ u) :=
  (contMDiffMapEquiv _ M ℂ).apply_symm_apply _

@[simp]
theorem pseudodifferentialCLM_apply (hP : P ∈ classicalPseudodifferentialOperators m)
    (u : BundleTest 𝓘(ℝ, CoordinateSpace n) ℂ (Bundle.Trivial M ℂ)) (x : M) :
    pseudodifferentialCLM hP u x = P (contMDiffMapEquiv _ M ℂ u) x := by
  rw [← contMDiffMapEquiv_apply, contMDiffMapEquiv_pseudodifferentialCLM]

/-- The identity acts on test functions as the identity. -/
@[simp]
theorem pseudodifferentialCLM_id
    (h : (LinearMap.id : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] _) ∈
      classicalPseudodifferentialOperators m) :
    pseudodifferentialCLM h = ContinuousLinearMap.id ℝ _ := by
  ext u x
  simp

/-- The action on test functions of a composite of pseudodifferential operators is the composite
of their actions. -/
theorem pseudodifferentialCLM_comp (hQ : Q ∈ classicalPseudodifferentialOperators m')
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQP : Q ∘ₗ P ∈ classicalPseudodifferentialOperators (m' + m) :=
      comp_mem_classicalPseudodifferentialOperators hQ hP) :
    pseudodifferentialCLM hQP = (pseudodifferentialCLM hQ).comp (pseudodifferentialCLM hP) := by
  ext u x
  simp

/-- The action on test functions of a sum of pseudodifferential operators is the sum of their
actions. -/
theorem pseudodifferentialCLM_add (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQ : Q ∈ classicalPseudodifferentialOperators m)
    (hPQ : P + Q ∈ classicalPseudodifferentialOperators m := add_mem hP hQ) :
    pseudodifferentialCLM hPQ = pseudodifferentialCLM hP + pseudodifferentialCLM hQ := by
  ext u x
  simp

section Dual

variable {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul ℝ G]

/-- The **transpose of a pseudodifferential operator** on the functionals on test functions: a
continuous linear functional `T` on the test functions of `M`, for instance a distribution density
on `M`, is sent to `T ∘ P`, as a continuous linear map for the topologies of uniform convergence on
compact sets of test functions. -/
def pseudodifferentialDualCLM (hP : P ∈ classicalPseudodifferentialOperators m) :
    (BundleTest 𝓘(ℝ, CoordinateSpace n) ℂ (Bundle.Trivial M ℂ) →L_c[ℝ] G) →L[ℝ]
      BundleTest 𝓘(ℝ, CoordinateSpace n) ℂ (Bundle.Trivial M ℂ) →L_c[ℝ] G :=
  (pseudodifferentialCLM hP).precompCompactConvergenceCLM G

@[simp]
theorem pseudodifferentialDualCLM_apply (hP : P ∈ classicalPseudodifferentialOperators m)
    (T : BundleTest 𝓘(ℝ, CoordinateSpace n) ℂ (Bundle.Trivial M ℂ) →L_c[ℝ] G)
    (u : BundleTest 𝓘(ℝ, CoordinateSpace n) ℂ (Bundle.Trivial M ℂ)) :
    pseudodifferentialDualCLM hP T u = T (pseudodifferentialCLM hP u) :=
  ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply _ _ _

/-- The transpose of the identity is the identity. -/
@[simp]
theorem pseudodifferentialDualCLM_id
    (h : (LinearMap.id : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] _) ∈
      classicalPseudodifferentialOperators m) :
    pseudodifferentialDualCLM (G := G) h = ContinuousLinearMap.id ℝ _ := by
  ext T u
  simp

/-- The transpose of a composite of pseudodifferential operators is the composite of their
transposes, in the reverse order. -/
theorem pseudodifferentialDualCLM_comp (hQ : Q ∈ classicalPseudodifferentialOperators m')
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQP : Q ∘ₗ P ∈ classicalPseudodifferentialOperators (m' + m) :=
      comp_mem_classicalPseudodifferentialOperators hQ hP) :
    pseudodifferentialDualCLM (G := G) hQP =
      (pseudodifferentialDualCLM hP).comp (pseudodifferentialDualCLM hQ) := by
  ext T u
  simp [pseudodifferentialCLM_comp hQ hP hQP]

/-- The transpose of a sum of pseudodifferential operators is the sum of their transposes. -/
theorem pseudodifferentialDualCLM_add (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQ : Q ∈ classicalPseudodifferentialOperators m)
    (hPQ : P + Q ∈ classicalPseudodifferentialOperators m := add_mem hP hQ) :
    pseudodifferentialDualCLM (G := G) hPQ =
      pseudodifferentialDualCLM hP + pseudodifferentialDualCLM hQ := by
  ext T u
  simp [pseudodifferentialCLM_add hP hQ hPQ]

end Dual

end TauCeti.BundleTest

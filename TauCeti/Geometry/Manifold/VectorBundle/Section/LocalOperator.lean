/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution
import TauCeti.Geometry.Manifold.DifferentialOperator.Peetre.Continuity

/-!
# Local operators on bundle tests and their transposes

Let `V` and `W` be smooth real vector bundles over a finite-dimensional Hausdorff boundaryless
Lindelöf manifold `M`, with `V` of finite rank. A linear map `P : Γ(V) → Γ(W)` between smooth
sections is *local* when `(P s) x = 0` whenever `s` vanishes near `x`; every differential operator
in Grothendieck's sense is local
(`TauCeti.differentialOperators_section_apply_eq_zero_of_eventuallyEq`). A local operator does not
enlarge closed supports, so it sends bundle tests to bundle tests, and it is continuous for the
test topologies (`TauCeti.BundleTest.localOperatorCLM`): on each fixed-compact support stage this
is the continuity of local operators for the compact derivative topologies
(`LinearMap.continuous_of_apply_eq_zero_of_eventuallyEq`), which needs no continuity assumption on
`P`.

Its transpose `T ↦ T ∘ P` (`TauCeti.BundleTest.localOperatorDualCLM`) acts on continuous linear
functionals on the bundle tests of `W`, for instance on the distributional sections of a bundle.
This is how differential operators act on distributions on manifolds: for a distributional section
`u` of a bundle, paired with tests through densities, `T ∘ P` is the action of the formal transpose
of `P` on `u`.

## Main declarations

* `TauCeti.tsupport_apply_subset_of_local`: a local operator does not enlarge closed supports.
* `TauCeti.BundleTest.localOperatorCLM`: a local operator acting on bundle tests, as a continuous
  linear map, with `TauCeti.BundleTest.localOperatorCLM_apply`.
* `TauCeti.BundleTest.localOperatorDualCLM`: its transpose on functionals on bundle tests.

## References

* J. Peetre, *Réctification à l'article « Une caractérisation abstraite des opérateurs
  différentiels »*, Math. Scand. 8 (1960), 116–120.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §6.3 (distributions on manifolds).
-/

public noncomputable section

open Bundle Set Filter TopologicalSpace ContMDiffSection
open scoped ContDiff Manifold Topology CompactConvergenceCLM

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [LindelofSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] [ContMDiffVectorBundle ∞ F' W I]
  {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [LindelofSpace M]
  [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] [ContMDiffVectorBundle ∞ F' W I] in
/-- A local operator does not enlarge closed supports. -/
theorem tsupport_apply_subset_of_local
    (hP : ∀ (s : Cₛ^∞⟮I; F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0)
    (s : Cₛ^∞⟮I; F, V⟯) : (P s).tsupport ⊆ s.tsupport :=
  ((P s).tsupport_subset_iff s.isClosed_tsupport).2 fun _ hx ↦ hP s _ <|
    mem_of_superset (s.isClosed_tsupport.isOpen_compl.mem_nhds hx) fun _ hy ↦
      s.eq_zero_of_notMem_tsupport hy

namespace BundleTest

/-- A **local operator acting on bundle tests.** A linear map `P : Γ(V) → Γ(W)` which is local,
that is `(P s) x = 0` whenever `s` vanishes near `x`, sends compactly supported sections to
compactly supported sections, and is continuous for the test topologies. -/
def localOperatorCLM (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯)
    (hP : ∀ (s : Cₛ^∞⟮I; F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0) :
    BundleTest I F V →L[ℝ] BundleTest I F' W where
  toLinearMap := (ofCompactlySupported I F' W).toLinearMap ∘ₗ
    (P.restrict fun s hs ↦ mem_compactlySupported.2 <|
      (mem_compactlySupported.1 hs).of_isClosed_subset (P s).isClosed_tsupport
        (tsupport_apply_subset_of_local hP s)) ∘ₗ
    (ofCompactlySupported I F V).symm.toLinearMap
  cont := by
    let := frameTopology (I := I) (n := ∞) (fun x : M ↦ trivializationAt F V x)
      (fun x ↦ ⟨_, (trivializationAt F V x).open_baseSet⟩) fun _ ↦ subset_rfl
    let := frameTopology (I := I) (n := ∞) (fun x : M ↦ trivializationAt F' W x)
      (fun x ↦ ⟨_, (trivializationAt F' W x).open_baseSet⟩) fun _ ↦ subset_rfl
    have hc : Continuous P := P.continuous_of_apply_eq_zero_of_eventuallyEq _ _ _ hP
      (fun x ↦ ⟨x, FiberBundle.mem_baseSet_trivializationAt' x⟩) _ _ fun _ ↦ subset_rfl
    refine (continuous_iff_continuous_comp _).2 fun K ↦ ?_
    -- On the stage of sections supported in `K`, the operator lands in the stage of `W`
    -- supported in `K`, continuously for the frame topologies.
    refine ((continuous_ofSupportedIn K).comp
      ((hc.comp continuous_subtypeVal).subtype_mk
        fun s ↦ mem_supportedIn.2 <|
          (tsupport_apply_subset_of_local hP s.val).trans (mem_supportedIn.1 s.property))).congr
      fun s ↦ ?_
    simp [LinearMap.restrict_apply, Subtype.ext_iff]

@[simp]
theorem localOperatorCLM_apply
    (hP : ∀ (s : Cₛ^∞⟮I; F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0)
    (s : BundleTest I F V) (x : M) :
    localOperatorCLM P hP s x = P ((ofCompactlySupported I F V).symm s).val x := by
  simp [localOperatorCLM, LinearMap.restrict_apply]

section Dual

variable {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul ℝ G]

/-- The **transpose of a local operator** on functionals on bundle tests: a continuous linear
functional `T` on the bundle tests of `W` is sent to `T ∘ P`, a functional on the bundle tests of
`V`, as a continuous linear map for the topologies of uniform convergence on compact sets of
tests. -/
def localOperatorDualCLM (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯)
    (hP : ∀ (s : Cₛ^∞⟮I; F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0) :
    (BundleTest I F' W →L_c[ℝ] G) →L[ℝ] BundleTest I F V →L_c[ℝ] G :=
  (localOperatorCLM P hP).precompCompactConvergenceCLM G

@[simp]
theorem localOperatorDualCLM_apply
    (hP : ∀ (s : Cₛ^∞⟮I; F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0)
    (T : BundleTest I F' W →L_c[ℝ] G) (s : BundleTest I F V) :
    localOperatorDualCLM P hP T s = T (localOperatorCLM P hP s) :=
  (rfl)

end Dual

end BundleTest

end TauCeti


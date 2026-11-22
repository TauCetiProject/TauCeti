/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Geometry.Manifold.VectorBundle.Section.Generic
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import TauCeti.Topology.VectorBundle.Trivialization
import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic

/-!
# Examples: regular sections avoiding prescribed points

The canonical real theorem applies to arbitrary compact complex bases through their underlying
real structure. These clients retain the actual section, its differentiability order, surjective
linearization at every zero, finite zero set and full avoidance conclusions. They include smooth
sections on the Riemann sphere, native `C¹` real bundles modelled on a complex line, and
order-zero, rank-zero and empty-base endpoints.
-/

open Bundle Function Set
open scoped Manifold ContDiff

-- Actual compact complex surface, with a complex line model not definitionally equal to ℂ.
example {S : Set (OnePoint ℂ)} (hS : S.Countable) :
    ∃ s : ContMDiffSection 𝓘(ℝ, ℂ) (Fin 1 → ℂ) ∞
        (Bundle.Trivial (OnePoint ℂ) (Fin 1 → ℂ)),
      (∀ x, s x = 0 → Surjective
        (TauCeti.sectionLinearization (F := Fin 1 → ℂ) 𝓘(ℝ, ℂ) id s x)) ∧
        {x | s x = 0}.Finite ∧ ∀ x ∈ S, s x ≠ 0 := by
  have hcomplex : IsManifold 𝓘(ℂ, ℂ) 1 (OnePoint ℂ) := inferInstance
  have := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero hcomplex
  apply TauCeti.exists_contMDiffSection_regular_finite_zero_forall_mem_ne_zero (X := ℂ) _ hS
  simp [Module.finrank_pi_fintype]

-- Point avoidance on the same actual compact surface retains smoothness and regular zeros.
example (x : OnePoint ℂ) :
    ∃ s : ContMDiffSection 𝓘(ℝ, ℂ) (Fin 1 → ℂ) ∞
        (Bundle.Trivial (OnePoint ℂ) (Fin 1 → ℂ)),
      (∀ y, s y = 0 → Surjective
        (TauCeti.sectionLinearization (F := Fin 1 → ℂ) 𝓘(ℝ, ℂ) id s y)) ∧
        {y | s y = 0}.Finite ∧ s x ≠ 0 := by
  have hcomplex : IsManifold 𝓘(ℂ, ℂ) 1 (OnePoint ℂ) := inferInstance
  have := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero hcomplex
  obtain ⟨s, hs, hZ, hx⟩ :=
    TauCeti.exists_contMDiffSection_regular_finite_zero_forall_mem_ne_zero
      (n := ∞) (X := ℂ) (F := Fin 1 → ℂ) (V := Bundle.Trivial (OnePoint ℂ) (Fin 1 → ℂ))
      (by simp [Module.finrank_pi_fintype]) (countable_singleton x)
  exact ⟨s, hs, hZ, hx x rfl⟩

-- Arbitrary smooth native line bundle on an arbitrary compact complex curve, not trivial data.
example {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) 1 X]
    {L : X → Type*} [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)]
    [∀ x, TopologicalSpace (L x)] [TopologicalSpace (TotalSpace (Fin 1 → ℂ) L)]
    [FiberBundle (Fin 1 → ℂ) L] [VectorBundle ℝ (Fin 1 → ℂ) L]
    [ContMDiffVectorBundle ∞ (Fin 1 → ℂ) L 𝓘(ℝ, ℂ)]
    {S : Set X} (hS : S.Countable) :
    ∃ s : ContMDiffSection 𝓘(ℝ, ℂ) (Fin 1 → ℂ) ∞ L,
      (∀ x, s x = 0 → Surjective
        (TauCeti.sectionLinearization (F := Fin 1 → ℂ) 𝓘(ℝ, ℂ) id s x)) ∧
        {x | s x = 0}.Finite ∧ ∀ x ∈ S, s x ≠ 0 := by
  have := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero
    ‹IsManifold 𝓘(ℂ, ℂ) 1 _›
  apply TauCeti.exists_contMDiffSection_regular_finite_zero_forall_mem_ne_zero (X := ℂ) _ hS
  simp [Module.finrank_pi_fintype]

-- Infinite indexing and complex scalars are permitted by the public spanning witness.
example (s : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) ℂ 0 (Bundle.Trivial ℂ ℂ)) (x : ℂ)
    (hspan : Submodule.span ℂ (range fun i ↦ s i x) = ⊤) : ∃ i, s i x ≠ 0 :=
  VectorBundle.exists_ne_zero_of_span_range_eq_top ℂ hspan

-- All complex base models and all matching nontrivial real fiber models remain available.
example {E X F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [TopologicalSpace X] [ChartedSpace E X]
    [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, E) 1 X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
    {L : X → Type*} [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)]
    [∀ x, TopologicalSpace (L x)] [TopologicalSpace (TotalSpace F L)]
    [FiberBundle F L] [VectorBundle ℝ F L] [ContMDiffVectorBundle ∞ F L 𝓘(ℝ, E)]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) {S : Set X} (hS : S.Countable) :
    ∃ s : ContMDiffSection 𝓘(ℝ, E) F ∞ L,
      (∀ x, s x = 0 → Surjective
        (TauCeti.sectionLinearization (F := F) 𝓘(ℝ, E) id s x)) ∧
        {x | s x = 0}.Finite ∧ ∀ x ∈ S, s x ≠ 0 := by
  have := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero ‹IsManifold 𝓘(ℂ, E) 1 X›
  exact TauCeti.exists_contMDiffSection_regular_finite_zero_forall_mem_ne_zero hdim hS

-- Native complex line subbundle from the geometric splitting, including its real smooth atlas.
example {E B F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [TopologicalSpace B] [ChartedSpace E B]
    [T2Space B] [CompactSpace B] [IsManifold 𝓘(ℂ, E) 1 B]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, TopologicalSpace (V x)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
    (hE : Module.finrank ℂ E = 1) {W : ∀ x, Submodule ℂ (V x)}
    (hL : TauCeti.HasLocalContMDiffSubbundleFrames 𝓘(ℝ, E) ∞ F (Fin 1) W)
    {S : Set B} (hS : S.Countable) :
    letI := TauCeti.subbundleTopology F (F' := Fin 1 → ℂ) W
    letI := hL.fiberBundle
    letI := hL.vectorBundle
    letI := VectorBundle.restrictScalars ℝ ℂ (Fin 1 → ℂ) fun x ↦ W x
    ∃ s : ContMDiffSection 𝓘(ℝ, E) (Fin 1 → ℂ) ∞ (fun x ↦ W x),
      (∀ x, s x = 0 → Surjective
        (TauCeti.sectionLinearization (F := Fin 1 → ℂ) (E := fun x ↦ W x) 𝓘(ℝ, E) id s x)) ∧
        {x | s x = 0}.Finite ∧ ∀ x ∈ S, s x ≠ 0 := by
  let := TauCeti.subbundleTopology F (F' := Fin 1 → ℂ) W
  let := hL.fiberBundle
  let := hL.vectorBundle
  let := VectorBundle.restrictScalars ℝ ℂ (Fin 1 → ℂ) fun x ↦ W x
  let := hL.contMDiffVectorBundle
  have := IsManifold.restrictScalars_of_ne_zero ∞ one_ne_zero ‹IsManifold 𝓘(ℂ, E) 1 B›
  apply TauCeti.exists_contMDiffSection_regular_finite_zero_forall_mem_ne_zero _ hS
  rw [finrank_real_of_complex, hE]
  simp [Module.finrank_pi_fintype]

/-! ## Finite-regularity and rank-zero endpoints -/

-- C¹ bundles with countable avoidance, retaining regularity and a finite zero set.
example {X M F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [TopologicalSpace M] [ChartedSpace X M]
    [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, X) 1 M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
    {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V 𝓘(ℝ, X)]
    (hdim : Module.finrank ℝ X = Module.finrank ℝ F) {S : Set M} (hS : S.Countable) :
    ∃ s : ContMDiffSection 𝓘(ℝ, X) F 1 V,
      (∀ x, s x = 0 → Surjective
        (TauCeti.sectionLinearization (F := F) 𝓘(ℝ, X) id s x)) ∧
        {x | s x = 0}.Finite ∧ ∀ x ∈ S, s x ≠ 0 := by
  exact TauCeti.exists_contMDiffSection_regular_finite_zero_forall_mem_ne_zero
    hdim hS le_rfl (by norm_num)

-- A C¹ real bundle modelled on a complex line: full countable avoidance.
example {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℂ, ℂ) 1 M]
    {L : M → Type*} [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)]
    [∀ x, TopologicalSpace (L x)] [TopologicalSpace (TotalSpace (Fin 1 → ℂ) L)]
    [FiberBundle (Fin 1 → ℂ) L] [VectorBundle ℝ (Fin 1 → ℂ) L]
    [ContMDiffVectorBundle 1 (Fin 1 → ℂ) L 𝓘(ℝ, ℂ)]
    {S : Set M} (hS : S.Countable) :
    ∃ s : ContMDiffSection 𝓘(ℝ, ℂ) (Fin 1 → ℂ) 1 L,
      (∀ x, s x = 0 → Surjective
        (TauCeti.sectionLinearization (F := Fin 1 → ℂ) 𝓘(ℝ, ℂ) id s x)) ∧
        {x | s x = 0}.Finite ∧ ∀ x ∈ S, s x ≠ 0 := by
  have := IsManifold.restrictScalars_of_ne_zero 1 one_ne_zero
    ‹IsManifold 𝓘(ℂ, ℂ) 1 M›
  apply TauCeti.exists_contMDiffSection_regular_finite_zero_forall_mem_ne_zero
    (n := 1) (X := ℂ) _ hS le_rfl (by norm_num)
  simp [Module.finrank_pi_fintype]

-- The actual point-avoidance conclusion under C¹, preserving regular and finite zeros.
example {X M F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [TopologicalSpace M] [ChartedSpace X M]
    [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, X) 1 M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F]
    {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V 𝓘(ℝ, X)]
    (hdim : Module.finrank ℝ X = Module.finrank ℝ F) (x : M) :
    ∃ s : ContMDiffSection 𝓘(ℝ, X) F 1 V,
      (∀ y, s y = 0 → Surjective
        (TauCeti.sectionLinearization (F := F) 𝓘(ℝ, X) id s y)) ∧
        {y | s y = 0}.Finite ∧ s x ≠ 0 := by
  obtain ⟨s, hr, hf, ha⟩ :=
    TauCeti.exists_contMDiffSection_regular_finite_zero_forall_mem_ne_zero
      (n := 1) (V := V) hdim (countable_singleton x) le_rfl (by norm_num)
  exact ⟨s, hr, hf, ha x rfl⟩

-- Negative index needs C¹ only; no finite-dimensionality of `X` or `F` is assumed.
example {X M F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [TopologicalSpace M] [ChartedSpace X M] [T2Space M] [CompactSpace M]
    [IsManifold 𝓘(ℝ, X) 1 M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V 𝓘(ℝ, X)]
    (hdim : Module.finrank ℝ X < Module.finrank ℝ F) :
    ∃ s : ContMDiffSection 𝓘(ℝ, X) F 1 V, ∀ x, s x ≠ 0 := by
  exact TauCeti.exists_contMDiffSection_forall_ne_zero_of_finrank_lt
    hdim le_rfl (by norm_num)

-- Spanning includes order zero, rank zero, corners and Empty without a chosen centre.
example {X H M F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [TopologicalSpace H] {I : ModelWithCorners ℝ X H}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
    [IsManifold I 0 M] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [Subsingleton F] {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 0 F V I] :
    ∃ (m : ℕ) (s : Fin m → ContMDiffSection I F 0 V),
      ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤ := by
  exact TauCeti.exists_fin_spanning_contMDiffSection (by norm_num)

example {X H M F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [TopologicalSpace H] {I : ModelWithCorners ℝ X H}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M] [IsEmpty M]
    [IsManifold I 0 M] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 0 F V I] :
    ∃ (m : ℕ) (s : Fin m → ContMDiffSection I F 0 V),
      ∀ x, Submodule.span ℝ (range fun i ↦ s i x) = ⊤ := by
  exact TauCeti.exists_fin_spanning_contMDiffSection (by norm_num)

-- Zero-dimensional regular-zero existence does not add a positive-rank assumption.
example {X M F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Subsingleton X] [TopologicalSpace M] [ChartedSpace X M]
    [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, X) 1 M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Subsingleton F]
    {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V 𝓘(ℝ, X)] :
    ∃ s : ContMDiffSection 𝓘(ℝ, X) F 1 V,
      (∀ x, s x = 0 → Surjective
        (TauCeti.sectionLinearization (F := F) 𝓘(ℝ, X) id s x)) ∧ {x | s x = 0}.Finite := by
  apply TauCeti.exists_contMDiffSection_regular_finite_zero_of_finrank_eq _ le_rfl (by norm_num)
  simp only [Module.finrank_eq_zero_of_subsingleton]

-- Rank zero cannot avoid even one actual point; the avoidance Nontrivial hypothesis has content.
example
    (s : ContMDiffSection 𝓘(ℝ, ℂ) (Fin 0 → ℝ) 1
      (Bundle.Trivial (OnePoint ℂ) (Fin 0 → ℝ))) : s (↑(0 : ℂ)) = 0 := by
  exact Subsingleton.elim _ _

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

The canonical real smooth theorem applies to arbitrary compact complex bases through their
underlying real smooth structure. These clients retain the actual smooth section, the surjective
linearization at every zero, finiteness of its zero set, and the full avoidance conclusions.
The concrete surface is the Riemann sphere, with native complex line model `Fin 1 → ℂ`.
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
      (X := ℂ) (F := Fin 1 → ℂ) (V := Bundle.Trivial (OnePoint ℂ) (Fin 1 → ℂ))
      (by simp [Module.finrank_pi_fintype]) (countable_singleton x)
  exact ⟨s, hs, hZ, hx x rfl⟩

-- A native real smooth bundle with complex line model on an arbitrary compact complex curve.
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

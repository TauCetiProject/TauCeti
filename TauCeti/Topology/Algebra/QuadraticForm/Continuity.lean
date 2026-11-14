/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Continuity of quadratic maps

A quadratic map on a finite module with the module topology is continuous into any
topological module. No invertibility assumption on two is needed: in finitely many generators,
the quadratic-map axioms express its values using continuous scalar multiplication and addition.
For any continuous quadratic map, its preserving endomorphisms form a closed set when the
codomain is Hausdorff.
-/

public section

/-- A quadratic map on a finite module with the module topology is continuous into any
topological module, including in characteristic two. -/
@[continuity, fun_prop]
theorem QuadraticMap.continuous
    {R M N : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [TopologicalSpace M] [IsModuleTopology R M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [ContinuousAdd N] [ContinuousSMul R N] (Q : QuadraticMap R M N) : Continuous Q := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  obtain ⟨B, hB⟩ := Q.exists_companion
  have : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
  let v (i : Fin n) := f (fun j => if i = j then 1 else 0)
  -- The quadratic-map axioms give continuity on every finite sum of generators.
  have hs (s : Finset (Fin n)) :
      Continuous (fun x : Fin n → R => Q (∑ i ∈ s, x i • v i)) := by
    induction s using Finset.induction_on with
    | empty => simpa using continuous_const
    | @insert i s hi ih =>
      have := IsModuleTopology.continuous_of_linearMap (B (v i))
      simp_rw [Finset.sum_insert hi, hB, Q.map_smul, map_smul, LinearMap.smul_apply]
      exact ((by fun_prop : Continuous fun x : Fin n → R => (x i * x i) • Q (v i)).add ih).add
        (by fun_prop)
  -- The coordinate surjection is a quotient map for the module topology.
  rw [(IsModuleTopology.isQuotientMap_of_surjective hf).continuous_iff]
  exact (hs Finset.univ).congr fun x => congrArg Q (f.pi_apply_eq_sum_univ x).symm

/-- Endomorphisms preserving a continuous quadratic map form a closed subset of the
endomorphism space when the codomain is Hausdorff. -/
theorem QuadraticMap.isClosed_setOfPred_forall_map_app
    {R M N : Type*} [CommSemiring R] [TopologicalSpace R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousSMul R M]
    [TopologicalSpace (Module.End R M)] [IsModuleTopology R (Module.End R M)]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N] [T2Space N]
    (Q : QuadraticMap R M N) (hQ : Continuous Q) :
    IsClosed {f : Module.End R M | ∀ x : M, Q (f x) = Q x} := by
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_eq
    (hQ.comp (IsModuleTopology.continuous_of_linearMap (LinearMap.applyₗ x))) continuous_const
